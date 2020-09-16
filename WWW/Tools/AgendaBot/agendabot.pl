#!/usr/bin/perl
#
# This IRC 'bot looks for lines of the form "agenda: URL" and tries to
# find a meeting agenda at that URL. If it succeeds, it prints the
# agenda on IRC in a form suitable for the Zakim 'bot.
#
# More documentation at the end in perlpod format.
#
#
# TODO: When given a -c option, agendabot loads all passwords into
# memory. It should either not keep them in memory permanently, or
# encrypt them.
#
# TODO: Fix information leak: Agendabot will extract an agenda from
# any resource it has a password for, even if the person asking for
# the agenda wouldn't be able to read that agenda himself.
# The only current protection is that Agendabot will only retrieve
# password-protected resources if asked on a server-local channel (one
# starting with "&"), and not if asked on a public channel (starting
# with "#") or in a private message.
#
# TODO: Judy's idea: after a meeting, defer remaining agenda items to
# the next meeting. (Or is that more something for Zakim?)
#
# TODO: If the nick is already in use, try again with a different one.
#
# TODO: Don't join a channel if there is another instance of AgendaBot
# already.
#
# TODO: Show the agenda and ask for confirmation before putting it in
# Zakim's format. (Vivien's idea.)
#
# TODO: Automatically part a channel after a certain period of
# inactivity?
#
# TODO: The list of security exceptions is searched with linear search.
# That's only fine if the list is short.
#
# TODO: Add a way to test the heuristic parsers without connecting to
# IRC.
#
# TODO: The associations of channels with mailing list archives should
# allow for channels on different IRC networks.
#
# TODO: Do more oparations that involve HTTP requests in the
# background.
#
# TODO: More intelligent and configurable $maxtries.
#
# TODO: Allow "... in the last week" instead of "in the last 1 weeks".
#
# TODO: Skip useless links. Use the anchor text instead of downloading
# and then looking for the subject.
#
# TODO: Automatically start looking for an agenda when Zakim joins the
# channel?
#
# Created: 2018-07-09
# Author: Bert Bos <bert@w3.org>
#
# Copyright © 2018-2020 World Wide Web Consortium, (Massachusetts Institute
# of Technology, European Research Consortium for Informatics and
# Mathematics, Keio University, Beihang). All Rights Reserved. This
# work is distributed under the W3C® Software License
# (http://www.w3.org/Consortium/Legal/2015/copyright-software-and-document)
# in the hope that it will be useful, but WITHOUT ANY WARRANTY;
# without even the implied warranty of MERCHANTABILITY or FITNESS FOR
# A PARTICULAR PURPOSE.

package AgendaBot;
use lib '.';
use parent 'My::BasicBot';
use strict;
use warnings;
use LWP;
use Getopt::Std;
use POSIX qw(strftime);
use Scalar::Util 'blessed';
use Term::ReadKey;		# To read a password without echoing
use utf8;
use DateTime;
use URI;
use HTML::Entities;
use POE;			# For OBJECT, ARG0 and ARG1

use constant HOME => 'https://www.w3.org/Tools/AgendaBot';
use constant MANUAL => 'https://www.w3.org/Tools/AgendaBot/manual.html';
use constant VERSION => '0.3';
use constant LIMIT => 20;	# Max # of downloads per day of archives


# Subroutines to try and recognize an agenda. The order is important:
# If several of them find agenda items, the first one to find more
# than one item is used. (This is because it is more common to find a
# bulleted list that is not an agenda than, e.g., "topic:" lines that
# are not agenda items.
my @parsers = (
  \&bb_agenda_parser,
  \&addison_agenda_parser,
  \&koalie_and_plh_agenda_parser,
  \&two_level_agenda_parser);


# init -- initialize some parameters
sub init($)
{
  my $self = shift;
  my $errmsg;

  $errmsg = $self->reload() and die "$errmsg\n";
  $self->{topics} = {};
  return 1;
}


# reload - reload configuration files, return error message or undef
sub reload($)
{
  my $self = shift;
  my $errmsg;

  if (($errmsg = $self->read_passwords_file())) {$self->log($errmsg);}
  elsif (($errmsg = $self->read_security_exceptions())) {$self->log($errmsg);}
  elsif (($errmsg = $self->read_mailing_lists())) {$self->log($errmsg);}
  return $errmsg;
}


# is_exception -- check if a channel may get this URI
sub is_exception($$$)
{
  my ($self, $channel, $uri) = @_;
  my @exceptions = @{$self->{exceptions} // []};

  # Find all URI prefixes that the channel may get. Check for each
  # prefix if it is a prefix of the given uri.
  #
  foreach my $u (grep s/^\Q$channel\E\t//, @exceptions) {
    $self->log("Security exception: $channel is allowed to get $uri");
    return 1 if $uri =~ /^$u/;
  }
  return 0;
}


# get -- get the contents of a file by its URL
sub get($$$)
{
  my ($self, $info, $uri) = @_;
  my $channel = $info->{channel};
  my ($ua, $res, $realm, $user, $password, $user_pass, $challenge, %passwords);

  $ua = LWP::UserAgent->new;
  $ua->agent(blessed($self) . '/' . VERSION);
  $ua->default_header('Accept' => 'text/*');
  $ua->timeout(10);
  $ua->env_proxy;

  $res = $ua->get($uri);

  if ($res->code == 401) {	# The resource requires authentication

    if ($channel !~ /^&/ &&	# Not a server-local channel
	! $self->is_exception($channel, $uri)) {
      $self->log("Refusing private page on public channel $channel: $uri");
      return (403, undef, undef);
    }

    # Check the authentication method, extract the realm.
    #
    $challenge = $res->header('WWW-Authenticate');
    if ($challenge !~ /(?:Basic|Digest) realm="(.*)"/i) {
      $self->log("$uri has an unknown authentication scheme: $challenge");
      return (401, undef, undef);
    }
    $realm = $1;

    # See if we know a password for this host and realm.
    #
    %passwords = %{$self->{passwords} // {}};
    $user_pass = $passwords{$res->base->host_port . "\t" . $realm};
    if (!defined $user_pass) {
      $self->log("No password known for $uri");
      return (401, undef, undef);
    }
    ($user, $password) = split /\t/, $user_pass;

    # Hand the login and password to $ua and try to get the URI again.
    #
    $ua->credentials($res->base->host_port, $realm, $user, $password);
    $res = $ua->get($uri);
  }

  $self->log("Code ".$res->code." on $uri");

  return $res->is_success
      ? ($res->code, $res->content_type, $res->decoded_content())
      : ($res->code, undef, undef);
}


# parse_and_print_agenda -- try to retrieve an agenda and print it on IRC
sub parse_and_print_agenda($$$)
{
  my ($self, $info, $uri) = @_;
  my $channel = $info->{channel};
  my $who = $info->{who};
  my @agenda = ();
  my ($code, $mediatype, $document);

  # Try to download the resource.
  #
  ($code, $mediatype, $document) = $self->get($info, $uri);
  return "$who, sorry, I don't have a password for $uri" if $code == 401;
  return "$who, sorry, the document at $uri is protected." if $code == 403;
  return "$who, sorry, $uri doesn't seem to exist." if $code == 404;
  return "$who, sorry, could not get $uri (code $code)." if !defined $document;

  # Try the parsers in order. Stop as soon as a parser returns an
  # agenda of two or more items. Otherwise use the first one that
  # returned one item.
  for my $parser (@parsers) {
    my @h = &$parser($mediatype, $document);
    @agenda = @h if scalar(@h) > 0;
    last if scalar(@h) > 1;
  }
  $self->log("Found ".($#agenda+1)." topics in $uri");
  return "$who, sorry, I did not recognize any agenda in $uri" if $#agenda==-1;

  # Print the agenda in Zakim's format.
  #
  $self->say({channel => $channel, body => "clear agenda"});
  $self->say({channel => $channel, body => "agenda+ " . $_})
      foreach (@agenda);

  return undef;
}


# get_subject_and_date -- get the subject and date from an archived message
sub get_subject_and_date($$)
{
  my ($self, $doc) = @_;
  my ($subject, $date) = ("", time); # Default is no subject and current time

  $subject = decode_entities($1)
      if $doc =~ /<meta name="Subject" content="(.*?)"/;
  # TODO: handle errors in new().
  $date = DateTime->new(year => $1, month => $2, day => $3)->epoch
      if $doc =~ /<meta name="Date" content="(\d+)-(\d\d)-(\d\d)/;

  return ($subject, $date);
}


# find_links -- return a list of all links in a document under a given base
sub find_links()
{
  my ($self, $doc, $base) = @_;
  my @urls;

  $doc =~ s/<!--.*?-->//g;	# Remove comments
  $base =~ s/[^\/]+$//;		# Remove everything after the last "/"
  while ($doc =~ /<a\b[^>]+\bhref\s*=\s*['"]([^'"]*)/g) {
    my $url = URI->new_abs($1, $base)->canonical->as_string;
    $url =~ s/#.*//;		# Remove fragments
    # Only keep URLs with $base as prefix, that end in "/" or ".html",
    # and that do not end in "/thread.html", "/author.html" or
    # "/subject.html".
    push @urls, $url if $url =~ /^\Q$base\E/ && $url =~ /(?:\.html|\/)$/ &&
	$url !~ /\/(?:thread|author|subject)\.html$/;
  }
  return @urls;
}


# find_agenda_process -- find an agenda in recent email (background process)
sub find_agenda_process($$$$$)
{
  my ($body, $self, $info, $lists, $period) = @_;
  my @urls = split(/ /, $lists);
  my $channel = $info->{channel};
  my (@agenda, $url, $oldest, %seen);
  my ($tries, $maxtries) = (0, LIMIT); # Max downloads if $period is "1 day"

  if ($period =~ /(\d+) day/) {$maxtries *= $1; $oldest = time - 60*60*24*$1;}
  elsif ($period =~ /(\d+) week/) {$maxtries *= 7*$1; $oldest = 60*60*24*7*$1;}
  else {print STDERR "Bug! find_agenda_process(... \"$period\")\n"; return;}

  $seen{$_} = 1 foreach @urls;
  while (scalar(@agenda) < 2 && @urls && $tries++ < $maxtries) {
    $url = shift @urls;
    my ($code, $mediatype, $document) = $self->get($info, $url);
    next if $code != 200;
    my ($subject, $date) = $self->get_subject_and_date($document);
    next if $date < $oldest;
    # Add all links from $document that are under $url and not already seen.
    unshift @urls, grep {!$seen{$_}++} $self->find_links($document, $url);
    next if $subject !~ /\bagenda\b/i;
    for my $parser (@parsers) {
      my @h = &$parser($mediatype, $document);
      if (scalar(@h) > 1) {@agenda = @h; last;}
    }
  }

  if (scalar(@agenda) > 1) {
    print STDERR "Found agenda with ".scalar(@agenda)." topics for $channel\n";
    print "$channel\t(\t$url\n";
    print "$channel\t-\t$_\n" foreach @agenda;
  # } elsif ($tries >= $maxtries) {
  #   print "$channel\t....
  } else {
    print STDERR "Found no agenda for $channel in $period\n";
    print "$channel\t)\n";
  }
}


# handle_find_agenda_results -- handle lines printed by find_agenda_process
sub handle_find_agenda_results
{
  my ($self, $body, $wheel_id) = @_[OBJECT, ARG0, ARG1];

  # Lines are of the form "CHANNEL<tab>C..." when C = "(", "-" or ")".
  chomp $body;
  if ($body =~ /^([^\t]+)\t\(\t(.*)/) {
    $self->say({channel => $1, body => "agenda: $2"});
    $self->say({channel => $1, body => "clear agenda"});
  } elsif ($body =~ /^([^\t]+)\t-\t(.*)/) {
    $self->say({channel => $1, body => "agenda+ $2"});
  } elsif ($body =~ /^([^\t]+)\t\)/) {
    $self->say({channel=>$1, body=>"Sorry, I did not find an agenda."});
  }
}


# find_agenda -- look for an agenda in recent mail messages and parse it
sub find_agenda($$$)
{
  my ($self, $info, $period) = @_;
  my $channel = $info->{channel};	# "#channel" or "msg"
  my $lists = $self->{mailing_lists}->{$channel};
  my $me = $self->nick();		# Our own name

  return "sorry, I don't know which mailing list is associated with this "
      . "channel. Try \"$me, help this is\"." if !defined $lists;

  # If there is already a process running, kill it.
  $self->{find_agenda_process}->kill() if defined $self->{find_agenda_process};

  # Start a background process.
  $self->{find_agenda_process} =
      $self->forkit({run => \&find_agenda_process,
		     handler => "handle_find_agenda_results",
		     channel => $channel,
		     arguments => [$self, $info, $lists, $period]});

  $self->log("Looking for an agenda for $channel in the background");
  return "OK. This may take a minute...";
}


# find_topics_process -- look for agenda+ in recent mail subjects
sub find_topics_process($$$$$)
{
  my ($body, $self, $info, $lists, $period) = @_;
  my @urls = split(/ /, $lists);
  my $channel = $info->{channel};
  my (@agenda, $url, $oldest, %seen);
  my ($tries, $maxtries) = (0, LIMIT); # Max downloads if $period is "1 day"

  if ($period =~ /(\d+) day/) {$maxtries *= $1; $oldest = time - 60*60*24*$1;}
  elsif ($period =~ /(\d+) week/) {$maxtries *= 7*$1; $oldest = 60*60*24*7*$1;}
  else {print STDERR "Bug! find_topics_process(... \"$period\")\n"; return;}

  print "$channel\t(\n";	# Signal the start of the array
  $seen{$_} = 1 foreach @urls;
  while (@urls && $tries++ < $maxtries) {
    $url = shift @urls;
    my ($code, $mediatype, $document) = $self->get($info, $url);
    next if $code != 200;
    my ($subject, $date) = $self->get_subject_and_date($document);
    next if $date < $oldest;
    # Add all links from $document that are under $url and not already seen.
    unshift @urls, grep {!$seen{$_}++} $self->find_links($document, $url);
    print "$channel\t-\t$1\n"
	if $subject !~ /^Re:/i && $subject =~ /\bagenda\+\s*(.*)/i;
  }
  print "$channel\t)\n";	# Signal the end of the array
}


# handle_find_topics_results -- handle lines printed by find_topics_process
sub handle_find_topics_results
{
  my ($self, $body, $wheel_id) = @_[OBJECT, ARG0, ARG1];
  my ($n, $channel);

  # Lines are of the form "CHANNEL<tab>C..." where C is "(", "-" or ")"
  chomp $body;
  if ($body =~ /^([^\t]+)\t\(/) { # Signals the start of the array
    $self->{topics}->{$1} = [];	  # Initalize the list of topics
  } elsif ($body =~ /^([^\t]+)\t-\t(.*)/) {
    push @{$self->{topics}->{$1}}, $2;
  } elsif ($body =~ /^([^\t]+)\t\)/) { # Signals the end of the array
    $channel = $1;
    $self->{topics_time}->{$channel} = time; # Add a time stamp
    $n = scalar(@{$self->{topics}->{$channel}});
    if ($n == 0) {
      delete $self->{topics}->{$channel};
      $self->say({channel => $channel,
		  body => "Sorry, I did not find any message with "
		      . "\"agenda+\" in the subject."});
    } elsif ($n == 1) {
      $self->say({channel => $channel, body => "I found 1 topic:"});
      $self->say({channel => $channel,
		  body => "1) ".$self->{topics}->{$channel}->[0]});
    } else {
      $self->say({channel => $channel, body => "I found $n topics:"});
      my $i = 1; $self->say({channel => $channel, body => $i++ . ") $_"})
		     foreach @{$self->{topics}->{$channel}};
    }
  }
}


# find_topics -- look for agenda+ in recent mail subjects
sub find_topics($$$)
{
  my ($self, $info, $period) = @_;
  my $channel = $info->{channel};	# "#channel" or "msg"
  my $lists = $self->{mailing_lists}->{$channel};
  my $me = $self->nick();		# Our own name

  # return "sorry, not yet implemented.";

  return "sorry, I don't know which mailing list is associated with this "
      . "channel. Try \"$me, help this is\"." if !defined $lists;

  # If there is a process running for $channel, kill it.
  $self->{find_topics_process}->kill() if defined $self->{find_topics_process};

  # Start a background process.
  $self->{find_topics_process} =
      $self->forkit({run => \&find_topics_process,
		     handler => "handle_find_topics_results",
		     channel => $channel,
		     arguments => [$self, $info, $lists, $period]});

  $self->log("Looking for agenda topics for $channel in the background");
  return "OK. This may take a minute...";
}


# accept_topics -- turn the found topics into an agenda
sub accept_topics($$)
{
  my ($self, $channel) = @_;
  my $me = $self->nick();		# Our own name

  return "Sorry, I haven't found any suggested agenda topics. "
      . "Please use \"$me, suggest agenda\" if you want me to look for some."
      if !defined $self->{topics}->{$channel};
  return "Sorry, I haven't looked for topics in the last hour. "
      . "Please use \"$me, suggest agenda\" if you want me to look for some."
      if $self->{topics_time} < time - 3600;

  $self->say({channel => $channel, body => "clear agenda"});
  $self->say({channel => $channel, body => "agenda+ $_"})
      foreach @{$self->{topics}->{$channel}};
  return undef;
}


sub find_mailing_list_archive($$$)
{
  my ($self, $info, $list_name) = @_;

  foreach my $base (("https://lists.w3.org/Archives/Public/",
		     "https://lists.w3.org/Archives/Member/",
		     "https://lists.w3.org/Archives/Team/",
		     "https://lists.w3.org/Archives/Public/public-",
		     "https://lists.w3.org/Archives/Public/www-",
		     "https://lists.w3.org/Archives/Member/member-",
		     "https://lists.w3.org/Archives/Member/w3c-",
		     "https://lists.w3.org/Archives/Team/team-",
		     "https://lists.w3.org/Archives/Team/w3t-")) {
    my $url = "$base$list_name/";
    my ($code, $mediatype, $document) = $self->get($info, $url);
    return $url if $code == 200; # TODO: check that type is HTML
  }

  return $list_name;		# Return the input if no archive found
}


# write_mailing_list_associations -- write the associations to file
sub write_mailing_list_associations($)
{
  my ($self) = @_;

  # Try to write the associations to file.
  #
  my %assoc = %{$self->{mailing_lists}};
  open my $fh, ">", $self->{mailing_lists_file} or return 0;
  print $fh $_, "\t", $assoc{$_}, "\n" foreach keys %assoc;
  close $fh;
  return 1;
}


# associate_mailing_lists -- define the mail archives to search in
sub associate_mailing_lists($$$)
{
  my ($self, $info, $channel, $lists) = @_;
  my ($urls, $sep) = ("", "");

  # Split the list of mailing lists and, if they are not already URLs,
  # try to find their URLs. Concatenate the URLs. If no URL could be
  # found for one of the mailing list names, return an error message.
  #
  foreach my $x (split(/\s*,\*|\s+and\s+/i, $lists)) {
    $x = $self->find_mailing_list_archive($info, $x) if $x !~ /^https?:\/\//i;
    return "I could not find (or not read) the archive for $x."
	if $x !~ /^https?:\/\//i;
    $urls .= $sep . $x;
    $sep = " ";
  }

  # Store the associations.
  #
  $self->{mailing_lists}->{$channel} = $urls;
  $self->log("New association: $channel -> $urls");

  # Try to write the associations to file.
  #
  my $result = $self->write_mailing_list_associations;
  $self->log("Writing to $self->{mailing_lists_file} failed") if !$result;
  return "I could not write a file. The new mailing list association "
      . "will be lost when I am restarted. Sorry." if !$result;
  return "OK, using $urls";
}


# forget_mailing_lists -- remove the mail archives to search in
sub forget_mailing_lists($$)
{
  my ($self, $channel) = @_;
  my $urls = $self->{mailing_lists}->{$channel};

  return "I already have no mailing list for this channel." if !defined $urls;

  # Remove the association.
  #
  delete $self->{mailing_lists}->{$channel};
  $self->log("Removed associations for $channel");

  # Write current associations to file.
  #
  my $result = $self->write_mailing_list_associations;
  $self->log("Writing to $self->{mailing_lists_file} failed") if !$result;
  return "I could not write a file. The new mailing list association "
      . "will be lost when I am restarted. Sorry." if !$result;
  return "OK, I removed the mailing list" . ($urls =~ / / ? "s." : ".");
}


# status -- display the associated mailing list(s)
sub status($$)
{
  my ($self, $channel) = @_;
  my $urls = $self->{mailing_lists}->{$channel};

  return "I know no mailing list for this channel." if !defined $urls;
  return "the mailing list for this channel is $urls" if $urls !~ / /;
  return "the mailing lists for this channel are " . ($urls =~ s/ /, /gr );
}


# invited -- handle an invitation to a channel
sub invited($$)
{
  my ($self, $info) = @_;
  my $who = $info->{who};
  my $raw_nick = $info->{raw_nick};
  my $channel = $info->{channel};

  $self->log("Invited by $who ($raw_nick) to $channel");
  $self->join_channel($channel);
}


# said -- handle a message
sub said($$)
{
  my ($self, $info) = @_;
  my $who = $info->{who};		# Nick (without the "!domain" part)
  my $text = $info->{body};		# What Nick said
  my $channel = $info->{channel};	# "#channel" or "msg"
  my $me = $self->nick();		# Our own name
  my $addressed = $info->{address};	# Defined if we're personally addressed

  # "Agenda:" does not need to be addressed to us.
  return $self->parse_and_print_agenda($info, $1)
      if $text =~ /^agenda\s*:\s*(.+)$/i;

  # We don't handle other text unless it is addressed to us.
  return $self->SUPER::said($info)
      if (!$addressed);

  # Remove the optional initial "please" and final period.
  $text =~ s/^please\s*,?\s*//i;
  $text =~ s/\s*\.\s*$//;

  return $self->part_channel($channel), undef # undef -> no reply
      if $text =~ /^bye$/i;

  return $self->reload() // "configuration files have been reloaded."
      if $text =~ /^reload$/i;

  return $self->find_agenda($info, $1 // "7 days")
      if $text =~ /^(?:find|search(?:\s+for)?|look\s+for)\s+
      	           (?:an\s+|the\s+)?agenda
		   (?:\s+(?:since|(?:in\s+)(?:the\s+)?last)\s+
		    (\d+\s+days?|\d+\s+weeks?))?$/xi;

  return $self->find_topics($info, $1 // "7 days")
      if $text =~ /^(?:suggest|propose)\s+
      	       	   (?:an\s+|the\s+)?(?:agenda|agenda\s+topics|topics)
		   (?:\s+(?:since|(?:in\s+)(?:the\s+)?last)\s+
		    (\d+\s+days?|\d+\s+weeks?))?$/xi ||
         $text =~ /^(?:since|(?:in\s+)?(?:the\s+)?last)\s+
	       	   (\d+\s+days?|\d+\s+weeks?)$/xi;

  return $self->accept_topics($channel)
      if $text =~ /^(?:accept|confirm)(?:\s+the|\s+this)?(?:agenda)?/i;

  return $self->associate_mailing_lists($info, $channel, $1)
      if $text =~ /^this\s+is\s+
      	       	   ([^\s,]+(?:(?:\s*,\s*(?:and\s+)?|\s+and\s+)[^\s,])*)$/xi;

  return $self->forget_mailing_lists($channel)
      if $text =~ /^forget(?:\s+(?:the\s+)?(?:mailing\s+)?lists?)?$/i;

  return $self->status($channel)
      if $text =~ /^(?:status|info)\s*\??$/i;

  return $self->help($info)
      if $text =~ /^help/i;

  return "Sorry, I don't understand \"$text\". Try \"help\"."
      if $channel eq 'msg';	# Omit "$me" in a private channel.

  return "sorry, I don't understand \"$text\". Try \"$me, help\".";
}


# help -- handle an "agendabot, help" message
sub help($$)
{
  my ($self, $info) = @_;
  my $me = $self->nick();		# Our own name
  my $text = $info->{body};		# What Nick said

  $text =~ s/^help\s*//;

  return "you can invite me to a channel with \"/invite $me\"."
      if $text =~ /^\/?invite/;

  return "if you say \"agenda: some-URL\", I will try and extract an "
      . "agenda for Zakim from that URL."
      if $text =~ /^agenda:?/i;

  return "if you say \"$me, find agenda\", I will scan the mailing list "
      . "for a message that contains an agenda. I also understand "
      . "\"search\", \"search for\" and \"look for\". If I should "
      . "look for messages older than 1 week, add the number of days "
      . "or weeks, e.g.: \"since 2 weeks\", \"in the last 10 days\"."
      if $text =~ /^find|search|look/i;

  return "if you say \"$me, suggest agenda\" (or \"$me, propose topics\" "
      . "or some mix of that), I will scan the mailing list for "
      . "messages with a subject of \"agenda+ ...topic\" and present "
      . "a list. If I need to look also for messages older than 1 week, "
      . "add the number of days or weeks, e.g.: \"since 3 weeks\", "
      . "\"in the last 21 days\". To turn my list into an agenda, say "
      . "\"$me, accept\". (See \"$me, help accept\".)"
      if $text =~ /^suggest|propose/i;

  return "if you say \"$me, accept\" (or \"confirm\" or \"accept agenda\" "
      . "or \"confirm this agenda\"), I will print the agenda topics "
      . "that I found when you said \"$me, suggest agenda\" in the form "
      . "of an agenda that Zakim understands. Note: This only works "
      . "if I suggested topics less than an hour ago."
      if $text =~ /^accept|confirm/i;

  return "if you say \"$me, this is xyz\", I will remember the "
      . "mailing list \"xyz\" (or \"public-xyz\", \"www-xyz\", "
      . "\"member-xyz\", \"w3c-xyz\" or \"team-xyz\" or "
      . "\"w3t-xyz\", whichever "
      . "I can find and read) and use it to search for agendas. "
      . "You can also give the URL: \"$me this "
      . "is https://lists.w3.org/Archives/Public/public-xyz/\". "
      . "Multiple lists is also possible. Just separate the names "
      . "or URLs with commas or with the word \"and\"."
      if $text =~ /^this\s+is/i;

  return "if you say \"$me, forget mailing list\" (or \"forget the "
      . "mailing lists\"), I will no longer use any mailing lists to "
      . "search for agendas. The \"find\" and \"suggest\" commands "
      . "will no longer work (but \"agenda:\" still does). Use the "
      . "\"this is\" command to associate a new mailing list."
      if $text =~ /^forget/i;

  return "if you say \"$me, status?\" (or \"$me, info\"), I will "
      . "show the URL of the mailing list archive where I look "
      . "for agendas."
      if $text =~ /^status|info/i;

  return "if you say \$me, reload\", I will re-read my configuration "
      . "files. This is only useful if they changed, of course."
      if $text =~ /^reload/i;

  return "if you say \"$me, bye\", I will leave this channel. "
      . "I will continue to remember any associated mailing lists and "
      . "suggested agenda topics, in case you /invite me back."
      if $text =~ /^bye/i;

  return "I am an instance of " . blessed($self) . " " . VERSION . ". "
      . "For detailed help, type \"help COMMAND\", where COMMAND is "
      . "one of invite, agenda, find, suggest, accept, "
      . "this is, forget, status, reload or bye. Or go to " . MANUAL;
}


# connected -- log a successful connection
sub connected($)
{
  my ($self) = @_;

  $self->log("Connected to " . $self->server());
}


# log -- print a message to STDERR, but only if -v (verbose) was specified
sub log
{
  my ($self, @messages) = @_;
  my $now = strftime "%Y-%m-%dT%H:%M:%SZ", gmtime;

  # Prefix all log lines with the current time.
  #
  $self->SUPER::log(map($now.' '.$_, @messages)) if $self->{'verbose'};
}


# read_passwords_file -- read passwords from file, return error msg or undef
sub read_passwords_file($)
{
  my $self = shift;
  my (%passwords, $fh);
  my $path = $self->{passwords_file};

  return undef if !defined $path; # No file to read, not an error

  # Each line must be HOST:PORT\tREALM\tLOGIN\tPASSWORD. Empty lines
  # and lines that start with "#" are ignored.
  #
  # TODO: Can there be tabs in any of these fields?
  #
  open $fh, "<", $path or return "$path: cannot be opened.";
  while (<$fh>) {
    if (/^#/) {}		# Comment line
    elsif (/^\s*$/) {}		# Empty line
    elsif (/^(.*\t.*)\t(.*\t.*)$/) {$passwords{$1} = $2;}
    else {return "$path:$.: Syntax error: line does not have four fields.";}
  }
  close $fh;
  $self->{passwords} = \%passwords;
  return undef;			# No error
}


# read_security_exceptions -- read channels that may read protected agendas
sub read_security_exceptions($)
{
  my $self = shift;
  my ($mime_type, $document, $code, $uri, @exceptions);
  my $info = {channel=>'&'};	# Simulate a server-local channel

  $uri = $self->{security_exceptions_uri} or return; # Nothing to read, OK

  ($code, $mime_type, $document) = $self->get($info, $uri);
  return "sorry, I don't have a password for $uri" if $code == 401;
  return "sorry, the document at $uri is protected." if $code == 403;
  return "sorry, $uri doesn't seem to exist." if $code == 404;
  return "sorry, I could not get $uri (code $code)." if !defined $document;

  # The document must be plain text, each line with tab-separated fields:
  # CHANNEL\tURL-PREFIX
  #
  return "sorry, $uri is not a text file." if $mime_type ne 'text/plain';
  foreach (split /\r?\n/, $document) {
    if (/^#\s+/) {}		# Comment line
    elsif (/^\s*$/) {}		# Empty line
    elsif (/^([^\t]*\t[^\t]*)$/) {push @exceptions, $1;}
    else {return "sorry, $uri does not have the correct syntax.";}
  }
  $self->{exceptions} = \@exceptions;
  return;			# No error message
}


# read_mailing_lists -- read the associations channel -> mailing lists
sub read_mailing_lists($)
{
  my ($self) = @_;
  my $path = $self->{mailing_lists_file};
  my ($fh, %assoc);

  return "Bug: No file defined for storing mailing list associations."
      if !defined $path;

  # Open $path, if it exists. Each line consists of a channel name, a
  # tab and a space-separated list of URLs. Empty lines are
  # ignored. Lines that consist of a "#" that is not followed by a
  # letter or digit are comment lines and are also ignored.
  #
  if (open $fh, "<", $path) {
    while (<$fh>) {
      chomp;
      if (/^$/ || /^#$/ || /^#[^a-zA-Z0-9_-]/) {
	next;
      } elsif (/^([#&][^\t]+)\t(.*)$/) {
	$assoc{$1} = $2;
      } else {
	return "$path:$.: Syntax error: line does not have a channel name and URL(s)."
      }
    }
    close $fh;
  }
  $self->{mailing_lists} = \%assoc;
  $self->log("Restore association: $_ -> " . $self->{mailing_lists}->{$_})
      foreach (keys %{$self->{mailing_lists}});
  return undef;			# No errors
}


# html_to_text -- remove tags and expand charactet entities
sub html_to_text($)
{
  return decode_entities($_[0] =~ s/<[^>]*>//gr);
}


# The following subroutines are parsers that try to find a meeting
# agenda in a given text string. Each parser implements a different
# style of writing an agenda. They return an array in which each item
# is an agenda topic. An empty array means no agenda was found.
#
# The routines are not meant as methods, i.e., they don't expect $self
# as their first argument.
#
# All the parsers are listed in the array @parsers, so they can be
# tried one by one (see parse_and_print_agenda() above).


# bb_agenda_parser -- find an agenda written in Bert's agenda style
sub bb_agenda_parser($$)
{
  my ($mediatype, $document) = @_;
  my @agenda = ();

  # Agenda topics have a number and are underlined, e.g.:
  #
  # 1. Welcome
  # ----------
  #
  $document = html_to_text($document) if $mediatype =~ /html|xml/;
  push @agenda, $1 while $document =~ /^[ \t]*[0-9]+.[ \t]*(.+)\r?\n----/mg;
  return @agenda;
}


# addison_agenda_parser -- find an agenda in Addison Phillips' style
sub addison_agenda_parser($$)
{
  my ($mediatype, $document) = @_;
  my @agenda = ();

  # The agenda looks like:
  #
  # ==== AGENDA ====
  # Topic: AOB?
  # Topic: Radar
  #
  $document = html_to_text($document) if $mediatype =~ /html|xml/;
  return () if $document !~ /==\h*AGENDA\h*==/i;
  push @agenda, $1 while $document =~ /^\h*Topic\h*:\h*(.+)/mgi;
  return @agenda;
}


# koalie_and_plh_agenda_parser -- find an agenda in Coralie's/Philippe's style
sub koalie_and_plh_agenda_parser($$)
{
  my ($mediatype, $document) = @_;
  my @agenda;

  # The agenda already uses Zakim's format, i.e., topics are prefixed
  # with "agenda+":
  #
  # agenda+ Roundtable
  # agenda+ TPAC registration
  #
  $document = html_to_text($document) if $mediatype =~ /html|xml/;
  push @agenda, $1 while $document =~ /^\h*agenda\+\h+(.*)/mgi;
  return @agenda;
}


# two_level_agenda_parser -- find an agenda in the style of Axel Polleres
sub two_level_agenda_parser($$)
{
  my ($mediatype, $doc) = @_;
  my @agenda;
  my $i = 10000;		# Bigger than any expected indent
  my $delim;

  # Topics and subtopics with various markers.
  #
  #     1) Roll call/self-introductions,
  #        * ask for self introductions on the wiki....
  #        * ... clarify how to register
  #     2) Report on the workshop that initiated the group
  # or:
  #     * review Action items
  #     * concrete topics per day:
  #       1) fix call-details for future calls
  #       2) discuss F2F at MyData, how can we reach out broader?
  #
  return () if $doc !~ /\bAgenda\b/i;
  $doc = html_to_text($doc) if $mediatype =~ /html|xml/;

  # Store the least indented marker in $delim, if any.
  #
  foreach my $d (qr/\d+\)/, qr/\d+\./, qr/\*/, qr/-/, qr/•/, qr/◦/, qr/⁃/) {
    if ($doc =~ /^(\h*)$d\h/m && length $1 < $i) {$i = length $1; $delim = $d}
  }
  return () if !defined $delim;
  push @agenda, $1 while $doc =~ /^\h*$delim\h+(.*)/mg;
  return @agenda;
}



# Main body

my (%opts, $ssl, $user, $password, $host, $port, %passwords);

$Getopt::Std::STANDARD_HELP_VERSION = 1;
getopts('c:e:m:n:N:v', \%opts) or die "Try --help\n";
die "Usage: $0 [options] [--help] irc[s]://server...\n" if $#ARGV != 0;

# The single argument must be an IRC-URL.
#
$ARGV[0] =~ m/^(ircs?):\/\/(?:([^:]+):([^@]+)?@)?([^:\/#?]+)(?::([^\/]*))?/i or
    die "Argument must be a URI starting with `irc:' or `ircs:'\n";
$ssl = $1 eq 'ircs';
$user = $2 =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/egr if defined $2;
$password = $3 =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/egr if defined $3;
$host = $4;
$port = $5 // ($ssl ? 6697 : 6667);
# TODO: Do something with any passed channel name
# TODO: Do something with other parameters, such as a key
if (defined $user && !defined $password) {
  print "Password for user \"$user\": ";
  ReadMode('noecho');
  $password = ReadLine(0);
  ReadMode('restore');
  print "\n";
}

my $bot = AgendaBot->new(
  server => $host,
  port => $port,
  ssl => $ssl,
  username => $user,
  password => $password,
  nick => $opts{'n'} // 'agendabot',
  name => $opts{'N'} // 'AgendaBot '.VERSION.' '.HOME,
  passwords_file => $opts{'c'},
  security_exceptions_uri => $opts{'e'},
  verbose => defined $opts{'v'},
  mailing_lists_file => $opts{'m'} // 'agendabot.assoc');

$bot->run();




=head1 NAME

agendabot - IRC 'bot that gets a meeting agenda from a URL

=head1 SYNOPSIS

agendabot [-n I<nick>] [-N I<name>] [-c I<passwordfile>] [-e I<URL>]
[-m I<mailing-list-file>] [-v] I<URL>

=head1 DESCRIPTION

agendabot is an IRC 'bot. It connects to the IRC server given by the
URL (e.g., "irc://irc.example.org/"), waits until it is /invite'd to
one or more channels and then watches those channels for lines of the
form

 agenda: URL

(where URL is some URL) and tries to find a meeting agenda at that
URL. If it succeeds in finding an agenda, it prints it on IRC in a
form suitable for the Zakim 'bot, i.e., it prints something like:

 clear agenda
 agenda+ TOPIC1
 agenda+ TOPIC2

It tries various parsers in turn to read the document and uses the
results of the parser that recognized the most agenda topics. (See
L</"Agenda formats"> below.)

=head2 Specifying the IRC server

The I<URL> argument is a URL that specifies the server to connect to.
It must be of one of the following forms:

=over

=item 1.

irc://I<server>/I<other_text>

=item 2.

irc://I<server>:I<port>/I<other_text>

=item 3.

irc://I<username>:I<password>@I<server>/I<other_text>

=item 4.

irc://I<username>:I<password>@I<server>:I<port>/I<other_text>

=item 5.

ircs://I<server>/I<other_text>

=item 6.

ircs://I<server>:I<port>/I<other_text>

=item 7.

ircs://I<username>:I<password>@I<server>/I<other_text>

=item 8.

ircs://I<username>:I<password>@I<server>:I<port>/I<other_text>

=back

The I<other_text>, if not empty, is ignored, i.e., if the text
contains a channel name, agendabot does not automatically join that
channel.

The prefix "ircs" indicates that the server uses SSL. The I<port>, if
omitted, defaults to 6667 (for "irc") or 6697 (for "ircs").

If the server requires a username and password, they can be be
inserted before the server name, separated by a colon and ending with
an at sign.

If username is given, but the passord is left empty, agendabot will
prompt for a password. This is useful to avoid that the password is
visible in the list of running processes or that somebody can read it
over your shoulder while you type the command.

Note that many characters in the username or password must be
URL-escaped. E.g., a "@" must be written as "%40", ":" must be written
as "%3a", "/" as "%2f", etc.

=head2 IRC commands

For more details about the commands Agendabot understands on IRC, see
the manual, or use the "agendabot, help" command on IRC. Here is a
brief list:

=over

=item "/invite agendabot"

When AgendaBot is invited to a channel, it tries to join that channel.

=item" agenda: I<URL>"

Makes agendabot try and retrieve the URL, parse the result to try and
find an agenda, and print that agenda on IRC in the right format for
Zakim 'bot. AgendaBot prints an error message if it fails to find an
agenda.

=item "agendabot, bye"

Tells AgendaBot to leave the current channel.

=item "agendabot, help" and "agendabot help I<command>"

Ask AgendaBot to give a brief description of itself. To get
information about a specific command, such as "find", type "agendabot,
help find".

=item "agendabot, reload"

If Agendabot was started with configuration files (options B<-c> and
B<-e>), this asks Agendabot to read those files again.

=item "agendabot, find agenda"

Ask Agendabot to look in the mail archives for an agenda. It looks
back one week. To search other periods, add a number of days or weeks,
e.g.: "agendabot, find agenda since 10 days".

=item "agendabot, suggest agenda"

Ask Agendabot to look in the mail archives for messages that have
"agenda+" in their subject. It looks for message less than one week
old. To search other periods, add a number of days or weeks, e.g.,
"agendabot, suggest agenda since 2 weeks".

=item "agendabot, accept"

Ask Agendabot to turn the suggested agenda into an actual agenda.

=item "agendabot, this is I<list>" and "agendabot, this is I<URL>"

Tell Agendabot in what mailing list to search for agendas. The short
form, e.g., "agendabot, this is style" or "agendabot, this is w3t",
causes Agendabot to guess the URL. In this case, it will find
".../Public/www-style/" and ".../Team/w3t". (It may not have access to
password-protected archives, see the B<-c> option.)

=item "agendabot, forget"

Ask Agendabot to forget the mailing list for this channel. Subsequent
"find" and "suggest" commands will fail, until a new mailing list is
associated with "this is".

=item "agendabot, status"

Ask Agendabot to display the URL of the mailing list where it searches
for agendas.

=back

All commands can be normal messages or "/me" messages.

Once started, the bot doesn't stop (unless a serious error occurs).
Stop it with Control-C or the kill(1) command.

=head2 Agenda formats

Agendabot currently recognizes agenda written in one of the following
forms. The document in which the agenda sits may be plain text, XHTML,
HTML, HTML5, XML (text/xml only), or any text format that is close to
plain text.

=over

=item 1.

In this format, agenda topics are lines that start with a number and a
period and are followed by a line starting with at least four dashes.
E.g.:

 1. Welcome
 ----------

 2. The apple tree
 ----------

 3. AOB
 ------

Any text before, after or in between these lines is ignored. The above
results in the following agenda:

 clear agenda
 agenda+ Welcome
 agenda+ The apple tree
 agenda+ AOB

=item 2.

This format requires the text "=== AGENDA ===" (upper- or lowercase and
possibly with more "=" signs) to occur in the document. All agenda
topics are lines that start with "Topic:". E.g.:

 ==== AGENDA ====

 Topic: AOB?

 Topic: Radar

Any text before, after or in between these lines is ignored. The above
results in the following agenda:

 clear agenda
 agenda+ AOB?
 agenda+ Radar

=item 3.

This format is simply the same as the output, apart from any redundant
whitespace. I.e., topics are lines that start with "agenda+". E.g.:

 agenda+ Roundtable
 agenda+ TPAC registration
 agenda+ Next meeting

Any text before, after or in between these lines is ignored. The above
results in the following agenda:

 clear agenda
 agenda+ Roundtable
 agenda+ TPAC registration
 agenda+ Next meeting

=item 5.

This format has the word "Agenda" somewhere in the text and there may
be topics and subtopics, which start with start with a "1)", "1.",
"*", "•", "-", "◦" or "⁃". Only the top level markers, the least indented,
are copied.

 Agenda telcon 20 July
 0. Extra agenda items and other digressions
    * Jan's items
    * Scribes
 1. [css-display] Blockifications
 2. [cssom-1] Replace steps of set a CSS declaration

Any text before, after or in between these lines is ignored. The above
results in the following agenda:

 clear agenda
 agenda+ Extra agenda items and other digressions
 agenda+ [css-display] Blockifications
 agenda+ [cssom-1] Replace steps of set a CSS declaration</pre>

=back

=head1 OPTIONS

=over

=item B<-n> I<nick>

The nickname the bot runs under. Default is "agendabot".

=item B<-N> I<name>

The real name of the bot. Default is "AgendaBot".

=item B<-c> I<passwordfile>

I<passwordfile> is a file with login names and passwords for various
servers. When agendabot is trying to retrieve a document over HTTP and
receives an authentication request, it looks in this file. The file
must contain lines with four tab-separated fields: host:port, realm,
login, password. The port is required. Empty lines and lines that
start with "#" are ignored. Other lines cause an error. E.g.:

 # This is a password file
 example.org:443	Member login/passw	joe	secret
 info.example.org:443	Member login/passw	joe	secret

=item B<-e> I<URL>

Normally, Agendabot only uses the password file (option B<-c>) when it
is asked to retrieve an agenda on a server-local channel, i.e., a
channel that starts with "&". It will refuse to retrieve
password-protected agendas on public channels or in private messages.
The B<-e> option points to a list of exceptions. Each line in the
indicated file consists of a channel name and a URL prefix, separated
by a tab. If a URL is asked for on a channel and the channel name and
the URL match a line in this file, Agendabot will try to retrieve the
agenda, even if it is password-protected. Empty lines and lines
that start with "# " are ignored. E.g.:

 # Security exceptions
 #i18n	https://lists.w3.org/Archives/Member/member-i18n-core/

The file with exceptions may itself be password-protected. Note that
it is a URL, not a file name. To refer to a local file, use a "file:".

=item B<-m> I<mailing-lists-file>

When IRC channels are associated with mailing lists (so that Agendabot
knows which archives to search for agendas), those associations are
stored in a file. This way, when Agendabot is restarted, it still
knows the associations. This option specifies the file. The default is
agendabot.assoc.

The file contains lines consisting of a channel name, a tab and a
space-separated list of URLs. Empty lines are ignored and lines that
start with "#" but not with a valid channel name are considered
comments and are also ignored. But note that the file will be
overwritten and the comments will be lost as soon as Agendabot
receives a new mailing list association on IRC.

=item B<-v>

Be verbose. Makes the 'bot print a log to standard error output of
what it is doing.

=back

=head1 BUGS

Parsing of XHTML/HTML/HTML5/XML is not complete. In particular
occurrences of E<lt> or E<gt> in attributes or CDATA sections may
cause missed or false matches.

The current parsers in agendabot will try to parse any other text/*
format as if it was plain text, which may give strange results. E.g.,
text/enriched may have formatting codes such as E<lt>bold> or
E<lt>italic>, which are not removed.

=head1 NOTES

This was a 2018 Geek Week project. The idea for the program is due to
Richard Ishida.

=head1 AUTHOR

Bert Bos E<lt>bert@w3.org>

=head1 SEE ALSO

L<Agendabot manual|https://www.w3.org/Tools/AgendaBot/manual.html>,
L<Zakim|https://www.w3.org/2001/12/zakim-irc-bot.html>,
L<RRSAgent|https://www.w3.org/2002/03/RRSAgent>,
L<scribe.perl|https://dev.w3.org/2002/scribe2/scribedoc>

=cut
