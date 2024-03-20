#!/usr/bin/env perl
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
# TODO: The associations of channels with mailing list archives should
# allow for channels on different IRC networks.
#
# TODO: Do more operations that involve HTTP requests in the
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
# TODO: An event in the W3C group calendar may also contain a link to
# an agenda instead of an agenda.
#
# TODO: When leaving a channel ("agendabot, bye"), stop any forked
# processes, not only stop printing the processes' output.
#
# TODO: When contents_to_text() encounters <math>, it just copies the
# text. It should convert it to LaTeX, or, if some day scribe.perl
# accepts literal HTML, copy it as MathML.
#
# TODO: Recognize agenda in
# https://www.w3.org/events/meetings/54fb3c39-8826-418b-bcac-46e112f08535/20220303T090000
#
# TODO: Is html_list_agenda_parser() needed? It runs after
# two_level_agenda_parser(), which probably already found all lists.
#
# TODO: Use a neural network (e.g., TensorFlow) to extract an agenda
# from a message?
#
# Created: 2018-07-09
# Author: Bert Bos <bert@w3.org>
#
# Copyright © 2018-2022 World Wide Web Consortium, (Massachusetts Institute
# of Technology, European Research Consortium for Informatics and
# Mathematics, Keio University, Beihang). All Rights Reserved. This
# work is distributed under the W3C® Software License
# (http://www.w3.org/Consortium/Legal/2015/copyright-software-and-document)
# in the hope that it will be useful, but WITHOUT ANY WARRANTY;
# without even the implied warranty of MERCHANTABILITY or FITNESS FOR
# A PARTICULAR PURPOSE.

package AgendaBot;
use FindBin;
use lib "$FindBin::Bin";	# Look for modules in agendabot's directory
use parent 'Bot::BasicBot::ExtendedBot';
use strict;
use warnings;
use feature 'state';
use LWP;
use HTTP::Cookies;
use LWP::ConnCache;
use Getopt::Std;
use POSIX qw(strftime);
use Scalar::Util 'blessed';
use Term::ReadKey;		# To read a password without echoing
use utf8;
use DateTime;
use URI;
use HTML::Entities;
use POE;			# For OBJECT, ARG0 and ARG1
use Encode qw(encode decode);
use Digest::SHA qw(sha256);
use MIME::Base64;
use HTML::TreeBuilder 5 -weak;
use open ':encoding(UTF-8)';	# Open all files assuming they are UTF-8

use constant HOME => 'https://github.com/w3c/AgendaBot';
use constant MANUAL => 'https://w3c.github.io/AgendaBot/manual.html';
use constant VERSION => '0.5';
use constant LIMIT => 20;	# Max # of downloads per day of archives
use constant MAX_REDIRECTS => 10; # Max # of HTTP redirect

use constant LISTS => 1;	# Bitset for forget_associations()
use constant CALENDARS => 2;	# Bitset for forget_associations()


# Subroutines to try and recognize an agenda. The order is important:
# If several of them find agenda items, the first one to find more
# than one item is used. (This is because it is more common to find a
# bulleted list that is not an agenda than, e.g., "topic:" lines that
# are not agenda items.
my @parsers = (
  \&bb_agenda_parser,
  \&addison_agenda_parser,
  \&koalie_and_plh_agenda_parser,
  \&two_level_agenda_parser,
  \&html_list_agenda_parser,
  \&quoted_agenda_parser);


# init -- initialize some parameters
sub init($)
{
  my $self = shift;
  my $errmsg;

  $errmsg = $self->load() and die "$errmsg\n";
  $errmsg = $self->read_rejoin_list() and die "$errmsg\n";
  $self->{topics} = {};
  $self->{cookies} = {};
  return 1;
}


# load - load configuration files, return error message or undef
sub load($)
{
  my $self = shift;
  my $errmsg;

  if (($errmsg = $self->read_passwords_file())) {$self->log($errmsg);}
  elsif (($errmsg = $self->read_security_exceptions())) {$self->log($errmsg);}
  elsif (($errmsg = $self->read_associations())) {$self->log($errmsg);}
  return $errmsg;
}


# is_exception -- check if a channel may get this URI
sub is_exception($$$)
{
  my ($self, $channel, $uri) = @_;
  my $chan_and_uri;

  # Each exception is of the form CHANNEL<TAB>URL-PREFIX. Check if one
  # of them matches the passed channel and URI.
  #
  return 0 if !$self->{exceptions};
  $chan_and_uri = "$channel\t$uri";
  foreach my $u (@{$self->{exceptions}}) {
    if ($chan_and_uri =~ /^\Q$u\E/) {
      $self->log("Security exception: $channel is allowed to get $uri");
      return 1;
    }
  }
  return 0;
}


# get_cookies -- make a request with a username and password to get a cookie jar
sub get_cookies($$$$)
{
  my ($self, $uri, $user, $password) = @_;
  my ($ua, $res, $set_cookie, $nredirects, $cookie);

  $self->log("get_cookies");

  # Don't use the UserAgent stored in $self->{ua}, because the
  # requests_redirectable() is different.
  #
  $ua = LWP::UserAgent->new;
  $ua->agent(blessed($self) . '/' . VERSION);
  $ua->default_header('Accept' => 'text/*');
  $ua->timeout(10);
  $ua->env_proxy;
  $ua->conn_cache(LWP::ConnCache->new);
  $ua->requests_redirectable(['GET', 'HEAD', 'POST']);

  # $uri is a URL that returned a WWW-Authenticate header with scheme
  # "w3state". Follow redirects on that $uri to arrive at a resource,
  # which we assume to be a form. If $uri is a resource on
  # lists.w3.org, there will be two redirects, first to
  # "https://auth.w3.org/?url=..." and then to
  # "https://auth.w3.org/login".
  #
  $res = $ua->head($uri);
  return undef if !$res->is_success && $res->code != 401;

  $self->log("get_cookies: " . $_->request->method . " on " . $_->base)
      foreach ($res->redirects);
  $self->log("get_cookies: " . $res->request->method . " on " . $res->base);

  # We assume the returned resource is a form with three fields:
  # "_username", "_password" and "_remember_me". If we started with a
  # URL on lists.w3.org, this resource will be
  # "https://auth.w3.org/login". POST to it and then follow
  # redirects. In this case there should be two more redirects, one to
  # "https://auth.w3.org/" and one to
  # "https://auth.w3.org/loggedin").
  #
  $self->log("get_cookies: Using username $user on " . $res->base );
  $ua->cookie_jar(HTTP::Cookies->new);
  $res = $ua->post($res->base, {'_username' => $user, '_password' => $password,
				    '_remember_me' => 'on'});
  $self->log("get_cookies: ".$res->code." on ".$res->base) if !$res->is_success;
  return undef if !$res->is_success;

  $self->log("get_cookies: " . $_->request->method . " on " . $_->base)
      foreach ($res->redirects);
  $self->log("get_cookies: " . $res->request->method . " on " . $res->base);

  # Each of the responses set or removed some cookies. Return a hash
  # of the remaining cookies. In the case of auth.w3.org, the response
  # to the POST sets a cookie "PHPSESSID=...", the response to
  # "https://auth.w3.org" sets a cookie "w3csess=..." and the response
  # to "https://auth.w3.org/loggedin" deletes the "PHPSESSID" cookie,
  # so we are left with a "w3csess=..." cookie.
  #
  return $ua->cookie_jar;
}


# request -- send a request to a server and read the response
sub request($$$$;$);
sub request($$$$;$)
{
  my ($self, $method, $info, $uri, $nredirects) = @_;
  my $channel = $info->{channel};
  my ($ua, $res, $realm, $user, $password, $user_pass, $challenge);
  my ($cookies ,$auth_scheme, $host_realm, $location);

  $nredirects //= 0;

  return (508, undef, undef) if $nredirects > MAX_REDIRECTS;

  $ua = LWP::UserAgent->new;
  $ua->ssl_opts(verify_hostname => $self->{ssl_verify_hostname});
  $ua->agent(blessed($self) . '/' . VERSION);
  $ua->default_header('Accept' => 'text/*');
  $ua->timeout(10);
  $ua->conn_cache(LWP::ConnCache->new);
  $ua->env_proxy;
  $ua->requests_redirectable([]); # We need to check WWW-Authenticate first

  $res = $method eq "GET" ? $ua->get($uri) :
      $method eq "HEAD" ? $ua->head($uri) : return (400, undef, undef);

  if ($res->code == 401 || $res->header('WWW-Authenticate')) {
    # The resource requires authentication, or will be different after
    # authentication.

    if ($channel !~ /^&/ &&	# Not a server-local channel
	! $self->is_exception($channel, $uri)) {
      $self->log("Refusing private page on public channel $channel: $uri");
      return (403, undef, undef);
    }

    # Check the authentication method, extract the realm.
    #
    $challenge = $res->header('WWW-Authenticate');
    if ($challenge !~ /\b(Basic|Digest|w3state)\b
        .*(?:\brealm\s*=\s*"([^"]*)")?/xi) {
      $self->log("$uri has an unknown authentication scheme: $challenge");
      return (401, undef, undef);
    }

    $realm = $2 // '';
    $auth_scheme = $1;
    $host_realm = $res->base->host_port . "\t" . $realm;

    # See if we know a password for this host and realm.
    # Instead of a login/password, there may also be a cookie.
    #
    $user_pass = $self->{passwords}->{$res->base->host_port . "\t" . $realm};
    if (!defined $user_pass) {
      $self->log("No password known for $uri");
      return (401, undef, undef);
    }
    ($user, $password) = split /\t/, $user_pass;

    # Hand the login and password to $ua and try to get the URI again.
    # If the authentication type if not Basic or Digest, try a cookie instead.
    #
    if ($auth_scheme =~ /Basic|Digest/i) {
      $ua->credentials($res->base->host_port, $realm, $user, $password);
      $res = $method eq "GET" ? $ua->get($uri) :
	  $method eq "HEAD" ? $ua->head($uri) : return (400, undef, undef);
    } elsif (($cookies = $self->{cookies}->{$host_realm})) {
      # Auth scheme is w3cstate, and a cookie was cached.
      # $self->log("Re-using cookie");
      $ua->cookie_jar($cookies);
      $res = $method eq "GET" ? $ua->get($uri) :
	  $method eq "HEAD" ? $ua->head($uri) : return (400, undef, undef);
      if ($res->header('WWW-Authenticate')) {
	# If we still get a WWW-Authenticate header, the cookies were
	# wrong. They maybe expired. Remove them and try again,
	# recursively.
	$self->log("request: cookie did not work on try $nredirects; delete it and try again");
	delete $self->{cookies}->{$host_realm};
	return $self->request($method, $info, $uri, $nredirects + 1);
      }
    } else {
      # Auth scheme is w3cstate, but no known cookie yet.
      # $cookies = $self->get_cookies($uri, $user, $password);
      $location = $res->header('Location');
      $location = URI->new_abs($location, $uri)->canonical->as_string;
      $cookies = $self->get_cookies($location, $user, $password);
      return (400, undef, undef) if !defined $cookies;
      $ua->cookie_jar($cookies);
      $self->{cookies}->{$host_realm} = $cookies;
      $res = $method eq "GET" ? $ua->get($uri) :
	  $method eq "HEAD" ? $ua->head($uri) : return (400, undef, undef);
    }

  }

  $self->log("Code ".$res->code." on $uri");

  # If we got a redirect, recurse.
  if (($location = $res->header('Location'))) {
    $location = URI->new_abs($location, $uri)->canonical->as_string;
    return $self->request($method, $info, $location, $nredirects + 1);
  }

  return $res->is_success
      ? ($res->code, join(';', $res->content_type), $res->decoded_content)
      : ($res->code, undef, undef);
}


# get -- get the contents of a file by its URL
sub get($$$)
{
  my ($self, $info, $uri) = @_;
  return $self->request('GET', $info, $uri);
}


# head -- get the content type of a file by its URL
sub head($$$)
{
  my ($self, $info, $uri) = @_;
  return $self->request('HEAD', $info, $uri);
}


# get_agenda_from_event -- return the part of an event that contains the agenda
sub get_agenda_from_event($)
{
  my $s = shift;

  # Return the text between id=agenda and id=export_component.
  if ($s =~ /(<h2 id="?agenda"?>Agenda<\/h2>.*)<div[^>]*id="?export_component\b/s) {
    return $1;
  } else {
    return '';
  }
}


# parse_and_print_agenda -- try to retrieve an agenda and print it on IRC
sub parse_and_print_agenda($$$)
{
  my ($self, $info, $uri) = @_;
  my $channel = $info->{channel};
  my $who = $info->{who};
  my @agenda = ();
  my ($code, $type, $document, $plaintext);

  # Try to download the resource.
  #
  ($code, $type, $document) = $self->get($info, $uri);
  return "$who, sorry, I don't have a password for $uri" if $code == 401;
  return "$who, sorry, the document at $uri is protected." if $code == 403;
  return "$who, sorry, $uri doesn't seem to exist." if $code == 404;
  return "$who, sorry, could not get $uri (code $code)." if !defined $document;
  return "$who, sorry, $uri doesn't seem to be text." if $type!~/^text\/|\+xml\b/;

  if ($uri =~ /^https:\/\/lists\.w3\.org\/Archives\//i) {
    # If it is a page in the mail archive, extract the original mail body.
    # $self->log("Extracting the mail body");
    $document =~ s/.*(<pre[^>]+(?:class|id)="body">.*<\/pre>).*/$1/s;
    $plaintext = html_to_text($document, $uri);
  } elsif ($uri =~ /^https:\/\/www\.w3\.org\/events\/meetings\//i) {
    # It is an event from the group calendar. Remove everything except
    # the agenda.
    $document = get_agenda_from_event($document); # May return ''
    $plaintext = html_to_text($document, $uri);
  } else {
    # If it is an HTML or XML document, render it to plain text. Some of
    # the parsers only handle plain text.
    $plaintext = html_to_text($document, $uri) if $type =~ /html|xml/;
  }

  # Try the parsers in order. Stop as soon as a parser returns an
  # agenda of two or more items. Otherwise use the first one that
  # returned one item.
  for my $parser (@parsers) {
    my @h = &$parser($type, $document, $plaintext // $document, $uri);
    @agenda = @h if scalar(@h) > 0;
    last if scalar(@h) > 1;
  }
  $self->log("Found ".($#agenda+1)." topics in $uri");
  return "$who, sorry, I did not recognize any agenda in $uri" if $#agenda==-1;

  # Print the agenda in Zakim's format.
  #
  if (ref $who eq 'GLOB') {	# We are testing (option -o)
    print $who "agenda: $uri\n";
    print $who "clear agenda\n";
    print $who "agenda+ $_\n" foreach (@agenda);
    print $who "\n";
  } else {
    $self->say({channel => $channel, body => "clear agenda"});
    $self->say({channel => $channel, body => "agenda+ " . $_})
	foreach (@agenda);
  }
  return undef;
}


# get_subject_and_date -- get the subject and date from an archived message
sub get_subject_and_date($$$)
{
  my ($self, $doc, $url) = @_;
  my ($subject, $date);

  $subject = decode_entities($1)
      if $doc =~ /<meta name="Subject" content="(.*?)"/;

  # Get the date from a <meta> tag, or from the URL.
  # TODO: handle errors in new().
  if ($doc =~ /<meta name="Date" content="(\d+)-(\d\d)-(\d\d)/) {
    $date = DateTime->new(year => $1, month => $2, day => $3)->epoch;
  } elsif ($url =~ m|^https://lists.w3.org/Archives/[^/]+/[^/]+/([0-9]{4})|) {
    $date = DateTime->new(year => $1, month => 12, day => 31)->epoch;
  }

  return ($subject // "", $date // time);
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


# promising_subject -- heuristic if a mail is an agenda, based on its subject
sub promising_subject($)
{
  my $subject = shift;
  return
      $subject !~ /^Re:/i &&
      $subject =~ /\bagenda\b/i &&
      $subject !~ /\bagenda\+/i;
}


# find_agenda_process -- find agenda in email or calendar (background process)
sub find_agenda_process($$$$$)
{
  my ($body, $self, $info, $lists, $calendars, $period) = @_;

  my @calendar_urls = $calendars ? split(/ /, $calendars) : ();
  my @urls = split(/ /, $lists);
  my $channel = $info->{channel};
  my (@agenda, $url, $oldest, %seen);

  binmode(STDOUT, ":utf8");
  binmode(STDERR, ":utf8");

  if ($period =~ /(\d+) day/) {$oldest = time - 60*60*24*$1;}
  elsif ($period =~ /(\d+) week/) {$oldest = time - 60*60*24*7*$1;}
  else {print STDERR "Bug! find_agenda_process(... \"$period\")\n"; return;}

  # First search in calendars for an agenda for today.

  while (scalar(@agenda) < 2 && @calendar_urls) {
    my $calendar = shift @calendar_urls;
    my ($code, $mediatype, $document) = $self->get($info, $calendar);
    next if $code != 200;

    # Find the first link with class="card__link". This is presumably
    # a link to the the next upcoming meeting. If there is none, try
    # the next calendar.
    $document =~ /<a\s+class="card__link"\s+href="(.+)"/ or next;

    # Get that upcoming meeting.
    $url = URI->new_abs($1, $calendar)->canonical->as_string;
    my ($code1, $mediatype1, $eventdoc) = $self->get($info, $url);
    next if $code1 != 200;

    # Remove everything except the agenda. Try the next calendar if
    # there is no agenda.
    $eventdoc = get_agenda_from_event($eventdoc);
    next if $eventdoc eq '';

    # Try each of the parsers until one returns two or more agenda items.
    my $plaintext = html_to_text($eventdoc, $url);
    for my $parser (@parsers) {
      my @h = &$parser($mediatype1, $eventdoc, $plaintext, $url);
      if (scalar(@h) > 1) {@agenda = @h; last;}
    }
  }

  # Next try all mailing lists, recursively following links in each archive.
  # (Unless the calendars already yielded an agenda.)

  $seen{$_} = 1 foreach @urls;
  while (scalar(@agenda) < 2 && @urls) {
    $url = shift @urls;
    my ($code, $mediatype, $document) = $self->get($info, $url);
    next if $code != 200;
    my ($subject, $date) = $self->get_subject_and_date($document, $url);
    next if $date < $oldest;
    # Add all links from $document that are under $url and not already seen.
    unshift @urls, grep {!$seen{$_}++} $self->find_links($document, $url);

    # See if the subject indicates an agenda.
    # print STDERR "Subject: $subject\n";
    next if !promising_subject($subject);

    # Extract the original mail body from the HTML page.
    # print STDERR "Extracting the mail body\n";
    $document =~ s/.*(<pre[^>]+(?:class|id)="body">.*<\/pre>).*/$1/s;

    # Try each of the parsers until one returns two or more agenda items.
    my $plaintext = html_to_text($document, $url);
    for my $parser (@parsers) {
      my @h = &$parser($mediatype, $document, $plaintext, $url);
      if (scalar(@h) > 1) {@agenda = @h; last;}
    }
  }

  if (scalar(@agenda) > 1) {
    print STDERR "Found agenda with ".scalar(@agenda)." topics for $channel\n";
    # print STDERR "$channel\t(\t$url\n";
    print "$channel\t(\t$url\n";
    # print STDERR "$channel\t-\t$_\n" foreach @agenda;
    print "$channel\t-\t$_\n" foreach @agenda;
  } else {
    print STDERR "Found no agenda for $channel in $period\n";
    print "$channel\t)\n";
  }
}


# handle_find_agenda_results -- handle lines printed by find_agenda_process
sub handle_find_agenda_results
{
  my ($self, $body, $wheel_id) = @_[OBJECT, ARG0, ARG1];
  my $channels = $self->{IRCOBJ}->channels();

  # Lines are of the form "CHANNEL<tab>C..." where C = "(", "-" or ")".
  # TODO: Truncate long lines, because say() will split them over two
  # or more lines, and Zakim doesn't understand continued lines.
  $body = decode('UTF-8', $body);
  my ($channel, $type, $text) = $body =~ /^([^\t]+)\t(.)(?:\t(.*))?/;
  return if !exists $channels->{$channel}; # We're no longer on this channel

  if ($type eq '(') {
    $self->say({channel => $channel, body => "agenda: $text"}); # $text is a URL
    $self->say({channel => $channel, body => "clear agenda"});
  } elsif ($type eq '-') {
    $self->say({channel => $channel, body => "agenda+ $text"});
  } elsif ($type eq ')') {
    $self->say({channel=>$channel, body=>"Sorry, I did not find an agenda."});
  }
}


# find_agenda -- look for an agenda in recent mail messages and parse it
sub find_agenda($$$)
{
  my ($self, $info, $period) = @_;
  my $channel = $info->{channel};	# "#channel" or "msg"
  my $calendars = $self->{calendars}->{$channel};
  my $lists = $self->{mailing_lists}->{$channel};
  my $me = $self->nick();		# Our own name

  return "sorry, I don't know which mailing list or calendar is associated " .
      "with this channel. Try \"$me, help this is\"."
      if !defined $lists && !defined $calendars;

  # If there is already a process running, kill it.
  $self->{find_agenda_process}->kill() if defined $self->{find_agenda_process};

  # Start a background process.
  $self->{find_agenda_process} =
      $self->forkit({run => \&find_agenda_process,
		     handler => "handle_find_agenda_results",
		     channel => $channel,
		     arguments => [$self, $info, $lists, $calendars, $period]});

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

  binmode(STDOUT, ":utf8");
  binmode(STDERR, ":utf8");

  if ($period =~ /(\d+) day/) {
    $maxtries *= $1;
    $oldest = time - 60 * 60 * 24 * $1;
  } elsif ($period =~ /(\d+) week/) {
    $maxtries *= 7*$1;
    $oldest = time - 60 * 60 * 24 * 7 * $1;
  } else {
    print STDERR "Bug! find_topics_process(... \"$period\")\n";
    return;
  }
  print "$channel\t(\n";	# Signal the start of the array
  $seen{$_} = 1 foreach @urls;
  while (@urls && $tries++ < $maxtries) {
    $url = shift @urls;
    my ($code, $mediatype, $document) = $self->get($info, $url);
    next if $code != 200;
    my ($subject, $date) = $self->get_subject_and_date($document, $url);
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
  my ($n, $channel, $type, $text);
  my $channels = $self->{IRCOBJ}->channels();

  # Lines are of the form "CHANNEL<tab>C..." where C is "(", "-" or ")"
  # TODO: Truncate long lines, because say() will split them over two
  # or more lines, and Zakim doesn't understand continued lines.
  $body = decode('UTF-8', $body);
  ($channel, $type, $text) = $body =~ /^([^\t]+)\t(.)(?:\t(.*))?/;
  return if !exists $channels->{$channel}; # We're no longer on this channel

  if ($type eq '(') {		      # Signals the start of the array
    $self->{topics}->{$channel} = []; # Initalize the list of topics
  } elsif ($type eq '-') {	      # Signals an additional topic
    push @{$self->{topics}->{$channel}}, $text;
  } elsif ($type eq ')') {	      # Signals the end of the array
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


# find_mailing_list_archive -- find the full URL of the mailing list $list_name
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
    my ($code, $mediatype, $document) = $self->head($info, $url);
    return $url if $code == 200; # TODO: check that type is HTML
  }

  return undef;
}


# find_calendar -- find the URL of the calendar for the group $name, or undef
sub find_calendar($$$)
{
  my ($self, $info, $group_name) = @_;

  foreach my $base (("https://www.w3.org/groups/wg/",
		     "https://www.w3.org/groups/ig/",
		     "https://www.w3.org/groups/cg/",
		     "https://www.w3.org/groups/bg/")) {
    my $url = "$base$group_name/calendar";
    my ($code, $mediatype, $document) = $self->head($info, $url);
    return $url if $code == 200; # TODO: check that type is HTML
  }

  return undef;
}


# write_associations -- write the mailing list and calendar associations to file
sub write_associations($)
{
  my ($self) = @_;
  my %assoc;

  # Try to write the associations to file.
  #
  open my $fh, ">", $self->{associations_file} or return 0;
  %assoc = %{$self->{mailing_lists}};
  print $fh $_, "\t", $assoc{$_}, "\tmailing list\n" foreach keys %assoc;
  %assoc = %{$self->{calendars}};
  print $fh $_, "\t", $assoc{$_}, "\tcalendar\n" foreach keys %assoc;
  return 1;
}


# associate_lists_and_calendars -- define the mail archives to search in
sub associate_lists_and_calendars($$$)
{
  my ($self, $info, $channel, $lists) = @_;
  my (@list_urls, @calendar_urls);

  # Split the list of mailing lists and, if they are not already URLs,
  # try to find their URLs. Concatenate the URLs. If no URL could be
  # found for one of the mailing list names, return an error message.
  #
  foreach my $x (split(/\s*,\s*|\s+and\s+/i, $lists)) {
    if ($x =~ /^https:\/\/lists\.w3\.org\//i) {
      # Looks like a the full URL of a mailing list.
      push @list_urls, $x;
    } elsif ($x =~ /^https:\/\/www\.w3\.org\/groups\//i) {
      # Looks like the calendar of a group.
      push @calendar_urls, $x;
    } elsif ($x =~ /^https:\/\//i) {
      # Looks like a full URL, guess that it is like a mailing list.
      push @list_urls, $x;
    } else {
      # Try if it is the name of a mailing list or group, or maybe both.
      my $list = $self->find_mailing_list_archive($info, $x);
      push @list_urls, $list if defined $list;
      my $calendar = $self->find_calendar($info, $x);
      push @calendar_urls, $calendar if defined $calendar;
    }
  }
  return "I could not find (or not read) an archive or calendar for $lists."
      if !@list_urls && !@calendar_urls;

  # Store the associations.
  #
  $self->{mailing_lists}->{$channel} = join(' ', @list_urls);
  $self->{calendars}->{$channel} = join(' ', @calendar_urls);
  $self->log("New association: $channel -> $_") foreach @calendar_urls;
  $self->log("New association: $channel -> $_") foreach @list_urls;

  # Try to write the associations to file.
  #
  my $result = $self->write_associations;
  $self->log("Writing to $self->{associations_file} failed") if !$result;
  return "I could not write a file. The new mailing list association "
      . "will be lost when I am restarted. Sorry." if !$result;
  my $s = join(', ', @calendar_urls, @list_urls);
  $s =~ s/, (?=[^ ]*$)/, and /;
  return "OK, using $s";
}


# forget_associations -- remove the mail archives and/or calendars to search in
sub forget_associations($$$)
{
  my ($self, $channel, $what) = @_;
  my $lists = $self->{mailing_lists}->{$channel};
  my $calendars = $self->{calendars}->{$channel};

  return "I already have no mailing lists or calendars for this channel."
      if !defined $lists && !defined $calendars;
  return "I already have no mailing lists for this channel."
      if $what == LISTS && !defined $lists;
  return "I already have no calendars for this channel."
      if $what == CALENDARS && !defined $calendars;

  # Remove the association.
  #
  delete $self->{mailing_lists}->{$channel} if $what & LISTS;
  delete $self->{calendars}->{$channel} if $what & CALENDARS;
  $self->log("Removed associations for $channel") if $what == LISTS + CALENDARS;
  $self->log("Removed calendars for $channel") if $what == CALENDARS;
  $self->log("Removed mailing lists for $channel") if $what == LISTS;

  # Write current associations to file.
  #
  my $result = $self->write_associations;
  $self->log("Writing to $self->{associations_file} failed") if !$result;
  return "I could not write a file. The new associations "
      . "will be lost when I am restarted. Sorry." if !$result;
  return "OK, I removed" .
      ($lists !~ / / ? " the mailing list" : "") .
      ($lists =~ / / ? " the mailing lists" : "") .
      "." if $what == LISTS;
  return "OK, I removed" .
      ($calendars !~ / / ? " the calendar" : "") .
      ($calendars =~ / / ? " the calendars" : "") .
      "." if $what == CALENDARS;
  return "OK, I removed" .
      (defined $lists && $lists !~ / / ? " the mailing list" : "") .
      (defined $lists && $lists =~ / / ? " the mailing lists" : "") .
      (defined $lists && defined $calendars ? " and" : "") .
      (defined $calendars && $calendars !~ / / ? " the calendar" : "") .
      (defined $calendars && $calendars =~ / / ? " the calendars" : "") .
      ".";
}


# status -- display the associated mailing list(s)
sub status($$)
{
  my ($self, $channel) = @_;
  my $lists = $self->{mailing_lists}->{$channel};
  my $calendars = $self->{calendars}->{$channel};
  my $s = "";

  return "I know no mailing list or calendars for this channel."
      if !defined $lists && !defined $calendars;

  if (defined $lists) {
    if ($lists !~ / /) {
      $s .= "the mailing list for this channel is $lists";
    } else {
      $s .= "the mailing lists for this channel are " . ($lists =~ s/ /, /gr );
    }
  }
  if (defined $calendars && $calendars ne '') {
    $s .= " and " if $s;
    if ($calendars !~ / /) {
      $s .= "the calendar for this channel is $calendars";
    } else {
      $s .= "the calendars for this channel are " . ($calendars =~ s/ /, /gr );
    }
  }
  return $s;
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
  $self->remember_channel($channel);
}


# remember_channel -- update the list of joined channels on disk, if needed
sub remember_channel($$)
{
  my ($self, $channel) = @_;

  return if !$self->{rejoinfile}; # Not remembering channels
  $channel = lc $channel;
  return if exists $self->{joined_channels}->{$channel}; # Already remembered
  $self->{joined_channels}{$channel} = 1;
  if (open my $fh, ">", $self->{rejoinfile}) {
    print $fh "$_\n" foreach keys %{$self->{joined_channels}};
  }
}


# forget_channel -- update the list of joined channels on disk, if needed
sub forget_channel($$)
{
  my ($self, $channel) = @_;

  return if !$self->{rejoinfile}; # Not remembering channels
  $channel = lc $channel;
  if (delete $self->{joined_channels}->{$channel}) { # Forget the channel
    if (open my $fh, ">", $self->{rejoinfile}) { # Can write file
      print $fh "$_\n" foreach keys %{$self->{joined_channels}};
    }
  }
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
      if !$addressed;

  # Remove the optional initial "please" and final period.
  $text =~ s/^please\s*,?\s*//i;
  $text =~ s/\s*\.\s*$//;

  return $self->part_channel($channel),
      $self->forget_channel($channel), undef # undef -> no reply
      if $text =~ /^bye$/i;

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

  return $self->associate_lists_and_calendars($info, $channel, $1)
      if $text =~ /^this\s+is\s+
      	       	   ([^\s,]+(?:(?:\s*,\s*(?:and\s+)?|\s+and\s+)[^\s,]+)*)$/xi;

  return $self->forget_associations($channel, LISTS | CALENDARS)
      if $text =~ /^forget(?:\s+all?)?$/i;

  return $self->forget_associations($channel, LISTS)
      if $text =~ /^forget(?:\s+(?:the\s+)?(?:mailing\s+)?lists?)?$/i;

  return $self->forget_associations($channel, CALENDARS)
      if $text =~ /^forget(?:\s+(?:the\s+)?calendars?)?$/i;

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

  return "if you say \"$me, find agenda\", I will scan the calendar and "
      . "mailing list "
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
      . "calendar \"group/wg/xyz\" (or similar), and the "
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
      . "mailing lists\" or \"forget calendars\" or \"forget associations\"), "
      . "I will no longer use any mailing lists or calendars to "
      . "search for agendas. The \"find\" and \"suggest\" commands "
      . "will no longer work (but \"agenda:\" still does). Use the "
      . "\"this is\" command to associate a new mailing list or calendar."
      if $text =~ /^forget/i;

  return "if you say \"$me, status?\" (or \"$me, info\"), I will "
      . "show the URLs of the mailing list archives and calendars where I look "
      . "for agendas."
      if $text =~ /^status|info/i;

  return "if you say \"$me, bye\", I will leave this channel. "
      . "I will continue to remember any associated mailing lists, "
      . "calendars and "
      . "suggested agenda topics, in case you /invite me back."
      if $text =~ /^bye/i;

  return "I am an instance of " . blessed($self) . " " . VERSION . ". "
      . "For detailed help, type \"help COMMAND\", where COMMAND is "
      . "one of invite, agenda, find, suggest, accept, "
      . "this is, forget, status or bye. Or go to " . MANUAL;
}


# connected -- handle a successful connection to a server
sub connected($)
{
  my ($self) = @_;

  $self->join_channel($_) foreach keys %{$self->{joined_channels}};
}


# log -- print a message to STDERR, but only if -v (verbose) was specified
sub log
{
  my ($self, @messages) = @_;

  if ($self->{'verbose'}) {
    # Prefix all log lines with the current time, unless the line
    # already starts with a time.
    #
    my $now = strftime "%Y-%m-%dT%H:%M:%SZ", gmtime;
    $self->SUPER::log(
      map /^\d\d\d\d-\d\d-\d\dT\d\d:\d\d:\d\dZ/ ? $_ : "$now $_", @messages);
  }
}


# decypt -- decrypt "user\tencrypted" into "user\tpassword"
sub decrypt($$$)
{
  my ($self, $user_and_encrypted, $passphrase) = @_;
  my ($user, $encrypted, $mask, $password, $len, $repeat);

  ($user, $encrypted) = $user_and_encrypted =~ /^(.*)\t(.*)$/;
  $mask = sha256(encode('UTF-8', $passphrase));
  $encrypted = decode_base64($encrypted);
  $len = length($mask);
  $repeat = int((length($encrypted) + $len - 1) / $len);
  $mask = $mask x $repeat;
  $password = $encrypted ^ $mask;
  $password = decode('UTF-8', $password);
  $password =~ s/\0+$//;
  return "$user\t$password";
}


# read_passwords_file -- read passwords file, return undef or error msg
sub read_passwords_file($)
{
  my $self = shift;
  my (%passwords, $fh, $passphrase, $crypt_pw);
  my $path = $self->{passwords_file};
  my $encrypted = 0;

  return undef if !defined $path; # No file to read, not an error

  # Each line must be HOST:PORT\tREALM\tLOGIN\tPASSWORD. Empty lines
  # and lines that start with "#" are ignored.
  #
  # TODO: Can there be tabs in any of these fields?
  #
  open $fh, "< :encoding(UTF-8)", $path or return "$path: cannot be opened.";
  while (<$fh>) {
    if (/^#/) {}		# Comment line
    elsif (/^\s*$/) {}		# Empty line
    elsif (/^\s*!encrypted\b(?:\t(.*))?/) {$encrypted = 1; $crypt_pw = $1}
    elsif (/^(.*\t.*)\t(.*\t.*)$/) {$passwords{$1} = $2;}
    else {return "$path:$.: Syntax error: line has less than four fields.";}
  }

  # If the passwords column is encrypted, decrypt it.
  if ($encrypted) {
    print "Passphrase to decrypt the passwords file: ";
    ReadMode('noecho');
    $passphrase = ReadLine(0);
    ReadMode('restore');
    print "\n";
    chomp $passphrase;
    if (defined $crypt_pw &&
      $self->decrypt("test\t$crypt_pw", $passphrase) ne "test\t$passphrase") {
      return "Incorrect passphrase";
    }
    foreach my $k (keys %passwords) {
      $passwords{$k} = $self->decrypt($passwords{$k}, $passphrase);
    }
    # TODO: Does this work to overwrite the memory location?
    $passphrase = "x" x length($passphrase);
  }

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


# read_associations -- read the mailing lists and calendars for each channel
sub read_associations($)
{
  my ($self) = @_;
  my $path = $self->{associations_file};
  my ($fh, %lists, %calendars);

  return "Bug: No file defined for storing mailing lists and calendars."
      if !defined $path;

  # Open $path, if it exists. Each line consists of a channel name, a
  # tab, a space-separated list of URLs, another tab and the type
  # (mailing list or calendar). Empty lines are
  # ignored. Lines that consist of a "#" that is not followed by a
  # letter or digit are comment lines and are also ignored.
  #
  if (open $fh, "<", $path) {
    while (<$fh>) {
      chomp;
      if (/^$/ || /^#$/ || /^#[^a-zA-Z0-9_-]/) {
	next;
      } elsif (/^([#&][^\t]+)\t(.*)\tmailing list$/) {
	$lists{$1} = $2;
      } elsif (/^([#&][^\t]+)\t(.*)\tcalendar$/) {
	$calendars{$1} = $2;
      } else {
	return "$path:$.: Syntax error: line should have a channel name, one or more URLs and a type."
      }
    }
  }
  $self->{mailing_lists} = \%lists;
  $self->{calendars} = \%calendars;
  $self->log("Restore association: $_ -> " . $self->{mailing_lists}->{$_})
      foreach (keys %{$self->{mailing_lists}});
  $self->log("Restore association: $_ -> " . $self->{calendars}->{$_})
      foreach (keys %{$self->{calendars}});
  return undef;			# No errors
}


# read_rejoin_list -- read or create the rejoin file, if any
sub read_rejoin_list($)
{
  my $self = shift;

  $self->{joined_channels} = {};
  if ($self->{rejoinfile}) {	# Option -r was given
    if (-f $self->{rejoinfile}) { # File exists
      $self->log("Reading $self->{rejoinfile}");
      open my $fh, "<", $self->{rejoinfile} or
	  return "$self->{rejoinfile}: $!\n";
      while (<$fh>) {chomp; $self->{joined_channels}->{lc $_} = 1;}
    } else {			# File does not exist yet
      $self->log("Creating $self->{rejoinfile}");
      open my $fh, ">", $self->{rejoinfile} or
	  return "$self->{rejoinfile}: $!\n";
    }
  }
  return undef;			# No errors
}


# get_date_from_datetime -- convert ISO date-time to seconds since epoch
sub get_date_from_datetime($$)
{
  my ($self, $isodate) = @_;

  $isodate =~ /(\d+)-(\d+)-(\d+)T(\d+):(\d+):(\d+)([+-][\d:]+)/ or return 0;
  return DateTime->new(year=>$1, month=>$2, day=>$3, hour=>$4, minute=>$5,
		       second=>$6, time_zone=>$7)->epoch;
}


# tree_to_text -- recursively render an HTML tree as plain text
sub tree_to_text($$);
sub tree_to_text($$)
{
  my ($elt, $status) = @_;
  state @ul_markers = ('  * ', '  - ', '  + ');

  if (ref $elt eq '' && !$status->{preformatted}) {
    my $s = $elt =~ s/\s+/ /gr;	     # Collapse white space
    return if $s eq '' || $s eq ' '; # Only white space; do nothing.
    my $sep = $s =~ s/^ // || $status->{pending_hspace} ? ' ' : '';
    $status->{pending_hspace} = scalar($s =~ s/ $//); # Postpone trailing space
    my @words = split / /, $s;
    if ($status->{pending_vspace}) { # At start of a paragraph
      my $word = shift @words;
      my $marker = $status->{list_counter} && $status->{pending_marker} ?
	  sprintf($status->{pending_marker}, $status->{list_counter}) :
	  $status->{pending_marker};
      $status->{text} .=	     # Add vertical space, indent and marker
	  "\n" x $status->{pending_vspace} .
	  ' ' x ($status->{indent} - length($status->{pending_marker})) .
	  $marker .
	  $word;
      $status->{pending_vspace} = 0;
      $status->{pending_marker} = '';
      $status->{line_length} = $status->{indent} + length($word);
      $sep = ' ';
    }
    foreach my $word (@words) {
      if ($status->{line_length} + length($sep) + length($word)
	> $status->{width}) {
	$status->{text} .= "\n" . ' ' x $status->{indent};
	$status->{line_length} = $status->{indent};
	$sep = '';
      }
      $status->{text} .= $sep . $word;
      $status->{line_length} += length($sep) + length($word);
      $sep = ' ';
    }

  } elsif (ref $elt eq '' && $status->{preformatted}) {
    my @lines = split(/\n/, $elt, -1);
    return if !scalar @lines;	     # No content; do nothing
    if ($status->{pending_vspace}) { # At start of a paragraph
      $status->{text} .=	     # Add vertical space, indent and marker
	  "\n" x $status->{pending_vspace} .
	  ' ' x ($status->{indent} - length($status->{pending_marker})) .
	  $status->{pending_marker};
      $status->{pending_vspace} = 0;
      $status->{pending_marker} = '';
    }
    $status->{text} .= shift @lines;	# Add first line
    $status->{text} .= "\n" . ' ' x $status->{indent} . $_ foreach @lines;

  } elsif ($elt->tag() =~ /^h[1-6]$/) {
    $status->{pending_vspace} = 3;
    $status->{indent} -= 2;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{text} .= "\n------";
    $status->{indent} += 2;
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;

  } elsif ($elt->tag() =~
    /^(?:p|section|article|address|header|footer|main|dl|table)$/) {
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;

  } elsif ($elt->tag() =~ /^(?:div|dt|tr)$/) {
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;

  } elsif ($elt->tag() eq 'dd') {
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;
    $status->{indent} += 4;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{indent} -= 4;
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;

  } elsif ($elt->tag() =~ /^(?:blockquote|figure)$/) {
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    $status->{indent} += 2;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{indent} -= 2;
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;

  } elsif ($elt->tag() =~ /^(?:pre|textarea)$/) {
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    $status->{indent} += 2;
    $status->{preformatted} = 1;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{preformatted} = 0;
    $status->{indent} -= 2;
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;

  } elsif ($elt->tag() eq 'ul') {
    my $save_marker = $status->{pending_marker};
    my $save_nesting = $status->{ul_nesting};
    my $save_list_counter = $status->{list_counter};
    $status->{pending_marker} = $ul_markers[$status->{ul_nesting}];
    $status->{list_counter} = 0;
    $status->{ul_nesting} = ($status->{ul_nesting} + 1) % scalar(@ul_markers);
    $status->{indent} += 4;
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    $status->{indent} -= 4;
    $status->{ul_nesting} = $save_nesting;
    $status->{list_counter} = $save_list_counter;
    $status->{pending_marker} = $save_marker;

  } elsif ($elt->tag() eq 'ol') {
    my $save_marker = $status->{pending_marker};
    my $save_list_counter = $status->{list_counter};
    $status->{pending_marker} = '%2d. ';
    $status->{list_counter} = 1;
    $status->{indent} += 4;
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{pending_vspace} = 2 if $status->{pending_vspace} < 2;
    $status->{indent} -= 4;
    $status->{list_counter} = $save_list_counter;
    $status->{pending_marker} = $save_marker;

  } elsif ($elt->tag() eq 'li') {
    my $save_marker = $status->{pending_marker};
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;
    tree_to_text($_, $status) foreach $elt->content_list();
    $status->{list_counter}++ if $status->{list_counter};
    $status->{pending_marker} = $save_marker;
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;

  } elsif ($elt->tag() =~ /^(?:head|script)$/) {
    # Skip.

  } elsif ($elt->tag() eq 'a' && defined $elt->attr('href')) {
    # TODO: Do we need to handle nested <a> elements?
    my $url = $elt->attr('href') =~ s/^\s+//r =~ s/\s+$//r;
    $url = URI->new_abs($url, $status->{base_url})->canonical->as_string;
    # If the anchor text is not the same as the URL, prefix it with
    # '->' and append the URL, to create an Ivan link.
    if ($url ne $elt->as_trimmed_text()) {
      # TODO: In preformatted text, the first and last space may be too much.
      $elt->unshift_content(' -> ');
      $elt->push_content(' ', $url, ' ');
    }
    tree_to_text($_, $status) foreach $elt->content_list();

  } elsif ($elt->tag() =~ /^(?:option|td|th)$/) {
    $status->{pending_hspace} = 1; # Force a space between these elements
    tree_to_text($_, $status) foreach $elt->content_list();

  } elsif ($elt->tag() eq 'hr') {
    $status->{pending_vspace} = 1 if $status->{pending_vspace} < 1;
    $status->{text} .=
	"\n" x $status->{pending_vspace} .
	' ' x $status->{indent} .
	'--------------------';
    $status->{pending_vspace} = 1;
    $status->{pending_marker} = '';
    $status->{pending_hspace} = 0;

  } elsif ($elt->tag() eq 'br') {
    $status->{pending_vspace} = 1 if !$status->{pending_vspace};

  } elsif ($elt->tag() eq 'img') {
    $elt->push_content($elt->attr('alt') // '[image]');
    tree_to_text($_, $status) foreach $elt->content_list();

  # } elsif ($elt->tag() =~ /^(?:em|i)$/) {
  #   $elt->unshift_content(' /');
  #   $elt->push_content('/ ');
  #   tree_to_text($_, $status) foreach $elt->content_list();

  # } elsif ($elt->tag() =~ /^(?:strong|b)$/) {
  #   $elt->unshift_content(' *');
  #   $elt->push_content('* ');
  #   tree_to_text($_, $status) foreach $elt->content_list();

  # } elsif ($elt->tag() eq 'u') {
  #   $elt->unshift_content(' _');
  #   $elt->push_content('_ ');
  #   tree_to_text($_, $status) foreach $elt->content_list();

  } else {
    tree_to_text($_, $status) foreach $elt->content_list();

  }
}


# html_to_text -- format HTML as plain text
sub html_to_text($$)
{
  my ($document, $url) = @_;
  my ($tree, $status);

  $tree = HTML::TreeBuilder->new();
  $tree->p_strict(1);		# Close P elements automatically
  $tree->parse_content($document);
  $tree->elementify();		# Just to protect against bugs
  $tree->simplify_pres();	# Expand tabs and turn \r\n into \n in <pre>
  $status = {text => '', pending_hspace => 0, pending_vspace => 1,
	     pending_marker => '', indent => 2, preformatted => 0,
	     ul_nesting => 0, base_url => $url, list_counter => 0,
	     line_length => 0, width => 99999};
  tree_to_text($tree, $status);
  # print STDERR $status->{text}, "\n";
  return $status->{text};
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
sub bb_agenda_parser($$$$)
{
  my ($mediatype, $document, $plaintext, $url) = @_;
  my @agenda = ();

  # Agenda topics have a number and are underlined, e.g.:
  #
  # 1. Welcome
  # ----------
  #
  push @agenda, $1 while $plaintext =~ /^\h*[0-9]+.\h*(.+?)\r?\n\h*----/mg;
  return @agenda;
}


# addison_agenda_parser -- find an agenda in Addison Phillips' style
sub addison_agenda_parser($$$$)
{
  my ($mediatype, $document, $plaintext, $url) = @_;
  my @agenda = ();

  # The agenda looks like:
  #
  # ==== AGENDA ====
  # Topic: AOB?
  # Topic: Radar
  #
  # or, in the calendar after conversion to plain text:
  #
  # Agenda
  # ------
  # Topic: AOB?
  # Topic: Radar
  #
  # or (Steven Pemberton's format):
  #
  # AGENDA ITEMS
  # Topic: ACTION-2309: Research xpath3 function definitions (Erik)
  # Topic: ACTION-2315: Report on event handling in web components (Erik)
  #
  # or variations starting with "Agenda topics" or "Agendabot agenda".
  #
  return () if $plaintext !~ /^\h*=+\h*AGENDA\h*=/mi
      && $plaintext !~ /^\h*Agenda\n\h*------/mi
      && $plaintext !~ /^\h*(?:Agendabot\h+)?agenda (?:items|topics)/mi;
  push @agenda, $1 while $plaintext =~ /^\h*Topic\h*:\h*(.+)/mgi;
  return @agenda;
}


# koalie_and_plh_agenda_parser -- find an agenda in Coralie's/Philippe's style
sub koalie_and_plh_agenda_parser($$$$)
{
  my ($mediatype, $document, $plaintext, $url) = @_;
  my @agenda;

  # The agenda already uses Zakim's format, i.e., topics are prefixed
  # with "agenda+":
  #
  # agenda+ Roundtable
  # agenda+ TPAC registration
  #
  push @agenda, $1 while $plaintext =~ /^\h*agenda\+\h+(.*)/mgi;
  return @agenda;
}


# contents_to_text -- return content, links as Ivan links, without nested lists
sub contents_to_text($$);
sub contents_to_text($$)
{
  my ($element, $baseurl) = @_;
  my $s = '';

  foreach my $child ($element->content_list()) {
    if ($child->tag() eq '~text') {
      $s .= $child->attr('text');
    } elsif ($child->tag() eq 'a' && $baseurl) {
      $s .= ' -> ' . contents_to_text($child, undef) . ' ' .
	  URI->new_abs($child->attr('href'), $baseurl)->canonical->as_string .
	  ' ';
    # } elsif ($child->tag() eq 'b' || $child->tag() eq 'strong') {
    #   $s .= ' *' . contents_to_text($child, $baseurl) . '* ';
    # } elsif ($child->tag() eq 'i' || $child->tag() eq 'em') {
    #   $s .= ' /' . contents_to_text($child, $baseurl) . '/ ';
    # } elsif ($child->tag() eq 'u') {
    #   $s .= ' _' . contents_to_text($child, $baseurl) . '_ ';
    # } elsif ($child->tag() eq 'code' || $child->tag() eq 'code') {
    #   $s .= ' `' . contents_to_text($child, $baseurl) . '` ';
    } elsif ($child->tag() ne 'ol' && $child->tag() ne 'ul') {
      $s .= contents_to_text($child, $baseurl);
    }
  }
  return $s;
}


# html_list_agenda_parser -- find an agenda as an OL or UL list in HTML
sub html_list_agenda_parser($$$$)
{
  my ($mediatype, $document, $plaintext, $url) = @_;
  my (@agenda, $tree, $start, $h, $s);

  return () if $mediatype !~ /^text\/html\b/i;
  $tree = HTML::TreeBuilder->new_from_content($document);
  $tree->objectify_text();

  # Find the word "agenda", assumed to indicate the start of the agenda.
  $start = $tree->look_down(_tag=>'~text', text=>qr/\bagenda\b/i);
  return () if !$start;

  # Find the first OL or UL after $start. Look in right siblings, then
  # right siblings of the parent, than right siblings of the parent's
  # parent, etc.
  while ($start && $start->tag() ne 'ol' && $start->tag() ne 'ul') {
    until (!$start || ($h = $start->right)) {$start = $start->parent()}
    $start = $h;
  }
  return () if !$start;

  # Convert the list items to text.
  foreach my $item ($start->content_list()) {
    push @agenda, contents_to_text($item, $url) if $item->tag() eq 'li';
  }

  return @agenda;
}


# two_level_agenda_parser -- find an agenda in the style of Axel Polleres
sub two_level_agenda_parser($$$$)
{
  my ($mediatype, $document, $plaintext, $url) = @_;
  my @agenda;
  my $i = 10000;		# Bigger than any expected indent
  my $delim;			# The least indented marker
  my $n = 0;			# The number of occurrences of the marker

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
  # return () if $plaintext !~ /\bAgenda\b/i;

  # If the word "agenda" occurs, remove text before the line that contains it.
  $plaintext =~ s/^.*?\n(?=[^\n]*\bagenda\b)//is;

  # Store the least indented marker in $delim, if any. If several
  # markers are indented the same, use the one that occurs most often.
  #
  foreach my $d (qr/\(?\d+\)/, qr/\d+\.(?:\d+\h)?/, qr/\d+\h*-/, qr/\*\h/,
    qr/-\h/, qr/•\h/, qr/◦\h/, qr/⁃\h/) {
    if ($plaintext =~ /^(\h*)$d/m) {
      my $indent = length $1;
      my $d1 = qr/\h{0,$indent}$d/;		# or: $1 . $d
      my @matches = $plaintext =~ /^$d1/mg;

      if ($indent < $i || ($indent == $i && scalar(@matches) > $n)) {
	$i = $indent;
	$delim = $d1;
	$n = scalar @matches;
      }
    }
  }
  return () if !defined $delim;

  push @agenda, $1 while $plaintext =~ /^$delim\h*+(.+?)\s*$/mg;
  return @agenda;
}


# quoted_agenda_parser -- find an agenda in email that is a quoted with ">"
sub quoted_agenda_parser($$$$)
{
  my ($mediatype, $document, $plaintext, $url) = @_;

  # Remove one level of quoting, or return empty if there are no quoted lines.
  $plaintext =~ s/^(\h*)>(?: |$)/$1/mg or return ();

  # Try each of the parsers (including ourselves) on that new plaintext.
  for my $parser (@parsers) {
    my @h = &$parser('text/plain', undef, $plaintext, $url);
    return @h if scalar(@h) > 0;
  }
  return ();
}



# Main body

my (%opts, $ssl, $user, $password, $host, $port, %passwords, $channel);

binmode(STDERR, ":utf8");

$Getopt::Std::STANDARD_HELP_VERSION = 1;
getopts('c:C:e:km:n:N:o:r:v', \%opts) or die "Try --help\n";

if (!$opts{'o'}) {
  # The single argument must be an IRC-URL.
  #
  die "Usage: $0 [options] [--help] irc[s]://server...\n" if $#ARGV != 0;
  $ARGV[0] =~ m/^(ircs?):\/\/(?:([^:]+):([^@]+)?@)?([^:\/#?]+)(?::([^\/]*))?(?:\/(.+)?)?$/i or
      die "Argument must be a URI starting with `irc:' or `ircs:'\n";
  $ssl = $1 eq 'ircs';
  $user = $2 =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/egr if defined $2;
  $password = $3 =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/egr if defined $3;
  $host = $4;
  $port = $5 // ($ssl ? 6697 : 6667);
  $channel = $6 =~ s/%([0-9A-Fa-f]{2})/chr(hex($1))/egr if defined $6;
  $channel = '#' . $channel if defined $channel && $channel !~ /^[#&]/;
  # TODO: Do something with other parameters, such as a key
  if (defined $user && !defined $password) {
    print "IRC password for user \"$user\": ";
    ReadMode('noecho');
    $password = ReadLine(0);
    ReadMode('restore');
    print "\n";
  }
}

my $bot = AgendaBot->new(
  server => $host,
  port => $port,
  ssl => $ssl,
  charset => $opts{'C'} // 'utf8',
  username => $user,
  password => $password,
  nick => $opts{'n'} // 'agendabot',
  name => $opts{'N'} // 'AgendaBot '.VERSION.' '.HOME,
  channels => (defined $channel ? [$channel] : []),
  rejoinfile => $opts{'r'},
  passwords_file => $opts{'c'},
  security_exceptions_uri => $opts{'e'},
  verbose => defined $opts{'v'},
  ssl_verify_hostname => $opts{'k'} ? 0 : 1,
  associations_file => $opts{'m'} // 'agendabot.assoc');

if ($opts{'o'}) {
  open my $fh, ">$opts{'o'}" or die "$opts{'o'}: $?";
  $bot->parse_and_print_agenda({channel => $opts{'o'}, who => $fh}, $_)
      foreach @ARGV;
  close $fh;
} else {
  $bot->run();
}



=encoding utf8

=head1 NAME

agendabot - IRC 'bot that gets a meeting agenda from a URL

=head1 SYNOPSIS

agendabot [-n I<nick>] [-N I<name>] [-c I<passwordfile>] [-e I<URL>]
[-m I<associations-file>] [-r rejoin-file] [-C charset] [-v] I<URL>

agendabot [-o I<outputfile>] [-c I<passwordfile>] [-e I<URL>]
[-v] I<URL> [I<URL>...]

=head1 DESCRIPTION

Agendabot is an IRC 'bot (unless the B<-o> option is given). It
connects to the IRC server given by the URL (e.g.,
"irc://irc.example.org/"), waits until it is /invite'd to one or more
channels and then watches those channels for lines of the form

 agenda: URL

(where URL is an arbitrary URL) and tries to find a meeting agenda at that
URL. If it succeeds in finding an agenda, it prints it on IRC in a
form suitable for the Zakim 'bot, i.e., it prints something like:

 clear agenda
 agenda+ TOPIC1
 agenda+ TOPIC2

It tries various parsers in turn to read the document and uses the
results of the parser that recognized the most agenda topics. (See
L</"Agenda formats"> below.)

=head2 W3C mail archives and W3C group calendars

You can also tell agendabot to search for agendas in a W3C mail
archive or a W3C group calendar and let it discover the URL of the
agenda by itself. First you need to tell agendabot where to search
with a command such as this:

 agendabot, this is i18n-core

You only need to do this once. Agendabot will find the relevant
mailing lists and calendars and remember them, even when it
disconnects and later reconnects to the same channel. Thereafter you
only need to say

 agendabot, find agenda

and agendabot will respond with the URL of the agenda and the agenda
itself (or a message that it didn't find any agenda)

=head2 Specifying the IRC server

The I<URL> argument specifies the server to connect to. It must be of
the following form:

=over

I<protocol>://I<username>:I<password>@I<server>:I<port>/I<channel>

=back

But many parts are optional. The I<protocol> must be either "irc" or
"ircs", the latter for an SSL-encrypted connection.

If the I<username> is omitted, the I<password> and the "@" must also
be omitted. If a I<username> is given, but the I<password> is omitted,
agendabot will prompt for it. (But if both the ":" and the I<password>
are omitted, agendabot assumes that no password is needed.)

The I<server> is required.

If the ":" and the I<port> are omitted, the port defaults to 6667 (for
irc) or 6697 (for ircs).

If a I<channel> is given, agendabot will join that channel (in
addition to any channels it rejoins, see the B<-r> option). If the
I<channel> does not start with a "#" or a "&", agendabot will add a
"#" itself.

Omitting the password is useful to avoid that the password is visible
in the list of running processes or that somebody can read it over
your shoulder while you type the command.

Note that many characters in the username or password must be
URL-escaped. E.g., a "@" must be written as "%40", ":" must be written
as "%3a", "/" as "%2f", etc.

=head2 IRC commands

For more details about the commands agendabot understands on IRC, see
the manual, or use the "agendabot, help" command on IRC. Here is a
brief list:

=over

=item "/invite agendabot"

When agendabot is invited to a channel, it tries to join that channel.

=item" agenda: I<URL>"

Makes agendabot try and retrieve the URL, parse the result to try and
find an agenda, and print that agenda on IRC in the right format for
Zakim 'bot. Agendabot prints an error message if it fails to find an
agenda.

=item "agendabot, bye"

Tells agendabot to leave the current channel.

=item "agendabot, help" and "agendabot help I<command>"

Ask agendabot to give a brief description of itself. To get
information about a specific command, such as "find", type "agendabot,
help find".

=item "agendabot, find agenda"

Ask agendabot to look in the mail archives and the W3C group calendar
for an agenda. It looks
back one week. To search other periods, add a number of days or weeks,
e.g.: "agendabot, find agenda since 10 days".

=item "agendabot, suggest agenda"

Ask agendabot to look in the mail archives for messages that have
"agenda+" in their subject. It looks for message less than one week
old. To search other periods, add a number of days or weeks, e.g.,
"agendabot, suggest agenda since 2 weeks".

=item "agendabot, accept"

Ask agendabot to turn the suggested agenda into an actual agenda.

=item "agendabot, this is I<name>" and "agendabot, this is I<URL>"

Tell agendabot in what mailing list or calendar to search for
agendas. The short
form, e.g., "agendabot, this is style" or "agendabot, this is w3t",
causes agendabot to guess the URL. In this case, it will find
".../Public/www-style/" and ".../Team/w3t". (It may not have access to
password-protected archives, see the B<-c> option.)

Note that a short name may resolve to multiple mailing lists and
calendars. E.g., "i18n-core" is the name of a calendar
"...groups/wg/i18n-core/calendar", and two mailing lists,
"...Member/member-i18n-core/", and "...Public/public-i18n-core/". If
agendabot finds too many sources to search in, use the full URLs
instead.

You may give multiple names and URLs, separated by commas or the word
"and". E.g.: "agendabot, this is foo and bar". Agendabot will search
in all given mailing lists and calendars.

=item "agendabot, forget"

Ask agendabot to forget the mailing lists and calendars for this
channel. Subsequent "find" and "suggest" commands will fail, until a
new mailing list or calendar is set with the "this is" command.

=item "agendabot, status"

Ask agendabot to display the URL of the mailing lists and calendars
where it searches for agendas.

=back

All commands can be normal messages or "/me" messages.

Once started, the bot doesn't stop (unless a serious error occurs).
Stop it with Control-C or the kill(1) command.

=head2 Agenda formats

Agendabot currently recognizes agendas written in one of the following
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

=item 4.

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

I<passwordfile> is a file with login names, passwords and cookies for
various servers. When agendabot is trying to retrieve a document over
HTTP and receives an authentication request, it looks in this
file. The file must contain lines with four tab-separated
fields: host:port, realm, login and password. The
port is required. Empty lines and lines that start with "#" are
ignored. Other lines cause an error. E.g.:

 # This is a password file
 example.org:443	Member login/passw	joe	secret
 info.example.org:443	Member login/passw	joe	secret

The passwords column can be encrypted with a passphrase. To indicate
that it is indeed encrypted, include a line "!encrypted", e.g., like
this:

 # This is a password file with encrypted passwords
 !encrypted
 example.org:443	Member login/passw	joe	34AF323AA218928
 info.example.org:443	Member login/passw	joe	125656340CD0990

When agendabot starts, it will prompt for the passphrase to decrypt
the passwords.

The password file must be in UTF-8.

=item B<-e> I<URL>

Normally, agendabot only uses the password file (option B<-c>) when it
is asked to retrieve an agenda on a server-local channel, i.e., a
channel that starts with "&". It will refuse to retrieve
password-protected agendas on public channels or in private messages.
The B<-e> option points to a list of exceptions. Each line in the
indicated file consists of a channel name and a URL prefix, separated
by a tab. If a URL is asked for on a channel and the channel name and
the URL match a line in this file, agendabot will try to retrieve the
agenda, even if it is password-protected. Empty lines and lines
that start with "# " are ignored. E.g.:

 # Security exceptions
 #i18n	https://lists.w3.org/Archives/Member/member-i18n-core/

The file with exceptions may itself be password-protected. Note that
it is a URL, not a file name. To refer to a local file, use a "file:".

=item B<-m> I<associations-file>

When IRC channels are associated with mailing lists and calendars (so
that agendabot
knows which archives to search for agendas), those associations are
stored in a file. This way, when agendabot is restarted, it still
knows the associations. This option specifies the file. The default is
agendabot.assoc.

The file contains lines consisting of three parts separated by tabs: a
channel name, a space-separated list of URLs, and the type of the
association (mailing list or calendar). Empty lines are ignored and
lines that
start with "#" but not with a valid channel name are considered
comments and are also ignored. But note that the file will be
overwritten and the comments will be lost as soon as agendabot
receives a new mailing list or calendar association on IRC.

=item B<-r> I<rejoin-file>

If the option B<-r> is given, agendabot joins the channels in
I<rejoin-file> as soon as it connects to the server, without having to
be invited. It updates the file when it is invited to an additional
channel or is dismissed from one. This way, when agendabot is stopped
and then restarted (with the same B<-r> option), it will automatically
rejoin the channels it was on when it was stopped.

=item B<-k>

Do not verify the hostname against the SSL certificate when
downloading a potential agenda from an HTTPS URL. This makes the
download insecure, but allows downloading an agenda from a web site
with an expired or self-signed certificate.

=item B<-C> I<charset>

Set the character encoding for messages. This should match what the
IRC server expects. The default is utf8.

=item B<-v>

Be verbose. Makes the 'bot print a log to standard error output of
what it is doing.

=item B<-o> I<outputfile>

Agendabot does not connect to
an IRC server, but downloads the documents that are given as I<URL>
arguments (there may be more than one) and tries to extract an agenda
from each of them. Those agendas are then written to the
I<outputfile>. If I<outputfile> is "-", they are written to the
standard output.

This option is mainly meant for regression testing of the built-in
parsers, but may be useful to get an agenda from the command line.

=back

=head1 BUGS

Parsing of XHTML/HTML/HTML5/XML is not complete. In particular
occurrences of E<lt> or E<gt> in attributes or CDATA sections may
cause missed or false matches.

The character encoding of an HTML file may be wrong, if it is declared
with a C<meta> element and is different from that set by the HTTP
header C<Content-Type>. Agendabot only uses the latter.

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
