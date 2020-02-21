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
# Created: 2018-07-09
# Author: Bert Bos <bert@w3.org>
#
# Copyright © 2018 World Wide Web Consortium, (Massachusetts Institute
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

use constant HOME => 'https://dev.w3.org/AgendaBot/manual.html';
use constant VERSION => '0.1';

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
  return 1;
}


# reload - reload configuration files, return error message or undef
sub reload($)
{
  my $self = shift;
  my $errmsg;

  if (($errmsg = $self->read_passwords_file())) {$self->log($errmsg);}
  elsif (($errmsg = $self->read_security_exceptions())) {$self->log($errmsg);}
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
  $self->say({channel => $channel, who => $who, body => "clear agenda"});
  $self->say({channel => $channel, who => $who, body => "agenda+ " . $_})
      foreach (@agenda);

  return undef;
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

  if ($text =~ /^agenda\s*:\s*(.+)$/i) {
    return $self->parse_and_print_agenda($info, $1);
  } elsif ($addressed && $text =~ /^bye\s*\.?$/i) {
    $self->part_channel($channel);
    return undef;			# No reply
  } elsif ($addressed && $text =~ /^reload\s*\.?$/i) {
    return $self->reload() // "configuration files have been reloaded.";
  } elsif ($addressed) {
    return "sorry, I don't understand \"$text\". Try \"$me, help\".";
  } else {
    return $self->SUPER::said($info);
  }
}


# help -- handle an "agendabot, help" message
sub help($$)
{
  my ($self, $info) = @_;
  my $me = $self->nick();		# Our own name

  return "I am an instance of " . blessed($self) . " " . VERSION . " (" . HOME
      . "). I look for \"agenda: URL\" to try and extract an agenda for Zakim. "
      . "Invite me to a channel with \"/invite $me\". "
      . "Dismiss me with \"$me, bye\"";
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


# html_to_text -- remove tags and expand charactet entities
sub html_to_text($)
{
  return $_[0] =~ s/<[^>]*>//gr =~ s/&lt;/</gr =~ s/&gt;/>/gr =~ s/&quot;/"/gr
    =~ s/&apos;/'/gr =~ s/&amp;/&/gr;
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
getopts('c:e:n:N:v', \%opts) or die "Try --help\n";
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
  name => $opts{'N'} // 'AgendaBot',
  passwords_file => $opts{'c'},
  security_exceptions_uri => $opts{'e'},
  verbose => defined $opts{'v'});

$bot->run();




=head1 NAME

agendabot - IRC 'bot that gets a meeting agenda from a URL

=head1 SYNOPSIS

agendabot [-n I<nick>] [-N I<name>] [-c I<passwordfile>] [-e I<URL>]
[-v] I<URL>

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

The commands Agendabot listens for on IRC are:

=over

=item agenda: I<URL>

Makes agendabot try and retrieve the URL, parse the result to try and
find an agenda, and print that agenda on IRC in the right format for
Zakim 'bot. AgendaBot prints an error message if it fails to find an
agenda.

=item /invite agendabot

When AgendaBot is invited to a channel, it tries to join that channel.

=item agendabot, bye

Tells AgendaBot to leave the current channel. (This may also be
written with a colon instead of a comma: "agendabot: bye")

=item agendabot, help

Ask AgendaBot to give a brief description of itself. (This may also be
written with a colon instead of a comma.)

=item agendabot, reload

If Agendabot was started with configuration files (options B<-c> and
B<-e>), this asks Agendabot to read those files again.

=back

All commands can be normal messages, "/me" messages or private
messages ("/msg agendabot").

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

L<Zakim|https://www.w3.org/2001/12/zakim-irc-bot.html>,
L<RRSAgent|https://www.w3.org/2002/03/RRSAgent>,
L<scribe.perl|https://dev.w3.org/2002/scribe2/scribedoc>

=cut
