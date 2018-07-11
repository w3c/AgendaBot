#!/usr/bin/perl
#
# This IRC 'bot looks for lines of the form "agenda: URL" (where URL
# is some URL) and tries to find a meeting agenda at that URL. If it
# succeeds in finding an agenda, it prints it on IRC in a form
# suitable for the Zakim 'bot. (More documentation at the end in
# perlpod format.)
#
# TODO: When given a -c option, agendabot loads all passwords into
# memory. It should either not keep them in memory permanently, or
# encrypt them.
#
# TODO: Fix information leak: Agendabot will extract an agenda from
# any resource it has a password for, even if the person asking for
# the agenda wouldn't be able to read that agenda himself.
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

use constant HOME => 'https://www.w3.org/SOME_URL_FOR_AgendaBot';
use constant VERSION => '0.1';

my @parsers = (
  \&bb_agenda_parser,
  \&addison_agenda_parser,
  \&vivien_agenda_parser);


# get -- get the contents of a file by its URL
sub get($$)
{
  my ($self, $uri) = @_;
  my ($ua, $res, $realm, $user, $password, $user_and_pass, $challenge);
  my %passwords;

  $ua = LWP::UserAgent->new;
  $ua->agent(blessed($self) . '/' . VERSION);
  $ua->default_header('Accept' => 'text/*');
  $ua->timeout(10);
  $ua->env_proxy;

  $res = $ua->get($uri);

  if ($res->code == 401) {

    # See if we have a password and try again. First extract the realm.
    #
    $challenge = $res->header('WWW-Authenticate');
    if ($challenge !~ /(?:Basic|Digest) realm="(.*)"/i) {
      $self->log("$uri has an unknown authentication scheme: $challenge");
      return (401, undef, undef);
    }
    $realm = $1;

    # See if we know a password for this host and realm.
    #
    %passwords = %{$self->{passwords}};
    $user_and_pass = $passwords{$res->base->host_port . "\t" . $realm};
    if (!defined $user_and_pass) {
      $self->log("No password known for $uri");
      return (401, undef, undef);
    }
    ($user, $password) = split /\t/, $user_and_pass;

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
  ($code, $mediatype, $document) = $self->get($uri);
  return "Sorry, I don't have a password for $uri" if $code == 401;
  return "Sorry, $uri doesn't seem to exist" if $code == 404;
  return "Sorry, could not retrieve $uri (code $code)" if !defined $document;

  # Try all parsers in turn to see which one returns the longest agenda.
  #
  for my $parser (@parsers) {
    my @h = &$parser($mediatype, $document);
    @agenda = @h if $#h > $#agenda;
  }
  $self->log("Found ".($#agenda+1)." topics in $uri");
  return "Sorry, I did not recognize any agenda in $uri" if $#agenda == -1;

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
  } elsif ($addressed && $text =~ /^bye$/i) {
    $self->part_channel($channel);
    return undef;		# No reply
  } elsif ($addressed) {
    return "Sorry, I don't understand \"$text\". Try \"$me, help\".";
  }
}


# help -- handle an "agendabot, help" message
sub help($$)
{
  my ($self, $info) = @_;
  my $me = $self->nick();		# Our own name

  return "I am an instance of " . blessed($self) . " " . VERSION . " (" . HOME
      . ") I look for \"agenda: URL\" to try and extract an agenda for Zakim. "
      . "Invite me to a channel with \"/invite $me\". "
      . "Dismiss me with \"$me, bye\"";
}


# connected -- log a successful connection
sub connected($)
{
  my ($self) = @_;

  $self->log("Connected to " . $self->server());
}


# log -- print a message to STDERR, if -v (verbose) was specified
sub log
{
  my ($self, @messages) = @_;
  my $now = strftime "%Y-%m-%dT%H:%M:%SZ", gmtime;

  # Prefix all log lines with the current time.
  #
  $self->SUPER::log(map($now.' '.$_, @messages)) if $self->{'verbose'};
}


# read_passwords_from_file -- read username/password for each domain/realm
sub read_passwords_from_file($)
{
  my ($path) = @_;
  my %passwords = ();
  my ($fh);

  open $fh, "<", $path or die "Cannot read $path\n";

  # Each line must be HOST:PORT\tREALM\tLOGIN\tPASSWORD. Empty lines
  # and lines that start with "#" are ignored.
  #
  # TODO: Can there be tabs in any of these fields?
  #
  while (<$fh>) {
    if (/^#/) {}
    elsif (/^\s*$/) {}
    elsif (/^(.*\t.*)\t(.*\t.*)$/) {$passwords{$1} = $2;}
    else {die "$path:$.: Syntax error: line does not have four fields.";}
  }

  close $fh;
  return %passwords;
}


# The following subroutines are parsers that try to find a meeting
# agenda in a given text string. Each parser implements a different
# style of writing an agenda. They return an array in which each item
# is an agenda topic. An empty arry means no agenda was found.
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
  $document =~ s/<[^>]*>//g if $mediatype =~ /html|xml/; # Strip tags
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
  $document =~ s/<[^>]*>//g if $mediatype =~ /html|xml/; # Strip tags
  return () if $document !~ /==\s*AGENDA\s*==/i;
  push @agenda, $1 while $document =~ /^\s*Topic\s*:\s*(.+)/mgi;
  return @agenda;
}


# vivien_agenda_parser -- find an agenda in Vivien's style
sub vivien_agenda_parser($$)
{
  my ($mediatype, $document) = @_;
  my @agenda;

  # The agenda follows "Agenda:" and items start with a "*":
  #
  # Agenda:
  # * Payment system
  # * AOB?
  #
  $document =~ s/<[^>]*>//g if $mediatype =~ /html|xml/; # Strip tags
  $document =~ s/.*?\nAgenda://si or return ();
  push @agenda, $1 while $document =~ /^\s*\*\s*(.*)/mg;
  return @agenda;
}


# Main body

my (%opts, $ssl, $host, $port, %passwords);

$Getopt::Std::STANDARD_HELP_VERSION = 1;
getopts('c:n:N:v', \%opts) or die "Try --help\n";
die "Usage: $0 [options] [--help] irc[s]://server...\n" if $#ARGV != 0;

# The single argument must be an IRC-URL.
#
$ARGV[0] =~ m#^(ircs?)://(?:[^:@/]+:[^@/]*@)?([^:/]+)(?::([^/]*))?/#i or
    die "Argument must be a URI starting with `irc:' or `ircs:'\n";
$ssl = $1 eq 'ircs';
$host = $2;
$port = $3 // ($ssl ? 6697 : 6667);
# TODO: Do something with the userinfo ("user:password")
# TODO: Do something with any passed channel name
# TODO: Do something with other parameters, such as a key

%passwords = read_passwords_from_file($opts{'c'}) if defined $opts{'c'};

my $bot = AgendaBot->new(
  server => $host,
  port => $port,
  ssl => $ssl,
  nick => $opts{'n'} // 'agendabot',
  name => $opts{'N'} // 'AgendaBot',
  passwords => \%passwords // {},
  verbose => defined $opts{'v'});

$bot->run();




=head1 NAME

agendabot - IRC 'bot that gets a meeting agenda from a URL

=head1 SYNOPSIS

agendabot [-n I<nick>] [-N I<name>] [-c passwordfile] [-v] I<URL>

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

In this format, the agenda follows a line "Agenda:" and topics are
lines that start with an asterisk. E.g.:

 Agenda:
 * Payment system
 * AOB?

Any text before, after or in between these lines is ignored. The above
results in the following agenda:

 clear agenda
 agenda+ Payment system
 agenda+ AOB?

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