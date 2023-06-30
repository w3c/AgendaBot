#!/usr/bin/env perl
#
# Compute the encrypted or decrypted version of a password. It gets
# three arguments: a command ("encrypt" or "decrypt"), a password to
# encrypt or decrypt and a passphrase to encrypt/decrypt it with. The
# output is a base64 string that is the encrypted version of the
# password, or the password that is decrypted from the base64-encoded
# string.
#
# If an argument is missing, the program will prompt for it. Prompting
# for the passphrase is done with echo off.
#
# The encrypted password is computed by taking the passphrase,
# converting it to a UTF-8 encoded byte string, computing the SHA246
# digest of it, and XOR'ing that with the UTF-8 encoded password. The
# resulting bitstring is base-64 encoded.

use strict;
use warnings;
use Encode qw(encode decode);
use Digest::SHA qw(sha256);
use MIME::Base64;
use Term::ReadKey;		# To read a password without echoing

my $progname = $0 =~ s|.*/||r;
my $USAGE = "Usage: $progname encrypt|decrypt [password] [passphrase]";


# decrypt -- decrypt a base-64-encoded, encrypted password
sub decrypt($$)
{
  my ($encrypted, $passphrase) = @_;
  my ($mask, $password, $repeat, $len);

  $mask = sha256(encode('UTF-8', $passphrase)); # SHA256 digest of passphrase
  $encrypted = decode_base64($encrypted);	# Get bitstring from base64
  $len = length($mask);				# Length of mask
  $repeat = int((length($encrypted) + $len - 1) / $len);
  $mask = $mask x $repeat;			# Make mask long enough
  $password = $encrypted ^ $mask;		# Unmask the password
  $password = decode('UTF-8', $password);	# Convert to a Perl string
  $password =~ s/\0+$//;			# Trim null bytes
  return $password;
}


# encrypt -- encrypt a password and base64-encode it
sub encrypt($$)
{
  my ($password, $passphrase) = @_;
  my ($mask, $encrypted, $repeat, $len);

  $mask = sha256(encode('UTF-8', $passphrase)); # SHA256 digest of passphrase
  $password = encode('UTF-8', $password);	# Perl string to bitstring
  $len = length($mask);				# Length of mask
  $repeat = int((length($password) + $len - 1) / $len);
  $mask = $mask x $repeat;			# Make mask long enough
  $encrypted = $password ^ $mask;		# Mask the pasword
  $encrypted = encode_base64($encrypted, '');	# Convert to base64 string
  return $encrypted;
}


my ($command, $password, $passphrase);

die "$USAGE\n" if !defined $ARGV[0] || $#ARGV >= 3;

if ($ARGV[0] =~ /^e(n(c(r(y(pt?)?)?)?)?)?$/i) {$command = "encrypt"}
elsif ($ARGV[0] =~ /^d(e(c(r(y(pt?)?)?)?)?)?$/i) {$command = "decrypt"}
else {die "$USAGE\n"}

if (defined $ARGV[1]) {
  $password = $ARGV[1];
} elsif ($command eq "encrypt") {
  print "Password to encrypt: ";
  $password = ReadLine(0);
} else {
  print "Password to decrypt: ";
  $password = ReadLine(0);
}
chomp $password;

if (defined $ARGV[2]) {
  $passphrase = $ARGV[2];
} else {
  print "Passphrase: ";
  ReadMode('noecho');
  $passphrase = ReadLine(0);
  ReadMode('restore');
  print "\n";
}
chomp $passphrase;

if ($command eq "encrypt") {
  print encrypt($password, $passphrase), "\n";
} else {
  print decrypt($password, $passphrase), "\n";
}
