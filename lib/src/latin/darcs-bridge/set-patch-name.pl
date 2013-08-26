use strict;
use warnings;
open my $p, "<",$ARGV[0] or die "File not found" ;
my $haveSubject = 0 ;
my $comment = "" ;
my $email = "bla\@blubb.de" ;
while (my $l = <$p>)
{
    chomp $l ;
    if (!$haveSubject && $l =~ /^From: (.+)/)
    {
	$email = $1;
    }
    elsif (!$haveSubject && $l =~ /^Subject: \[PATCH \d+\/\d+\] (.+)/)
    {
	$haveSubject = 1 ;
	$comment = $1 ;
    }
    elsif ($haveSubject && !($l =~ /^---$/))
    {
	$comment .= $l;
    }
    elsif ($l =~ /^---$/)
    {
	last;
    }
    else {
	# Before patch
    }
}
print `darcs record --look-for-adds --repodir=$ARGV[1] --name='$comment' --all --author='$email'`;
