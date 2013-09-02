use strict;
use warnings;

open(my $tagged,"<",$ARGV[0]);
open(my $xml,">",$ARGV[1]);
print $xml "<tagged>\n";
while (my $l = <$tagged>)
{
  my @cols = split(/\s+/,$l);
  my $word = $cols[0];
  my $pos;
  my $atts;
  if ($cols[1] =~ /.+:.+/)
  {
    my @tmp = split(/:/,$cols[1]);
    $pos = $tmp[0];
    $atts = "atts=\"$tmp[1]\"";
  }
  else
  {
    $pos = $cols[1];
    $atts = "";
  }
  my $stem="";
  $cols[2] =~ s/(")/'/g;
  $stem = "stem=\"$cols[2]\"" if (length($cols[2])>0); 
  $stem =~ s/[<>]//g;
  print $xml "<$pos $stem $atts>$word</$pos>";
}
print $xml "</tagged>\n";