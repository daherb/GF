use strict;
use warnings;
my %freq;
while(my $l = <>)
{
  chomp $l;
  for my $w (split /\s+/,$l)
  {
    $w =~ s/\W//g;
    $freq{$w}++;
  }
}
foreach my $k (sort { $freq{$a} <=> $freq{$b} } keys %freq)
{
  print "$k\t$freq{$k}\n";
}
