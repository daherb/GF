while(<>)
{
  @ws=split(/\s+/,lc $_);
  foreach $w (@ws)
  {
    $w =~ s/\W//g;
    $freq{$w}++ if ($w =~ /que$/);
  }
}
foreach $k (sort { length($b) <=> length($a) } keys %freq)
{
  print "$k - $freq{$k}\n";
}