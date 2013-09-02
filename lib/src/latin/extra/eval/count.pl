use strict;
use warnings;
my $et = 0;
my $que = 0;
my $atque = 0;
while(my $l = <>)
{
  chomp $l;
  for my $w (split /\s+/,$l)
  {
    $w =~ s/\W//g;
    if ($w eq "et")
    {
      print "et: $l\n";
      $et++ ;
    }
    elsif ($w eq "atque")
    {
      print "atque: $l\n";
      $atque++;
    }
    elsif ($w =~ /que$/)
    {
      print "que: $l\n";
      $que++;
    }
  }
}
print "et: $et\natque: $atque\nque: $que\n";
