include tut1.Abs.gf ;

param Ord = dir | indir | sub  ;
lincat S  = {s : Ord => Str} ;
lincat NP = {s : Str} ;
lincat A1 = {s : Str} ;
lincat CN = {s : Str} ;
lin PredA1 Q F = {s = table {
   dir   => Q.s ++ "�r" ++ F.s ; 
   indir => "�r" ++ Q.s ++ F.s ; 
   sub   => Q.s ++ "�r" ++ F.s}} ;
lin CondS A B = {s = table {
   dir   => "om" ++ A.s ! sub ++ "s�" ++ B.s ! indir ; 
   indir => B.s ! indir ++ "om" ++ A.s ! sub ; 
   sub   => B.s ! sub ++ "om" ++ A.s ! sub}} ;
lin DisjA1 F G =
  {s = F.s ++ "eller" ++ G.s} ;
lin Every A =
  {s = "varje" ++ A.s} ;
lin ModA1 A F =
  {s = F.s ++ A.s} ;
lin Number  =
  {s = "tal"} ;
lin Even  =
  {s = "j�mnt"} ;
lin Odd  =
  {s = "udda"} ;
lin Prime  =
  {s = "primt"} ;
lin Zero  =
  {s = "noll"} ;

