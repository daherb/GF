-- File name System/general.Swe.gf

concrete genSystemSwe of genSystem = generalSwe ** open icm100ResSwe in {

---- flags lexer=codelit ; unlexer=codelit ; startcat=DMoveList ;

pattern
greet = ["V�lkommen till videobandspelaren"] ;
quit = "hejd�" ;

lin
ask a = {s = a.s} ;

lin
---Language
change_language = {s = "byt" ++ "spr�k"} ;
language_alt = {s = ["vill du anv�nda svenska eller engelska"]} ;

---Actions
lin
actionQ = {s = "Vad" ++ "kan" ++ "jag" ++ "st�" ++ "till" ++ "tj�nst" ++ "med"} ;

lin
whQuestion w = {s = w.s };
altQuestion a1 a2 = {s = "vill" ++ "du" ++ "spela" ++ "in" ++ a1.s ++ "eller" ++ a2.s};

--- Issue
issue i = {s = i.s} ;

pattern
nil = "[]" ;
}