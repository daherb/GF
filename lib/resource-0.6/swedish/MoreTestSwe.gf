--# -path=.:../abstract:../../prelude

concrete MoreTestSwe of MoreTest = StructuralSwe ** open Prelude, SyntaxSwe in {

flags startcat=Phr ; lexer=text ; unlexer=text ;

-- a random sample from the lexicon

lin
--aFin, aFager, aGrund, aVid, aVaken, aKorkad,  aAbstrakt

Big = stor_25 ;
Small = liten_1146 ;
Old = gammal_16 ;
Young = ung_29 ;

American = extAdjective (aFin "amerikansk") ;
Finnish = extAdjective (aFin "finsk") ;
Married = extAdjective (aAbstrakt "gift") ** {s2 = "med"} ;

Happy = aFin "lycklig" ;
Free = aFin "ledig" ;
Slow = aFin "l�ngsam" ;
New = aVid "ny" ;
Own = aVaken "eg" ;
Fresh = aFin "frisk" ; 
Interested = aGrund "intressera" ;


--sApa, sBil sPojke, sNyckel sKam sSak , sVarelse , 
--sNiv�, sParti,sMuseum sRike sLik sRum sHus sPapper 
--sNummer sKikare, sProgram
Finale = extCommNoun NoMasc (sSak "final") ; 
Idea = extCommNoun NoMasc (sBil "id�") ; 
Orientation = extCommNoun NoMasc (sBil "orientering") ; 
Air = extCommNoun NoMasc (sBil "luft") ;
Golf = extCommNoun NoMasc (sBil "golf") ;
Man = extCommNoun Masc man_1144 ;
Bar = extCommNoun NoMasc (sSak "bar") ;
DrinkS = extCommNoun NoMasc (sSak "drink") ;
Book = extCommNoun NoMasc (sSak "bok") ; -- omljud?
Bottle = extCommNoun NoMasc (sApa "flask") ;
Letter = extCommNoun NoMasc (sHus "brev") ;
Fiance = extCommNoun NoMasc (sNiv� "f�stm�") ;
Woman = extCommNoun NoMasc (sApa "kvinn") ;
Car = extCommNoun NoMasc (sBil "bil") ;
House = extCommNoun NoMasc (sHus "hus") ;
Glass = extCommNoun NoMasc (sHus "glas") ;
Light = extCommNoun NoMasc (sHus "ljus") ;
Wine = extCommNoun NoMasc (sParti "vin") ;
Success = extCommNoun NoMasc (sBil "framg�ng") ;
Seriousness = extCommNoun NoMasc (sHus "allvar") ;
Chair = extCommNoun NoMasc (sBil "stol") ;
Fever = extCommNoun NoMasc (sBil "feber") ;
HomeBake = extCommNoun NoMasc (sBil "hembakt") ; --m�ste �ndra sen
Competition = extCommNoun NoMasc (sBil "t�vling") ;
CinemaVisit = extCommNoun NoMasc (sHus "biobes�k") ;

-- Nomen med en-st�llig funktion
Mother = mkFun (extCommNoun NoMasc mor_1) "till" ;
Uncle = mkFun (extCommNoun Masc farbror_8) "till" ;

-- Nomen med tv�-st�llig funktion
Connection = mkFun (extCommNoun NoMasc (sVarelse "f�rbindelse")) "fr�n" ** 
         {s3 = "till"} ;


--vTala, vLeka vTyda vV�nda
--vByta vG�mma vHyra vT�la
--vFinna

-- Intransitiva verb
Walk = extVerb Act g�_1174 ;
Run = extVerb Act (vFinna "spring" "sprang" "sprung") ;
Dance = extVerb Act (vTala "dans") ;
Rain = extVerb Act (vTala "regn") ;
Sleep = extVerb Act (vFinna "sov" "sov" "sov") ;
Sail = extVerb Act (vTala "segl") ;

--Monotransitiva verb
Surprise = extTransVerb (vTala "�verrask") [] ;
Drink = extTransVerb (vFinna "drick" "drack" "druck") [] ;
Love = extTransVerb (vTala "�lsk") [] ;
Send = extTransVerb (vTala "skick") [] ;
Wait = extTransVerb (vTala "v�nt") "p�" ;
Build = extTransVerb (vLeka "bygg") [] ;
Buy = extTransVerb (vLeka "k�p") [] ;
Rent = extTransVerb (vHyra "hyr") [] ;
MakeDo = extTransVerb (vHyra "g�r") [] ; --Hack!
Hug = extTransVerb (vTala "kram") [] ;
Have = extTransVerb hava_1198 [] ;
Like = extTransVerb (vTala "gill") [] ;
Take = extTransVerb (vFinna "ta" "tog" "tag") [] ; --
Start = extTransVerb (vTala "start") [] ;
Play = extTransVerb (vTala "spel") [] ;
Win = extTransVerb (vFinna "vinn" "vann" "vunn") [] ;

--Bitransitiva verb
Give2 = extTransVerb (vFinna "giv" "gav" "giv") [] ** {s3 = ""} ; -- ge
Envy = extTransVerb (vTala "missunn") [] ** {s3 = ""} ; 

--(Bi)transverb med obligatorisk pp
Give = extTransVerb (vFinna "giv" "gav" "giv") [] ** {s3 = "till"} ; -- ge
Accustomize = extTransVerb (vFinna "v�nj" "vande" "van")  [] ** {s3 = "vid"} ; -- 
Steal = extTransVerb (vHyra "stj�l") [] ; -- oh o hur ska detta b�jas?

Devote = extTransVerb (vTala "�gn")  [] ** {s3 = "�t"} ; -- 
Remind = extTransVerb (vT�la "p�minn")  [] ** {s3 = "om"} ; -- 

Prefer = extTransVerb (vFinna "f�redrag" "f�redrog" "f�redrag") [] ** {s3 = "framf�r"} ; --- f�redra
Put = extTransVerb (vFinna "s�tt" "satte" "satt") [] ** {s3 = "i"} ; 
Talk2 = extTransVerb (vTala "tal") ["med"] ** {s3 = "om"} ;


-- Verb med satskomplement
-- kan bara ta fullst�ndiga satser, inledda med att?
Say = extVerb Act (vLeka "s�g") ;
Prove = extVerb Act (vTala "bevis") ;


Hope  = extVerb Pass(vTala "hopp") ;-- har ej deponens?
Believe = extTransVerb (vTala "lit") "p�" ;
Know = extVerb Act (vTala "vet") ;

-- Verb som tar infinitivt verb, "ha" tar emellertid supinum
UseToVV = extVerb Act (vTala "bruk") ** {isAux = True} ;
RefuseVV    = extVerb Act (vTala "v�gr") ** {isAux = variants{False;True}} ;
HaveVV    = extVerb Act (vHyra "har") ** {isAux = True} ; -- finns ju redan, m�ste kolla
SeemVV = extVerb Act (vTala "verk")  ** {isAux = True};
ShallVV = extVerb Act (vTala "skull")  ** {isAux = True};
ContinueVV = extVerb Act (vFinna "forts�tt" "fortsatte" "fortsatt")  ** {isAux = variants{False;True}} ;
DeserveVV = extVerb Act (vTala "f�rtj�n")  ** {isAux = variants{False;True}} ;
TryVV    = extVerb Act (vLeka "f�rs�k") ** {isAux = variants{False;True}} ;

--Partikelverb
SwitchOn = mkDirectVerb (extVerbPart Act (vFinna "s�tt" "satte" "satt") "p�") ;
SwitchOff = mkDirectVerb (extVerbPart Act (vLeka "st�ng") "av") ;
ArriveX = extVerbPart Act (vFinna "komm" "kom" "kommit") "fram" ;

-- Transitiva verb med obligatorisk pp
Talk = extTransVerb (vTala "prat") "med" ;
Trust = extTransVerb (vTala "lit") "p�" ;

--Adverb
Always = advPre "alltid" ;
Well = advPost "bra" ;
Now = advPost "nu" ;
Difficult = advPost "sv�rt" ;
ToNight = advPost "ikv�ll" ;

-- Pronomen
John = mkProperName "Johan" Utr Masc ;
Mary = mkProperName "Maria" Utr NoMasc ;
Pelle = mkProperName "Pelle" Utr Masc ;
Liza = mkProperName "Lisa" Utr NoMasc ;
Phido = mkProperName "Fido" Utr NoMasc ;
Charlie = mkProperName "Kalle" Utr Masc ;
Anders = mkProperName "Anders" Utr Masc ;

-- verbVara = extVerb Act vara_1200 ;
-- verbHava = extVerb Act hava_1198 ;
-- verbFinnas = mkVerb "finnas" "finns" "finns" ;

} ;