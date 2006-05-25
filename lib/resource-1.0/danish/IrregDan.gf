--# -path=.:../scandinavian:../common:../abstract:../../prelude

-- http://users.cybercity.dk/~nmb3879/danishgram3.html

concrete IrregDan of IrregDanAbs = CatDan ** open Prelude, ParadigmsDan in {

  flags optimize=values ;

  lin

  b�re_V = irregV "b�re" "bar" "b�ret" ;--
  bede_V = mkV "bede" "beder" "bedes" "bad" "bedt" "bed" ;--
  bide_V = irregV "bite" "bed" "bitt" ;--
  blive_V = irregV "blive" "blev" "blevet" ;
  br�nde_V = irregV "br�nde" "brant" "br�nt" ;--
  bringe_V = irregV "bringe" "bragte" "bragt" ;--
  burde_V = irregV "burde" "burde" "burdet" ;--
  d�_V = irregV "d�" "d�de" "d�d" ;
--  dra_V = mkV "dra" "drar" "dras" "drog" (variants {"dradd" ;-- "dratt"}) "dra" ;--
  drikke_V = irregV "drikke" "drak" "drukket" ;
--  drive_V = irregV "drive" (variants {"drev" ;-- "dreiv"}) "drevet" ;--
--  eie_V = irregV "eie" (variants {"eide" ;-- "�tte"}) (variants {"eid" ;-- "�tt"}) ;--
  falle_V = irregV "falle" "falt" "falt" ;--
  f�_V = irregV "f�" "fik" "f�et" ;
  finde_V = irregV "finde" "fand" "fundet" ;--
  flyde_V = irregV "flyde" "fl�d" "flytt" ;--
  flyve_V = irregV "flyve" "fl�g" "flydd" ;--
  foretrekke_V = irregV "foretrekke" "foretrakk" "foretrukket" ;--
  forlade_V = irregV "forlade" "forlod" "forladet" ;
  forst�_V = irregV "forst�" "forstod" "forst�tt" ;--
  fort�lle_V = irregV "fort�lle" "fortalte" "fortalt" ;--
  fryse_V = irregV "fryse" "fr�s" "frosset" ;--
  g�_V = irregV "g�" "gik" "g�et" ;
  give_V = irregV "give" "gav" "givet" ;
--  gjelde_V = irregV "gjelde" (variants {"gjaldt" ;-- "galdt"}) "gjeldt" ;--
  gnide_V = irregV "gnide" "gned" "gnidd" ;--
  g�re_V = irregV "g�re" "gjorde" "gjort" ;
  have_V =  mkV "have" "har" "havde" "haft" nonExist "hav" ;
  hente_V = irregV "hente" "hentet" "hendt" ;--
--  hete_V = irregV "hete" (variants {"het" ;-- "hette"}) "hett" ;--
--  hjelpe_V = irregV "hjelpe" "hjalp" "hjulpet" ;--
  holde_V = irregV "holde" "holdt" "holdt" ;--
  komme_V = irregV "komme" "kom" "kommet" ;
  kunne_V = irregV "kunne" "kunne" "kunnet" ;
  lade_V = irregV "lade" "lod" "ladet" ;
  l�gge_V = irregV "l�gge" "lagde" "lagt" ;
  le_V = irregV "le" "lo" "leet" ;
  ligge_V = irregV "ligge" "l�" "ligget" ;
  l�be_V = irregV "l�be" "l�b" "l�bet" ;
  m�tte_V = irregV "m�tte" "m�tte" "m�ttet" ;
  renne_V = irregV "renne" "rant" "rent" ;--
  s�lge_V = irregV "s�lge" "solgte" "solgt" ;
  s�tte_V = irregV "s�tte" "satte" "sat" ;
  se_V = irregV "se" "s�" "set" ;
  sidde_V = irregV "sidde" "sad" "siddet" ;
  sige_V = irregV "sige" "sagde" "sagt" ;
  sk�re_V = irregV "sk�re" "skar" "sk�ret" ;--
  skrive_V = irregV "skrive" "skrev" "skrevet" ;
  skulle_V = irregV "skulle" "skulle" "skullet" ;
  sl�_V = irregV "sl�" "slog" "sl�tt" ;--
  sove_V = irregV "sove" "sov" "sovet" ;
  sp�rge_V = irregV "sp�rge" "spurgte" "spurgt" ;
  springe_V = irregV "springe" "sprang" "sprunget" ;--
  st�_V = irregV "st�" "stod" "st�et" ;
  stikke_V = irregV "stikke" "stakk" "stukket" ;--
  synge_V = irregV "synge" "sang" "sunget" ;--
  tage_V = irregV "tage" "tog" "taget" ;
--  treffe_V = irregV "treffe" "traff" "truffet" ;--
--  trives_V = irregV "trives" "trivdes" (variants {"trives" ;-- "trivs"}) ;--
  vide_V = irregV "vide" "vidste" "vidst" ;

}

-- readFile "vrbs.tmp" >>= mapM_ (putStrLn . (\ (a:_:b:c:_) -> "  " ++ a ++ "_V = irregV \"" ++ a ++ "\" \"" ++ b ++ "\" \"" ++ c ++ "\" ;") . words) . lines