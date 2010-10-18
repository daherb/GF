concrete BirdsSwe of Birds = MergeSwe ** open SyntaxSwe, ParadigmsSwe, Prelude in {

flags
  coding=utf8 ;

lin
  GaviaStellata = mkCN (mkN "smålom") ;
  GaviaArctica  = mkCN (mkN "storlom") ;
  PodicepsCristatus  = mkCN (mkN "skäggdopping") ;
  PodicepsAuritus = mkCN (mkN "svarthakedopping") ;
  ArdeaCinerea = mkCN (mkN "gråhäger") ;
  BotaurusStellaris = mkCN (mkN "rördrom") ;
  CygnusOlor = mkCN (mkN "knölsvan") ;
  CygnusCygnus = mkCN (mkN "sångsvan") ;
  AnserFabalis = mkCN (mkN "sädgås") ;
  AnserAnser = mkCN (mkN "grågås") ;
  BrantaCanadensis = mkCN (mkN "kanadagås") ;
  BrantaLeucopsis = mkCN (mkA "vitkindad") (mkN "gås") ; -- fixme  vitkindada -> vitkindade
  TadornaTadorna = mkCN (mkN "gravand") ;
  AnasPlatyrhynchos = mkCN (mkN "gräsand") ;
  AnasPenelope = mkCN (mkN "bläsand") ;
  AnasCrecca = mkCN (mkN "kricka") ;
  BucephalaClangula = mkCN (mkN "knipa") ;
  ClangulaHyemalis = mkCN (mkN "alfågel") ;
  SomateriaMollissima = mkCN (mkN "ejder") ;
  MergusMerganser = mkCN (mkN "storskrake") ;
  MelanittaNigra = mkCN (mkN "sjöorre") ;
  HaliaeetusAlbicilla = mkCN (mkN "havsörn") ;
  PandionHaliaetus = mkCN (mkN "fiskgjuse") ;
  ButeoButeo = mkCN (mkN "ormvråk") ;
  AccipiterGentilis = mkCN (mkN "duvhök") ;
  AccipiterNisus = mkCN (mkN "sparvhök") ;
  FalcoTinnunculus = mkCN (mkN "tornfalk") ;
  LagopusLagopus = mkCN (mkN "dalripa") ;
  LagopusMutus = mkCN (mkN "fjällripa") ;
  TetraoUrogallus = mkCN (mkN "tjäder") ;
  LyrurusTetrix = mkCN (mkN "orre") ;
  PhasianusColchicus = mkCN (mkN "fasan") ;
  RallusAquaticus = mkCN (mkN "vattenral") ;
  FulicaAtra = mkCN (mkN "sothöna") ;
  GallinulaChloropus = mkCN (mkN "rörhöna") ;
  GrusGrus = mkCN (mkN "trana") ;
  HaematopusOstralegus = mkCN (mkN "strandskata") ;
  CharadriusHiaticula = mkCN (mkA "större") (mkN "strandpipare" utrum) ;
  PluvialisApricaria = mkCN (mkN "ljungpipare") ;
  VanellusVanellus = mkCN (mkN "tofsvipa") ;
  CalidrisAlpina = mkCN (mkN "kärrsnäppa") ;
  TringaGlareola = mkCN (mkN "grönbena") ;
  TringaOchropus = mkCN (mkN "skogssnäppa") ;
  NumeniusArquata = mkCN (mkN "storspov") ;
  ScolopaxRusticola = mkCN (mkN "morkulla") ;
  GallinagoGallinago = mkCN (mkN "enkelbeckasin") ;
  LymnocryptesMinimus = mkCN (mkN "dvärgbeckasin") ;
  TringaTotanus = mkCN (mkN "rödbena") ;
  TringaErythropus = mkCN (mkN "svartsnäppa") ;
  TringaNebularia = mkCN (mkN "gluttsnäppa") ;
  StercorariusParasiticus = mkCN (mkN "kustlabb") ;
  LarusRidibundus = mkCN (mkN "skrattmås") ;
  LarusCanus = mkCN (mkN "fiskmås") ;
  LarusArgentatus = mkCN (mkN "gråtrut") ;
  LarusFuscus = mkCN (mkN "silltrut") ;
  LarusMarinus = mkCN (mkN "havstrut") ;
  SternaSandvicensis = mkCN (mkA "kentsk") (mkN "tärna") ;
  SternaCaspia = mkCN (mkN "skräntärna") ;
  SternaHirundo = mkCN (mkN "fisktärna") ;
  SternaParadisaea = mkCN (mkN "silvertärna") ;
  AlcaTorda = mkCN (mkN "tordmule") ;
  ColumbaOenas = mkCN (mkN "skogsduva") ;
  ColumbaPalumnbus = mkCN (mkN "ringduva") ;
  StreptopeliaDecaocto = mkCN (mkN "turkduva") ;
  StrixAluco = mkCN (mkN "kattuggla") ;
  StrixUralensis = mkCN (mkN "slaguggla") ;
  BuboBubo = mkCN (mkN "berguv") ;
  AsioFlammeus = mkCN (mkN "jorduggla") ;
  AsioOtus = mkCN (mkN "hornuggla") ;
  AegoliusFunereus = mkCN (mkN "pärluggla") ;
  GlaucidiumPasserinum = mkCN (mkN "sparvuggla") ;
  CuculusCanorus = mkCN (mkN "gök") ;
  CaprimulgusEuropaeus = mkCN (mkN "nattskärra") ;
  PicusViridis = mkCN (mkN "gröngöling") ;
  DryocopusMartius = mkCN (mkN "spillkråka") ;
  JynxTorquilla = mkCN (mkN "göktyta") ;
  DendrocoposMajor = mkCN (lin AP {s=(comparAP (irregA "stor" "större" "störst")).s; isPre=True}) (mkN "hackspett") ;
  DendrocoposMinor = mkCN (lin AP {s=(comparAP (mkA "liten" "litet" "lilla" "små" "mindre" "minst" "minsta")).s; isPre=True}) (mkN "hackspett") ;
  AlaudaArvensis = mkCN (mkN "sånglärka") ;
  LullulaArborea = mkCN (mkN "trädlärka") ;
  ApusApus = mkCN (mkN "tornseglare") ;
  HirundoRustica = mkCN (mkN "ladusvala") ;
  DelichonUrbicum = mkCN (mkN "hussvala") ;
  AnthusPratensis = mkCN (mkN "ängspiplärka") ;
  AnthusTrivialis = mkCN (mkN "trädpiplärka") ;
  MotacillaAlba = mkCN (mkN "sädesärla") ;
  MotacillaFlava = mkCN (mkN "gulärla") ;
  TroglodytesTroglodytes = mkCN (mkN "gärdsmyg") ;
  BombycillaGarrulus = mkCN (mkN "sidensvans") ;
  PrunellaModularis = mkCN (mkN "järnsparv") ;
  LusciniaLuscinia = mkCN (mkN "näktergal") ;
  ErithacusRubecula = mkCN (mkN "rödhake") ;
  LusciniaSvecica = mkCN (mkN "blåhake") ;
  PhoenicurusPhoenicurus = mkCN (mkN "rödstjärt") ;
  OenantheOenanthe = mkCN (mkN "stenskvätta") ;
  SaxicollaRubetra = mkCN (mkN "buskskvätta") ;
  TurdusPhilomelos = mkCN (mkN "taltrast") ;
  TurdusIliacus = mkCN (mkN "rödvingetrast") ;
  TurdusViscivorus = mkCN (mkN "dubbeltrast") ;
  TurdusPilaris = mkCN (mkN "björktrast") ;
  TurdusMerula = mkCN (mkN "koltrast") ;
  SylviaBorin = mkCN (mkN "trädgårdssångare") ;
  SylviaAtricapilla = mkCN (mkN "svarthätta") ;
  SylviaCurruca = mkCN (mkN "ärtsångare") ;
  SylviaCommunis = mkCN (mkN "törnsångare") ;
  AcrocephalusSchoenobaenus = mkCN (mkN "sävsångare") ;
  AcrocephalusScirpaceus = mkCN (mkN "rörsångare") ;
  AcrocephalusPalustris = mkCN (mkN "kärrsångare") ;
  PhylloscopusTrochilus = mkCN (mkN "lövsångare") ;
  PhylloscopusCollybita = mkCN (mkN "gransångare") ;
  PhylloscopusSibilatrix = mkCN (mkN "grönsångare") ;
  HippolaisIcterina = mkCN (mkN "härmsångare") ;
  RegulusRegulus = mkCN (mkN "kungsfågel") ;
  FicedulaHypoleuca = mkCN (mkA "svartvit") (mkN "flugsnappare" utrum) ;
  ParisMajor = mkCN (mkN "talgoxe" utrum) ;
  ParisCaeruleus = mkCN (mkN "blåmes") ;
  SittaEuropaea = mkCN (mkN "nötväcka") ;
  ParisCristatus = mkCN (mkN "tofsmes") ;
  ParusAter = mkCN (mkN "svartmes") ;
  ParusMontanus = mkCN (mkN "talltita") ;
  ParusPalustris = mkCN (mkN "entita") ;
  AegithalosCaudatis = mkCN (mkN "stjärtmes") ;
  PanururBiarmicus = mkCN (mkN "skäggmes") ;
  LaniusCollurio = mkCN (mkN "törnskata") ;
  GarrulusGlandarius = mkCN (mkN "nötskrika") ;
  PicaPica = mkCN (mkN "skata") ;
  NucifragaCaryocatactes = mkCN (mkN "nötkråka") ;
  CorvusMonedula = mkCN (mkN "kaja") ;
  CorvusFrugilegus = mkCN (mkN "råka") ;
  CorvusCorone = mkCN (mkN "kråka") ;
  CorvusCorax = mkCN (mkN "korp") ;
  SturnusVulgaris = mkCN (mkN "stare") ;
  PasserDomesticus = mkCN (mkN "gråsparv") ;
  PasserMontanus = mkCN (mkN "pilfink") ;
  FringillaCoelebs = mkCN (mkN "bofink") ;
  FringillaMontifringilla = mkCN (mkN "bergfink") ;
  CarpodacusErythrinus = mkCN (mkN "rosenfink") ;
  CarduelisCannabina = mkCN (mkN "hämpling") ;
  CarduelisFlammea = mkCN (mkN "gråsiska") ;
  CarduelisCarduelis = mkCN (mkN "steglits") ;
  CarduelisChloris = mkCN (mkN "grönfink") ;
  CarduelisSpinus = mkCN (mkN "grönsiska") ;
  PyrrhulaPyrrhula = mkCN (mkN "domherre") ;
  LoxiaCurvirostra = mkCN (lin AP {s=(comparAP (mkA "liten" "litet" "lilla" "små" "mindre" "minst" "minsta")).s; isPre=True}) (mkN "korsnäbb") ;
  EmberizaSchoeniclus = mkCN (mkN "sävsparv") ;
  PlectrophenaxNivalis = mkCN (mkN "snösparv") ;
  CalcariusLapponicus = mkCN (mkN "lappsparv") ;
  EmberizaHortulana = mkCN (mkN "ortolansparv") ;
  EmberizaCitrinella = mkCN (mkN "gulsparv") ;
  
}
