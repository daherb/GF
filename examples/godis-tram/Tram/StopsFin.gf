--# -path=.:../Common:alltenses

concrete StopsFin of Stops = open Prelude, CatFin, GodisLangFin, ParadigmsFin in {

lincat Stop = NP;

lin
Angered = sing_NP ["angeredia"];
AxelDahlstromsTorg = sing_NP ["axel_dahlstroms_torgia"];
Bergsjon = sing_NP ["bergsj�nia"];
Biskopsgarden = sing_NP ["biskopsgardenia"];
Botaniska = singNP (nTalo ["botaniska"]);
Broplatsen =  sing_NP ["broplatsenia"];
Brunnsbotorget = sing_NP ["brunnsbotorgetia"];
Brunnsparken = sing_NP ["brunnsparkenia"];
Centralstationen = sing_NP ["centralstationenia"];
Chalmers = sing_NP ["chalmersia"];
Eriksberg = sing_NP ["eriksbergia"];
Frihamnen = sing_NP ["frihamnenia"];
FrolundaTorg = sing_NP ["fr�lunda_torgia"];
Gamlestadstorget = sing_NP ["gamlestadstorgetia"];
Gronsakstorget = sing_NP ["gr�nsakstorgetia"];
Guldheden = sing_NP ["guldhedenia"];
Hagakyrkan = sing_NP ["hagakyrkania"];
Harlanda = singNP (nTalo ["h�rlanda"]);
Hinnebacksgatan = sing_NP ["hinneb�cksgatania"];
HjBrantingsplatsen = sing_NP ["hjalmar_brantingsplatsenia"];
Jarntorget = sing_NP ["j�rntorgetia"];
Kalleback = sing_NP ["kalleb�ckia"];
Karralundsgatan = sing_NP ["k�rralundsgatania"];
Klareberg = sing_NP ["klarebergia"]; --- �
Klippan = sing_NP ["klippania"];
Korkarlensgata = singNP (nTalo ["k�rkarlens_gata"]);
Korsvagen = sing_NP ["korsv�genia"];
Kortedala = sing_NP ["kortedalaia"];
Kungssten = sing_NP ["kungsstenia"];
Lansmansgarden = sing_NP ["l�nsmansgardenia"];
LillaBommen = sing_NP ["lilla_bommenia"];
Lindholmen = sing_NP ["lindholmenia"];
Linneplatsen = sing_NP ["linn�platsenia"];
LundbyStrand = sing_NP ["lundby_strandia"];
Mariaplan = sing_NP ["mariaplania"];
Marklandsgatan = sing_NP ["marklandsgatania"];
Nordstan = sing_NP ["nordstania"];
Olivedalsgatan = sing_NP ["olivedalsgatania"];
Olskrokstorget = sing_NP ["olskrokstorgetia"];
OstraSjukhuset = sing_NP ["�stra_sjukhusetia"];
Pilbagsgatan = sing_NP  ["pilb�gsgatania"];
Redbergsplatsen = sing_NP ["redbergsplatsenia"];
Rosenlund = sing_NP ["rosenlundia"];
Sahlgrenska = singNP (nTalo ["sahlgrenska"]);
Saltholmen = sing_NP ["saltholmenia"];
SanktSigfridsplan = sing_NP ["sankt_sigfrids_plania"];
Sannaplan = sing_NP ["sannaplania"];
Skogome = singNP (nTalo ["skogome"]);
Sorgardsskolan = sing_NP ["sorgardsskolania"];
Stigbergstorget = sing_NP ["stigbergstorgetia"];
Tagene = singNP (nTalo ["tagene"]);
Torp = sing_NP ["torpia"];
Tynnered = sing_NP ["tynneredia"];
Ullevi = singNP (nTalo ["ullevi"]);
Valand = sing_NP ["valandia"];
VasaViktoriagatan = sing_NP ["vasa_viktoriagatania"];
Vasaplatsen = sing_NP ["vasaplatsenia"];
WavrinskysPlats = sing_NP ["wavrinskys_platsia"];

oper

singNP : N -> NP = \n -> mkNP n singular ;

}
