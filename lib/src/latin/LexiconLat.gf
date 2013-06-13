--# -path=.:prelude

concrete LexiconLat of Lexicon = CatLat ** open 
  ParadigmsLat, 
--  IrregLat,
  ResLat,
  Prelude in {

flags 
  optimize=values ;
  coding = utf8;
lin
  airplane_N = mkN "aëroplanum" ; -- -i n. http://la.wikipedia.org/wiki/A%C3%ABroplanum
  -- Category not yet implemented
--  answer_V2S = mkV2S (mkV "respondere") noPrep ; -- -spondeo, -spondi, -sponsum 2 Langenscheidts Schulwörterbuch Lateinisch 1984
  apartment_N = mkN "domicilium" ; -- -i n. L...
  apple_N = mkN "malum" ; -- -i n. L...
  art_N = mkN "ars" "artis" feminine ; -- Ranta; artis f. L...
  -- Category not yet implemented
--  ask_V2Q = mkV2Q (mkV "rogare") noPrep ; -- rogo 1 L...
  baby_N = mkN "infans" "infantis" ( variants { feminine ; masculine } );  -- Ranta; -antis m./f. L...
  bad_A = mkA "malus" ; -- Ranta; peior, pessimus 3 L...
  bank_N = mkN "argentaria" ; -- -ae f. http://la.wikipedia.org/wiki/Argentaria (the financial institution or the river shore?)
  beautiful_A = mkA "pulcher" ; -- -chra, -chrum L...
  -- Category not yet implemented
--  become_VA = mkVA (mkV "fieri")  ; -- fio, factus L...
  beer_N = mkN ( variants { "cerevisia" ; "cervisia"} ) ; -- Ranta; -ae f. http://la.wikipedia.org/wiki/Cervisia
  -- Category not yet implemented
--  beg_V2V = mkV2V (mkV "petere") abP ; -- -tivi/tii, -titum 3 L...
  big_A = mkA "magnus" ; -- Ranta; maior, maximus 3 L...
  bike_N = mkN "birota" ; -- -ae f. http://la.wikipedia.org/wiki/Birota
  bird_N = mkN "avis" "avis" feminine ; -- Ranta; -is f. L...
  black_A = mkA "niger" ;  -- Ranta; -gra, -grum L...
  blue_A = mkA ( variants { "caeruleus" ; "caerulus" } ) ; -- 3 L...
  boat_N = mkN "navicula" ; -- -ae f. L...
  book_N = mkN "liber" ; -- Ranta; -bri m. L...
  boot_N = mkN "calceus" ; -- -i m. L...
  boss_N = mkN "dux" "ducis" ( variants { feminine ; masculine } ) ; -- ducis m./f. L...
  boy_N = mkN "puer" ; -- -eri m. L...
  bread_N = variants { (mkN "panis" "panis" masculine ) ; (mkN "pane" "panis" neuter ) } ; -- -is m./n. L...
  break_V2 = mkV2 (mkV "rumpo" "rupi" "ruptum" "rumpere") ; -- Ranta; 3 L...
  broad_A = mkA "latus" ; -- 3 L...
  -- Category not yet implemented
  brother_N2 = mkN2 ( mkN "frater" "fratris" masculine ) noPrep; -- -tris m. L...
  brown_A = mkA "fulvus" ; -- 3 L...
  butter_N = mkN "butyrum" ; -- -i n. http://la.wikipedia.org/wiki/Butyrum
  buy_V2 = mkV2 (mkV "emere") ; -- emo, emi, emptum 3 L...
  -- Trying to work with Machina ++ photographica
  camera_N = mkN "Machina" ++ "photographica" ; -- http://la.wikipedia.org/wiki/Machina_photographica
  cap_N = mkN "galerus" ; -- -i m. L...
  car_N = mkN "autocinetum" ; -- -i n. http://la.wikipedia.org/wiki/Autocinetum
  carpet_N = mkN ( "teges" ++ "pavimenti" ) ( "tegetis" ++ "pavimenti" ) feminine ; -- -entis f. http://la.wikipedia.org/wiki/Teges_pavimenti
  cat_N = mkN ( variants {"feles" ; "felis" } ) "felis" feminine ; -- -is f. L... 
  ceiling_N = mkN "tegimentum" ; -- -i n. L...
  chair_N = mkN "sedes" "sedis" feminine; -- -is f. L...
  cheese_N = mkN "caseus" ; -- -i m. L...
  child_N = mkN "proles" "prolis" feminine ; -- -is f. L...
  church_N = mkN "ecclesia" ; -- -ae f. L...
  city_N = mkN "urbs" "urbis" feminine; -- Ranta; urbis f. L...
  clean_A = mkA "lautus" ; -- 3 L...
  clever_A = mkA "callidus" ; -- 3 L...
  close_V2 = mkV2 (mkV "claudere") ; -- claudo, clasi, clausum 3 L...
  coat_N = mkN "pallium" ; -- -i n. L...
  cold_A = mkA "frigidus" ; -- 3 L...
  come_V = mkV "venire" ; -- veno, veni, ventum 4 L...
  computer_N = mkN "computatrum" ; -- -i n. http://la.wikipedia.org/wiki/Computatrum
  country_N = mkN "terra" ; -- -ae f. L...
  cousin_N = mkN ( variants {"consobrinus" ; "consobrina" } ) ; -- -i/-ae m./f. L...
  cow_N = mkN "bos" "bovis" ( variants { feminine ; masculine } ) ; -- bovis (gen. pl. boum, dat./abl. pl. bobus/bubus) m./f. L...
-- Breaks verb
--  die_V = mkV "mori" ; -- morior, mortuus sum, morturus L...
  dirty_A = mkA "sordidus" ; -- 3 L...

  distance_N3 = mkN3 (mkN "distantia") fromP toP ; -- -ae f. L...
  doctor_N = mkN "medicus" ; -- -i m. L...
  dog_N = mkN "canis" "canis" ( variants { masculine ; feminine } ) ; -- -is m./f. L...
  door_N = mkN "porta" ; -- -ae f. L...
  drink_V2 = mkV2 (mkV "bibere") ; -- bibo, potum 3 L...
  -- Category not yet implemented
--  easy_A2V = mkA2V (mkA "facilis") forP ; -- -e sup -illimus L...
  eat_V2 = mkV2 (mkV "cenare") ; -- ceno 1 L...
  empty_A = mkA "vacuus" ; -- 3 L...
  enemy_N = mkN "hostis" "hostis" ( variants { masculine ; feminine } ) ; -- -is m./f. L...
  factory_N = mkN "officina" ; -- -ae f. L...
  father_N2 = mkN2 (mkN "pater" "patris" masculine ) noPrep ; -- -tris m. gen pl -um L...
  -- Category not yet implemented
--  fear_VS = mkVS (mkV "timere") ; -- timeo, timui, --- 2 L...
  find_V2 = mkV2 (mkV "reperire") ; -- reperio, repperi, repertum 4 L...
  fish_N = mkN "piscis" "piscis" masculine ; -- -is m. L...
  floor_N = mkN "pavimentum" ; -- -i n. L...
-- Breaks ResLat.verb
--  forget_V2 = mkV2 (mkV "oblivisci") ; -- obliscor, oblitus sum 3 L...
  fridge_N = mkN ( "armarium" ++ "frigidarium" ) ; -- http://la.wikipedia.org/wiki/Armarium_frigidarium
  friend_N = mkN ( variants { "amicus" ; "amica" } ) ; -- -i/-ae m./f. L...
  fruit_N = mkN "fructus" "fructus" masculine; -- -us m. L...
  -- Category not yet implemented
--  fun_AV = mkAV (mkA "iocosus") ; -- 3 L...
  garden_N = mkN "hortus" ; -- -i m. L...
  girl_N = mkN "puella" ; -- -ae f. L...
  glove_N = mkN "caestus" "caestus" masculine ; --us m. L...
  gold_N = mkN "aurum" ; -- Ranta; -i n. L...
  good_A = mkA "bonus" ; -- Ranta; 3 comp melior, -us; sup optimus 3; adv bene
  go_V = mkV "ire" ; -- eo, i(v)i, itum L...
  green_A = mkA "viridis" ; -- -e L...
  harbour_N = mkN "portus" "portus" masculine ; -- -us m. L...
-- Breaks ResLat.verb
--  hate_V2 = mkV2 (mkV "odisse") ; -- odi, osurus/odivi L...
  hat_N = mkN "petasus" ; -- -i m. L...
  have_V2 = mkV2 (mkV "habere") ; -- habeo, -ui, -itum 2 L...
  hear_V2 = mkV2 (mkV "audire") ; -- 4 L...
  hill_N = mkN "collis" "collis" masculine ; -- -is m. L...
  -- Category not yet implemented
--  hope_VS = mkVS (mkV "sperare") ; -- 1 L...
  horse_N = mkN "equus" ; -- -i m. L...
  hot_A = mkA "calidus" ; -- 3 L... 
  house_N = mkN "domus" "domus" feminine ; -- -us f. L...
  important_A = mkA "gravis" ; -- -e L...
  industry_N = mkN "industria" ; -- -ae f. http://la.wikipedia.org/wiki/Industria
  iron_N = mkN "ferrum" ; -- -i m. L...
  king_N = mkN "rex" "regis" masculine; -- regis m. L...
  know_V2 = mkV2 (mkV "scire") ; -- scio, scivi/scii, scitum 4 L...
  lake_N = mkN "lacus" "lacus" masculine; -- -us m. L...
  lamp_N = mkN "lucerna" ; -- -ae f. L...
  learn_V2 = mkV2 (mkV "discere") ; -- disco, didici, - 3 (-isc-?) L...
  leather_N = mkN "scortum" ; -- -i n. L...
  leave_V2 = mkV2 (mkV "relinquere") ; -- relinquo, relinqui, relictum 3 L...
-- Breaks ResLat.verb
--  like_V2 = mkV2 (mkV "velle") ; -- vello, velli (volsi, vulsi), vulsum 3 L...
  listen_V2 = mkV2 (mkV "auscultare") ; -- ausculto 1 L...
  live_V = mkV "vivere" ; -- vivo, vixi, victurus 3 L...
  long_A = mkA "longus" ; -- 3 L...
  lose_V2 = mkV2 (mkV "amittere") ; -- amitto, amissi, amissum 3 L...
  love_N = mkN "amor" "amoris" masculine ; -- Ranta; -oris m. L...
  love_V2 = mkV2 "amare" ; -- Ranta; amo 1 L...
  man_N = mkN "vir" ; -- viri m. L...
  -- Category not yet implemented
--  married_A2 = mkA2 (mkA "coniunctus") noPrep ; -- 3 http://www.perseus.tufts.edu/hopper/text?doc=Perseus:text:1999.04.0060:entry=coniunctus&highlight=married
  meat_N = mkN "carnis" "carnis" feminine ; -- -is f. L...
  milk_N = mkN "lac" "lactis" neuter ; -- -- lactis n. L...
  moon_N = mkN "luna" ; -- -ae f. L...
  mother_N2 = mkN2 ( mkN "mater" "matris" feminine ) noPrep ; -- matris f. L...
  mountain_N = mkN "mons" "montis" masculine ; -- montis m. L...
  music_N = mkN "musica" ; -- -ae f. L..
  narrow_A = mkA "angustus" ; -- 3 L...
  new_A = mkA "novus" ; -- 3 L...
  newspaper_N = mkN "diarium" ; -- http://la.wikipedia.org/wiki/Diarium
  oil_N = mkN "oleum" ; -- -i n. L...
  old_A = mkA "antiquus" ; -- 3 L...
  open_V2 = mkV2 (mkV "aperire") ; -- aperio, aperui, apertum 4 L...
  -- Category not yet implemented
--  paint_V2A = mkV2A (mkV "pingere") noPrep ; -- pingo, pinxi, pictum 3 L...
  paper_N = mkN "charta" ; -- -ae f. http://la.wikipedia.org/wiki/Charta
  paris_PN = mkPN (mkN "Lutetia") ; -- -ae f. http://la.wikipedia.org/wiki/Lutetia
  peace_N = mkN "pax" "pacis" feminine ; -- pacis f. L...
  pen_N = mkN "stilus" ; -- -i m. L...
  planet_N = mkN "planeta" ; -- -ae m. http://la.wikipedia.org/wiki/Planeta
  plastic_N = mkN "plastica" "plasticae" feminine ; -- -ae f. http://la.wikipedia.org/wiki/Plasticum
  play_V2 = mkV2 (mkV "ludere") ; -- ludo, lusi, lusum 3 L...
  policeman_N = mkN "custos" "custodis" ( variants { masculine ; feminine } ) ; -- -odis m./f. L...
  priest_N = mkN "sacerdos" "sacerdotis" ( variants { masculine ; feminine } ) ; -- -dotis m./f. L...
  -- Category not yet implemented
--  probable_AS = mkAS (mkA "verisimilis") ; -- -e L...
  queen_N = mkN "regina" ; -- -ae f. L...
  radio_N = mkN "radiophonia" ; -- http://la.wikipedia.org/wiki/Radiophonia 
  -- Category not yet implemented
--  rain_V0 = mkV0 (mkV "pluit") ; -- L...
  read_V2 = mkV2 (mkV "legere") ; -- lego, legi, lectum 3 L...
  red_A = mkA "ruber" ; -- rubra, rubrum L...
  religion_N = mkN "religio" "religionis" feminine ; -- -onis f. L...
  restaurant_N = mkN "taberna" ; -- -ae f. L...
  river_N = mkN "fluvius" ; -- -i m. L...
  rock_N = mkN "saxum" ; -- -i n. L...
  roof_N = mkN "tectum" ; -- -i n. L...
  rubber_N = mkN "cummis" "cummis" feminine ; -- -is f. Der kleine Stowasser
  run_V = mkV "currere" ; -- curro, cucurri, cursum 3 L...
  -- Category not yet implemented
--  say_VS = mkVS (mkV "dicere") ; -- dico, dixi, dictum 3 L...
  school_N = mkN "schola" ; -- -ae f. L...
  -- Irregular
--  science_N = mkN "literae" ; -- nur pl. L...
  sea_N = mkN "mare" "maris" neuter ; -- -is n. L...
  seek_V2 = mkV2 (mkV "quaerere") ; -- quaero, quaesivi, quaesitum 3 L...
  see_V2 = mkV2 (mkV "videre") ; -- video, vidi, visum 2 L...
  -- Category not yet implemented
--  sell_V3 = mkV3 (mkV "vendere") toP ; -- vendo, vendidi, venditum 3 L...
  -- Category not yet implemented
--  send_V3 = mkV3 (mkV "mittere") toP ; -- mitto, misi, missum 3 L...
  sheep_N = mkN "ovis" "ovis" feminine ; -- -is f. L...
  ship_N = mkN "navis" "navis" feminine ; -- -is f. acc. -em (-im) abl meist -i L...
  shirt_N = mkN "tunica" ; -- -ae f. L...
  shoe_N = boot_N ;
  shop_N = mkN "institorium" ; -- -i n. L...
  short_A = mkA "brevis" ; -- -e L...
  silver_N = mkN "argentum" ; -- -i n. L...
  sister_N = mkN "soror" "sororis" feminine; -- -oris f. L...
--  sleep_V = mkV "dormio" "dormivi" "dormitus" "dormire" ; -- Ranta; 
  sleep_V = mkV "dormire" ; -- 4 L...
  small_A = mkA "parvus" ; -- 3 L...
  snake_N = mkN "serpens" "serpentis" ( variants { masculine ; feminine } ) ; -- -entis m./f. L...
  sock_N = mkN "udo" "udonis" masculine ; -- -onis m. http://la.wikipedia.org/wiki/Udo
-- Breaks ResLat.verb
--  speak_V2 = mkV2 (mkV "loqui") ; -- loquor, locutus sum 3 L...
  star_N = mkN "stella" ; -- -ae f. L...
  steel_N = mkN "chalybs" "chalybis" masculine ; -- chalybis m. L...
  stone_N = mkN "lapis" "lapidis" masculine ; -- -idis m. L...
  stove_N = mkN "fornax" "formacis" feminine ; -- -acis f. L...
  student_N = mkN ( variants { "discipulus"; "discipula" } ) ; -- -i/-ae m./f. L...
  stupid_A = mkA "stultus" ; -- 3 L...
  sun_N = mkN "sol" "solis" masculine ; -- solis m. L...
  switch8off_V2 = mkV2 (mkV "accendere") ; -- -cendo, -cendi, -censum 3 L...
  switch8on_V2 = mkV2 (mkV ( variants { "exstinguere" ; "extinguere" } ) ); -- -ingo, -inxi, -inctum 3 L...
  table_N = mkN "mensa" ; -- -ae f. L...
  -- Category not yet implemented
--  talk_V3 = mkV3 speak_V2 ;
  teacher_N = mkN "magister" ; -- -tri m. L...
  teach_V2 = mkV2 (mkV "docere") ; -- doceo, docui, doctum 2 L...
  television_N = mkN "televisio" "televisionis" feminine ; -- -onis f. http://la.wikipedia.org/wiki/Televisio and visio in L...
  thick_A = mkA "crassus" ; -- 3 L...
  thin_A = mkA "tenuis" ; -- -e L...
  train_N = mkN "hamaxostichus" ; -- -i m. http://la.wikipedia.org/wiki/Hamaxostichus
  travel_V = mkV "iter facere" ; -- facio, feci, factum 3
  tree_N = mkN "arbor" "arboris" feminine ; -- -oris f.
  -- Not even in English implemented
---- trousers_N = mkN "trousers" ;
  ugly_A = mkA "foedus" ; -- 3 L...
  understand_V2 = mkV2 (mkV "intellegere") ; -- intellego, intellexi, intellectum 3 L...
  university_N = mkN "universitas" "universitatis" feminine ; -- -atis f. http://la.wikipedia.org/wiki/Universitas and L...
  village_N = mkN "vicus" ; -- -i m. L...
  wait_V2 = mkV2 (mkV "exspectare") ; -- 1 L...
  walk_V = mkV "vadere" ; -- 3 L...
  warm_A = mkA "calidus" ; -- 3 L...
  war_N = mkN "bellum" ; -- -i m. L...
  watch_V2 = mkV2 (mkV "spectare") ; -- 1 L...
  water_N = mkN "aqua" ; -- -ae f. L...
  white_A = mkA "albus" ; -- 3 L...
  window_N = mkN "fenestra" ; -- -ae f. L...
  wine_N = mkN "vinum" ; -- -i n. L...
  win_V2 = mkV2 (mkV "vincere") ; -- vinco, vici, victum 3 L...
  woman_N = mkN "femina" ; -- -ae f. L...
  -- Category not yet implemented
--  wonder_VQ = mkVQ (mkV "mirari") ; -- 1 L...
  wood_N = mkN "lignum" ; -- -i n. 
  write_V2 = mkV2 (mkV "scribere") ; -- scribo, scripsi, scriptum 3 L...
  yellow_A = mkA "flavus" ; -- 3 L...
  young_A = mkA "parvus" ; -- 3 L...

  do_V2 = mkV2 (mkV "agere") ; -- ago, egi, actum 3 L...
  now_Adv = mkAdv "nunc" ;
  already_Adv = mkAdv "iam" ;
  song_N = mkN "carmen" "carminis" neuter ; -- -inis n. L...
  -- Category not yet implemented
--  add_V3 = mkV3 (mkV "addere") toP ; -- addo, addidi, additum 3 L...
  number_N = mkN "numerus" ; -- -i m.
  put_V2 = mkV2 (mkV "ponere") ; -- pono, posui, positum 3 L...
  stop_V = mkV "sistere" ; -- sisto, stiti/steti, statum 3 L...
  jump_V = mkV "saltare" ; -- 1 L...

  left_Ord = ss "sinister" ; -- -tra, -trum L...
  right_Ord = ss "dexter" ; -- -t(e)ra, -t(e)rum L...
  far_Adv = mkAdv "longe" ; -- L...
  correct_A = mkA "rectus" ; -- 3 L...
  dry_A = mkA "aridus" ; -- 3 L...
  dull_A = mkA "bardus" ; -- 3 L... u. http://www.perseus.tufts.edu/hopper/text?doc=Perseus:text:1999.04.0060:entry=bardus&highlight=dull
  full_A = mkA "plenus" ; -- 3 L...
  heavy_A = mkA "gravis" ; -- -e L...
  near_A = mkA "propinquus" ; -- 3 (comp. durch propior, -ius sup. durch proximus 3) L...
  rotten_A = mkA "perditus" ; -- 3 L...
  round_A = mkA "rotundus" ; -- 3 L...
  sharp_A = mkA "acer" ; -- acris, acre L...
  smooth_A = mkA "lubricus" ; -- 3 L...
  straight_A = mkA "rectus" ; -- 3 L...
  wet_A = mkA "umidus" ; -- 3 L...
  wide_A = mkA "vastus" ; -- 3 L...
  animal_N = mkN "animal" "animalis" neuter ; -- -alis n. L...
  ashes_N = mkN "cinis" "cineris" masculine ; -- -eris m. L... & Bayer-Landauer 33 1.2 
  back_N = mkN "tergum" ; -- -i n. L...
  bark_N = mkN "cortex" "corticis" ( variants { masculine ; feminine } ) ; -- -icis m./(f.) L...
  belly_N = mkN "venter" "ventris" masculine ; -- -tris m. L...
  blood_N = variants { mkN "sanguis" "sanguinis" masculine ; mkN "sangis" "sanginis" masculine} ; -- -inis m. L...
  bone_N = mkN "os" "ossis" neuter ; -- ossis n. L...
  breast_N = mkN "pectus""pectoris" neuter ; -- pectoris n. L...
  cloud_N = mkN "nubes" "nubis" feminine ; -- -is f. L...
  day_N = mkN "dies" "diei" ( variants { masculine ; feminine } ) ; -- -ei m./f. L...
  dust_N = mkN "pulvis" "pulveris" masculine;  -- -veris m. L...
  ear_N = mkN "auris" "auris" feminine; -- -is f. L...
  earth_N = mkN "terra" ; -- -ae f. L...
  egg_N = mkN "ovum" ; -- -i n. L...
  eye_N = mkN "oculus" ; -- -i m. L...
  fat_N = mkN "omentum" ; -- -i n. L...
  feather_N = mkN "penna" ; -- -ae f. L...
  fingernail_N = mkN "unguis" "unguis" masculine ; -- -is m. L...
  fire_N = mkN "ignis" "ignis" masculine; -- -is m. L...
  flower_N = mkN "flos" "floris" masculine ; -- floris m. L...
  fog_N = mkN "nebula" ; -- -ae f. L...
  foot_N = mkN "pes" "pedis" masculine ; -- pedis m. L...
  forest_N = mkN "silva" ; -- -ae f. L...
  grass_N = mkN "gramen" "graminis" neuter ; -- -inis n. L...
  guts_N = mkN "intestinum" ; -- -i n. L...
  hair_N = mkN "capillus" ; -- -i m. L...
  hand_N = mkN "manus" "manus" feminine ; -- -us f. L...
  head_N = mkN "caput" "capitis" neuter ; -- -itis n. L...
  heart_N = mkN "cor" "cordis" neuter; -- cordis n. L...
  horn_N = mkN ( variants { "cornu" ; "cornus" } ) "cornus" neuter ; -- -us n. L...
  husband_N = mkN "maritus" ; -- -i m. L...
  ice_N = mkN "glacies" "glaciei" feminine ; -- -ei f. L...
  knee_N = mkN "genu" "genus" neuter ; -- -us n. L...
  leaf_N = mkN "folium" ; -- -i n. L...
  leg_N = bone_N ;
  liver_N = variants { ( mkN "iecur" "iecoris" neuter ) ; ( mkN "iocur" "iocineris" neuter ) } ; -- iecoris/iocineris n. L...
  louse_N = mkN "pedis" "pedis" ( variants { masculine ; feminine } ) ; -- -is m./f. L...
  mouth_N = mkN "os" "oris" neuter ; -- oris n. L...
  name_N = mkN "nomen" "nominis" neuter ; -- -inis n. L...
  neck_N = mkN "cervix" "cervicis" feminine ; -- -icis f. (meist pl.) L...
  night_N = mkN "nox" "noctis" feminine ; -- noctis f. L...
  nose_N = mkN ( variants { "nasus" ; "nasum" } ) ; -- -i m./n. L...
  person_N = mkN "persona" ; -- -ae f. L...
  rain_N = mkN "pluvia" ; -- -ae f. L...
  road_N = mkN "via" ; -- -ae f. L...
  root_N = mkN "radix" "radicis" feminine ; -- -icis f. L...
  rope_N = mkN "funis" "funis" ( variants { masculine ; feminine } ) ; -- -is m.(/f.) L...
  salt_N = mkN "sal" "salis" ( variants { masculine ; neuter } ) ; -- salis m./n. L...
  sand_N = mkN "arena" ; -- -ae f. L...
  seed_N = mkN "semen" "seminis" neuter ; -- -inis n. L...
  skin_N = mkN "cutis" "cutis" feminine ; -- -is f. L...
  sky_N = mkN "caelum" ; -- -i n. L...
  smoke_N = mkN "fumus" ; -- -i m. L...
  snow_N = mkN "nix" "nivis" feminine ; -- nivis (gen. pl. -ium) f. L...
  stick_N = mkN ( variants { "baculum" ; "baculus" } ) ; -- -i n./m.
  tail_N = mkN "cauda" ; -- -ae f. L...
  tongue_N = mkN "lingua" ; -- -ae f. L...
  tooth_N = mkN "dens" "dentis" masculine; -- dentis m. L...
  wife_N = mkN "mulier" "mulieris" feminine; -- -eris f. L...
  wind_N = mkN "ventus" ; --  -i m. L...
  wing_N = mkN "ala" ; -- -ae f. L...
  worm_N = mkN "vermis" "vermis" masculine ; -- -is m. L...
  year_N = mkN "annus" ; -- -i m. L...
  blow_V = mkV "flare" ; -- flo 1 L...
  breathe_V = mkV "spirare" ; -- spiro 1 L...
  burn_V = mkV "ardere" ; -- ardeo, arsi, arsum 2 L...
  dig_V = mkV "fodere" ; -- fodio, fodi, fossum 3 L...
  fall_V = mkV "caedere" ; -- caedo, cecidi, caesum 3 L...
  float_V = mkV "fluitere" ; -- fluito 1 L...
  flow_V = mkV "fluere" ; -- fluo, fluxi, fluxum 3 L...
  fly_V = mkV "volare" ; -- volo 1 L...
  freeze_V = mkV "gelare" ; -- gelo 1 L...
  -- Category not yet implemented
--  give_V3 = mkV3 give_V toP ;
  laugh_V = mkV "ridere" ; -- rideo, -si, -sum 2 L...
  lie_V = mkV "iacere" ; -- iaceo, iacui, - 2 L...
  play_V = mkV "ludere" ; -- ludo, -si, -sum 3 L...
  sew_V = mkV "serere" ; -- sero, sevi, satum 3 L...
  sing_V = mkV "cantare" ; -- canto 1 L...
  sit_V = mkV "sedere" ; -- sedeo, sedi, sessum 2 L...
  smell_V = mkV "olere" ; -- oleo, -ui, - 2 L...
  spit_V = mkV "spuere" ; -- spuo, -ui, -utum 3 L...
  stand_V = mkV "stare" ; -- sto, steti, staturus, statum 1 L...
  swell_V = mkV "intumescere" ; -- intumesco, -mui, - 3 L...
  swim_V = mkV "natare" ; -- nato 1 L...
  think_V = mkV "cogitare" ; -- cogito 1 L...
  turn_V = mkV "vertere" ; -- verso 1 L...
  vomit_V = mkV "vomere" ; -- vomo, -ui, -itum 3 L...

  bite_V2 = mkV2 "mordere" ; -- mordeo, momordi, morsum 2 L...
  count_V2 = mkV2 (mkV "numerare") ; -- numero 1 L...
  cut_V2 = mkV2 (mkV "secare" ) ; -- seco, secui, sectum, secaturus 1 L...
  fear_V2 = mkV2 (mkV "timere") ; -- timeo, ui, - 2 L...
  fight_V2 = mkV2 (mkV "pugnare" ) ; -- pugno 1 L...
  hit_V2 = mkV2 ( mkV "ferire" ) ; -- ferio, -, - 4 L...
  hold_V2 = mkV2 ( mkV "tenere" ) ; -- teneo, tenui, tentum 2 L...
  hunt_V2 = mkV2 (mkV "agitare") ; -- agito 1 L...
  kill_V2 = mkV2 (mkV "necare") ; -- neco 1 L...
  pull_V2 = mkV2 (mkV "trahere") ; -- traho, traxi, tractum 3 L...
  push_V2 = mkV2 (mkV "premere") ; -- premo, pressi, pressum 3 L...
  rub_V2 = mkV2 (mkV "radere") ; -- raso, -si, -sum 3 L...
  scratch_V2 = mkV2 (mkV "scalpere") ; -- scalpo, -psi, -ptum 3 L...
  split_V2 = mkV2 ( mkV "scindere" ) ; -- scindo, -idi, -issum 3 L...
  squeeze_V2 = mkV2 (mkV "premere") ; -- premo, pressi, pressum 3 L... 
  stab_V2 = mkV2 (mkV "transfigere") ; -- -figo, -fixi, fixum 3 L...
  suck_V2 = mkV2 (mkV "fellare") ; -- fel(l)o 1 L...
  throw_V2 = mkV2 (mkV "iacere" ) ; -- iacio, ieci, iactum L...
  tie_V2 = mkV2 (mkV "vincire") ; -- vincio, vinxi, vinctum 4 L...
  wash_V2 = mkV2 (mkV "lavare") ; -- lavo, lavi, lautum (lotum)/lavatum 1 L...
  wipe_V2 = mkV2 (mkV "detergere") ; -- setergeo, -tersi, -tersum 2/ detergo, -, - 3 L...

----  other_A = mkA "other" ;

  grammar_N = mkN "grammatica" ; -- -ae/-orum f./n. http://la.wikipedia.org/wiki/Grammatica / L...
  language_N = mkN "lingua" ; -- -ae f. L...
  rule_N = mkN "regula" ; -- -ae f. L...

-- added 4/6/2007
    john_PN = mkPN (mkN "Iohannes") ; -- http://en.wikipedia.org/wiki/John_(given_name)
    question_N = mkN "rogatio" "rogationis" feminine; -- -onis f. L...
    ready_A = mkA "paratus" ; -- 3 L...
    reason_N = mkN "causa" ; -- -ae f. L...
    today_Adv = mkAdv "hodie" ; -- L...
    uncertain_A = mkA "incertus" ; -- 3 L...

oper
-- Bayer-Lindauer $149ff.
  aboutP = mkPrep "de" ; -- L...
  atP = mkPrep "ad" Acc ; -- L...
  forP = mkPrep "pro" Abl ; -- L...
  fromP = mkPrep "ab" Abl ; -- L...
  inP = mkPrep "in" ( variants { Abl ; Acc } ) ; -- L...
  onP = mkPrep "ad" ; -- L...
  toP = mkPrep "ad" Acc ; -- L...
  noPrep = mkPrep "" Gen ;
}
