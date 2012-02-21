--# -path=.:prelude:alltenses

concrete LexiconSnd of Lexicon = CatSnd ** 
--open ResSnd, Prelude in {
  open ParadigmsSnd,MorphoSnd, Prelude in {

  flags 
    optimize=values ;
    coding = utf8;

  lin
  
  airplane_N = mkN03 "جھاج" ; 
  answer_V2S = mkV2  (compoundV "جواب" (mkV "ڏیڻ ")) ;
  apple_N = mkN03 "سوف"  ;
  art_N = mkN13 "فن"  ;
  ask_V2Q = mkV2 (mkV "پڇڻ ");
  baby_N = mkN05 "ٻار" ;
  bad_A = mkAdj3 "ڪراب"  ;
  bank_N = mkN03 "بانڪ"  ;
  beautiful_A = mkAdj1 "پیارو"  ;
  become_VA = mkV "ٿیڻ ";
  beer_N = mkN03 "شراب" ;
--beg_V2V =  mkV  "پنڻ " ; 
  big_A = mkAdj1 "وڏو" ; 
  bike_N = mkN03 "سایچl"  ;
  bird_N = mkN01 "پکی"  ;
  black_A =  mkAdj1 "ڪارو"  ;
  blue_A = mkAdj1 "نیرو"  ;
  boat_N = mkN04 "ڀیری"  ;
  book_N = mkN03 "ڪتاب"  ;
  boot_N = mkN01 "جوتو" ;
  boss_N = mkN03 "بالادست" ;
  boy_N = mkN01 "چوڪرو"  ;
  bread_N = mkN03 "مانی"  ;
  break_V2 = mkV2  "ٽورڻ " ;
  broad_A = mkAdj1 "ویڪرو"  ;
--brother_N2 = mkN10 "ڀا۶ " "جo " ; --not correct
  brown_A = mkAdj3 "ناسی"  ;
  butter_N = mkN13 "مکڻ" ;
  buy_V2 = mkV2(compoundV "ئرید "  do_V2);
  camera_N = mkN01 "ڪیمیرا";
  cap_N = mkN03 "ڻوپY"  ;
  car_N = mkN03 "گاڏی" ; 
  carpet_N = mkN01 "تڏو" ;
  cat_N = mkN09 "ٻلی"  ;
  ceiling_N = mkN01 "ڇت" ;
  chair_N = mkN09 "ڪرسی"  ;
  cheese_N = mkN14 "پنیر"  ; 
  child_N = mkN01 "ٻار"  ; 
--church_N = mkN03 "گرجا" (mkN "گرجا") ;
  clean_A = mkAdj3 "ساف" ;
  clever_A = mkAdj3 "hوشیار" ;  
  close_V2 =  mkV2 (compoundV "بند"  do_V2); 
  coat_N = mkN03 "ڪوٽ" ;
  cold_A = mkAdj1 "ٿڌو" ;
  computer_N = mkN03 "ڪمپیوٽر" ;
  country_N = mkN03 "مlڪ"  ;
  cousin_N = mkN03 "س۶وٽ"  ; -- a compund noun made of two nouns
  cow_N = mkN09 "گان" ;
  die_V = mkV "مرڻ "  ;
  dirty_A = mkAdj1 "میرو"  ;
--distance_N3 = mkN3 (mkN "پنڌ") (mkPrep "دا") "دE" "توN"  ;
  doctor_N = mkN03 "ڊاڪتر"  ;
  dog_N = mkN01 "ڪتو"  ;
  door_N = mkN01 "دروزو" ; 
  drink_V2 = mkV2 "پی۶ڻ "; 
  easy_A2V = mkA "سولو"  "" ; 
  eat_V2 = mkV2( mkV "کا۶ڻ ");
  empty_A = mkAdj3 "ئالی" ; 
  enemy_N = mkN03 "دشمن" ;
  factory_N = mkN02 "ڪارئانو" ; 
  father_N2 = mkN2 (mkN06  "پی") (mkPrep "جو") "جی"  ;
  fear_VS = mkV "ڊڄڻ "; 
  fish_N = mkN09 "مڇی" ; 
  floor_N = mkN03 "فرش"  ;
  fridge_N = mkN03 "گرج" ;
  friend_N = mkN05 "دوست"  ;
  fruit_N = mkN13 "ثمر" ; 
--fun_AV = mkAdj1V (regA "مزو") ;
  garden_N = mkN03 "باغ"  ;
  girl_N = mkN09 "ڇوڪری"  ;
  glove_N = mkN01 "دستانو" ; 
  gold_N = mkN13 "سون"  ;
  good_A = mkAdj1 "سٺو"  ;
--  go_V = mkIrrgV  "وڃڻ" "" ;
  green_A = mkAdj1 "ساعو"  ;
  harbour_N = mkN08 "پاناگاھ" ; 
  hate_V2 = mkV2 (compoundV "نفرت" do_V2) ; 
  hat_N = mkN01 "توپlو" ;
--have_V = dirV2 (mk5V "ha?ع" "hاس" "hاد" "hاد" "ھجڻ ") ;
  hear_V2 = mkV2 (mkV "ٻڌڻ ") ; 
  hill_N = mkN09 "ٽڪری"  ;
  hope_VS = (compoundV "امید"  do_V2);
  horse_N = mkN01 "گورو" ; 
  hot_A = mkAdj1 "ڪوسو" ;
  house_N = mkN03 "گھر"  ;
  important_A = mkAdj3 "ضروری"  ;
  industry_N = mkN01 "دندو"  ; 
  iron_N = mkN09 "لوھ " ;   
  king_N = mkN01 "بادشاھ"  ;
  know_V2 = mkV2 (mkV "Jاڻڻ") ; 
  know_VS = (mkV "ڄاڻڻ ") ;
  know_VQ = (mkV "ڄاڻڻ ") ;
  lake_N = mkN09 "ڍنڍ"  ;
  lamp_N = mkN09 "بتی " ; 
  learn_V2 = mkV2 ( mkV "سK'ڻ ")  ;
  leather_N = mkN01 "چمڙو"  ;
  leave_V2 = mkV2 (mkV "چڏڻ") ;  
  like_V2 = mkV2 (compoundV "پصند" do_V2);  
  listen_V2 = mkV2 (mkV "ئن ڍیڻ ") ;
  live_V = mkV "رhڻ "  ; ---- touch
  long_A = mkAdj1 "ڊگو"  ;
  lose_V2= mkV2 "hارا۶ڻ "   ;
  love_N = mkN08 "مھبت" ; 
  love_V2 = mkV2  (compoundV "عشق" do_V2) "سان";
  man_N = mkN03 "ماڻھو" ;--not correct according to rules should be discussed
--married_A2 = mkAdj1 "پرڻیل" ; 
  meat_N = mkN01 "کادو" ; 
  milk_N = mkN13 "کیر"  ;
  moon_N = mkN13 "چنڊ" ; 
--mother_N2 = mkN2(mkN07 "ما۶ " "جو" "جی" );--not covered need to be discussed
  mountain_N = mkN03 "جبل" ; 
  music_N = mkN14 "موسیقی"  ;
  narrow_A = mkAdj1 "سوڙھو" ;
  new_A = mkAdj1 "ن۶ون"  ;
  newspaper_N = mkN04 "ائبار" ; 
  oil_N = mkN03 "تیل"   ;
  old_A = mkAdj1 "پوڙھی"  ; 
--  open_V2 = mkV2 (mkIrrgV "ئولڻ"  "ئوl") ; 
  paint_V2A = mkV2 (compoundV "رنگ" do_V2) ;
  paper_N = mkN01 "پنو" ;
--paris_PN = mkN13 "پیرس" masculine;
  peace_N = mkN13 "امن" ;
  pen_N = mkN14 "قلم" ;
  planet_N = mkN01 "سیارو"  ;
  plastic_N = mkN13 "مڙندڙ" ;
  play_V2 = mkV2 (mkV "راند") ; 
  policeman_N = mkN05 "سپاھی"  ;
  priest_N = mkN05 "پیغمبر" ;
--probable_AS = mkAdj1S (regA "امڪان" ) ;
  queen_N = mkN09 "شھزادی" ;  
  radio_N = mkN01 "باجو"  ;
--rain_V0 = compoundV "مینھن"  ""; 
  red_A = mkAdj1 "ڳاڙھو"  ; -- worst case
  religion_N = mkN03 "مزھب" ;
  restaurant_N = mkN05 "ھوٽl" ;
  river_N = mkN12 "دریا" ;
  rock_N = mkN08 "ٽڪری" ;
  roof_N = mkN14 "ڇت"  ;
  rubber_N = mkN13 "ربڙ" ;
  run_V = mkV "ڊوڙڻ " ;  	 
  say_VS = mkV "چوڻ " ;  	
  school_N = mkN03 "اسڪول" ;
  science_N = mkN13 "ساعنص" ;
  sea_N = mkN14 "سمنڊ" ;
  seek_V2 = mkV2 (compoundV "تlاش" do_V2) ;
  see_V2 = mkV2 (mkV "ڏسڻ ") ;
  sell_V = mkV  "وڪڻڻ "; 
  send_V= mkV "موڪلڻ "; 
  sheep_N = mkN09 "رڍ"  ;
  ship_N = mkN03 "جhاز" ;
  shirt_N = mkN01 "چولو";
  shoe_N = mkN01 "جوتو" ;
  shop_N = mkN03 "دوڪان" ;
  short_A = mkAdj1 "ننڍو " ;
  silver_N = mkN14 "چاندی" ;
  sister_N = mkN11 "ٻیڻ " ;
  sleep_V = mkV "سمھڻ " ;
  small_A = mkAdj1 "ننڍو" ;
  snake_N = mkN03 "نانگ" ;
  sock_N = mkN04 "جوراب" ;
  speak_V2 = mkV2 (mkV "غالh۶ڻ ") ;
  star_N = mkN01 "شروعات" ;
  steel_N = mkN13 "استیل" ;
  stone_N = mkN05 "پٽر" ;
  stove_N = mkN01 "چلھو" ;
  student_N = mkN05 "شاگرد" ;
  stupid_A = mkAdj1 "چریو" ;
  sun_N = mkN13 "سج" ;
  switch8off_V2 = mkV2 (mkV "ھلاعت") ;
  switch8on_V2 = mkV2 (compoundV "بند" do_V2) ;
  table_N = mkN04 "میز" ;
  talk_V = mkV "غالhاعڻ  ";
  teacher_N = mkN05 "استاد" ;
  teach_V = mkV "سیکارڻ ";
  television_N = mkN14 "تیلیوزن" ;
  thick_A = mkAdj1 "موتو" ;
  thin_A = mkAdj1 "سنھو" ;
  train_N = mkN09 "ریل" ;
  travel_V = (compoundV "سفر" do_V2) ;
  tree_N = mkN13 "وڻ " ;
  trousers_N = mkN01 "پاجامو" ;
  ugly_A = mkAdj3 "بدسورت" ;
  understand_V = mkV "سمجھڻ ";
  university_N = mkN09 "یونیورسٽY" ; 
  village_N = mkN03 "غوٺ " ;
  wait_V2 = mkV2 (compoundV "انتظار" (mkV "انتظار")) ;
  walk_V = mkV "ھلڻ " ;
  warm_A = mkAdj3 "گرم" ;
  war_N = mkN03 "جنگ" ;
  watch_V2 = mkV2 (mkV "ڍسڻ ") ;
  water_N = mkN14 "پاڻی" ; -- not covered masculine ending with y
  white_A = mkAdj1 "اڇو" ;
  window_N = mkN09 "دری" ;
  wine_N = mkN04 "شراب";
  win_V = mkV"کٽڻ " ;
  woman_N = mkN09 "استری" ;
  wonder_VQ = compoundV "ھیران"(mkV "ٿیڻ ") ;
  wood_N = mkN13 "ڪاٺ" ;
  write_V = mkV "لئڻ " ;
  yellow_A = mkAdj1 "پیلو" ;
  young_A = mkAdj3 "جوان" ;
  do_V2 = mkV2 (mkV "ڪرڻ ")  ;
  now_Adv = mkAdv "ھاڻی" ;
--already_Adv = mkAdj1dv "پھریاعین" ;
  song_N = mkN01 "گانو" ;
--  number_N = mkN03 "انگ" ;
  put_V = mkV "وجڻ " ;
  stop_V = mkV "بیھڻ "  ;
  jump_V = compoundV "ٽپو " (mkV "") ; -- here
  left_Ord = {s = "کابو" ; n = singular};
  right_Ord = {s= "سڄو" ; n = singular};
--far_Adv = mkAdj1dv "پری" ;
  correct_A = mkAdj3 "سھی" ;
  dry_A = mkAdj3 "ئشڪ" ;
  dull_A = mkAdj1 "جڏو" ;
  full_A = mkAdj3 "ٻریل" ;
  heavy_A = mkAdj1 "گرو" ;
  near_A = mkAdj1 "ویجھو" ;
  rotten_A = mkAdj3 "ئراب" ;
  round_A = mkAdj3 "گول" ;
  sharp_A = mkAdj3 "تیز" ;
  smooth_A = mkAdj3 "hموار" ;
  straight_A = mkAdj1 "سڌو" ;
  wet_A = mkAdj1 "االو";
  wide_A = mkAdj1 "ویڪرو" ;
  animal_N = mkN03 "جانور" ;
  ashes_N = mkN14 "راک "  ; -- FIXME: plural only?
  back_N = mkN09 "پٺ " ;
  bark_N = mkN13 "ٻ۶ونڪڻ " ;
  belly_N = mkN14 "پیٽ" ;
  blood_N = mkN13 "رت" ;
  bone_N = mkN09 "hڏی" ;
  breast_N = mkN09 "ڇاتی" ;
  cloud_N = mkN03 "جھڙ" ;
  day_N = mkN13 "ڏینھن" ;
  dust_N = mkN14"ڌوڙ" ;
  ear_N = mkN03 "ڪن" ;
  earth_N = mkN08 "زمین"  ;
  egg_N = mkN01 "بیدو" ;
  eye_N = mkN09 "اک "  ;
  fat_N = mkN09 "چرٻی" ;
  feather_N = mkN13 "کنڀ" ;
  fingernail_N = mkN03 "نھ " ;
  fire_N = mkN14 "باھ" ;
  flower_N = mkN03 "گل" ;
  fog_N = mkN13 "ماڪ"  ;
  foot_N = mkN03 "پیر" ; -- not properly covered need to be discussed
  forest_N = mkN01 "ٻیلو" ;
  grass_N = mkN04 "گاh"  ;
--guts_N = mkN "g?ت" ; -- FIXME: no singular
  hair_N = mkN03 "وار" ;
  hand_N = mkN03 "hٿ ";
  head_N = mkN01 "مٿو" ;
  heart_N = mkN09 "دل"; 
  horn_N = mkN13 "سڱ "  ;
  husband_N = mkN03 "مڙس" ;
  ice_N = mkN09 "برف" ;
  nee_N = mkN01 "گوڏو" ;
  leaf_N = mkN03 "پن" ;
  leg_N = mkN09 "ٽنگ" ;
  liver_N = mkN03 "جیرو" ;
  louse_N = mkN14 "جون۶ " ;
  mouth_N = mkN03 "وات" ;
  name_N = mkN01 "نالو";
  neck_N = mkN04 "ڪنڌ " ;
  night_N = mkN09 "رات" ;
  nose_N = mkN03 "نڪ" ;
  person_N = mkN03 "شئس" ;
  rain_N = mkN14 "مینhن"  ;
  road_N = mkN01 "رستو" ;
  root_N = mkN09 "پاڙ" ;
  rope_N = mkN09 "رسی";
  salt_N = mkN14 "لوڻ "  ;
  sand_N = mkN14 "واری"  ;
  seed_N = mkN03 "ٻج"  ;
  skin_N = mkN09 "چمڙی" ;
  sky_N = mkN03 "ااسمان";
  smoke_N = mkN13 "دونھو"; -- singular masc nouns ending with aN,wN yet to be implemented
  snow_N = mkN13 "برف" ;
  stick_N = mkN09 "ڏنڊی" ;
  tail_N = mkN13 "پڇ " ;
  tongue_N = mkN08 "زبان" ;
  tooth_N = mkN03 "ڏاند";
  wife_N = mkN09 "زال" ;
  wind_N = mkN08 "ھوا" ;
  wing_N = mkN05 "پر" ;
  worm_N = mkN01 "ڪینعون"  ;
  year_N = mkN03 "سال" ;
  blow_V = mkV "وڄڻ " ;
  breathe_V = compoundV "ساh " (mkV "K'ڻڻ " ) ;
  burn_V = mkV "سڙڻ " ;
  dig_V = mkV "K'ٽڻ " ;
  fall_V = mkV "ڪرڻ " ;
  float_V = mkV "ترڻ " ;
  flow_V = mkV "وھڻ " ;
  fly_V = mkV "اڏڻ ";
  freeze_V = mkV "ڄمڻ " ;
  give_V3= mkV3 (mkV "ڏیڻ ") "" "" ; -- here
  laugh_V = mkV "کلڻ "  ;
  lie_N = mkN01 "ڪوڙ"  ;
  lie_V = compoundV "ڪوڙ " ( mkV "غالhاعڻ  ") ;
  play_V = mkV "کیڍڻ " ;
  sew_V = mkV "سبڻ " ;
  sing_V = mkV "گا۶ڻ " ;
  sit_V = mkV "ویھڻ ";
  smell_V = mkV "سنگڻ " ;
  spit_V = mkV "ٿڪڻ " ;
  stand_V = mkV "باھڻ ";
  swell_V = mkV "سبڻ" ;
  swim_V = mkV "ترڻ " ;
  think_V = mkV "سوچڻ " ;
  turn_V = mkV "مڙڻ ";
  vomit_V = compoundV "الٽی" (mkV "ڪرڻ ") ; 
  bite_V2 = mkV2 (mkV "چئ پا۶ڻ ") ;
  count_V = mkV "غڻڻ ";
  cut_V = mkV "ڪٽڻ ";
  fear_V = mkV "ڊڄڻ " ;
  fight_V = mkV "وڙھڻ " ;
  hit_V = mkV "مارڻ " ;
  hold_V = mkV "جھلڻ " ;
  hunt_V2 = mkV2 (compoundV "شڪار" do_V2);
  kill_V =  mkV  "مارن" ;
  pull_V = mkV "چڪڻ ";
  push_V = mkV  "ڌڪڻ "  ;
  rub_V = mkV "مھٽڻ " ;
  scratch_V= mkV "ئرچڻ "  ;
  split_V= mkV "ھارڻ " ;
--squeeze_V2 = dirV2 (regV "سq?ععزع") ;
--stab_V2 = dirV2 (regDuplV "ستاب") ;
  suck_V = mkV "چوسڻ " ;
  throw_V = mkV  "اڇلڻ " ;
  tie_V = mkV "ٻڌڻ " ;
  wash_V = mkV "ڌو۶ڻ" ;
  wipe_V= mkV "اگھڻ ";
--other_A = regA "ٻیا";
  grammar_N = mkN03 "گردان" ;
  language_N = mkN09 "ٻولی" ;
  rule_N = mkN03 "اصول" ;

 ---- added 4/6/2007
  john_PN = mkPN "جان" masculine ;
  question_N = mkN03 "سواl" ;
--ready_A = regA "تیار" ;
  reason_N = mkN03 "سبب"  ;
  today_Adv = mkAdv "اڄ " ;
  uncertain_A = mkAdj3 ["اچانڪ"] ;
  
 
}

