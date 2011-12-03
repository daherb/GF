--# -path=.:prelude

concrete LexiconTha of Lexicon = CatTha ** 
  open ParadigmsTha, ResTha, Prelude in {

flags 
  coding = utf8 ;

lin
--  add_V3 = dirV3 (regV "add") toP ;
  airplane_N = mkN (thword "เครึอง" "บิน") "ลำ" ;
--  already_Adv = mkAdv "already" ;
  animal_N = animalN (thword "สัตว์") ;
  answer_V2S = mkV2S (regV "ขาน") [] ; ---- prep
--  apartment_N = regN "apartment" ;
  apple_N = mkN (thbind "แอป" "เปิ้ล") "ลูก" ;
--  art_N = regN "art" ;
  ashes_N = mkN (thword "เถ้า") ;
  ask_V2Q = regV "ถาน" ** {c2 = []} ;
--  atP = mkPrep "at" ;
--  baby_N = regN "baby" ;
  back_N = mkN (thword "หลัง") ;
  bad_A = mkA (thword "เลว") ;
--  bank_N = regN "bank" ;
  bark_N = mkN (thword "เปลือก") ;
--  beautiful_A = regADeg "beautiful" ;
  become_VA = mkVA (regV "กลาย") ; -- pen
  beer_N = mkN biar_s kew_s ; 
  beg_V2V = regV "ขอ" ** {c2 = []} ;
  belly_N = mkN (thword "พุง") ;
  big_A = mkA (thword "ใหญ่") ;
  bike_N = mkN (thword "จัก" "รยาน") "คัน" ;
  bird_N = animalN (thword "นก") ;
  bite_V2 = mkV2 (thword "กัด") ;
  black_A = mkA (thword "ดำ") ;
  blood_N = mkN (thword "เลือด") ;
  blow_V = mkV (thword "พัด") ;
  blue_A = mkA (thword "สี" "น้ำ" "เงิน") ;
--  boat_N = regN "boat" ;
  bone_N = mkN (thword "กระดูก") ;
  book_N = mkN (thword nag_s svv_s) lem_s ;
--  boot_N = regN "boot" ;
--  boss_N = regN "boss" ;
--  boy_N = regN "boy" ;
  bread_N = mkN (thword "ขนม" "ปัง") "ห่อ" ;
--  break_V2 = dirV2 (irregV "break" "broke" "broken") ;
  breast_N = mkN (thword "นม") ;
  breathe_V = mkV (thword "หาย" "ใจ") ;
--  broad_A = regADeg "broad" ;
--  brother_N2 = regN2 "brother" ;
--  brown_A = regADeg "brown" ;
  burn_V = mkV (thword "เผา") ;
--  butter_N = regN "butter" ;
  buy_V2 = mkV2 "ซื้อ" ;
--  camera_N = regN "camera" ;
--  cap_N = regN "cap" ;
  car_N = mkN "รถ" "คัน" ;
--  carpet_N = regN "carpet" ;
--  cat_N = regN "cat" ;
--  ceiling_N = regN "ceiling" ;
--  chair_N = regN "chair" ;
  cheese_N = mkN (thword "เนย" "แข็ง") "ก้อน" ; 
  child_N = personN (thword "ลูก") ; --- personN (thword "เด็ก") ;
--  church_N = regN "church" ;
  city_N = mkN "นคร" "แห่ง" ;
--  clean_A = regADeg "clean" ;
--  clever_A = regADeg "clever" ;
--  close_V2 = dirV2 (regV "close") ;
  cloud_N = mkN (thword "เมฆ") ;
--  coat_N = regN "coat" ;
  cold_A = mkA (thword "หนาว") ;
  come_V = mkV (thword "มา") ;
--  computer_N = regN "computer" ;
  correct_A = mkA (thword "แท้") ;
  count_V2 = mkV2 (thword "นับ") ;
  country_N = placeN (thword "ประ" "เทศ") ;
--  cousin_N = regN "cousin" ;
--  cow_N = regN "cow" ;
  cut_V2 = mkV2 (thword "ตัด") ;
  day_N = mkN (thword "กลาง" "วัน") ;
  die_V = mkV (thword "ตาย") ;
  dig_V = mkV (thword "ขุด") ;
  dirty_A = mkA (thword "สก" "ปรก") ;
  distance_N3 = mkN3 (mkN (thword "ระ" "ยะ" "ฑาง")) "จาก" "ถืง" ;
--  do_V2 = dirV2 (mkV "do" "does" "did" "done" "doing") ;
--  doctor_N = regN "doctor" ;
  dog_N = animalN (thword "หมา") ;
--  door_N = regN "door" ;
  drink_V2 = mkV2 (thword "ดื่ม") ;
  dry_A = mkA (thword "แห้ง") ;
  dull_A = mkA (thword "ทื่อ") ;
  dust_N = mkN (thword "ฝุ่น") ;
  ear_N = mkN (thword "หู") ;
  earth_N = mkN (thword "ดิน") ;
--  easy_A2V = mkA2V (regA "easy") forP ;
  eat_V2 = mkV2 (thword "กิน") ;
  egg_N = mkN (thword "ไข่") "ฟอง" ;
--  empty_A = regADeg "empty" ;
--  enemy_N = regN "enemy" ;
  eye_N = mkN (thword "ตา") ;
--  factory_N = regN "factory" ;
  fall_V = mkV (thword "ตก") ;
  far_Adv = ss (thword "ไกล") ;
  fat_N = mkN (thword "มัน") ;
  father_N2 = mkN2 (personN (thword "พ่อ")) [] ;
---  fear_N = mkN (thword "กลัว") ;
--  fear_V2 = dirV2 (regV "fear") ;
--  fear_VS = mkVS (regV "fear") ;
  feather_N = mkN (thword "ขน") ;
  fight_V2 = mkV2 (thword "สู้") ;
--  find_V2 = dirV2 (irregV "find" "found" "found") ;
  fingernail_N = mkN (thword "เล็บ") ;
  fire_N = mkN (thword "ไฟ") ;
  fish_N = animalN (thword "ปลา") ;
  float_V = mkV (thword "ลอย") ;
--  floor_N = regN "floor" ;
  flow_V = mkV (thword "ไหล") ;
  flower_N = mkN (thword "ดอก") ;
  fly_V = mkV (thword "บิน") ;
  fog_N = mkN (thword "หมอก") ;
  foot_N = mkN (thword "เท้า") ;
--  forP = mkPrep "for" ;
  forest_N = mkN (thword "ดง") ;
--  forget_V2 = dirV2 (irregDuplV "forget" "forgot" "forgotten") ;
  freeze_V = mkV (thword "แข็ง") ;
--  fridge_N = regN "fridge" ;
  friend_N = personN "เพี่อน" ;
--  fromP = mkPrep "from" ;
  fruit_N = mkN (thword "หมาก") ;
  full_A = mkA (thword "เต็ม") ;
--  fun_AV = mkAV (regA "fun") ;
--  garden_N = regN "garden" ;
--  girl_N = regN "girl" ;
---  give_V3 = mkV3 (thword "ให้") ;
--  glove_N = regN "glove" ;
  go_V = regV pay_s ;
--  gold_N = regN "gold" ;
  good_A = mkA (thword "ดี") ;
--  grammar_N = regN "grammar" ;
  grass_N = mkN (thword "หญ้า") ;
  green_A = mkA (thword "เขียว") ;
  guts_N = mkN (thword "ไส้") ;
  hair_N = mkN (thword "ผม") ;
  hand_N = mkN (thword "มือ") ;
--  harbour_N = regN "harbour" ;
--  hat_N = regN "hat" ;
--  hate_V2 = dirV2 (regV "hate") ;
--  have_V2 = dirV2 (mkV "have" "has" "had" "had" "having") ;
  head_N = mkN (thword "หัว") ;
  hear_V2 = mkV2 (thword "ยิน") ;
  heart_N = mkN (thword "ใจ") ;
  heavy_A = mkA (thword "หนัก") ;
  hill_N = placeN (thword "เนิน" "เขา") ;
  hit_V2 = mkV2 (thword "ตี") ;
  hold_V2 = mkV2 (thword "อุ้ม") ;
--  hope_VS = mkVS (regV "hope") ;
  horn_N = mkN (thword "เขา") ;
--  horse_N = regN "horse" ;
--  hot_A = duplADeg "hot" ;
  house_N = mkN baan_s lag_s ;
  hunt_V2 = mkV2 (thword "ล่า") ;
  husband_N = personN (thword "ผัว") ;
  ice_N = mkN (thword "น้ำ" "แข็ง") ;
--  important_A = compoundADeg (regA "important") ;
--  inP = mkPrep "in" ;
--  industry_N = regN "industry" ;
--  iron_N = regN "iron" ;
  john_PN = ss "จน" ;
--  jump_V = regV "jump" ;
  kill_V2 = mkV2 (thword "ฆ่า") ;
  king_N = mkN (thword "พระ" "รา" "ชา") (thword "พระ" "องด์") ;
  knee_N = mkN (thword "เข่า") ;
  know_V2 = mkV2 "รู้" ; -----
  know_VQ = lin VQ (regV "รู้") ; -----
  know_VS = lin VS (regV "รู้") ; -----
  lake_N = mkN (thword "ทะ" "เล" "สาบ") ;
--  lamp_N = regN "lamp" ;
  language_N = mkN (thword "ภา" "ษา") ;
  laugh_V = mkV (thword "หัว" "เราะ") ;
  leaf_N = mkN (thword "ใบ") ;
--  learn_V2 = dirV2 (regV "learn") ;
--  leather_N = regN "leather" ;
  leave_V2 = mkV2 "ละ" ;
--  left_Ord = ss "left" ;
  leg_N = mkN (thword "ขา") ;
  lie_V = mkV (thword "นอน") ;
--  like_V2 = dirV2 (regV "like") ;
--  listen_V2 = mkV2 (regV "listen") toP ;
  live_V = mkV (thword "อยู่") ;
  liver_N = mkN (thword "ตับ") ;
  long_A = mkA (thword "ยาว") ;
--  lose_V2 = dirV2 (irregV "lose" "lost" "lost") ;
  louse_N = animalN (thword "เล็น") ;
  love_N = mkN (thword "ความ" rak_s) ;
  love_V2 = mkV2 rak_s ;
  man_N = personN (thword "ชาย") ;
  married_A2 = mkA2 (mkA (thword "แต่ง" "งาน" "แล้ว")) "กับ" ;
  meat_N = mkN (thword "เนื้อ") ;
  milk_N = mkN (thword "นาม" "นม") kew_s ;
  moon_N = mkN (thword "เดือน") ;
  mother_N2 = personN "แม่" ** {c2 = []} ;
  mountain_N = mkN (thword "เขา") ;
  mouth_N = mkN (thword "ปาก") ;
--  music_N = regN "music" ;
  name_N = mkN (thword "ชื่อ") ;
  narrow_A = mkA (thword "แคบ") ;
  near_A = mkA "ใกล้" ;
  near_Adv = mkAdv "ใกล้" ;
  neck_N = mkN (thword "คอ") ;
  new_A = mkA (thword "ใหม่") ;
--  newspaper_N = regN "newspaper" ;
  night_N = mkN (thword "กลาง" "คืน") ;
  nose_N = mkN (thword "จมูก") ;
  now_Adv = mkAdv (thword "เดี่ยว" "นี้") ;
--  number_N = regN "number" ;
--  oil_N = regN "oil" ;
  old_A = mkA (thword "แก่") ;
--  onP = mkPrep "on" ;
--  open_V2 = dirV2 (regV "open") ;
---  other_A = mkA (thword "อื่น") ;
  paint_V2A = mkV2A (regV "ปาย") [] ;
--  paper_N = regN "paper" ;
  paris_PN = ss "ปารีส" ;
--  peace_N = regN "peace" ;
--  pen_N = regN "pen" ;
--  person_N = genderN human (regN "person") ;
--  planet_N = regN "planet" ;
--  plastic_N = regN "plastic" ;
  play_V = mkV (thword "เล่น") ;
--  play_V2 = dirV2 (regV "play") ;
--  policeman_N = regN "policeman" ;
--  priest_N = regN "priest" ;
--  probable_AS = mkAS (regA "probable") ;
  pull_V2 = mkV2 (thword "ดึง") ;
  push_V2 = mkV2 (thword "ผลัก") ;
--  put_V2 = mkV2 (irregDuplV "put" "put" "put") noPrep ;
--  queen_N = regN "queen" ;
--  radio_N = regN "radio" ;
  rain_N = mkN (thword "ฝน") ;
  rain_V0 = mkV "มี" "ฝน" ; ----
  ready_A = mkA "พร้อม" ;
  reason_N = verbalN "เหตู" ;
  read_V2 = mkV2 "อา่น" ;
  red_A = mkA (thword "แดง") ;
--  religion_N = regN "religion" ;
  restaurant_N = placeN (thword "ร้าน" "อาหาร") ;
--  right_Ord = ss "right" ;
  river_N = mkN (thword "แม่" "น้ำ") ;
  road_N = mkN (thword "ทาง") ;
--  rock_N = regN "rock" ;
--  roof_N = regN "roof" ;
  root_N = mkN (thword "ราก") ;
  rope_N = mkN (thword "เชือก") ;
  rotten_A = mkA (thword "เน่า") ;
  round_A = mkA (thword "กลม") ;
  rub_V2 = mkV2 (thword "ถู") ;
--  rubber_N = regN "rubber" ;
--  rule_N = regN "rule" ;
  run_V = mkV "วิง" ;
  salt_N = mkN (thword "เกลือ") ;
  sand_N = mkN (thword "ทราย") ;
  say_VS = mkVS (regV ("ว่า")) ;
  school_N = placeN (thword "อาศ" "รม") ;
--  science_N = regN "science" ;
  scratch_V2 = mkV2 (thword "เกา") ;
  sea_N = mkN (thword "ทะ" "เล") ;
  see_V2 = mkV2 (thword "เห็น") ;
  seed_N = mkN (thword "เม็ด") ;
--  seek_V2 = dirV2 (irregV "seek" "sought" "sought") ;
--  sell_V3 = dirV3 (irregV "sell" "sold" "sold") toP ;
  send_V3 = regV "ส่ง" ** {c2,c3 = []} ; ---- prep
  sew_V = mkV (thword "เย็บ") ;
  sharp_A = mkA (thword "คม") ;
--  sheep_N = mk2N "sheep" "sheep" ;
--  ship_N = regN "ship" ;
--  shirt_N = regN "shirt" ;
--  shoe_N = regN "shoe" ;
  shop_N = placeN (thword "ร้าน" "ค้า") ;
  short_A = mkA (thword "สั้น") ;
--  silver_N = regN "silver" ;
  sing_V = mkV (thword "ร้อง") ;
--  sister_N = regN "sister" ;
  sit_V = mkV (thword "นั่ง") ;
  skin_N = mkN (thword "หนัง") ;
  sky_N = mkN (thword "ฟ้า") ;
  sleep_V = mkV "นอน" "หลับ" ;
  small_A = mkA (thword "เล็ก") ;
  smell_V = mkV (thword "มีก" "ลิ่น") ;
  smoke_N = mkN (thword "ควัน") ;
  smooth_A = mkA (thword "ละ" "มุน") ;
  snake_N = animalN (thword "งู") ;
  snow_N = mkN (thword "หิมะ") ;
--  sock_N = regN "sock" ;
--  song_N = regN "song" ;
  speak_V2 = mkV2 "พูด" ;
  spit_V = mkV (thword "ถ่ม") ;
  split_V2 = mkV2 (thword "ผ่า") ;
  squeeze_V2 = mkV2 (thword "คั้น") ;
  stab_V2 = mkV2 (thword "แทง") ;
  stand_V = mkV (thword "ยืน") ;
  star_N = mkN (thword "ดาว") ;
--  steel_N = regN "steel" ;
  stick_N = mkN (thword "กิ่ง") ;
  stone_N = mkN (thword "หิน") ;
--  stop_V = regDuplV "stop" ;
--  stove_N = regN "stove" ;
  straight_A = mkA (thword "ดิ่ง") ;
  student_N = personN (thword "นัก" "สืก" "สา") ;
--  stupid_A = regADeg "stupid" ;
  suck_V2 = mkV2 (thword "ดูด") ;
  sun_N = mkN (thword "ตะ" "วัน") ;
  swell_V = mkV (thword "ตุ่ม") ;
  swim_V = mkV (thword "ว่าย") ;
--  switch8off_V2 = dirV2 (partV (regV "switch") "off") ;
--  switch8on_V2 = dirV2 (partV (regV "switch") "on") ;
--  table_N = regN "table" ;
  tail_N = mkN (thword "หาง") ;
--  talk_V3 = mkV3 (regV "talk") toP aboutP ;
  teach_V2 = mkV2 "สอน" ;
--  teacher_N = regN "teacher" ;
--  television_N = regN "television" ;
  thick_A = mkA (thword "หนา") ;
  thin_A = mkA (thword "บาง") ;
  think_V = mkV (thword "คิด") ;
  throw_V2 = mkV2 (thword "ขว้าง") ;
  tie_V2 = mkV2 (thword "ผูก") ;
--  toP = mkPrep "to" ;
  today_Adv = ss (thword "วัน" "นี้") ;
  tongue_N = mkN (thword "ลิ้น") ;
  tooth_N = mkN (thword "ฟัน") ;
  train_N = mkN (thword "รถ" "ไฟ") "ขนาน" ;
--  travel_V = (regDuplV "travel") ;
  tree_N = mkN (thword "ไม้") ;
  turn_V = mkV (thword "หัน") ;
--  ugly_A = regADeg "ugly" ;
  understand_V2 = mkV2 (mkV (thword "เข้า" "ไจ")) ;
  university_N = placeN (thword "มหา" "วิ" "ทยา" "ลัย") ;
--  village_N = regN "village" ;
  vomit_V = mkV (thword "อ้วก") ;
  wait_V2 = mkV2 "รอ" ;
  walk_V = mkV (thword "เดิน") ;
--  war_N = regN "war" ;
  warm_A = mkA (thword "ร้อน") ;
  wash_V2 = mkV2 (thword "ล้าง") ;
--  watch_V2 = dirV2 (regV "watch") ;
  water_N = mkN (thword "น้ำ") ;
  wet_A = mkA (thword "เปียก") ;
  white_A = mkA (thword "ขาว") ;
  wide_A = mkA (thword "กว้าง") ;
  wife_N = personN (thword "เมีย") ;
--  win_V2 = dirV2 (irregDuplV "win" "won" "won") ;
  wind_N = mkN (thword "ลม") ;
--  window_N = regN "window" ;
  wine_N = mkN (thword "เหล้าอ" "งุ่น") "ขวด" ;
  wing_N = mkN (thword "ปิก") ;
  wipe_V2 = mkV2 (thword "เช็ด") ;
  woman_N = personN (thword "หญิง") ;
  wonder_VQ = mkVQ (regV (thword "ประ" "หลาด" "ไจ")) ; ----
--  wood_N = regN "wood" ;
  worm_N = animalN (thword "หนอน") ;
  write_V2 = mkV2 "ลง" ;
  year_N = mkN (thword "ปี") ;
  yellow_A = mkA (thword "เหลือง") ;
--  young_A = regADeg "young" ;
}
