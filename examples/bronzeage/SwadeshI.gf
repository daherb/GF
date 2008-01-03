incomplete concrete SwadeshI of Swadesh = open Lang in {

  lincat
    MassN = Lang.N ;

  lin

    -- Pronouns

    i_NP = Lang.i_Pron ;
    youSg_NP = Lang.youSg_Pron ;
    he_NP = Lang.he_Pron ;
    we_NP = Lang.we_Pron ;
    youPl_NP = Lang.youPl_Pron ;
    they_NP = Lang.they_Pron ;
    whoPl_IP = Lang.whoPl_IP ;
    whoSg_IP = Lang.whoSg_IP ;
    whatPl_IP = Lang.whatPl_IP ;
    whatSg_IP = Lang.whatSg_IP ;

    -- Determiners

    this_Det = DetSg (this_Quant) NoOrd ;
    that_Det = DetSg (that_Quant) NoOrd ;
    many_Det = Lang.many_Det ;
    some_Det = someSg_Det ;
----    few_Det =  few_Det ;

   left_Ord = Lang.left_Ord ;
   right_Ord = Lang.right_Ord ;
    -- Adverbs
    here_Adv = Lang.here_Adv;
    there_Adv = Lang.there_Adv;
    where_IAdv = Lang.where_IAdv;
    when_IAdv = Lang.when_IAdv;
    how_IAdv = Lang.how_IAdv;
   far_Adv = Lang.far_Adv ;
    -- not : Adv ; -- ?
    -- Conjunctions
    and_Conj = Lang.and_Conj ;
    -- Prepositions
    in_Prep = Lang.in_Prep ;
    with_Prep = Lang.with_Prep ;
    -- Numerals
    one_Det = Lang.DetPl IndefArt 
      (Lang.NumNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01))))) NoOrd ;
    two_Num = Lang.NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))) ;
    three_Num = Lang.NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))) ;
    four_Num = Lang.NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n4))))) ;
    five_Num = Lang.NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n5))))) ;
    -- Adjectives
    bad_A = Lang.bad_A ;
    big_A = Lang.big_A ;
    black_A = Lang.black_A ;
    cold_A = Lang.cold_A ;
   correct_A = Lang.correct_A ;
    dirty_A = Lang.dirty_A ;
   dry_A = Lang.dry_A ;
   dull_A = Lang.dull_A ;
   full_A = Lang.full_A ;
    good_A = Lang.good_A ;
    green_A = Lang.green_A ;
   heavy_A = Lang.heavy_A ;
    long_A = Lang.long_A ;
    narrow_A = Lang.narrow_A ;
   near_A = Lang.near_A ;
    new_A = Lang.new_A ;
    old_A = Lang.old_A ;
---- other_A = Lang.other_A ;
    red_A = Lang.red_A ;
   rotten_A = Lang.rotten_A ;
   round_A = Lang.round_A ;
   sharp_A = Lang.sharp_A ;
    short_A = Lang.short_A ;
    small_A = Lang.small_A ;
   smooth_A = Lang.smooth_A ;
   straight_A = Lang.straight_A ;
    thick_A = Lang.thick_A ;
    thin_A = Lang.thin_A ;
    warm_A = Lang.warm_A ;
   wet_A = Lang.wet_A ;
    white_A = Lang.white_A ;
   wide_A = Lang.wide_A ;
    yellow_A = Lang.yellow_A ;
    -- Nouns
   animal_N = Lang.animal_N ;
   ashes_N = Lang.ashes_N ;
   back_N = Lang.back_N ;
   bark_N = Lang.bark_N ;
   belly_N = Lang.belly_N ;
    bird_N = Lang.bird_N;
   blood_N = Lang.blood_N ;
   bone_N = Lang.bone_N ;
   breast_N = Lang.breast_N ;
    child_N = Lang.child_N ;
   cloud_N = Lang.cloud_N ;
   day_N = Lang.day_N ;
    dog_N = Lang.dog_N ;
   dust_N = Lang.dust_N ;
   ear_N = Lang.ear_N ;
   earth_N = Lang.earth_N ;
   egg_N = Lang.egg_N ;
   eye_N = Lang.eye_N ;
   fat_N = Lang.fat_N ;
   feather_N = Lang.feather_N ;
   fingernail_N = Lang.fingernail_N ;
   fire_N = Lang.fire_N ;
    fish_N = Lang.fish_N ;
   flower_N = Lang.flower_N ;
   fog_N = Lang.fog_N ;
   foot_N = Lang.foot_N ;
   forest_N = Lang.forest_N ;
    fruit_N = Lang.fruit_N ;
   grass_N = Lang.grass_N ;
   guts_N = Lang.guts_N ;
   hair_N = Lang.hair_N ;
   hand_N = Lang.hand_N ;
   head_N = Lang.head_N ;
   heart_N = Lang.heart_N ;
   horn_N = Lang.horn_N ;
    husband_N = Lang.man_N ; --- aviomies
   ice_N = Lang.ice_N ;
   knee_N = Lang.knee_N ;
    lake_N = Lang.lake_N ;
   leaf_N = Lang.leaf_N ;
   leg_N = Lang.leg_N ;
   liver_N = Lang.liver_N ;
   louse_N = Lang.louse_N ;
    man_N = Lang.man_N ;
    meat_N = Lang.meat_N ;
    moon_N = Lang.moon_N ;
----   mother_N = Lang.mother_N ;
    mountain_N = Lang.mountain_N ;
   mouth_N = Lang.mouth_N ;
   name_N = Lang.name_N ;
   neck_N = Lang.neck_N ;
   night_N = Lang.night_N ;
   nose_N = Lang.nose_N ;
   person_N = Lang.person_N ;
   rain_N = Lang.rain_N ;
    river_N = Lang.river_N ;
   road_N = Lang.road_N ;
   root_N = Lang.root_N ;
   rope_N = Lang.rope_N ;
   salt_N = Lang.salt_N ;
   sand_N = Lang.sand_N ;
    sea_N = Lang.sea_N ;
   seed_N = Lang.seed_N ;
   skin_N = Lang.skin_N ;
   sky_N = Lang.sky_N ;
   smoke_N = Lang.smoke_N ;
    snake_N = Lang.snake_N ;
   snow_N = Lang.snow_N ;
    star_N = Lang.star_N ;
   stick_N = Lang.stick_N ;
    stone_N = Lang.stone_N ;
    sun_N = Lang.sun_N ;
   tail_N = Lang.tail_N ;
   tongue_N = Lang.tongue_N ;
   tooth_N = Lang.tooth_N ;
    tree_N = Lang.tree_N ;
    water_N = Lang.water_N ;
   wife_N = Lang.wife_N ;
   wind_N = Lang.wind_N ;
   wing_N = Lang.wing_N ;
    woman_N = Lang.woman_N ;
   worm_N = Lang.worm_N ;
   year_N = Lang.year_N ;
    -- Verbs
   bite_V2 = Lang.bite_V2 ;
   blow_V = Lang.blow_V ;
   breathe_V = Lang.breathe_V ;
   burn_V = Lang.burn_V ;
    come_V = Lang.come_V ;
   count_V2 = Lang.count_V2 ;
   cut_V2 = Lang.cut_V2 ;
   die_V = Lang.die_V ;
   dig_V = Lang.dig_V ;
   drink_V2 = Lang.drink_V2 ;
   eat_V2 = Lang.eat_V2 ;
   fall_V = Lang.fall_V ;
   fear_V2 = Lang.fear_V2 ;
   fight_V2 = Lang.fight_V2 ;
   float_V = Lang.float_V ;
   flow_V = Lang.flow_V ;
   fly_V = Lang.fly_V ;
   freeze_V = Lang.freeze_V ;
   give_V3 = Lang.give_V3 ;
   hear_V2 = Lang.hear_V2 ;
   hit_V2 = Lang.hit_V2 ;
   hold_V2 = Lang.hold_V2 ;
   hunt_V2 = Lang.hunt_V2 ;
   kill_V2 = Lang.kill_V2 ;
   know_V2 = Lang.know_V2 ;
   laugh_V = Lang.laugh_V ;
   lie_V = Lang.lie_V ;
    live_V = Lang.live_V ;
    play_V = Lang. play_V2 ;
   pull_V2 = Lang.pull_V2 ;
   push_V2 = Lang.push_V2 ;
   rub_V2 = Lang.rub_V2 ;
   say_V = Lang.say_VS ;
   scratch_V2 = Lang.scratch_V2 ;
    see_V2 = Lang.see_V2 ;
   sew_V = Lang.sew_V ;
   sing_V = Lang.sing_V ;
   sit_V = Lang.sit_V ;
    sleep_V = Lang.sleep_V ;
   smell_V = Lang.smell_V ;
   spit_V = Lang.spit_V ;
   split_V2 = Lang.split_V2 ;
   squeeze_V2 = Lang.squeeze_V2 ;
   stab_V2 = Lang.stab_V2 ;
   stand_V = Lang.stand_V ;
   suck_V2 = Lang.suck_V2 ;
   swell_V = Lang.swell_V ;
   swim_V = Lang.swim_V ;
   think_V = Lang.think_V ;
   throw_V2 = Lang.throw_V2 ;
   tie_V2 = Lang.tie_V2 ;
   turn_V = Lang.turn_V ;
   vomit_V = Lang.vomit_V ;
    walk_V = Lang.walk_V ;
   wash_V2 = Lang.wash_V2 ;
   wipe_V2 = Lang.wipe_V2 ;

}
