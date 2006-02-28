--# -path=.:present:prelude

concrete SwadeshSwe of Swadesh = CatSwe
  ** open MorphoSwe, LangSwe, ParadigmsSwe, IrregSwe, Prelude in {

  lincat
    MassN = N ;

  lin

    -- Pronouns

    i_NP = i_Pron ;
    youSg_NP = youSg_Pron ;
    he_NP = he_Pron ;
    we_NP = we_Pron ;
    youPl_NP = youPl_Pron ;
    they_NP = they_Pron ;
    whoPl_IP = whoPl_IP ;
    whoSg_IP = whoSg_IP ;
    whatPl_IP = whatPl_IP ;
    whatSg_IP = whatSg_IP ;

    -- Determiners

    this_Det = DetSg (SgQuant this_Quant) NoOrd ;
    that_Det = DetSg (SgQuant that_Quant) NoOrd ;
    all_Det  = {s = \\_,_ => "alla" ; n = Pl ; det = DDef Indef} ;
    many_Det = many_Det ;
    some_Det = someSg_Det ;
    few_Det  = {s = \\_,_ => "f�" ; n = Pl ; det = DDef Indef} ;
    other_Det = {s = \\_,_ => "andra" ; n = Pl ; det = DDef Indef} ;

    left_Ord = {s = "v�nstra" ; isDet = True} ;
    right_Ord = {s = "h�gra" ; isDet = True} ;

    -- Adverbs

    here_Adv = here_Adv ;
    there_Adv = there_Adv ;
    where_IAdv = where_IAdv ;
    when_IAdv = when_IAdv ;
    how_IAdv = how_IAdv ;
    far_Adv = mkAdv "l�ngt" ;

    -- not : Adv ; -- ?

    -- Conjunctions

    and_Conj = and_Conj ;

    -- Prepositions

    at_Prep = ss "vid" ;
    in_Prep = ss "i" ;
    with_Prep = ss "med" ;

    -- Numerals

    one_Det = DetSg one_Quant NoOrd ;
    two_Num = NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))) ;
    three_Num = NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))) ;
    four_Num = NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n4))))) ;
    five_Num = NumNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n5))))) ;

    -- Adjectives

    bad_A = bad_A ;
    big_A = big_A ;
    black_A = black_A ;
    cold_A = cold_A ;
    correct_A = regA "riktig" ;
    dirty_A = dirty_A ;
    dry_A = regA "torr" ;
    dull_A = mk2A "sl�" "sl�tt";
    full_A = regA "full" ;
    good_A = good_A ;
    green_A = green_A ;
    heavy_A = irregA "tung" "tyngre" "tyngst" ;
    long_A = long_A ;
    narrow_A = narrow_A ;
    near_A = mkA "n�ra" "n�ra" "n�ra" "n�ra"
                       "n�rmare" "n�rmast" "n�rmaste" ;
    new_A = new_A ;
    old_A = old_A ;
    red_A = red_A ;
    rotten_A = mk3A "rutten" "ruttet" "ruttna" ;
    round_A = regA "rund" ;
    sharp_A = regA "vass" ;
    short_A = short_A ;
    small_A = small_A ;
    smooth_A = regA "sl�t" ;
    straight_A = regA "rak" ;
    thick_A = thick_A ;
    thin_A = thin_A ;
    warm_A = warm_A ;
    wet_A = regA "v�t" ;
    white_A = white_A ;
    wide_A = mk2A "bred" "brett" ;
    yellow_A = yellow_A ;


    -- Nouns

    animal_N = mk2N "djur" "djur" ;
    ashes_N = mk2N "aska" "askor" ;
    back_N = mk2N "rygg" "ryggar" ;
    bark_N = mk2N "bark" "barkar" ;
    belly_N = mk2N "mage" "magar" ;
    bird_N = bird_N ;
    blood_N = mk2N "blod" "blod" ;
    bone_N = mk2N "ben" "ben" ;
    breast_N = mk2N "br�st" "br�st" ;
    child_N = child_N ;
    cloud_N = mk2N "moln" "moln" ;
    day_N = mk2N "dag" "dagar" ;
    dog_N = dog_N ;
    dust_N = mk2N "damm" "damm" ;
    ear_N = mkN "�ra" "�rat" "�ron" "�ronen" ;
    earth_N = mk2N "jord" "jordar" ;
    egg_N = mk2N "�gg" "�gg" ;
    eye_N = mkN "�ga" "�gat" "�gon" "�gonen" ;
    fat_N = mk2N "fett" "fett" ;
    father_N = (mkN "far" "fadern" "f�der" "f�derna") ;
--    father_N = UseN2 father_N2 ;
    feather_N = mk2N "fj�der" "fj�drar" ;
    fingernail_N = mkN "nagel" "nageln" "naglar" "naglarna";
    fire_N = mk2N "eld" "eldar" ;
    fish_N = fish_N ;
    flower_N = mk2N "blomma" "blommor" ;
    fog_N = mk2N "dimma" "dimmor" ;
    foot_N = mk2N "fot" "f�tter" ;
    forest_N = mk2N "skog" "skogar" ;
    fruit_N = fruit_N ;
    grass_N = mk2N "gr�s" "gr�s" ;
    guts_N = mk2N "in�lva" "in�lvor" ;
    hair_N = mk2N "h�r" "h�r" ;
    hand_N = mk2N "hand" "h�nder" ;
    head_N = mkN "huvud" "huvudet" "huvuden" "huvudena" ;
    heart_N = mkN "hj�rta" "hj�rtat" "hj�rtan" "hj�rtana" ;
    horn_N = mk2N "horn" "horn" ;
    husband_N = (mk2N "make" "makar") ;
    ice_N = mk2N "is" "isar" ;
    knee_N = mkN "kn�" "kn�et" "kn�n" "kn�na" ;
    lake_N = lake_N ;
    leaf_N = mk2N "l�v" "l�v" ;
    leg_N = mk2N "ben" "ben" ;
    liver_N = mkN "lever" "levern" "levrar" "levrarna";
    louse_N = mkN "lus" "lusen" "l�ss" "l�ssen" ;
    man_N = man_N ;
    meat_N = meat_N ;
    moon_N = moon_N ;
    mother_N = mkN "mor" "modern" "m�drar" "m�drarna" ;
--    mother_N = UseN2 mother_N2 ;
    mountain_N = mountain_N ;
    mouth_N = mkN "mun" "munnen" "munnar" "munnarna" ;
    name_N = mk2N "namn" "namn" ;
    neck_N = mk2N "nacke" "nackar" ;
    night_N = mk2N "natt" "n�tter" ;
    nose_N = mk2N "n�sa" "n�sor" ;
    person_N = mk2N "person" "personer" ;
    rain_N = mk2N "regn" "regn" ;
    river_N = river_N ;
    road_N = mk2N "v�g" "v�gar" ;
    root_N = mk2N "rot" "r�tter" ;
    rope_N = mk2N "rep" "rep" ;
    salt_N = mkN "salt" "saltet" "salter" "salterna";
    sand_N = mk2N "sand" "sander" ;
    sea_N = sea_N ;
    seed_N = mkN "fr�" "fr�et" "fr�n" "fr�na" ;
    skin_N = mk2N "skinn" "skinn" ;
    sky_N = mk2N "himmel" "himlar" ;
    smoke_N = mk2N "r�k" "r�kar" ;
    snake_N = snake_N ;
    snow_N = mkN "sn�" "sn�n" "sn�er" "sn�erna" ;
    star_N = star_N ;
    stick_N = mk2N "pinne" "pinnar" ;
    stone_N = stone_N ;
    sun_N = sun_N ;
    tail_N = mk2N "svans" "svansar" ;
    tongue_N = mk2N "tunga" "tungor" ;
    tooth_N = mk2N "tand" "t�nder" ;
    tree_N = tree_N ;
    water_N = water_N ;
    wife_N = mk2N "fru" "fruar" ;
    wind_N = mk2N "vind" "vindar" ;
    wing_N = mk2N "vinge" "vingar" ;
    woman_N = woman_N ;
    worm_N = mk2N "mask" "maskar" ;
    year_N = mk2N "�r" "�r" ;

    -- Verbs

    bite_V = dirV2 (bita_V) ;
    blow_V = mk2V "bl�sa" "bl�ste" ;
    breathe_V = dirV2 (depV (regV "anda")) ;
    burn_V = brinna_V ; -- FIXME: br�nna?
    come_V = komma_V ;
    count_V = dirV2 (regV "r�kna") ;
    cut_V = dirV2 (sk�ra_V) ;
    die_V = d�_V ;
    dig_V = mk2V "gr�va" "gr�vde" ;
    drink_V = dirV2 (dricka_V) ;
    eat_V = dirV2 (�ta_V) ;
    fall_V = falla_V ;
    fear_V = dirV2 (regV "frukta") ;
      -- FIXME: passive forms are very strange
    fight_V = mkV2 (mkV "sl�ss" "sl�ss" "sl�ss" "slogs" "slagits" "slagen") "med" ;
    float_V = flyta_V ;
    flow_V = rinna_V ;
    fly_V = flyga_V ;
    freeze_V = frysa_V ;
    give_V = dirdirV3 giva_V ; ----
    hear_V = dirV2 (mk2V "h�ra" "h�rde") ;
    hit_V = dirV2 (sl�_V) ;
    hold_V = dirV2 (h�lla_V) ;
    hunt_V = dirV2 (regV "jaga") ;
    kill_V = dirV2 (regV "d�da") ;
    know_V = dirV2 (veta_V) ;
    laugh_V = regV "skratta" ;
    lie_V = ligga_V ;
    live_V = leva_V ;
    play_V = mk2V "leka" "lekte" ;
    pull_V = dirV2 (draga_V) ;
    push_V = dirV2 (mk2V "trycka" "tryckte") ;
    rub_V = dirV2 (gnida_V) ;
    say_V = s�ga_V ;
    scratch_V = dirV2 (regV "klia") ;
    see_V = dirV2 (se_V) ;
    sew_V = sy_V ;
    sing_V = sjunga_V ;
    sit_V = sitta_V ;
    sleep_V = sova_V ;
    smell_V = regV "lukta" ;
    spit_V = regV "spotta" ;
    split_V = dirV2 (klyva_V) ;
    squeeze_V = dirV2 (kl�mma_V) ;
    stab_V = dirV2 (sticka_V) ;
    stand_V = st�_V ;
    suck_V = dirV2 (suga_V) ;
    swell_V = sv�lla_V ;
    swim_V = regV "simma" ;
    think_V = mk2V "t�nka" "t�nkte" ;
    throw_V = dirV2 (regV "kasta") ;
    tie_V = dirV2 (knyta_V) ;
    turn_V = v�nda_V ;
    vomit_V = mk2V "spy" "spydde" ;
    walk_V = g�_V ;
    wash_V = dirV2 (regV "tv�tta") ;
    wipe_V = dirV2 (regV "torka") ;

}
