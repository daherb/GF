--# -path=.:../abstract:../scandinavian:../../prelude

concrete SwadeshLexSwe of SwadeshLex = CategoriesSwe 
  ** open ResourceSwe, SyntaxSwe, ParadigmsSwe, VerbsSwe, 
          BasicSwe, Prelude in {

  lin

    -- Pronouns

    i_NP = i_NP ;
    thou_NP = thou_NP ;
    he_NP = he_NP ;
    we_NP = we_NP ;
    you_NP = you_NP ;
    they_NP = they_NP ;
    who8many_IP = who8many_IP ;
    who8one_IP = who8one_IP ;
    what8many_IP = what8many_IP ;
    what8one_IP = what8one_IP ;

    -- Determiners

    this_Det = this_Det ;
    that_Det = that_Det ;
    all_NDet = all_NDet ;
    many_Det = many_Det ;
    some_Det = some_Det ;
    few_Det = mkDeterminerPl "f�" IndefP ;
    other_Det = mkDeterminerPl "andra" IndefP ;


    -- Adverbs

    here_Adv = here_Adv ;
    there_Adv = there_Adv ;
    where_IAdv = where_IAdv ;
    when_IAdv = when_IAdv ;
    how_IAdv = how_IAdv ;

    -- not : Adv ; -- ?

    -- Conjunctions

    and_Conj = and_Conj ;

    -- Prepositions

    at_Prep = ss "vid" ;
    in_Prep = ss "i" ;
    with_Prep = ss "med" ;

    -- Numerals

    one_Num = UseNumeral (num (pot2as3 (pot1as2 (pot0as1 pot01)))) ;
    two_Num = UseNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n2))))) ;
    three_Num = UseNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n3))))) ;
    four_Num = UseNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n4))))) ;
    five_Num = UseNumeral (num (pot2as3 (pot1as2 (pot0as1 (pot0 n5))))) ;

    -- Adjectives

    bad_ADeg = bad_ADeg ;
    big_ADeg = big_ADeg ;
    black_ADeg = black_ADeg ;
    cold_ADeg = cold_ADeg ;
    correct_ADeg = regADeg "riktig" ;
    dirty_ADeg = dirty_ADeg ;
    dry_ADeg = regADeg "torr" ;
    dull_ADeg = regADeg "sl�" ;
    far_ADeg = regADeg "avl�gsen" ;
    full_ADeg = regADeg "full" ;
    good_ADeg = good_ADeg ;
    green_ADeg = green_ADeg ;
    heavy_ADeg = irregADeg "tung" "tyngre" "tyngst" ;
    left_A = mkA "v�nstra" "v�nstra" "v�nstra" ;
    long_ADeg = long_ADeg ;
    narrow_ADeg = narrow_ADeg ;
    near_ADeg = mkADeg "n�ra" "n�ra" "n�ra" "n�ra" 
                       "n�rmare" "n�rmast" "n�rmaste" ;
    new_ADeg = new_ADeg ;
    old_ADeg = old_ADeg ;
    red_ADeg = red_ADeg ;
    right_A = mkA "h�gra" "h�gra" "h�gra" ;
    rotten_ADeg = mk3ADeg "rutten" "ruttet" "ruttna" ;
    round_ADeg = regADeg "rund" ;
    sharp_ADeg = regADeg "vass" ;
    short_ADeg = short_ADeg ;
    small_ADeg = small_ADeg ;
    smooth_ADeg = regADeg "sl�t" ;
    straight_ADeg = regADeg "rak" ;
    thick_ADeg = thick_ADeg ;
    thin_ADeg = thin_ADeg ;
    warm_ADeg = warm_ADeg ;
    wet_ADeg = regADeg "v�t" ;
    white_ADeg = white_ADeg ;
    wide_ADeg = mk2ADeg "bred" "brett" ;
    yellow_ADeg = yellow_ADeg ;


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
    father_N = mascN (mkN "far" "fadern" "f�der" "f�derna") ; 
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
    husband_N = mascN (mk2N "make" "makar") ;
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
    mouth_N = mk2N "mun" "munnar" ;
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
    salt_N = mk2N "salt" "salter" ;
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

    bite_V = bita_V ;
    blow_V = mk2V "bl�sa" "bl�ste" ;
    breathe_V = depV (regV "anda") ;
    burn_V = brinna_V ; -- FIXME: br�nna?
    come_V = komma_V ;
    count_V = regV "r�kna" ;
    cut_V = sk�ra_V ;
    die_V = d�_V ;
    dig_V = mk2V "gr�va" "gr�vde" ;
    drink_V = dricka_V ;
    eat_V = �ta_V ;
    fall_V = falla_V ;
    fear_V = regV "frukta" ;
      -- FIXME: passive forms are very strange
    fight_V = mkV "sl�ss" "sl�ss" "sl�ss" "slogs" "slagits" "slagen" ;
    float_V = flyta_V ;
    flow_V = rinna_V ;
    fly_V = flyga_V ;
    freeze_V = frysa_V ;
    give_V = giva_V ;
    hear_V = mk2V "h�ra" "h�rde" ;
    hit_V = sl�_V;
    hold_V = h�lla_V ;
    hunt_V = regV "jaga" ;
    kill_V = regV "d�da" ;
    know_V = veta_V ;
    laugh_V = regV "skratta" ;
    lie_V = ligga_V ;
    live_V = leva_V ;
    play_V = mk2V "leka" "lekte" ;
    pull_V = draga_V ;
    push_V = mk2V "trycka" "tryckte" ;
    rub_V = gnida_V ;
    say_V = s�ga_V ;
    scratch_V = regV "klia" ;
    see_V = se_V ;
    sew_V = sy_V ;
    sing_V = sjunga_V ;
    sit_V = sitta_V ;
    sleep_V = sova_V ;
    smell_V = regV "lukta" ;
    spit_V = regV "spotta" ;
    split_V = klyva_V ;
    squeeze_V = kl�mma_V ;
    stab_V = sticka_V ;
    stand_V = st�_V ;
    suck_V = suga_V ;
    swell_V = sv�lla_V ;
    swim_V = regV "simma" ;
    think_V = mk2V "t�nka" "t�nkte" ;
    throw_V = regV "kasta" ;
    tie_V = knyta_V ;
    turn_V = v�nda_V ;
    vomit_V = mk2V "spy" "spydde" ;
    walk_V = g�_V ;
    wash_V = regV "tv�tta" ;
    wipe_V = regV "torka" ;

}