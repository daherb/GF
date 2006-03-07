--# -path=.:../norwegian:../common:../abstract:../scandinavian:../../prelude

concrete SwadeshNor of Swadesh = CatNor
  ** open MorphoNor, LangNor, ParadigmsNor, IrregNor, Prelude in {

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
    all_Det  = {s = \\_,_ => "alle" ; n = Pl ; det = DDef Indef} ;
    many_Det = many_Det ;
    some_Det = someSg_Det ;
    few_Det  = {s = \\_,_ => "f�" ; n = Pl ; det = DDef Indef} ;
    other_Det = {s = \\_,_ => "andre" ; n = Pl ; det = DDef Indef} ;

    left_Ord = {s = "venstre" ; isDet = True} ;
    right_Ord = {s = "h�yre" ; isDet = True} ;

    -- Adverbs

    here_Adv = here_Adv ;
    there_Adv = there_Adv ;
    where_IAdv = where_IAdv ;
    when_IAdv = when_IAdv ;
    how_IAdv = how_IAdv ;

    far_Adv = mkAdv "fjern" ;

    -- not : Adv ; -- ?

    -- Conjunctions

    and_Conj = and_Conj ;

    -- Prepositions

    at_Prep = ss "ved" ;
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
    dry_A = mk2A "t�rr" "t�rt" ;
    dull_A = regA "sl�v" ;
    full_A = regA "full" ;
    good_A = good_A ;
    green_A = green_A ;
    heavy_A = irregADeg "tung" "tyngre" "tyngst" ;
    long_A = long_A ;
    narrow_A = narrow_A ;
    near_A = mkADeg "n�re" "n�re" "n�re" "n�rmere" "n�rmest" ;
    new_A = new_A ;
    old_A = old_A ;
    red_A = red_A ;
    rotten_A = mk3ADeg "r�tten" "r�ttent" "r�tne" ;
    round_A = regA "rund" ;
    sharp_A = mk2A "kvass" "kvast" ;
    short_A = short_A ;
    small_A = small_A ;
    smooth_A = mk2A "slett" "slett" ;
    straight_A = regA "rak" ;
    thick_A = thick_A ;
    thin_A = thin_A ;
    warm_A = warm_A ;
    wet_A = regA "v�t" ;
    white_A = white_A ;
    wide_A = regA "bred" ;
    yellow_A = yellow_A ;


    -- Nouns

    animal_N = mk2N "dyr" "dyret" ;
    ashes_N = mk2N "aske" "aska" ;
    back_N = mk2N "rygg" "ryggen" ;
    bark_N = mk2N "bark" "barken" ;
    belly_N = mk2N "mage" "magen" ;
    bird_N = bird_N ;
    blood_N = mk2N "blod" "blodet" ;
    bone_N = mk2N "bein" "beinet" ;
    breast_N = mk2N "bryst" "brystet" ;
    child_N = child_N ;
    cloud_N = mk2N "sky" "skya" ;
    day_N = mk2N "dag" "dagen" ;
    dog_N = dog_N ;
    dust_N = mk2N "st�v" "st�vet" ;
    ear_N = mk2N "�re" "�ret" ;
    earth_N = mk2N "jord" "jorda" ;
    egg_N = mk2N "egg" "egget" ;
    eye_N = mkN "�ye" "�yet" "�yne" "�ynene" ;
    fat_N = mk2N "fett" "fettet" ;
    father_N = mkN "far" "faren" "fedre" "fedrene" ;
--    father_N = UseN2 father_N2 ;
    feather_N = mk2N "fj�r" "fj�ra" ;
    fingernail_N = mk2N "negl" "neglen" ;
    fire_N = mk2N "ild" "ilden" ;
    fish_N = fish_N ;
    flower_N = mk2N "blomst" "blomsten" ;
    fog_N = mk2N "t�ke" "t�ka" ;
    foot_N = mk2N "fot" "f�tter" ;
    forest_N = mk2N "skog" "skogen" ;
    fruit_N = fruit_N ;
    grass_N = mk2N "gras" "graset" ;
    guts_N = mk2N "tarm" "tarmen" ; ---- involler
    hair_N = mk2N "h�r" "h�ret" ;
    hand_N = mk2N "h�nd" "h�nden" ;

    head_N = mk2N "hode" "hodet" ;
    heart_N = mk2N "hjerte" "hjertet" ;
    horn_N = mk2N "horn" "hornet" ;
    husband_N = mkN "ektemann" "ektemannen" "ektemenn" "ektemennen" ;
    ice_N = mk2N "is" "isen" ;
    knee_N = mkN "kne" "kneet" "kn�r" "kn�ne" ;
    lake_N = lake_N ;
    leaf_N = mk2N "l�v" "l�vet" ;
    leg_N = mk2N "bein" "beinet" ;
    liver_N = mkN "lever" "leveren" "levrer" "levrene" ;
    louse_N = mk2N "lus" "lusa" ;
    man_N = man_N ;
    meat_N = meat_N ;
    moon_N = moon_N ;
    mother_N = mkN "mor" "moren" "m�dre" "m�drene" ;
--    mother_N = UseN2 mother_N2 ;
    mountain_N = mountain_N ;
    mouth_N = mk2N "munn" "munnen" ;
    name_N = mk2N "navn" "navnet" ;
    neck_N = mk2N "nakke" "nakken" ;
    night_N = mkN "natt" "natta" "netter" "nettene" ;
    nose_N = mk2N "nese" "nesen" ;
    person_N = mk2N "person" "personen" ;
    rain_N = mk2N "regn" "regnet" ;
    river_N = river_N ;
    road_N = mk2N "vei" "veien" ;
    root_N = mkN "rot" "rota" "r�tter" "r�ttene" ;
    rope_N = mk2N "tau" "tauet" ;
    salt_N = mk2N "salt" "saltet" ;
    sand_N = mk2N "sand" "sanden" ;
    sea_N = sea_N ;
    seed_N = mk2N "fr�" "fr�et" ;
    skin_N = mk2N "skinn" "skinnet" ;
    sky_N = mkN "himmel" "himmelen" "himler" "himlene" ;
    smoke_N = mk2N "r�yk" "r�yken" ;
    snake_N = snake_N ;
    snow_N = mk2N "sn�" "sn�en" ;
    star_N = star_N ;
    stick_N = mk2N "pinne" "pinnen" ;
    stone_N = stone_N ;
    sun_N = sun_N ;
    tail_N = mk2N "hale" "halen" ;
    tongue_N = mk2N "tunge" "tunga" ;
    tooth_N = mkN "tann" "tanna" "tenner" "tennene" ;
    tree_N = tree_N ;
    water_N = water_N ;
    wife_N = mk2N "kone" "kona" ;
    wind_N = mk2N "vind" "vinden" ;
    wing_N = mk2N "vinge" "vingen" ;
    woman_N = woman_N ;
    worm_N = mk2N "mark" "marken" ;
    year_N = mk2N "�r" "�ret" ;

    -- Verbs

    bite_V = dirV2 (IrregNor.bite_V) ;
    blow_V = mk2V "bl�se" "bl�ste" ;
    breathe_V = dirV2 (regV "puste") ;
    burn_V = brenne_V ;
    come_V = komme_V ;
    count_V = dirV2 (regV "regne") ;
    cut_V = dirV2 (skj�re_V) ;
    die_V = d�_V ;
    dig_V = mk2V "grave" "gravde" ;
    drink_V = dirV2 (drikke_V) ;
    eat_V = dirV2 (mk2V "spise" "spiste") ;
    fall_V = falle_V ;
    fear_V = dirV2 (regV "frykte") ;
    fight_V = dirV2 (sl�ss_V) ;
    float_V = flyte_V ;
    flow_V = renne_V ;
    fly_V = fly_V ;
    freeze_V = fryse_V ;
    give_V = dirdirV3 gi_V ;
    hear_V = dirV2 (mk2V "h�re" "h�rde") ;
    hit_V = dirV2 (sl�_V) ;
    hold_V = dirV2 (holde_V) ;
    hunt_V = dirV2 (regV "jakte") ;
    kill_V = dirV2 (mk2V "drepe" "drepte") ;
    know_V = dirV2 (vite_V) ;
    laugh_V = mkV "le" "ler" "les" "lo" "ledd" "le" ;
    lie_V = ligge_V ;
    live_V = mk2V "leve" "levde" ;
    play_V = mk2V "leke" "lekte" ;
    pull_V = dirV2 (dra_V) ;
    push_V = dirV2 (irregV "skyve" "skj�v" "skj�vet") ;
    rub_V = dirV2 (gni_V) ;
    say_V = si_V ;
    scratch_V = dirV2 (regV "kl�") ;
    see_V = dirV2 (se_V) ;
    sew_V = mk2V "sy" "sydde" ;
    sing_V = synge_V ;
    sit_V = sitte_V ;
    sleep_V = sove_V ;
    smell_V = regV "lukte" ;
    spit_V = regV "spytte" ;
    split_V = dirV2 (mk2V "kl�yve" "kl�yvde") ;
    squeeze_V = dirV2 (mk2V "klemme" "klemte") ;
    stab_V = dirV2 (stikke_V) ;
    stand_V = st�_V ;
    suck_V = dirV2 (suge_V) ;
    swell_V = partV (regV "hovne") "opp" ;
    swim_V = regV "simme" ;
    think_V = mk2V "tenke" "tenkte" ;
    throw_V = dirV2 (regV "kaste") ;
    tie_V = dirV2 (regV "knytte") ;
    turn_V = mk2V "vende" "vendte" ;
    vomit_V = partV (regV "kaste") "opp" ;
    walk_V = g�_V ;
    wash_V = dirV2 (regV "vaske") ;
    wipe_V = dirV2 (regV "t�rke") ;

}
