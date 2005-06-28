--# -path=.:../abstract:../../prelude

concrete SwadeshLexFin of SwadeshLex = CategoriesFin 
  ** open ResourceFin, SyntaxFin, ParadigmsFin, 
          BasicFin, Prelude in {

  lin

    -- Pronouns

    i_NP = i_NP ;
    thou_NP = thou_NP ;
    he_NP = he_NP ;
----    we_NP = we_NP ;
    you_NP = you_NP ;
    they_NP = they_NP ;
----    who8many_IP = who8many_IP ;
----    who8one_IP = who8one_IP ;
----    what8many_IP = what8many_IP ;
----    what8one_IP = what8one_IP ;

    -- Determiners

    this_Det = this_Det ;
    that_Det = that_Det ;
----    all_NDet = all_NDet ;
    many_Det = many_Det ;
    some_Det = some_Det ;
----    few_Det = mkDeterminer Pl "few" ;
----    other_Det = mkDeterminer Pl "other" ;


    -- Adverbs

    here_Adv = here_Adv;
    there_Adv = there_Adv;
    where_IAdv = where_IAdv;
    when_IAdv = when_IAdv;
    how_IAdv = how_IAdv;

    -- not : Adv ; -- ?

    -- Conjunctions

    and_Conj = and_Conj ;

    -- Prepositions

----    at_Prep = ss "at" ;
----    in_Prep = ss "in" ;
----    with_Prep = ss "with" ;

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
    correct_ADeg = regADeg "oikea" ;
    dirty_ADeg = dirty_ADeg ;
    dry_ADeg = mkADeg (regN "kuiva") "kuivempi" "kuivin" ;
    dull_ADeg = mkADeg (regN "tyls�") "tylsempi" "tylsin" ;
    far_ADeg = regADeg "kaukainen" ;
    full_ADeg = mkADeg (reg3N "t�ysi" "t�yden" "t�ysi�") "t�ydempi" "t�ysin" ;
    good_ADeg = good_ADeg ;
    green_ADeg = green_ADeg ;
    heavy_ADeg = regADeg "raskas" ;
    long_ADeg = long_ADeg ;
    narrow_ADeg = narrow_ADeg ;
    near_ADeg = regADeg "l�heinen" ;
    new_ADeg = new_ADeg ;
    old_ADeg = old_ADeg ;
    red_ADeg = red_ADeg ;
    rotten_ADeg = regADeg "m�t�" ;
    round_ADeg = regADeg "py�re�" ;
    sharp_ADeg = regADeg "ter�v�" ;
    short_ADeg = short_ADeg ;
----    small_ADeg = small_ADeg ;
    smooth_ADeg = regADeg "sile�" ;
    straight_ADeg = mkADeg (regN "suora") "suorempi" "suorin" ;
    thick_ADeg = thick_ADeg ;
    thin_ADeg = thin_ADeg ;
----    warm_ADeg = warm_ADeg ;
    wet_ADeg = mkADeg (regN "m�rk�") "m�rempi" "m�rin" ;
    white_ADeg = white_ADeg ;
    wide_ADeg = regADeg "leve�" ;
    yellow_ADeg = yellow_ADeg ;

    left_A = mkA (regN "vasen") ; ----
    right_A = mkA (regN "oikea") ;

    -- Nouns

    animal_N = regN "el�in" ;
    ashes_N = regN "tuhka" ;
    back_N = regN "selk�" ;
    bark_N = regN "kaarna" ;
    belly_N = regN "vatsa" ;
    bird_N = bird_N;
    blood_N = reg2N "veri" "veri�" ;
    bone_N = regN "luu" ;
    breast_N = regN "rinta" ;
    child_N = child_N ;
    cloud_N = reg2N "pilvi" "pilvi�" ;
    day_N = regN "p�iv�" ;
    dog_N = dog_N ;
    dust_N = regN "p�ly" ;
    ear_N = regN "korva" ;
    earth_N = regN "maa" ;
    egg_N = regN "muna" ;
    eye_N = regN "silm�" ;
    fat_N = regN "rasva" ;
----    father_N = UseN2 father_N2 ;
    feather_N = reg3N "h�yhen" "h�yhenen" "h�yheni�" ; -----
    fingernail_N = reg3N "kynsi" "kynnen" "kynsi�" ;
    fire_N = reg2N "tuli" "tulia" ;
    fish_N = fish_N ;
    flower_N = regN "kukka" ;
    fog_N = regN "sumu" ;
    foot_N = regN "jalka" ;
    forest_N = regN "mets�" ;
    fruit_N = fruit_N ;
    grass_N = regN "ruoho" ;
    guts_N = regN "sis�lmys" ; --- suoli
    hair_N = regN "hius" ;
    hand_N = reg3N "k�si" "k�den" "k�si�" ;
    head_N = regN "p��" ;
    heart_N = regN "syd�n" ; -----
    horn_N = reg2N "sarvi" "sarvia" ;
    husband_N = man_N ; --- aviomies
    ice_N = regN "j��" ;
    knee_N = reg2N "polvi" "polvia" ;
    lake_N = lake_N ;
    leaf_N = reg2N "lehti" "lehti�" ;
    leg_N = regN "jalka" ; --- s��ri
    liver_N = regN "maksa" ;
    louse_N = regN "lude" ;
    man_N = man_N ;
    meat_N = meat_N ;
    moon_N = moon_N ;
----    mother_N = UseN2 mother_N2 ;
    mountain_N = mountain_N ;
    mouth_N = regN "suu" ;
    name_N = reg2N "nimi" "nimi�" ;
    neck_N = regN "niska" ;
    night_N = regN "y�" ;
    nose_N = regN "nen�" ;
    person_N = regN "henkil�" ;
    rain_N = regN "sade" ;
----    river_N = river_N ;
    road_N = regN "tie" ;
    root_N = regN "juuri" ; -----
    rope_N = reg3N "k�ysi" "k�yden" "k�ysi�" ;
    salt_N = regN "suola" ;
    sand_N = regN "hiekka" ;
    sea_N = sea_N ;
    seed_N = regN "seed" ;
    skin_N = regN "skin" ;
    sky_N = regN "sky" ; -----
    smoke_N = regN "savu" ;
    snake_N = snake_N ;
    snow_N = regN "lumi" ; -----
    star_N = star_N ;
    stick_N = regN "keppi" ;
    stone_N = stone_N ;
    sun_N = sun_N ;
    tail_N = regN "h�nt�" ;
    tongue_N = regN "kieli" ;
    tooth_N = regN "hammas" ;
    tree_N = tree_N ;
    water_N = water_N ;
    wife_N = regN "vaimo" ;
    wind_N = reg2N "tuuli" "tuulia" ;
    wing_N = reg2N "siipi" "siipi�" ;
    woman_N = woman_N ;
    worm_N = regN "mato" ;
    year_N = reg2N "vuosi" "vuosia" ;

    -- Verbs

    bite_V = regV "purra" ;
    blow_V = regV "puhaltaa" ;
    breathe_V = regV "hengitt��" ;
    burn_V = regV "palaa" ;
    come_V = BasicFin.come_V ;
    count_V = regV "laskea" ;
    cut_V = regV "leikata" ;
    die_V = regV "kuolla";
    dig_V = regV "kaivata" ;
    drink_V = UseV2 drink_V2 ;
    eat_V = UseV2 eat_V2 ;
    fall_V = regV "pudota" ;
    fear_V = regV "fear" ;
    fight_V = regV "taistella" ;
    float_V = regV "kellua" ;
    flow_V = regV "virrata" ;
    fly_V = regV "lent��" ;
    freeze_V = regV "j��ty�" ;
    give_V = regV "antaa" ;
    hear_V = UseV2 hear_V2 ;
    hit_V = regV "sy�d�" ;
    hold_V = regV "pit��" ;
    hunt_V = regV "mets�st��" ;
    kill_V = regV "tappaa" ;
    know_V =reg2V "tiet��" "tiesin" ;
    laugh_V = regV "nauraa" ; -----
    lie_V = regV "maata" ;
    live_V = live_V ;
    play_V = UseV2 play_V2 ;
    pull_V = regV "vet��" ;
    push_V = regV "ty�nt��" ;
    rub_V = regV "hieroa" ;
    say_V = regV "sanoa" ;
    scratch_V = regV "raapia" ;
-----    see_V = UseV2 see_V2 ;
    sew_V = regV "kylv��" ;
    sing_V = regV "laulaa" ;
    sit_V = regV "istua" ;
    sleep_V = sleep_V ;
    smell_V = regV "haista" ;
    spit_V = regV "sylke�" ;
----    split_V = split_V ;
    squeeze_V = regV "puristaa" ;
    stab_V = regV "pist��" ;
----    stand_V = stand_V ;
    suck_V = regV "ime�" ;
----    swell_V = swell_V ;
----    swim_V = swim_V ;
----    think_V = think_V ;
----    throw_V = throw_V ;
    tie_V = regV "sitoa" ;
    turn_V = regV "k��nty�" ;
    vomit_V = regV "oksentaa" ;
    walk_V = walk_V ;
    wash_V = regV "pest�" ;
    wipe_V = regV "pyyhki�" ;

}