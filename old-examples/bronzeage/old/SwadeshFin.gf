--# -path=.:../present:../finnish:../common:../abstract:../../prelude

concrete SwadeshFin of Swadesh = CatFin
  ** open MorphoFin, LangFin, ParadigmsFin, Prelude in {

  flags optimize=values ;

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
    all_Det = mkDet Pl {s = \\nf => 
      let
        kaiket = (nhn (sKorpi "kaikki" "kaiken" "kaikkena")).s
      in
      case nf of {
        NCase Pl Nom => "kaikki" ;
        _ => kaiket ! nf
        }
      } ;
    many_Det = many_Det ;
    some_Det = someSg_Det ;
    few_Det  = mkDet Sg (regN "harva") ;
    other_Det = mkDet Sg (regN "muu") ;

    left_Ord = mkOrd (regN "vasen") ;
    right_Ord = mkOrd (regN "oikea") ;

  oper
    mkOrd : N -> Ord ;
    mkOrd x = {s = \\n,c => x.s ! NCase n c; lock_Ord = <> } ;

  lin

    -- Adverbs

    here_Adv = here_Adv;
    there_Adv = there_Adv;
    where_IAdv = where_IAdv;
    when_IAdv = when_IAdv;
    how_IAdv = how_IAdv;
    far_Adv = mkAdv "kaukana" ;

    -- not : Adv ; -- ?

    -- Conjunctions

    and_Conj = and_Conj ;

    -- Prepositions

    at_Prep = casePrep adessive ;
    in_Prep = casePrep inessive ;
    with_Prep = postGenPrep "kanssa" ;

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
    correct_A = regA "oikea" ;
    dirty_A = dirty_A ;
    dry_A = mkADeg (regN "kuiva") "kuivempi" "kuivin" ;
    dull_A = mkADeg (regN "tyls�") "tylsempi" "tylsin" ;
    full_A = mkADeg (reg3N "t�ysi" "t�yden" "t�ysi�") "t�ydempi" "t�ysin" ;
    good_A = good_A ;
    green_A = green_A ;
    heavy_A = regA "raskas" ;
    long_A = long_A ;
    narrow_A = narrow_A ;
    near_A = regA "l�heinen" ;
    new_A = new_A ;
    old_A = old_A ;
    red_A = red_A ;
    rotten_A = regA "m�t�" ;
    round_A = regA "py�re�" ;
    sharp_A = regA "ter�v�" ;
    short_A = short_A ;
    small_A = small_A ;
    smooth_A = regA "sile�" ;
    straight_A = mkADeg (regN "suora") "suorempi" "suorin" ;
    thick_A = thick_A ;
    thin_A = thin_A ;
    warm_A = warm_A ;
    wet_A = mkADeg (regN "m�rk�") "m�rempi" "m�rin" ;
    white_A = white_A ;
    wide_A = regA "leve�" ;
    yellow_A = yellow_A ;

    -- Nouns

    animal_N = reg3N "el�in" "el�imen" "el�imi�" ;
    ashes_N = regN "tuhka" ;
    back_N = regN "selk�" ;
    bark_N = regN "kaarna" ;
    belly_N = regN "vatsa" ;
    bird_N = bird_N;
    blood_N = nMeri "veri" ;
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
    father_N = regN "is�" ;
    feather_N = reg3N "h�yhen" "h�yhenen" "h�yheni�" ;
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
    heart_N = reg3N "syd�n" "syd�men" "syd�mi�" ;
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
    mother_N = regN "�iti" ;
    mountain_N = mountain_N ;
    mouth_N = regN "suu" ;
    name_N = reg2N "nimi" "nimi�" ;
    neck_N = regN "niska" ;
    night_N = regN "y�" ;
    nose_N = regN "nen�" ;
    person_N = regN "henkil�" ;
    rain_N = regN "sade" ;
    river_N = river_N ;
    road_N = regN "tie" ;
    root_N = reg2N "juuri" "juuria" ;
    rope_N = reg3N "k�ysi" "k�yden" "k�ysi�" ;
    salt_N = regN "suola" ;
    sand_N = regN "hiekka" ;
    sea_N = sea_N ;
    seed_N = regN "siemen" ;
    skin_N = regN "nahka" ;
    sky_N = reg3N "taivas" "taivaan" "taivaita" ;
    smoke_N = regN "savu" ;
    snake_N = snake_N ;
    snow_N = sgpartN (nMeri "lumi") "lunta" ;
    star_N = star_N ;
    stick_N = regN "keppi" ;
    stone_N = stone_N ;
    sun_N = sun_N ;
    tail_N = regN "h�nt�" ;
    tongue_N = reg2N "kieli" "kieli�" ;
    tooth_N = regN "hammas" ;
    tree_N = tree_N ;
    water_N = water_N ;
    wife_N = regN "vaimo" ;
    wind_N = reg2N "tuuli" "tuulia" ;
    wing_N = reg2N "siipi" "siipi�" ;
    woman_N = woman_N ;
    worm_N = regN "mato" ;
    year_N = reg3N "vuosi" "vuoden" "vuosia" ;

    -- Verbs

    bite_V2 = dirV2 (regV "purra") ;
    blow_V = regV "puhaltaa" ;
    breathe_V2 = dirV2 (regV "hengitt��") ;
    burn_V = regV "palaa" ;
    come_V = come_V ;
    count_V2 = dirV2 (regV "laskea") ;
    cut_V2 = dirV2 (reg2V "leikata" "leikkasi") ;
    die_V = regV "kuolla";
    dig_V = regV "kaivaa" ;
    drink_V2 = dirV2 ( drink_V2) ;
    eat_V2 = dirV2 ( eat_V2) ;
    fall_V = reg3V "pudota" "putoan" "putosi" ;
    fear_V2 = dirV2 (reg3V "pel�t�" "pelk��n" "pelk�si") ;
    fight_V2 = dirV2 (regV "taistella") ;
    float_V = regV "kellua" ;
    flow_V = reg3V "virrata" "virtaan" "virtasi" ;
    fly_V = regV "lent��" ;
    freeze_V = regV "j��ty�" ;
    give_V = dirdirV3 (regV "antaa") ;
    hear_V2 = dirV2 ( hear_V2) ;
    hit_V2 = dirV2 (regV "ly�d�") ;
    hold_V2 = dirV2 (regV "pit��") ;
    hunt_V2 = dirV2 (regV "mets�st��") ;
    kill_V2 = dirV2 (regV "tappaa") ;
    know_V2 = dirV2 (reg2V "tuntea" "tunsin") ;
    laugh_V = reg3V "nauraa" "nauran" "nauroi" ;
    lie_V = reg3V "maata" "makaan" "makasi" ;
    live_V = live_V ;
    play_V =  play_V2 ;
    pull_V2 = dirV2 (regV "vet��") ;
    push_V2 = dirV2 (regV "ty�nt��") ;
    rub_V2 = dirV2 (regV "hieroa") ;
    say_V = regV "sanoa" ;
    scratch_V2 = dirV2 (regV "raapia") ;
    see_V = ( see_V2) ;
    sew_V = regV "kylv��" ;
    sing_V = regV "laulaa" ;
    sit_V = regV "istua" ;
    sleep_V = sleep_V ;
    smell_V = reg2V "haistaa" "haistoi" ;
    spit_V = regV "sylke�" ;
    split_V2 = dirV2 (reg2V "halkaista" "halkaisi") ;
    squeeze_V2 = dirV2 (regV "puristaa") ;
    stab_V2 = dirV2 (regV "pist��") ;
    stand_V = mkV "seist�" "seisoo" "seison" "seisovat" "seisk��" "seist��n"
      "seisoi" "seisoin" "seisoisi" "seissyt" "seisty" "seistyn" ; --- *seisoiv�t
    suck_V2 = dirV2 (regV "ime�") ;
    swell_V = mkV "turvota" "turpoaa" "turpoan" "turpoavat" "turvotkaa" "turvotaan"
      "turposi" "turposin" "turpoaisi" "turvonnut" "turvottu" "turvotun" ;
    swim_V = reg3V "uida" "uin" "ui" ;
    think_V = reg3V "ajatella" "ajattelen" "ajatteli" ;
    throw_V2 = dirV2 (regV "heitt��") ;
    tie_V2 = dirV2 (regV "sitoa") ;
    turn_V = regV "k��nty�" ;
    vomit_V = regV "oksentaa" ;
    walk_V = walk_V ;
    wash_V2 = dirV2 (regV "pest�") ;
    wipe_V2 = dirV2 (regV "pyyhki�") ;

oper 
  regA = regADeg ; ----


}
