--# -path=.:../../prelude

instance SyntaxIta of SyntaxRomance = 
  TypesIta ** open Prelude, (CO=Coordination), MorphoIta in {
oper
  nameNounPhrase = \jean -> 
    normalNounPhrase
      (\\c => prepCase c ++ jean.s) 
      jean.g 
      Sg ;

  chaqueDet  = mkDeterminer1 Sg "ogni" ;
  tousDet    = mkDeterminer  Pl ["tutti i"] ["tutte le"] ; --- gli
  plupartDet = mkDeterminer1 Pl ["la maggior parte di"] ;  --- dei, degli, delle
  unDet      = mkDeterminer  Sg artUno artUna ;
  plDet      = mkDeterminer1 Pl [] ;                       --- dei, degli, delle

  quelDet  = mkDeterminer1 Sg "quale" ;

  npGenPoss = \n,ton,mec ->
    \\c => artDef mec.g n c ++ ton.s ! Poss n mec.g ++ mec.s ! n ; --- mia madre

  mkAdjSolo : Str -> Bool -> Adjective = \adj,p ->
    mkAdjective (adjSolo adj) p ;

  mkAdjTale : Str -> Bool -> Adjective = \adj,p ->
    mkAdjective (adjTale adj) p ;

  mkAdjDegrSolo : Str -> Bool -> AdjDegr = \adj,p ->
    mkAdjDegrLong (adjSolo adj) p ;

  mkAdjDegrTale : Str -> Bool -> AdjDegr = \adj,p ->
    mkAdjDegrLong (adjTale adj) p ;

  comparConj = variants {"di" ; "che"} ;

-- The commonest case for functions is common noun + "di".

  funDi : CommNounPhrase -> Function = \mere -> 
    mere ** complementCas genitive ;

-- Chains of "cui" - "cui" do not arise.

  funRelPron = \mere,lequel -> 
    {s = table {
           RComplex g n c => variants {
               case mere.c of {
                 CPrep P_di => artDef mere.g n c ++ 
                               lequel.s ! RSimple dative ++ mere.s ! n ;
                 _ => nonExist} ;
               artDef mere.g n c ++ mere.s ! n ++ 
                  mere.s2 ++ lequel.s ! RComplex g n mere.c
               } ;
           _ => nonExist
         } ;
     g = RG mere.g
    } ;

-- Verbs

  negVerb = \va -> "non" ++ va ;

  copula = \b -> \\v => (if_then_else Str b [] "non") ++ verbEssere.s ! v ;

  isTransVerbClit = \v -> case v.c of { 
     Acc => True ;
     _   => False  --- hmmm
     } ;

-- The negation of a verb.

  posNeg = \b,v,c -> 
    if_then_else Str b
      (v ++ c)
      ("non" ++ v ++ c) ;

  locativeNounPhrase = \jean ->
    {s = "in" ++ jean.s ! Ton Acc} ; ----

  embedConj = "che" ;

-- Relative pronouns

  identRelPron = {
    s = table {
      RSimple c => relPronForms ! c ;
      RComplex g n c => composRelPron g n c
      } ; 
    g = RNoGen
    } ;

  suchPron = talPron ;

  composRelPron = ilqualPron ;

  allRelForms = \lequel,g,n,c ->
    variants {
      lequel.s ! RSimple c ;
      lequel.s ! RComplex g n c
      } ;

-- Interrogative pronouns

  nounIntPron = \n, mec ->
    {s = \\c => prepCase c ++ qualPron mec.g n ++ mec.s ! n ;
     g = mec.g ; 
     n = n
    } ; 

  intPronWho = \num -> {
    s = \\c => prepCase c ++ "chi" ;
    g = Masc ; --- can we decide this?
    n = num
  } ;

  intPronWhat = \num -> {
    s = table {
          c => prepCase c ++ "che" ++ optStr "cosa" 
          } ;
    g = Masc ; --- can we decide this?
    n = num
  } ;

-- Questions

  questVerbPhrase = \jean,dort ->
    {s = table {
      DirQ   => (predVerbPhrase jean dort).s ! Ind ;
      IndirQ => "se" ++ (predVerbPhrase jean dort).s ! Ind
      }
    } ;

  intVerbPhrase = \qui, dort ->
    {s = table {
      DirQ => qui.s ! Nom ++ 
              dort.s ! qui.g ! VFin Ind qui.n P3 ;
      IndirQ => qui.s ! Nom ++ dort.s ! qui.g ! VFin Ind qui.n P3
      }
    } ;

  intSlash = \Qui, Tuvois ->
    let {qui = Tuvois.s2 ++ Qui.s ! Tuvois.c ; tuvois = Tuvois.s ! Ind} in
    {s = table {
      DirQ   => qui ++ tuvois ; 
      IndirQ => ifCe Tuvois.c ++ qui ++ tuvois
      }
    } ;

-- An auxiliary to distinguish between
-- "je ne sais pas" ("ce qui dort" / "ce que tu veux" / "� qui tu penses").

  ifCe : Case -> Str = \c -> case c of { ---
    Nom => "ci�" ;
    Acc => "ci�" ; 
    _   => []
    } ;

  questAdverbial = \quand, jean, dort ->
    let {jeandort = (predVerbPhrase jean dort).s ! Ind} in
    {s = table {
      DirQ   => quand.s ++ jeandort ;  --- inversion? 
      IndirQ => quand.s ++ jeandort
      }
    } ;

---- moved from MorphoIta

-- A macro for defining gender-dependent tables will be useful.
-- Its first application is in the indefinite article.

  genForms = \matto, matta ->
    table {Masc => matto ; Fem => matta} ; 

  artUno : Str = elision "un" "un" "uno" ;
  artUna : Str = elision "una" "un'" "una" ;

  artIndef = \g,n,c -> case n of {
    Sg  => prepCase c ++ genForms artUno artUna ! g ;
    _   => prepCase c ++ []
    } ;

  artDef = \g,n,c -> artDefTable ! g ! n ! c ;

-- The composable pronoun "il quale" is inflected by varying the definite
-- article and the determiner "quale" in the expected way.

  ilqualPron : Gender -> Number -> Case -> Str = \g,n,c -> 
    artDef g n c ++ qualPron g n ;

  pronJe = mkPronoun
    "io"
    "mi"
    "mi"
    "me"
    "mio" "mia" "miei" "mie"
    PNoGen     -- gender cannot be known from pronoun alone
    Sg
    P1
    Clit1 ;

  pronTu = mkPronoun
    "tu"
    "ti"
    "ti"
    "te"
    "tuo" "tua" "tuoi" "tue"
    PNoGen
    Sg
    P2
    Clit1 ;

  pronIl = mkPronoun
    "lui"
    "lo"
    "gli"
    "lui"
    "suo" "sua" "suoi" "sue"
    (PGen Masc)
    Sg
    P3
    Clit2 ;

  pronElle = mkPronoun
    "lei"
    "la"
    "le"
    "lei"
    "suo" "sua" "suoi" "sue"
    (PGen Fem)
    Sg
    P3
    Clit2 ;

  pronNous = mkPronoun
    "noi"
    "ci"
    "ci"
    "noi"
    "nostro" "nostra" "nostri" "nostre"
    PNoGen
    Pl
    P1
    Clit3 ;

  pronVous = mkPronoun
    "voi"
    "vi"
    "vi"
    "voi"
    "vostro" "vostra" "vostri" "vostre"
    PNoGen
    Pl   --- depends!
    P2
    Clit3 ;

  pronIls = mkPronoun
    "loro"
    "loro"
    "li"   --- le !
    "loro"
    "loro" "loro" "loro" "loro"
    PNoGen
    Pl
    P3
    Clit1 ;

-- moved from ResIta

  commentAdv = ss "comme" ;
  quandAdv = ss "quando" ;
  ouAdv = ss "o" ;
  pourquoiAdv = ss "perch�" ;

  etConj = ss "e" ** {n = Pl} ;
  ouConj = ss "o" ** {n = Sg}  ;
  etetConj = sd2 "e" "e" ** {n = Pl}  ;
  ououConj = sd2 "o" "o" ** {n = Sg}  ;
  niniConj = sd2 "n�" "n�" ** {n = Sg}  ; --- requires ne !
  siSubj = ss "se" ;
  quandSubj = ss "quando" ;

  ouiPhr = ss ["S� ."] ;  
  nonPhr = ss ["No ."] ;

}

