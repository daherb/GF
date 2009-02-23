--# -path=.:../Romance:../common:../../prelude

resource MorphoRon = ResRon ** 
  open  Prelude, Predef in {

flags optimize=noexpand ;

---------------------------------------------------------------------------------
------------------------------ARTICLES-------------------------------------------
---------------------------------------------------------------------------------

--defined article (enclitic)
-- we need two forms, as the Singular AGenDat form for Feminine is obtained from the
-- Plural form, except for irregular nouns that need an additional form  

oper artDf : Str -> Str -> Gender -> Number -> ACase -> Str =
\bun, buni, g, n, a ->
case <g,n,a> of
{ <Masc,Sg,ANomAcc>  => case last bun of
                        { "u" => bun + "l";
                          "e" => bun + "le"; 
                          "�" => bun + "a";
                           _   => bun + "ul"
                        };
  <Masc,Sg,AGenDat>  => case last bun of
                        {("u"|"e" ) => bun + "lui" ;
                         _          => bun + "ului"
                         };              
  <Masc,Sg,AVoc>  => case bun of
					    { x+"u"           => bun + "le";
					      x + "itor"      => bun + "ule" ;
					      x + ("en"|"or") => bun + "e" ;
					      x+("e"|"�") => bun;
						  _           => bun + "ule"
					    };                                  
  <Masc,Pl,ANomAcc>  => buni + "i";
  <Masc,Pl, _>    => buni + "lor";
  <Fem,Sg,ANomAcc>   =>  case bun of
				        { x + ("a"|"i") => bun + "ua";
					      x + "ie"      => x + "ia";
						  x + "�"       => x + "a";
						  _             => bun + "a"			
						};
						 
 <Fem,Sg,AGenDat>   => case  bun of
                        { x + ("a"|"e")+"ie" => buni+"i";
                          x + "ie"  => bun + "i"; 
                          _   => buni + "i"
                         };
                            
 <Fem,Sg,AVoc>   => case bun of
					    { x + "�"       => x + "o";
					      x + "ie"      => x + "io";
					      _             => bun + "o"
					    };						  
 <Fem,Pl,ANomAcc>   => buni + "le";
 <Fem,Pl,_>   => buni + "lor"
                            };
 
--Undefined article (proclitical) -- 
--we keep the non-articled form of the noun and glue it with the article on syntactical level

oper artUndef : Gender -> Number -> NCase -> Str = \g,n,a ->
case <g,n,a> of
{<Masc,Sg,No> => "un"; <Masc,Sg,Ac> => "un" ; <Masc,Sg,Ge> => "unui"; <Masc,Sg,Da> => "unui" ;<_,_,Vo> => "" ;
 <_,Pl,No> => "ni�te"; <_,Pl,Ac> => "ni�te"; <_,Pl,Da> => "unor"; <_,Pl,Ge> => "unor" ; 
 <Fem,Sg,No> => "o"; <Fem,Sg,Ac> => "o"; <Fem,Sg,Da> => "unei"; <Fem,Sg,Ge> => "unei"
};

--possesive article 
-- used for Cardinals and for Genitive case		  				    	

oper artPos : Gender -> Number -> Str = \g,n ->
 case <g,n> of
{ <Masc,Sg> => "al";
  <Masc,Pl> => "ai";
  <Fem,Sg>  => "a";
  <Fem,Pl>  => "ale"
};

	     		  
--demonstrative article 
-- used as Determined article in order to emphasise on the noun/adjective, and for Dative/Genitive for of ordinals

oper artDem : Gender -> Number -> ACase -> Str = \g,n,c ->
 case <g,n,c> of
{<Masc,Sg,ANomAcc> => "cel"; <Masc,Pl,ANomAcc> => "cei"; <Masc,Sg,AGenDat> => "celui"; 
<Fem,Sg,ANomAcc>  => "cea"; <Fem,Pl,ANomAcc>  => "cele"; <Fem,Sg,AGenDat>  => "celei";
 <_,Pl,AGenDat>    => "celor";
 <Masc,Sg,AVoc> => "cel"; 
<Masc,Pl,AVoc> => "cei"; <Fem,Sg,AVoc> => "cea"; <Fem,Pl,AVoc> => "cele"
  
};

--flexion forms of a noun without article

oper artUnf : Str -> Str -> Gender -> Number -> ACase -> Str = \buna,bune,g,n,a ->
case <g,n,a> of
{<Masc,Sg,_> => buna ; <Masc,Pl,_> => bune ;
 <Fem,Sg,ANomAcc> => buna ; <Fem,Sg,AGenDat> => bune ; <Fem,Sg,AVoc> => buna;
 <Fem,Pl,_> => bune 
} ;

--undefined article form 

oper artUndefMasc : Str -> Number -> ACase -> Str = \s,n,a -> s;

oper artUndefFem : Str -> Str -> Number -> ACase -> Str = \buna, bune, n, a ->
case <n,a> of
{
<Sg,ANomAcc>  => buna;
<Sg,AGenDat>  => bune;
<Sg,AVoc>   => buna;  
<Pl,_>     => bune
}; 
          	


---------------------------------------------------------------------------------
------------------------------- NOUNS-------------------------------------------- 
---------------------------------------------------------------------------------

-- the irregular nouns (of feminine gender) need 3 forms in order to build the
-- morfological table : (Singular ANomAcc Indef, Plural ANomAcc Indef and 
-- Singular AGenDat Indef)


oper mkNomVIrreg : Str -> Str -> Str -> Noun = \iarba, ierburi, ierbi ->
let noun = mkNomIrreg iarba ierburi NFem
 in
  {s = \\n,a,c => case n of
                    {Sg => case c of 
                            {AGenDat => case a of {Indef => ierbi;
                                                   Def   => artDf iarba ierbi Fem Sg AGenDat
                                                   };
                              _ => noun.s ! Sg ! a ! c                  
                            };
                     Pl => noun.s ! Pl ! a ! c     
                     };
 g = NFem ;
 a = Animate 
   }; 
 
-- usual nouns need two forms (Singular + Plural ANomAcc Indef)
-- because the Neuter behaves like Masculine for Singular and Feminine for Plural,
-- we pass 2 parameters - gender for Singular and for Plural, so that we can define 
-- the forms for Neuter as a combination of Feminine and Masculine

 
oper mkNomIrreg : Str -> Str -> NGender -> Noun = \obiect, obiecte , gen ->
 case gen of
  { NMasc =>  {s = mkNom obiect obiecte Masc Masc ; g = gen ; a = Animate };
    NFem  =>  {s = mkNom obiect obiecte Fem Fem ; g = gen ; a = Animate };
    NNeut =>  {s = mkNom obiect obiecte Masc Fem ; g = gen ; a = Animate } 
  };
 
--creates the table for a noun : 
 
oper mkNom : Str -> Str -> Gender -> Gender -> Number => Species => ACase => Str = \obiect, obiecte, gs, gp ->
     table  { Sg => table {Def => \\p => artDf obiect obiecte gs Sg p;    
                           Indef => \\p => artUnf obiect obiecte gs Sg p
                           };
              Pl => table { Def   => \\p => artDf obiect obiecte gp Pl p ;
                            Indef => \\p => artUnf obiect obiecte gp Pl p              
                           }             
            } ;


-- for regular nouns, we need just the Singular ANomAcc Indef form :
-- for obtaining the plural form, we apply almost the same rules as for adjectives
-- for Neuter we treat the Singular ANomAcc Indef for as the Masculine Singular form of an Adjective
-- and we obtains it's plural form as the Feminine Plural form of the adjective 
-- (with potential o -> oa mutations, that occur in most of the cases)
      
mkNomReg : Str -> NGender -> Noun = \obiect, g ->
case g of 
       {NMasc => mkNomIrreg obiect ((mkAdjReg obiect).s ! (AF Masc Pl Indef ANomAcc)) NMasc ;
        NFem  => case (Predef.dp 4 obiect) of 
                   { "ai"+x+"�"  => mkNomIrreg obiect (init obiect + "e") NFem ; --always
                      _ => case (Predef.dp 3 obiect) of
                      {"i"+("c"|"n"|"m"|"p")+"�" => mkNomIrreg obiect (init obiect + "i") NFem ; -- 60% cases frequently used words, not frequent for neological words
                         _                       => mkNomIrreg obiect (mkFemPl obiect) NFem 
                      }
                   };
        NNeut => if_then_else Noun (pbool2bool (Predef.occur "o" (Predef.dp 3 obiect) ))  
                           (mkNomIrreg obiect ((mkAdjRegO obiect).s ! (AF Fem Pl Indef ANomAcc)) NNeut) 
                                       (mkNomIrreg obiect ((mkAdjReg obiect).s ! (AF Fem Pl Indef ANomAcc)) NNeut)                                      
       };

--for nouns that have a different vocative form than the one inferred

mkVocc : Noun -> Str -> Noun  = \n -> \vo ->
 {s = table{ Sg => \\p, c => case c of
                                     { AVoc => vo ;
                                       _    => n.s ! Sg ! p ! c
                                      };
             Pl => \\p,c => n.s ! Pl ! p ! c                     
           };
  g = n.g ;
  a = n.a

  };                                 
 
 -- composes a noun with an invariable string ( Ex camera foto)
 -- with/without dash
 
 ccompose : Noun -> Str -> Noun = \noun, y ->
 { s = \\n,p,c => noun.s ! n ! p ! c +"-"+ y ;
   g = noun.g ;
   a = noun.a
 };
 
 
 composeN : Noun -> Str -> Noun = \noun, y ->
 { s = \\n,p,c => noun.s ! n ! p ! c ++ y ;
   g = noun.g ;
   a = noun.a
 };
 
 -- changes the Animacy attribute 
 
 mkInanimate : Noun -> Noun = \n ->
 {s = table { Sg => \\p,c => case c of 
                       {AVoc => n.s ! Sg ! Indef ! ANomAcc ;
                        _    => n.s ! Sg ! p ! c
                       };
              Pl => \\p, c => n.s ! Pl ! p ! c         
            };
  g = n.g ;
  a = Inanimate          
  };
 
 mkAnimate : Noun -> Noun = \n ->
  let ob = n.s ! Sg ! Indef ! ANomAcc ;
     obs = n.s ! Pl ! Indef ! ANomAcc 
     in
 {s = table { Sg => \\p,c => case <p,c> of 
                       {<Indef,AVoc> => n.s ! Sg ! Indef ! ANomAcc ;
                        <Def,AVoc>   => case (n.g) of 
                                          {NFem  => artDf ob obs Fem Sg AVoc ;
                                           _     => artDf ob obs Masc Sg AVoc 
                                          } ;
                        _            => n.s ! Sg ! p ! c
                       };
              Pl => \\p, c => n.s ! Pl ! p ! c         
            };
  g = n.g ;
  a = Animate      
};
 
--a special case of neuter nouns -- the ones that just add -ri/-uri to the Singular Form
 
mkNomNeut : Str -> Noun = \obiect ->
case last obiect of
{"u" => mkNomIrreg obiect (obiect + "ri") NNeut;
  _  => mkNomIrreg obiect (obiect + "uri") NNeut
};


---------------------------------------------------------------------------------
-----------------------------ADJECTIVES------------------------------------------
---------------------------------------------------------------------------------



-- in the worst case, the adjective needs 5 forms for Singular/Plural - Masculine/Feminine +  Adverb		  				    	


oper mkAdjSSpec : Str -> Str -> Str -> Str -> Str -> Adj
= \bun -> \buna -> \buni -> \bune -> \bine ->
{ s = table {AF Masc Sg Def c   => artDf bun buni Masc Sg c ;
              AF Fem Sg Def c    => artDf buna bune Fem Sg c ;
              AF Masc Pl Def c   => artDf bun buni Masc Pl c; 
              AF Fem Pl Def c    => artDf buna bune Fem Pl c ;
              AF Masc Pl Indef c => artUndefMasc buni Pl c;
              AF Fem Pl Indef c  => artUndefFem buna bune Pl c;
              AF Masc Sg Indef c => artUndefMasc bun Sg c;
              AF Fem Sg Indef c  => artUndefFem buna bune Sg c;
              AA                  => bine
             }

};

-- usually the determined adverb is identical to the Singular Masculine form of the adjective

oper mkAdjSpec : Str -> Str -> Str -> Str -> Adj 
= \bun -> \buna -> \buni -> \bune ->
                mkAdjSSpec bun buna buni bune bun ;


-- special classes of adjectives :

oper adjAuriu : Str -> Adj = \s ->
  let f  = init s + "e";
      pl = init s + "i" 
       in
   mkAdjSpec s f pl pl ;
  
oper adjMuncitor : Str -> Adj = \s ->
 let f   = Predef.tk 2 s + "oare";
     pl  = s + "i";
     adv = s + "e�te"
     in
 mkAdjSSpec s f pl f adv ;
 
 oper adjRomanesc : Str -> Adj = \s ->
  let f   = Predef.tk 2 s + "asc�";
      pl  = Predef.tk 2 s + "�ti";
      adv = Predef.tk 2 s + "�te"
      in
 mkAdjSSpec s f pl pl adv ;
 
oper adjMare : Str -> Adj = \s ->
  let pl = mkStemPlReg s
   in
   mkAdjSpec s s pl pl;                    
  
oper adjDimin : Str -> Adj = \s ->
  let f  = Predef.tk 2 s + "ic�";
     pl  = init s + "i";  
     plf = s + "e" 
     in
     mkAdjSpec s f pl plf;
 
 
 -- the phonetical mutations that occur in Romanian (Singular Masculine -> Singular Feminine) are 
 -- o -> oa  (Ex : frumos -> frumoas�)
 -- e -> ea / ie -> ia (Ex : des -> deas�)
 -- on the last occurence of o/e in the word (usually 2rd or 3rd last letter)
     
  mkStemMutE : Str -> Str = \s ->
   let  s1 = if_then_Str (pbool2bool (Predef.occur "ie" (Predef.dp 4 s))) ((Predef.tk 3 s) +"a"+(Predef.dp 2 s)) ((Predef.tk 3 s) +"ea" + (Predef.dp 2 s));
        s2 = if_then_Str (pbool2bool (Predef.occur "ie" (Predef.dp 3 s))) ((Predef.tk 2 s) +"a" + (last s)) ((Predef.tk 2 s) +"ea" + (last s))
         in
  case Predef.dp 3 s of
		  {"e"+x => s1;
			_    => s2
		  };
		  
  mkStemMutO : Str -> Str = \s ->
  case Predef.dp 3 s of
  {"o"+x => (Predef.tk 3 s) +"oa" + x;
    _    => (Predef.tk 2 s) + "oa" + (last s)
  };

  -- another phonetical mutation is � -> e (Ex : proasp�t� -> proaspete) 
  -- Singular Feminine -> Plural Feminine
  -- on the last occurence of � -- 2nd last letter of the root 
  
  mkStemMutA : Str -> Str = \s ->
   case (Predef.dp 2 s) of
   { "�" + x => (Predef.tk 2 s) + "e" + (last s);
      _      => s
   };
   
  
-- obtaining the Masculine Plural form from the Masculine Singular
-- contains most usual mutations  

oper mkStemPlReg : Str -> Str = \s -> 
case s of
{x + ("st"|"sc"|"�c")=> x + "�ti"; -- always -- usually the nouns/adj can end in an "u", but we eliminate that first
 x + "str"           => x + "�tri"; 
 x + "s"             => x + "�i"; 
 x + "x"             => x + "c�i"; 
 x + "xt"            => x + "c�ti"; 
 x + "ian"           => x + "ieni"; 
 x + "ean"           => x + "eni"; 
 x + "ead"           => x + "ezi"; 
 x + ("de"|"d")      => x + "zi";  
 x + ("te"|"t�"|"t") => x + "�i";
 x + ("e"|"i"|"a"|"�")=> x + "i";
 _                   => s + "i"
}; --all the mutations occur always for adjectives, appart from the exception that mutate other syllables from the word


-- special cases that imply other mutations that don't occur for all words
-- because these rules don't apply for neological words, which are more frequent, they are treated
-- separately

oper mkStemPlSpec : Str -> Str = \s ->
case s of 
{x + "l"    => x + "i";
 x + "z"    => x + "j";
 _          => s
};


--obtaining the Feminine Singular form from the Masculine Singular one for Adjectives :

mkFemSg : Str -> Str = \s ->
case s of
{x + "hi" => x + "he";
 x + "i"  => s + "e";
 x + "iu" => x + "ie";
 x + "u"  => x + "�";
 _        => s + "�"
};

-- obtaining the Feminine Plural from Feminine Singular for Nouns :

mkFemPl : Str -> Str = \s ->
case s of
{ x + "are"           => x + "�ri"; --always
  x + ("ui"|"ai")     => s + "e"; -- from Masc (adjectives)
  x + "ur�"           => x + "uri"; -- always
  x + "oaie"          => x + "oi"; -- almost always
  x + "aie"           => x + "�i"; --always
  x + "eie"           => x + "ei"; --always
  x + "i"             => s + "le" ; --always - special cases of Feminines ending in "i" like zi = day
  x + "a"             => x + "le"; --always - special cases of Feminines ending in "a" -- most of Turkish origine like cafea = coffee
  x + "une"           => x + "uni"; --always - abstract collective nouns like "na�iune" = nation, French origine
  x + "ate"           => x + "��i"; --always same as above like "libertate" = freedom--  x + "��"            => x + "�i"; -- 70% of cases
  x + "re"            => x + "ri"; -- almost always, exception nouns ending in "oare" which are treated as special case in adjReg
  x + "e"             => x + "i"; -- almost always for Nouns, always for Adjectives
  _                   => case init s of
                        { 
                          x + ("g"|"h"|"nc")   => (init s) + "i"; -- always for Adjectives, almost always for Nouns (g - ending has exceptions)
                          
                          x + "�t"                 => x + "ete"; --always
                          x + "�nt"                => x + "inte"; --always
                          _                        => case s of
                                                  { x + "�" => x + "e" ; -- default -- exception occur
                                                    _       => s + "e" -- worst case
                                                  }

                        }
};


--obtainint Feminine Plural from Masculine Singular for Adjectives :

mkFemAdj : Str -> Str = \s ->
case s of 
{ x + ("g"|"h"|"nc") => s + "i";
  x + "�nt"              => x + "inte";
  x + "�t"               => x + "ete";
  _                      => s + "e"

};


---------------------------------------------------------------

-- invariable adjective - where all the forms are identical
 
mkAdjInvar : Str -> Adj  = \s ->
{s =  table {AF g n a c         => s ;
             AA                 => s
             }
 };

-- regular adjective - just the Masculine Singular Form is needed
 
mkAdjReg : Str -> Adj = \s ->
 let  r    = mkStemMutA s ; 
      rad  = if_then_Str (pbool2bool (Predef.occur "u" (last r))) (init r) r;
      radF = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s
 in
 case s of 
 {x + "tor" => adjMuncitor s;
  x + "esc" => adjRomanesc s;
  x + "e"   => adjMare s;
  x + "iu"  => adjAuriu s;
  x + "el"  => adjDimin s;
  _         => mkAdjSpec s (mkFemSg radF) (mkStemPlReg rad) (mkFemAdj rad)
 
 };
 
 -- regular adjective that has the e -> ea mutation from Masculine Singular to Feminine Singular
 
 mkAdjRegE : Str -> Adj = \s ->
 let rad = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s 
  in
    mkAdjSpec s (mkFemSg (mkStemMutE rad)) (mkStemPlReg rad) (mkFemAdj rad);

    
-- regular adjective that has the e -> ea mutation as above, and also the l -> _ / z -> j
-- mutations from Masculine Singular -> Masculine Plural   
    
 mkAdjSpecE : Str -> Adj = \s ->
 let rad = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s 
 in
    mkAdjSpec s (mkFemSg (mkStemMutE rad)) (mkStemPlSpec rad) (mkFemAdj rad);
    
-- regular adjective that has the o -> oa mutation from Masculine Singular to Feminine Singular    
    
 mkAdjRegO : Str -> Adj = \s ->
 let rad = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s 
 in
    mkAdjSpec s (mkFemSg (mkStemMutO rad)) (mkStemPlReg rad) (mkFemPl (mkStemMutO rad));      
 
 -- regular adjective that has the o -> oa mutation as above and also the l -> _ / z -> j
 -- mutations from Masculine Singular -> Masculine Plural
 
 mkAdjSpecO : Str -> Adj = \s ->
 let rad = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s 
 in
    mkAdjSpec s (mkFemSg (mkStemMutO rad)) (mkStemPlSpec rad) (mkFemPl (mkStemMutO rad));
 
 
 -- the two categories mkAdjRegE and mkAdjRegO have been merge into one category of adjectives
 -- that have mutations from Masculine Singular to Feminine Singular
 
 mkRegMut : Str -> Adj = \s ->
 let rad = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s 
     in
      if_then_else Adj (pbool2bool (Predef.occur "o" (Predef.dp 3 rad)))  
              (mkAdjSpec s (mkFemSg (mkStemMutO rad)) (mkStemPlReg rad) (mkFemPl (mkStemMutO rad)))
              (mkAdjSpec s (mkFemSg (mkStemMutE rad)) (mkStemPlReg rad) (mkFemAdj rad));
 
 -- the two categories mkAdjSpecE and mkAdjSpecO have been merge into one category of adjectives
 -- that have mutations from Masculine Singular to Feminine Singular
 -- and also from Masculine Singular to Masculine Plural
               
mkSpecMut : Str -> Adj = \s ->              
  let rad = if_then_Str (pbool2bool (Predef.occur "u" (last s))) (init s) s 
     in
      if_then_else Adj (pbool2bool (Predef.occur "o" (Predef.dp 3 rad)))  
              (mkAdjSpec s (mkFemSg (mkStemMutO rad)) (mkStemPlSpec rad) (mkFemPl (mkStemMutO rad)))
              (mkAdjSpec s (mkFemSg (mkStemMutE rad)) (mkStemPlSpec rad) (mkFemAdj rad));            
        





-----------------------------------------------------------------------------------
------------------------------VERBS------------------------------------------------
----------------------------------------------------------------------------------- 

--with rules based on the book "Conjugarea verbelor romanesti" by Ana-Maria Barbu--


-- for building the table for a verb, there are needed 29 forms
-- infinitive - 1 form 
-- tables for Present, Imperfect, Past Simple, Past Perfect - 24 forms
-- 3rd person Singular form for Conjunctive Present (= 3rd person Plural) - 1 form
-- Adjective that describes the Past Participe Form (regular adjective)- 1 form
-- Gerund - 1 form 
-- 2nd person Singular form for Imperative - 1 form

  Verbe : Type = VForm => Str ;
  
   verbAffixes :
     Str-> (a,b,c,d: Number => Person => Str) ->  Str -> Adj -> Str -> Str -> Verbe =
    \fi,pres, imperf, pSimple, pPerf, subj, adj, ger, imp  ->
    table {
      Inf                     => fi  ;
      Indi  Presn n p         => pres ! n ! p ;
      Indi  Imparf  n p       => imperf ! n ! p;
      Indi  PSimple n p       => pSimple ! n ! p ;
      Indi  PPerfect   n p    => pPerf ! n ! p ;
      Subjo SPres   n P3      => subj ;
      Subjo SPres   n p       => pres ! n ! p;
      Imper        SgP2       => imp ;
      Imper        PlP2       => pres ! Pl ! P2 ;
      Imper        PlP1       => pres ! Pl ! P1 ;
      Ger                     => ger ;
      PPasse g n a d          => adj. s ! (AF g  n  a  d) 
      } ;


-- syntactical verb : 
-- obtains all the verb forms present in Romanian, based on the primitive forms found in Verbe 

SVerbe : Type = VerbForm => Str ;

  mkVerb : Verbe -> SVerbe = \vb -> 
    table {   
      TInf                    => "a" ++ vb ! Inf  ;
      TIndi  TPresn n p       => vb ! (Indi Presn n p) ;
      TIndi  TImparf  n p     => vb ! (Indi Imparf n p);
      TIndi  TPComp n  p      => pComp ! n ! p ++ vb ! (PPasse Masc Sg Indef ANomAcc) ;
      TIndi  TPSimple n p     => vb ! (Indi PSimple n p) ;
      TIndi  TPPerfect n p    => vb ! (Indi PPerfect n p) ;
      TIndi  TFutur   n p     => pFut ! n ! p ++ vb ! Inf ;
      TSubjo TSPres   n p     => "s�" ++ vb ! (Subjo SPres n p) ;
      TSubjo TSPast   n p     => "s�" ++ "fi" ++ vb ! (PPasse Masc Sg Indef ANomAcc) ;
      TCondi n p              => pCond ! n ! p ++ vb ! Inf ;
      TImper        PlP1      => "s�" ++ vb ! (Imper PlP1) ;
      TImper        p         => vb ! (Imper p) ;
      TGer                    => vb ! Ger ;
      TPPasse g n a d         => vb ! (PPasse g n a d)
           }; 

-- auxiliary for Past Composite (to have - as auxiliary) :

pComp : Number => Person => Str = table {Sg => table {P1 => "am" ; P2 => "ai" ; P3 => "a"} ;
                                         Pl => table {P1 => "am" ; P2 => "a�i"; P3 => "au"}
                                         };
                                         
-- auxiliary for Future Simple :
                                         
pFut : Number => Person => Str = table  {Sg => table {P1 => "voi" ; P2 => "vei" ; P3 => "va"} ;
                                         Pl => table {P1 => "vom" ; P2 => "ve�i"; P3 => "vor"}
                                         };                                          

--auxiliary for Condional Present :

pCond : Number => Person => Str = table {Sg => table {P1 => "a�" ; P2 => "ai" ; P3 => "ar"} ;
                                         Pl => table {P1 => "am" ; P2 => "a�i"; P3 => "ar"}
                                         };
 
-- make Reflexive verbe :  ? with variants ?
-- syntactical category of reflexive verbs based on the primitive forms in Verbe                                   
                                         
mkVerbRefl : Verbe -> SVerbe = \vb ->
table {   
      TInf                    => "a" ++ "se" ++ vb ! Inf  ;
      TIndi  TPresn n p       => pronRefl ! n ! p ++ vb ! (Indi Presn n p) ;
      TIndi  TImparf  n p     => pronRefl !n ! p ++ vb ! (Indi Imparf n p);
      TIndi  TPComp n  p      => pronReflClit ! n ! p + "-" + pComp ! n ! p ++ vb ! (PPasse Masc Sg Indef ANomAcc) ;
      TIndi  TPSimple n p     => pronRefl ! n ! p ++ vb ! (Indi PSimple n p) ;
      TIndi  TPPerfect n p    => pronRefl ! n ! p ++ vb ! (Indi PPerfect n p) ;
      TIndi  TFutur   n p     => pronRefl ! n ! p ++ pFut ! n ! p ++ vb ! Inf ;
      TSubjo TSPres   n p     => "s�" ++ pronRefl ! n ! p ++ vb ! (Subjo SPres n p) ;
      TSubjo TSPast   n p     => "s�" ++ pronRefl ! n ! p ++ "fi" ++ vb ! (PPasse Masc Sg Indef ANomAcc) ;
      TCondi n p              => pronReflClit ! n ! p + "-" + pCond ! n ! p ++ vb ! Inf ;
      TImper        PlP1      => "s�" ++ pronRefl ! Pl ! P1 ++ vb ! (Imper PlP1) ;
      TImper        PlP2      => vb ! (Imper PlP2) + "-"+ pronRefl ! Pl ! P2  ;
      TImper        SgP2      => vb ! (Imper SgP2) + "-"+ pronRefl ! Sg ! P2  ;
      TGer                    => vb ! Ger + "u" + "-" + pronRefl ! Sg ! P3 ;
      TPPasse g n a d         => vb ! (PPasse g n a d)
           };                                 

-- reflexive pronouns - full form

pronRefl : Number => Person => Str = 
table {Sg => table {P1 => "m�" ; P2 => "te" ; P3 => "se"};
       Pl => table {P1 => "ne" ; P2 => "v�" ; P3 => "se" } 
};

-- reflexive pronouns - short form (clitics)

pronReflClit : Number => Person => Str =
table {Sg => table {P1 => "m" ; P2 => "te" ; P3 => "s"};
       Pl => table {P1 => "ne" ; P2 => "v" ; P3 => "s" } 
};


{-
  verbAffixes1 :
     Str-> (a,b,c,d: Number => Person => Str) -> (e,f,g,h : Str) -> Verbe =
    \fi,pres, imperf, pSimple, pPerf, subj, part, ger, imp ->
    table {
      Inf                     => fi  ;
      Indi  Presn n p         => pres ! n ! p ;
      Indi  Imparf  n p       => imperf ! n ! p;
      Indi  PComp   n  p      => "aa"  ++ part ;
      Indi  PSimple n p       => pSimple ! n ! p ;
      Indi  PPerf   n p       => pPerf ! n ! p ;
      Indi  Futur   n  p      => "va" ++ fi ;
      Condi         n  p      => "as" ++ fi ;
      Subjo SPres   n P3      => subj ;
      Subjo SPres   n p       => pres ! n ! p;
      Subjo SPast   n  p      => "sa" ++ "fi" ++ part ;
      Imper        SgP2       => imp ;
      Imper        PlP2       => pres ! Pl ! P2 ;
      Imper        PlP1       => "sa" ++ pres ! Pl ! P1 ;
      Part PPres              => ger ;
      Part (PPasse g n a d)   => (mkAdjReg part). s ! (AF g  n  a  d) 
      } ;
-}

-- This is a conversion to the type in $CommonRomance$.

oper
  vvf : (VerbForm => Str) -> (VF => Str) = \aller -> table { 
    VInfin _       => aller ! TInf ;
    VFin (VPres   Indic) n p => aller ! TIndi TPresn n p ; 
    VFin (VPres   Subjunct) n p => aller ! TSubjo TSPres n p ;
    VFin (VImperf Indic) n p => aller ! TIndi TImparf n p ;     --# notpresent
    VFin (VImperf Subjunct) n p => aller ! TSubjo TSPast n p ;  --# notpresent
    VFin VPasse n p  => aller ! TIndi TPComp n p ;  --# notpresent
    VFin VFut n p    => aller ! TIndi TFutur n p ;  --# notpresent
    VFin VCondit n p => aller ! TCondi n p ;  --# notpresent
    VImper np        => aller ! TImper np ;
    VPart g n a d    => aller ! TPPasse g n a d ;
    VGer             => aller ! TGer 
    } ;



-- vowells in Romanian - used for clitics

   vocale : Str = ("a"|"e"|"i"|"u"|"�"|"�"|"�");

-- phonetical mutations that occur when declining verbs :

-- last � in the word -> a

modALast : Str -> Str = \root ->
if_then_Str (pbool2bool (Predef.occur "�" (Predef.dp 2 root))) 
                   ((Predef.tk 2 root) + "a" + (last root)) ((Predef.tk 3 root) + "a" + (Predef.dp 2 root)); 
           
-- last u in the word -> o
           
modU : Str -> Str = \root ->
if_then_Str (pbool2bool (Predef.occur "u" (Predef.dp 2 root))) 
                   ((Predef.tk 2 root) + "o" + (last root)) ((Predef.tk 3 root) + "o" + (Predef.dp 2 root)); 
                      
-- first � in the word -> a           
           
modAFirst : Str -> Str = \root ->
if_then_Str (pbool2bool (Predef.occur "�" (Predef.take 2 root))) 
                   ((Predef.take 1 root) + "a" + (Predef.drop 2 root)) ((Predef.take 2 root) + "a" + (Predef.drop 3 root)); 
           
-- � -> a (general)           

modA : Str -> Str = \root ->
  if_then_Str (pbool2bool (Predef.occur "�" (Predef.dp 3 root))) (modALast root) (modAFirst root) ;


-- e -> ea mutation (general)

mkMutE : Str -> Str = \root ->
  if_then_Str (pbool2bool (Predef.occur "e" (Predef.dp 3 root))) (mkStemMutE root) 
                     (mkStemMutE (Predef.take 4 root) + (Predef.drop 4 root)) ;

-- o -> oa mutation (general)

mkMutO : Str -> Str = \root ->
    if_then_Str (pbool2bool (Predef.occur "o" (Predef.dp 3 root))) (mkStemMutO root) 
                     (mkStemMutO (Predef.take 4 root) + (Predef.drop 4 root)) ;
             
-- general mutation - last occurence of a letter in the word is replaced by other string
-- the letter should occurd 2nd or 3rd last in the word

--for replacing 1 character with a string             
genMut : Str -> Str -> Str -> Str = \root, e, a ->
   if_then_Str (pbool2bool (Predef.occur e (Predef.dp 2 root))) 
                   ((Predef.tk 2 root) + a + (last root)) ((Predef.tk 3 root) + a + (Predef.dp 2 root)); 
                           
-- for replacing 2 characters with a string

genMut2 : Str -> Str -> Str -> Str = \root,e , a ->
   if_then_Str (pbool2bool (Predef.occur e (Predef.dp 3 root))) 
                   ((Predef.tk 3 root) + a + (last root)) ((Predef.tk 4 root) + a + (Predef.dp 2 root)); 
                           

-- oa -> o mutation (last occurence in the word)

mkStemMutOa : Str -> Str = \s ->
  case Predef.dp 4 s of
  {"oa" + x => (Predef.tk 4 s) + "o" + x;
   _        => (Predef.tk 3 s) + "o" + (last s)  
  };                            
          

-- Affixes :
-- It is convenient to have sets of affixes as data objects.

  Affixe : Type = Person => Str ;

  afixe : (_,_,_ : Str) -> Affixe = \x,y,z -> table {
      P1 => x ;
      P2 => y ;
      P3 => z
      } ;
     
-- Empty table (for verbs that lack certain tenses and moods )

empty : Number => Person => Str = \\n,p => nonExist ;      
     
specTab : Str -> Str -> Number => Person => Str = \ploua, plouau ->
\\n,p => case <n,p> of     
         {<Sg,P3> => ploua ;
          <Pl,P3> => plouau ;
          _  => nonExist 
          };
                                                            
-- VERB GROUPS :     
      
      
---------------------------------------------------
-----------Group 1 - ending in -a, with exceptions
---------------------------------------------------
   
-- Much of variation can be described in terms of affix sets:
---------------------------------
--for Present :
---------------------------------
--for subGroups 1,13

  affixSgGr1Ez  : Affixe = afixe "ez" "ezi" "eaz�" ;
  affixPlGr1Ez  : Affixe = afixe "�m" "a�i" "eaz�" ;
------
--for subGroups 2-3
  affixSgGr1EzI : Affixe = afixe "ez" "ezi" "az�" ;
  affixPlGr1EzI : Affixe = afixe "em" "a�i" "az�" ;
------
--for subGroup 4
  affixSgGr1I  : Affixe = afixe "i" "i" "e" ;
  affixPlGr1I  : Affixe = afixe "em" "a�i" "e";
------
--for subGroup 5
  affixSgGr1VI  : Affixe = afixe "" "" "e" ;
  affixPlGr1VI  : Affixe = affixPlGr1I ; 
------
--for subGroups 6-7
  affixSgGr1    : Affixe = afixe "" "i" "�" ; 
  affixPlGr1    : Affixe = afixe "�m" "a�i" "�" ;   
------
--for subGroup 8
  affixSgGr1U   : Affixe = afixe "u" "i" "�" ;
  affixPlGr1U   : Affixe = affixPlGr1 ;
------
--for subGroup 9,11,12
  affixSgGr1AU   : Affixe = afixe "au" "ai" "�" ;
  affixPlGr1AU   : Affixe =  afixe "�m" "a�i" "au" ;
-------
--for subGroup 10
  affixSgGr1EU   : Affixe = afixe "au" "ei" "a" ;
  affixPlGr1EU   : Affixe =  afixe "�m" "a�i" "au" ;
-------
 --for subGroup 14 
  affixSgGr1CI  : Affixe = afixe "i" "i" "e" ;
  affixPlGr1CI  : Affixe = afixe "em" "ea�i" "e";
-----  


-------------------------  
--for Imperfect :
-------------------------
--for subGroups 1-10
 affixSgI : Affixe = afixe "am" "ai" "a" ;
 affixPlI : Affixe = afixe "am" "a�i" "au" ;
 
--for subGroups 11-14 
 affixSgII : Affixe = afixe "eam" "eai" "ea" ;
 affixPlII : Affixe = afixe "eam" "ea�i" "eau" ;

---------------------------
 --for Perfect Simple :
 ---------------------------
 --for subGroups 1, 6-10
 
 affixSgPS1 : Affixe = afixe "ai" "a�i" "�" ;
 affixPlPS1 : Affixe = afixe "ar�m" "ar��i" "ar�" ;
 
 --for subGroups 2-5
 
 affixSgPS2 : Affixe = afixe "ai" "a�i" "e" ;
 affixPlPS2 : Affixe = afixe "ar�m" "ar��i" "ar�" ;
 
 --for subGroups 11-12
 
 affixSgPS3 : Affixe = afixe "ui" "u�i" "u" ;
 affixPlPS3 : Affixe = afixe "ur�m" "ur��i" "ur�" ;
 
 --for subGroups 13-14
 
 affixSgPS4 : Affixe = afixe "eai" "ea�i" "e" ;
 affixPlPS4 : Affixe = afixe "ear�m" "ear��i" "ear�" ;
 
--------------------------  
-- for Past Perfect :
---------------------------

--for subGroups 1-10

affixSgPP : Affixe = afixe "asem" "ase�i" "ase" ;
affixPlPP : Affixe = afixe "aser�m" "aser��i" "aser�" ;

--for subGroups 11-12

affixSgPP2 : Affixe = afixe "usem" "use�i" "use" ;
affixPlPP2 : Affixe = afixe "user�m" "user��i" "user�" ;

--for subGroups 13-14

affixSgPP3 : Affixe = afixe "easem" "ease�i" "ease" ;
affixPlPP3 : Affixe = afixe "easer�m" "easer��i" "easer�" ;


-- functions that build a tense table for a verb :

 
-- worst case : we need 5 forms and an affixe -
-- root, 1st Sg, 2nd Sg, 3rd Sg, 3rd Pl and affixe
                     
mkTab : (a,b,c,d,e : Str) -> Affixe -> Number => Person => Str =
\lua -> \iau -> \iei -> \ia -> \iaP -> \aff ->
table {Sg => table {P1 => iau; P2 => iei; P3 => ia};
       Pl => table {P3 => iaP; p => lua + aff ! p} 
       };


-- regular case : we need just the root and affixes for Singular and Plural

mkFromAffix : Str -> Affixe -> Affixe -> Number => Person => Str = \ar,affSg,affPl ->
 table {Sg => table {p => ar + affSg ! p};
        Pl => table {p => ar + affPl ! p}
        };

-- case where we need 2 roots and two affixes 


mkFromAffixes1 : Str -> Str -> Affixe -> Affixe -> Number => Person => Str =
\ar,arr,affSg, affPl ->
table {Sg => table {p => ar + affSg ! p };
       Pl => table {P3 => ar + affSg ! P3 ;
                    p  => arr + affPl ! p 
                    } 
       };
 
       
mkFromAffixes2 : Str -> Str -> Affixe -> Affixe -> Number => Person => Str =
\ar,arr,affSg, affPl ->
table {Sg => table {p => ar + affSg ! p};
       Pl => table {P3 => ar + affPl ! P3;
                    p => arr + affPl ! p
                    }
      };      

-- cases where the 3rd Person Singular is formed with a different root :

mkAffixSpec1 : Str -> Str -> Affixe -> Affixe -> Number => Person => Str = 
\ar, arr, affSg, affPl ->
table {Sg => table {P3 => arr + affSg ! P3 ;
                    p  => ar + affSg ! p
                    };
       Pl => table {P3 => arr + affSg ! P3 ;
                    p  => ar + affPl ! p 
                    } 
      };
      
mkAffixSpec2 : Str -> Str -> Affixe -> Affixe -> Number => Person => Str = 
\ar, arr, affSg, affPl ->
table {Sg => table {P3 => arr + affSg ! P3 ;
                    p  => ar + affSg ! p
                    };
       Pl => table {P3 => ar + affSg ! P1 ;
                    p  => ar + affPl ! p 
                    } 
      };      
     
     
-- case where the 2nd person Singular has a different form, than the usual one :      
      
changeP2 : Str -> (Number => Person => Str) -> Number => Person => Str =
\ari -> \pres ->
table {Sg => table {P2 => ari;
                    p => pres ! Sg ! p};
       Pl => \\p => pres ! Pl ! p             
      };       
     
-- case where the 1st person Singular has a different form than the usual one :      
      
changeP1 : Str -> (Number => Person => Str) -> Number => Person => Str =
\ari -> \pres ->
table {Sg => table {P1 => ari;
                    p => pres ! Sg ! p};
       Pl => \\p => pres ! Pl ! p             
      };       
             
             
--subGroup 1
mkV6: Str -> Verbe = \lucra ->
   let  root = init lucra in
verbAffixes lucra (mkFromAffix root affixSgGr1Ez affixPlGr1Ez) 
               (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
                  (mkFromAffix root affixSgPP affixPlPP) (root + "eze") (mkAdjReg(root + "at")) 
                        (root + "�nd") (root + "eaz�") ;


mkV7 : Str -> Verbe = \crea ->
     mkV6 crea ;
     
mkV8 : Str -> Verbe = \parca ->
    let   r = init parca ;
          root = r + "h"
              in
verbAffixes parca (mkFromAffixes1 r root  affixSgGr1Ez affixPlGr1Ez)
          (mkFromAffix r affixSgI affixPlI) (mkFromAffix r affixSgPS1 affixPlPS1)
             (mkFromAffix r affixSgPP affixPlPP) (root + "eze") (mkAdjReg (r + "at"))
                    (r + "�nd") (root + "eaz�") ;
                    
mkV9 : Str -> Verbe = \divaga ->
          mkV8 divaga ;                    


--subGroup 2

mkV10 : Str -> Verbe = \studia ->
    let root = init studia in
 verbAffixes studia (mkFromAffix root affixSgGr1EzI affixPlGr1EzI) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (root + "eze") (mkAdjReg (root + "at"))
                    (root + "ind") (root + "az�") ;

--subGroup 3 

mkV11 : Str -> Verbe = \ardeia ->
    let root = init ardeia in
    verbAffixes ardeia (mkFromAffix root affixSgGr1EzI affixPlGr1EzI) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (root + "eze") (mkAdjReg (root + "at"))
                    (root + "nd") (root + "az�") ;

--subGroup 4

mkV12 : Str -> Verbe = \speria ->
   let root = init speria in
   verbAffixes speria (mkFromAffix root affixSgGr1I affixPlGr1I) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (root + "e") (mkAdjReg (root + "at"))
                    (root + "ind") (root + "e") ;
                    
--subGroup 5

mkV13 : Str -> Verbe = \incuia -> 
         let root = init incuia in
   verbAffixes incuia (mkFromAffix root affixSgGr1VI affixPlGr1VI) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (root + "e") (mkAdjReg (root + "at"))
                    (root + "nd") (root + "e") ;
                             
mkV14 : Str -> Verbe = \taia ->
        let root = init taia ;
            r = modA root
               in
verbAffixes taia (mkFromAffixes1 r root affixSgGr1VI affixPlGr1VI) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (r + "e") (mkAdjReg (root + "at"))
                    (root + "nd") (r + "e") ;
                               
mkV15 : Str -> Verbe = \infoia ->
    let root = init infoia ;
        r = mkStemMutO root 
        in
 verbAffixes infoia (mkAffixSpec1 root r affixSgGr1VI affixPlGr1VI) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (r + "e") (mkAdjReg (root + "at"))
                    (root + "nd") (r + "e") ;       
                               
mkV16 : Str -> Verbe = \muia ->
     let root = init muia ;
         r1   = modU root ;
         r2   = mkStemMutO r1
         in
 verbAffixes muia (mkTab root r1 r1 (r2 + "e") (r2+"e") affixPlGr1VI) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS2 affixPlPS2)
             (mkFromAffix root affixSgPP affixPlPP) (r2 + "e") (mkAdjReg (root + "at"))
                    (root + "nd") (r2 + "e") ;       
                        
--subGroup 6 

mkV17 : Str -> Verbe = \acuza ->
   let root = init acuza
    in
  verbAffixes acuza (mkFromAffix root affixSgGr1 affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") (root + "�") ;       
                    
mkV18 : Str -> Verbe = \ajuta ->
   let root = init ajuta ;
       newF = mkStemPlReg root;                    
       pres = changeP2 newF (mkFromAffix root affixSgGr1 affixPlGr1)
in
verbAffixes ajuta pres 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") (root + "�") ;  


mkV19 : Str -> Verbe = \acorda ->
  mkV18 acorda ;
   
mkV20 : Str -> Verbe = \asista ->
  mkV18 asista ;
  
  
  
mkV21 : Str -> Verbe = \risca ->
      let root = init risca ;
       newF = mkStemPlReg root ;                    
       newP = init newF + "e" ;
       pres = changeP2 newF (mkFromAffix root affixSgGr1 affixPlGr1)
in
verbAffixes risca pres 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) newP (mkAdjReg (root + "at"))
                    (root + "�nd") (root + "�") ;  

 
 mkV22 : Str -> Verbe = \misca ->
   mkV21 misca ;
   
 mkV23 : Str -> Verbe = \calca ->
   let root = init calca ;
       r    = modA root 
       in  
   verbAffixes calca (mkFromAffixes1 r root affixSgGr1 affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r + "�") ;  

mkV24 : Str -> Verbe = \cauta ->
    let root = init cauta ;
        r    = modA root ;
        newF = mkStemPlReg r ;                    
        pres = changeP2 newF (mkFromAffixes1 r root  affixSgGr1 affixPlGr1)
     in
   verbAffixes cauta pres 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r + "�") ;  

mkV25 : Str -> Verbe = \lauda ->
   mkV24 lauda ;

mkV26 : Str -> Verbe = \lasa ->
   mkV24 lasa ;
   
mkV27 : Str -> Verbe = \adasta ->
  mkV24 adasta ;
  
mkV28 : Str -> Verbe = \casca ->
   let root = init casca ;
       r    = modA root ; 
       newF = mkStemPlReg r ;                  
       newP = init newF + "e"
       in
  verbAffixes casca (changeP2 newF (mkFromAffixes1 r root  affixSgGr1 affixPlGr1)) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) newP (mkAdjReg (root + "at"))
                    (root + "�nd") (r + "�") ;  
                    
 mkV29 : Str -> Verbe = \chema ->
  let root = init chema ;
      r    = mkMutE root
      in
    verbAffixes chema (mkAffixSpec1 root r affixSgGr1 affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root+"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r + "�") ; 
                    
  mkV30 : Str -> Verbe = \certa ->
   let root = init certa ;
       newF = mkStemPlReg root ;
       newP = mkMutE root + "�"
       in
     verbAffixes certa (mkTab root root newF newP newP affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root+"e") (mkAdjReg (root + "at"))
                    (root + "�nd") newP ;
                    
 mkV31 : Str -> Verbe = \toca ->
  let root = init toca ;
      r    = mkStemMutO root
      in
    verbAffixes toca (mkAffixSpec1 root r affixSgGr1 affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root+"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r + "�") ; 
                                              
  mkV32 : Str -> Verbe = \inota -> 
   let root = init inota ;
       newF = mkStemPlReg root ;
       newP = mkStemMutO root + "�"
       in
     verbAffixes inota (mkTab root root newF newP newP affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root+"e") (mkAdjReg (root + "at"))
                    (root + "�nd") newP ;
                             
  mkV33 : Str -> Verbe = \innoda ->
     mkV32 innoda ;
     
  mkV34 : Str -> Verbe = \improsca ->
    let root = init improsca ;
        newF = mkStemPlReg root ;                  
        newS = mkStemMutO (init newF) + "e" ;
        newP = mkStemMutO root + "�"
       in
  verbAffixes improsca (mkTab root root newF newP newP affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) newS (mkAdjReg (root + "at"))
                    (root + "�nd") newP ;  
        
 mkV35 : Str -> Verbe = \apara ->
    let root = init apara ;
        newP = mkStemMutA root ;
        pres = changeP2 (newP + "i") (mkFromAffix root affixSgGr1 affixPlGr1)
          in
  verbAffixes apara pres 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (newP + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") (root + "�") ;  
                
  mkV36 : Str -> Verbe = \semana -> 
     let root = init semana ;          
         newP = mkStemMutA root ;
         newF = mkMutE root + "�" 
         in                           
  verbAffixes semana (mkTab root root (newP+"i") newF newF affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (newP + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") newF ;  
                         
   mkV37 : Str -> Verbe = \fremata ->
       let root = init fremata ;
           r    = mkMutE root ;
           newC = (mkStemMutA root) + "e" ;
           newP = mkStemPlReg r ;
           newF = r + "�" 
           in                      
  verbAffixes fremata (mkTab root r newP newF newF affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) newC (mkAdjReg (root + "at"))
                    (root + "�nd") newF ;
                    
  mkV38 : Str -> Verbe = \lepada -> 
    mkV37 lepada ;
    
  mkV39 : Str -> Verbe = \scapara ->
     let root = init scapara ;
         r    = modAFirst root ;
         newP = mkStemMutA r ;
         newF = r + "�"
         in
    verbAffixes scapara (mkTab root r (newP + "i") newF newF affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (newP + "e") (mkAdjReg (root + "at"))
                    (root + "�nd") newF ;     
         
  mkV40 : Str -> Verbe = \capata ->
  let root = init capata ;
         r    = modAFirst root ;
         newC = mkStemMutA r + "e" ;
         newP = mkStemPlReg(mkStemMutA r)  ;
         newF = r + "�"
         in
    verbAffixes capata (mkTab root r newP newF newF affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) newC (mkAdjReg (root + "at"))
                    (root + "�nd") newF ;            
         
  mkV41 : Str -> Verbe = \aseza ->
     let root = init aseza ;
         r    = genMut root "e" "a"  
           in                                           
  verbAffixes aseza (mkAffixSpec1 root r  affixSgGr1 affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root+"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"�") ;
        
 mkV42 : Str -> Verbe = \ierta ->
    mkV30 ierta ;
    
 mkV43 : Str -> Verbe = \dezmierda ->
    mkV30 dezmierda ;
    
 mkV44 : Str -> Verbe = \pieptana ->
    mkV36 pieptana ;
    
 mkV45 : Str -> Verbe = \invata ->
   let root = init invata ;
       newP = mkStemMutA root ;
       r   = genMut root "�" "a"       
         in
   verbAffixes invata (mkTab root root (newP + "i") (r+"�") (r+"�") affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (newP +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"�") ;      
   
 mkV46 : Str -> Verbe = \imbata ->
   let root = init imbata ;
       newP = mkStemMutA root ;
       r   = genMut root "�" "a"       
         in
   verbAffixes imbata (mkTab root root (mkStemPlReg newP) (r+"�") (r+"�") affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (newP +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"�") ;      
                    
 mkV47 : Str -> Verbe = \varsa ->
      mkV46 varsa ;
      
 mkV48 : Str -> Verbe = \juca ->
    let root = init juca ;
         r1   = modU root ;
         r2   = mkStemMutO r1
         in                      
   verbAffixes juca (mkTab root r1 (mkStemPlReg r1)  (r2+"�") (r2+"�") affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r2 +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r2 +"�") ;      
                    
 mkV49 : Str -> Verbe = \purta ->
     mkV48 purta ;
     
 mkV50 : Str -> Verbe = \prezenta ->
    let root = init prezenta ;
        r1   = genMut root "e" "i" 
        in
  verbAffixes prezenta (mkTab root r1 (mkStemPlReg r1)  (r1+"�") (r1+"�") affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r1 +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r1 +"�") ; 
           
  mkV51 : Str -> Verbe = \usca ->
     let root = init usca ;
          r   = "usuc"
      in
    verbAffixes usca (mkTab root r (r + "i") (r+"�") (r+"�") affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"�") ;          
        
   mkV52 : Str -> Verbe = \manca ->
      let root = init manca ;     
          r    = "m�n�nc"   
        in
   verbAffixes manca (mkTab root r (r + "i") (r+"�") (r+"�") affixPlGr1) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"�") ; 
     
 --subGroup 7                   
  mkV53 : Str -> Verbe = \preceda ->
        let root = init preceda ;
            newP = mkStemPlReg root ;
            newC = mkMutE root
            in
   verbAffixes preceda (changeP2 newP (mkFromAffix root affixSgGr1 affixPlGr1)) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (newC +"�") (mkAdjReg (root + "at"))
                    (root + "�nd") (root +"�") ;          
                               
  mkV54 : Str -> Verbe = \ploua ->
          let root = init ploua
          in
    verbAffixes ploua (specTab (root + "�") (root + "�")) (specTab ploua (ploua+ "u")) 
      (specTab (root + "�") (root + "ar�")) (specTab (root + "ase") (root + "aser�")) 
       (root + "�") (mkAdjReg (root + "at")) (root + "�nd") (root + "�") ;     
                                           
 --subGroup8
   mkV55 : Str -> Verbe = \umbla ->
        let root = init umbla
        in
   verbAffixes umbla (mkFromAffix root affixSgGr1U affixPlGr1U) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (root +"�") ;          
                                      
   mkV56 : Str -> Verbe = \latra ->
         let root = init latra ;
             r    = genMut root "�" "a"
             in
   verbAffixes latra (mkFromAffixes1 r root  affixSgGr1U affixPlGr1U) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r +"e") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"�") ;          
     
  --subGroup 9 
                                  
  mkV57 : Str -> Verbe = \reda -> 
          let root = init reda
            in          
   verbAffixes reda (mkFromAffix root affixSgGr1AU affixPlGr1AU) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (root +"ea") (mkAdjReg (root + "at"))
                    (root + "�nd") (root +"�") ;          
  
  --subGroup 10
  mkV58 : Str -> Verbe = \lua ->
      let root = init lua ;
          r = Predef.tk 2 root + "i" 
          in
   verbAffixes lua (mkFromAffixes1 r root  affixSgGr1EU affixPlGr1EU) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS1 affixPlPS1)
             (mkFromAffix root affixSgPP affixPlPP) (r +"a") (mkAdjReg (root + "at"))
                    (root + "�nd") (r +"a") ;          
                                                                         
  --subGroup 11
  mkV59 : Str -> Verbe = \sta ->
       let root = init sta ;
           r    = Predef.tk 2 root + "st�t" 
           in
   verbAffixes sta (mkFromAffix root  affixSgGr1AU affixPlGr1AU) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (root +"ea") (mkAdjReg (root + "at"))
                    (root + "�nd") (root +"ai") ;          
                                             
 --subGroups 12
 mkV60 : Str -> Verbe = \da ->
      let root = init da ;
          r    = init root + "d�d"
          in
   verbAffixes da (mkFromAffix root  affixSgGr1AU affixPlGr1AU) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (root +"ea") (mkAdjReg (root + "at"))
                    (root + "�nd") (root +"ai") ;          
                                   
 --subGroups 13 
 mkV61 : Str -> Verbe = \veghea ->
    let root = Predef.tk 2 veghea 
    in
     verbAffixes veghea (mkFromAffix root  affixSgGr1Ez affixPlGr1Ez) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS4 affixPlPS4)
             (mkFromAffix root affixSgPP3 affixPlPP3) (root +"eze") (mkAdjReg (root + "eat"))
                    (root + "ind") (root +"eaz�") ;          
            
--subGroups 14                 
mkV62 : Str -> Verbe = \deochea ->
   let root = Predef.tk 2 deochea ;
       newP = mkMutO root                                     
     in
   verbAffixes deochea (mkAffixSpec1 root newP  affixSgGr1CI affixPlGr1CI) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS4 affixPlPS4)
             (mkFromAffix root affixSgPP3 affixPlPP3) (newP +"e") (mkAdjReg (root + "eat"))
                    (root + "ind") (newP + "e") ;          
     
-----------------------------------
---------GROUP 2 -- verbs ending in -ea (same syllable)
-----------------------------------
----------
--Present
----------

--subGroup 1-2
affixSgGr21  : Affixe = afixe "" "i" "e" ;
affixPlGr21  : Affixe = afixe "em" "e�i" "" ;

--subGroup 3
affixSgGr23  : Affixe = afixe "eau" "ei" "ea" ;
affixPlGr23  : Affixe = afixe "em" "e�i" "eau" ;

--subGroup 4 
affixSgGr24  : Affixe = afixe "eau" "ei" "ea" ; 
affixPlGr24  : Affixe = afixe "em" "e�i" "" ;

----------
--Imperf
----------

--subGroups 1-3
--affixSgII and affixPlII

--subGroup 4
affixSgI2 : Affixe = afixe "iam" "iai" "ia" ;
affixPlI2 : Affixe = afixe "iam" "ia�i" "iau" ;

---------------
--Past Simple
--------------
--affixSgPS3 and affixPlPS3

--------------
--Past Perfect
--------------
-- for subGroups 1-3
-- affixSgPP2 and affixPlPP2

--for subGroup 4 
affixSgPP4 : Affixe = afixe "usem" "use�i" "use" ;
affixPlPP4 : Affixe = afixe "useser�m" "useser��i" "useser�" ;


-----------------

-- subGroup 1

mkV64 : Str -> Verbe = \aparea ->
   let root = Predef.tk 2 aparea ;
       r    = genMut root "�" "a"
       in
   verbAffixes aparea (mkFromAffixes2 r root   affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (root + "ut"))
                    (root + "�nd") (r + "i") ;            

mkV65 : Str -> Verbe = \cadea ->
    let root = Predef.tk 2 cadea ;
        r    = genMut root "�" "a";
        rad  = init (mkStemPlReg root) 
      in
   verbAffixes cadea (changeP2 (mkStemPlReg r) (mkFromAffixes2 r root  affixSgGr21 affixPlGr21) )
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") (mkStemPlReg r) ;
                    
mkV66 : Str -> Verbe = \sedea ->
     let root = Predef.tk 2 sedea ;
         r    = genMut root "e" "a";                                
         rad  = init (mkStemPlReg root)
       in
   verbAffixes sedea (mkTab root root (mkStemPlReg root) (r + "e") root affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") (rad + "i") ;            
   
mkV67 : Str -> Verbe = \vedea ->
     let root = Predef.tk 2 vedea ;
         r    = genMut root "e" "�" ;
         newC = genMut root "e" "a" ;
         rad  = init (mkStemPlReg r)
        in
  verbAffixes vedea (mkTab root r (mkStemPlReg root) (root + "e") r affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (newC +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") (mkStemPlReg root) ;
                    
mkV68 : Str -> Verbe = \putea ->
      let root = Predef.tk 2 putea ;
          r    = modU root ;
          newP = mkMutO r 
       in
   verbAffixes putea (mkTab root r (mkStemPlReg r) (newP + "e") r affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP2 affixPlPP2) (newP +"�") (mkAdjReg (root + "ut"))
                    (root + "�nd") (mkStemPlReg r) ;

--subGroup 2
                    
 mkV69 : Str -> Verbe = \scadea ->
   let root = Predef.tk 2 scadea ;
       r    = genMut root "�" "a";
       rad  = init (mkStemPlReg root) 
      in
   verbAffixes scadea (changeP2 (mkStemPlReg r) (mkFromAffixes2 r root  affixSgGr21 affixPlGr21) )
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") (r + "e") ;
      
  mkV70 : Str -> Verbe = \prevedea ->
     let root = Predef.tk 2 prevedea ;
         r    = genMut root "e" "�" ;
         newC = genMut root "e" "a" ;
         rad  = init (mkStemPlReg r)
        in
  verbAffixes prevedea (mkTab root r (mkStemPlReg root) (root + "e") r affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (newC +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") (root + "e") ;
                    
  mkV71 : Str -> Verbe = \placea ->
     let root = Predef.tk 2 placea ;
         r    = genMut root "�" "a"
       in
   verbAffixes placea (mkFromAffixes2 r root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (root + "ut"))
                    (root + "�nd") (r + "e") ;       
                    
  mkV72 : Str -> Verbe = \durea ->
                  mkV68 durea ;

--subGroup 3 
                  
  mkV73 : Str -> Verbe = \bea ->
      let root = Predef.tk 2 bea ;
          r    = root + "�"                
     in              
    verbAffixes bea (mkFromAffix root affixSgGr23 affixPlGr23) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (root +"ea") (mkAdjReg (r + "ut"))
                    (root + "�nd") (root + "ea") ;

--subGroup 4
                    
   mkV74 : Str -> Verbe = \vrea ->
     let root = Predef.tk 2 vrea ;                                                                          
         r    = root + "o"
      in
       verbAffixes vrea (mkTab root (root+"eau") (root+"ei")(root +"ea") (init root + "or")  affixPlGr24) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP4 affixPlPP4) (root +"ea") (mkAdjReg (r + "ut"))
                    (root + "�nd") (root + "ei") ;
                    
  ----------------------------------------------------------------------
  -------Group 3 -- verbs ending in -e
  -------------------------------------------------------------------------
  -----------------------
  --Present
  -----------------------                  
--subGroups 1-6
--affixSgGr21 + affixPlGr21

--subGroup 7-8
affixSgGr31 : Affixe = afixe "u" "i" "e" ;
affixPlGr31 : Affixe = afixe "em" "e�i" "u" ;

----------------
--Imperfect
----------------
--subGroups 1-6  affixSgII affixPlII

--subGroups 7-8 affixSgI affixPlI

----------------
--Past Simple
----------------
--subGroups 1-4,8
affixSgPS5 : Affixe = afixe "sei" "se�i" "se" ;
affixPlPS5 : Affixe = afixe "ser�m" "ser��i" "ser�" ;

--subGroups 5-7 affixSgPS3 + affixPlPS3

---------------
--P Perfect 
---------------
--subGroups 1-4,8
affixSgPP5 : Affixe = afixe "sesem" "sese�i" "sese" ;
affixPlPP5 : Affixe = afixe "seser�m" "seser��i" "seser�" ;

--subGroups 5-7
--affixSgPP2 and affixPlPP2 

--subGroup 1

mkV76 : Str -> Verbe = \pune ->
   let root = init pune ;
       r    = init root
       in
verbAffixes pune (changeP2 (r+"i") (mkFromAffix root affixSgGr21 affixPlGr21) )
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (root + "�nd") (root + "e") ;
       
mkV77 : Str -> Verbe = \atinge ->
    let root = init atinge ;
        r    = init root 
        in
verbAffixes atinge (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (root + "�nd") (root + "e") ;
                    
mkV78 : Str -> Verbe = \trage ->                    
     let root = init trage ;
         rad1  = genMut root "a" "�" ;
         r    = init root ;
         rad2 = genMut r "a" "�"
        in
verbAffixes trage (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix rad1 affixSgII affixPlII) 
        (mkTab rad2 (r + "ei") (r + "se�i") (rad2 + "e") (rad2 + "er�") affixPlPS5)
             (mkFromAffix rad2 affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (rad1 + "�nd") (root + "e") ;
              
mkV79 : Str -> Verbe = \decide ->
     let root = init decide ;
         r    = init root 
         in
verbAffixes decide (changeP2 (mkStemPlReg root) (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (r + "z�nd") (root + "e") ;
                    
mkV80 : Str -> Verbe = \rade ->
      let root = init rade ;
          rad1  = genMut root "a" "�" ;
          r    = init root ;
          rad2 = genMut r "a" "�"
        in
verbAffixes rade (changeP2 (mkStemPlReg root) (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix rad1 affixSgII affixPlII) 
        (mkTab rad2 (r + "ei") (r + "se�i") (rad2 + "e") (rad2 + "er�") affixPlPS5)
             (mkFromAffix rad2 affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (rad2 + "z�nd") (root + "e") ;

mkV81 : Str -> Verbe = \ucide ->
     let root = init ucide ;
         r    = init root 
         in
verbAffixes ucide (changeP2 (mkStemPlReg root) (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (r + "g�nd") (root + "e") ;

mkV82 : Str -> Verbe = \admite ->
    let root = init admite ;
         r    = init root 
         in
verbAffixes admite (changeP2 (mkStemPlReg root) (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (r + "��nd") (root + "e") ;

mkV83 : Str -> Verbe = \alege ->
    let root = init alege ;
        r    = init root ;
        newP = mkMutE root 
        in
verbAffixes alege (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (newP +"�") (mkAdjRegE (r + "s"))
                    (root + "�nd") (root + "e") ;

mkV84 : Str -> Verbe = \sumete ->
	let root = init sumete ;
		r    = init root ;
		newP = mkMutE root 
			in
verbAffixes sumete (changeP2 (mkStemPlReg root) (mkAffixSpec2 root newP affixSgGr21 affixPlGr21)) 
			(mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
				 (mkFromAffix r affixSgPP5 affixPlPP5) (newP +"�") (mkAdjRegE (r + "s"))
						(r + "��nd") (root + "e") ;

mkV85 : Str -> Verbe = \scoate ->
    let root = init scoate ;
        r    = mkStemMutOa root ;
        rad  = init r ;
        rad1 = init root 
           in 
verbAffixes scoate (mkTab root r (mkStemPlReg r) scoate r affixPlGr21) 
	    	(mkFromAffix r affixSgII affixPlII) 
	    	(mkTab rad1 (rad + "sei") (rad + "se�i") (rad1 + "se") (rad1 + "er�") affixPlPS5)
    			 (mkFromAffix rad affixSgPP5 affixPlPP5) (root +"�") (mkAdjRegO (rad + "s"))
						(rad + "��nd") (root + "e") ;
     
        
mkV86 : Str -> Verbe = \roade ->
	let root = init roade ;
		r    = mkStemMutOa root ;
		rad  = init r ;
		rad1 = init root
		   in 
verbAffixes roade (mkTab root r (mkStemPlReg r) roade r affixPlGr21) 
	    		(mkFromAffix r affixSgII affixPlII) 
	    		(mkTab rad1 (rad + "sei") (rad + "se�i") (rad1 + "se") (rad1 + "er�") affixPlPS5)
    				 (mkFromAffix rad affixSgPP5 affixPlPP5) (root +"�") (mkAdjRegO (rad + "s"))
							(rad + "z�nd") (root + "e") ;
	     

mkV87 : Str -> Verbe = \purcede ->
     let root = init purcede ;
         r    = init root ;
         newP = mkMutE root
           in
verbAffixes purcede (changeP2 (mkStemPlReg root) (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (newP +"�") (mkAdjRegE (r + "s"))
                    (r + "z�nd") (root + "e") ;


mkV88 : Str -> Verbe = \toarce ->
	let root = init toarce ;
	    r    = mkStemMutOa root ;
		rad  = init r ;
        rad1 = init root
				   in 
verbAffixes toarce (mkTab root r (mkStemPlReg r) toarce r affixPlGr21) 
	    (mkFromAffix r affixSgII affixPlII) 
	    (mkTab rad1 (rad + "sei") (rad + "se�i") (rad1 + "se") (rad1 + "er�") affixPlPS5)
    			 (mkFromAffix rad affixSgPP5 affixPlPP5) (root +"�") (mkAdjRegO (rad + "s"))
						(rad + "c�nd") (root + "e") ;

--subGroup 2

mkV89 : Str -> Verbe = \curge ->
	let root = init curge ;
		r    = init root 
			in
	verbAffixes curge (mkFromAffix root affixSgGr21 affixPlGr21) 
			(mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
				 (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
						(root + "�nd") (root + "i") ;
						
mkV90 : Str -> Verbe = \merge ->
let root = init merge ;
    r    = init root ;
    newP = mkMutE root 
        in
verbAffixes merge (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (newP +"�") (mkAdjRegE (r + "s"))
                    (root + "�nd") (root + "i") ;

mkV91 : Str -> Verbe = \ride ->
let root = init ride ;
     r    = init root 
         in
verbAffixes ride (changeP2 (mkStemPlReg root) (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (r + "z�nd") (mkStemPlReg root) ;
                    

mkV92 : Str -> Verbe = \ramane ->
let root = init ramane ;
    r    = init root ;
    r1   = genMut root "�" "�" ;
    r2   = genMut root "�" "a"
       in
verbAffixes ramane (changeP2 (r + "i") (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) 
        (mkTab (init r2) (init r1 + "sei") (init r1 + "se�i") (init r2 + "se") (init r2 + "ser�")  affixPlPS5)
             (mkFromAffix (init r1) affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (init r2 + "s"))
                    (root + "�nd") (r + "i") ;       

--subGroup 3 :

mkV93 : Str -> Verbe = \zice ->
 let root = init zice ;
        r    = init root 
        in
verbAffixes zice (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "s"))
                    (root + "�nd") r ;
                    
--subGroup 4 :
                    
mkV94 : Str -> Verbe = \rupe ->
  let root = init rupe 
  in 
verbAffixes rupe (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS5 affixPlPS5)
             (mkFromAffix root affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (root + "t"))
                    (root + "�nd") rupe ;  

mkV95 : Str -> Verbe = \frige ->
   let root = init frige ;
       r    = init root + "p"
       in
verbAffixes frige (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "t"))
                    (root + "�nd") frige ;


mkV96 : Str -> Verbe = \frange ->
 let root = init frange ;
       r  = init root 
       in
verbAffixes frange (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "t"))
                    (root + "�nd") frange ;

mkV97 : Str -> Verbe = \sparge ->
  let root = init sparge ;
      r    = init root ;
      r1   = genMut root "a" "�";
      r2   = genMut r "a" "�"
      in
verbAffixes sparge (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix r1 affixSgII affixPlII) 
        (mkTab r2 (init r1 + "sei") (init r1 + "se�i") (r2 + "se") (r2 + "ser�")  affixPlPS5)
             (mkFromAffix r2 affixSgPP5 affixPlPP5) (root +"�") (mkAdjReg (r + "t"))
                    (r1 + "�nd") sparge ;

mkV98 : Str -> Verbe = \fierbe ->
  let root = init fierbe ;
      r    = init root ;
      r1   = genMut root "e" "a"
      in
verbAffixes fierbe (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS5 affixPlPS5)
             (mkFromAffix r affixSgPP5 affixPlPP5) (r1 +"�") (mkAdjRegE (r + "t"))
                    (root + "�nd") fierbe ;      

mkV99 : Str -> Verbe = \coace ->
   let root = init coace ;
       r    = genMut2 root "oa" "o" ;
       r1   = init r + "p"
       in
verbAffixes coace (mkTab root r1 (r1+"i") (root+"e") r1 affixPlGr21) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix r1 affixSgPS5 affixPlPS5)
             (mkFromAffix r1 affixSgPP5 affixPlPP5) (root +"�") (mkAdjRegO (r1 + "t"))
                    (r + "�nd") coace ;       
--subGroup 5 :

mkV100 : Str -> Verbe = \cere ->
  let root = init cere ;
      r    = mkMutE root 
      in
verbAffixes cere (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (root + "ut"))
                    (root + "�nd") cere ;
    

mkV101 : Str -> Verbe = \crede ->
   let root = init crede ;
       newP = init (mkStemPlReg root) ;
       r    = mkMutE root
       in
verbAffixes crede (changeP2 (newP + "i") (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix newP affixSgPS3 affixPlPS3)
             (mkFromAffix newP affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (newP + "ut"))
                    (newP + "�nd") crede ;  

mkV102 : Str -> Verbe = \tese ->
   let root = init tese ;
       newP = init (mkStemPlReg root) ;
       r    = mkMutE root
       in
verbAffixes tese (changeP2 (newP + "i") (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (root + "ut"))
                    (root + "�nd") tese ;  

mkV103 : Str -> Verbe = \creste ->
  let root = init creste ;
      r    = Predef.tk 2 root + "sc" ;
      newC = mkMutE r 
      in
verbAffixes creste (changeP1 r (mkFromAffix  root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (newC +"�") (mkAdjReg (r + "ut"))
                    (r + "�nd") creste ;
      

mkV104 : Str -> Verbe = \investe ->
  let root = init investe ;
      r    = Predef.tk 2 root + "sc" ;
      newC = mkMutE r ;
      rad  = genMut r "e" "�" 
      in
verbAffixes investe (changeP1 r (mkFromAffix  root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (newC +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") investe ;


mkV105 : Str -> Verbe = \bate ->
 let root = init bate ;
     r    = genMut root "a" "�"
     in
verbAffixes bate (changeP2 (mkStemPlReg root) (mkFromAffix  root affixSgGr21 affixPlGr21)) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (root +"�") (mkAdjReg (r + "ut"))
                    (r + "�nd") bate ;

mkV106 : Str -> Verbe = \naste ->
  let root = init naste ;
      r    = Predef.tk 2 root + "sc" ;
      rad  = genMut r "a" "�" 
      in
verbAffixes naste (changeP1 r (mkFromAffix  root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (rad + "ut"))
                    (rad + "�nd") naste ;

--mkV107 : Str -> Verbe = \rage ->

  
mkV108 : Str -> Verbe = \tine ->
let root = init tine ;
     r    = init root + "i"
     in
verbAffixes tine (changeP2 r (mkFromAffix  root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP2 affixPlPP2) (root +"�") (mkAdjReg (root + "ut"))
                    (root + "�nd") tine ;

mkV109 : Str -> Verbe = \cunoaste ->
let   root = init cunoaste ;
      newC = Predef.tk 2 root + "sc" ;
      r    = mkStemMutOa newC ;
      rad  = mkStemMutOa root
      in
verbAffixes cunoaste (mkTab root r (mkStemPlReg r) cunoaste r affixPlGr21) 
        (mkFromAffix rad affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (newC +"�") (mkAdjReg (r + "ut"))
                    (r + "�nd") cunoaste ;    

mkV110 : Str -> Verbe = \coase ->
let root = init coase ;
    r    = mkStemMutOa root ;
    rad  = genMut2 root "oa" "u" 
    in
verbAffixes coase (mkTab root r (mkStemPlReg r) coase r affixPlGr21) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix rad affixSgPS3 affixPlPS3)
             (mkFromAffix rad affixSgPP2 affixPlPP2) (root +"�") (mkAdjReg (rad + "ut"))
                    (r + "�nd") coase ;     
    
mkV111 : Str -> Verbe = \divide ->
let root = init divide ;
    newP = mkStemPlReg root
    in
verbAffixes divide (changeP2 newP (mkFromAffix root affixSgGr21 affixPlGr21)) 
        empty empty empty (root +"�") (variants{})
                    (root + "�nd") divide ;
                       
mkV112 : Str -> Verbe = \vinde ->
let root = init vinde ;
    r    = genMut root "i" "�" ;
    in
verbAffixes vinde (mkTab root r (mkStemPlReg root) vinde r affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (root +"�") (mkAdjReg (r + "ut"))
                    (init r + "z�nd") vinde ;   
   
mkV113 : Str -> Verbe = \pierde ->
let root = init pierde ;
    r    = mkMutE root ;
    rad  = init (mkStemPlReg root)
    in
verbAffixes pierde (changeP2 (rad + "i") (mkFromAffix root affixSgGr21 affixPlGr21)) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP2 affixPlPP2) (r +"�") (mkAdjReg (root + "ut"))
                    (rad + "�nd") pierde ;

--mkV114 : Str -> Verbe = \exige ->


--subGroup 6

mkV115 : Str -> Verbe = \face -> 
let root = init face ;
    r    = genMut root "a" "�" 
    in
verbAffixes face (mkFromAffix root affixSgGr21 affixPlGr21) 
        (mkFromAffix r affixSgII affixPlII) (mkFromAffix r affixSgPS3 affixPlPS3)
             (mkFromAffix r affixSgPP2 affixPlPP2) (root +"�") (mkAdjReg (r + "ut"))
                    (r + "�nd") (init r) ;
--subGroup 7
mkV116 : Str -> Verbe = \umple ->
let root = init umple 
     in
verbAffixes umple (mkFromAffix root affixSgGr31 affixPlGr31) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP2 affixPlPP2) (root +"e") (mkAdjReg (root + "ut"))
                    (root + "�nd") umple ;   

--subGroup 8
mkV117 : Str -> Verbe = \scrie ->
let root = init scrie 
   in 
verbAffixes scrie (mkFromAffix root affixSgGr31 affixPlGr31) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS5 affixPlPS5)
             (mkFromAffix root affixSgPP5 affixPlPP5) (root +"e") (mkAdjReg (root + "s"))
                    (root + "ind") scrie ;

------------------------------------
---GROUP 4 -- verbs ending in -i/-�
------------------------------------
--------------
--Present 
--------------

--subGroups 1-2
affixSgGr41 : Affixe = afixe "esc" "e�ti" "e�te" ;
affixPlGr41 : Affixe = afixe "im" "i�i" "esc" ;

--subGroup 3

affixSgGr43 : Affixe = afixe "iesc" "ie�ti" "ie�te" ;
affixPlGr43 : Affixe = afixe "im" "i�i" "iesc" ;

--subGroup 4

affixSgGr44 : Affixe = afixe "iu" "ii" "ie" ;
affixPlGr44 : Affixe = afixe "im" "i�i" "iu" ;

--subGroup 5 

affixSgGr45 : Affixe = afixe "i" "i" "ie" ;
affixPlGr45 : Affixe = afixe "im" "i�i" "ie" ;

--subGroups 6 -8

affixSgGr468 : Affixe = afixe "" "i" "e" ;
affixPlGr468 : Affixe = afixe "im" "i�i" "" ;

--subGroup 9 

affixSgGr49 : Affixe = afixe "" "i" "�" ;
affixPlGr49 : Affixe = afixe "im" "i�i" "�" ;

--subGroup 10

affixSgGr410 : Affixe = afixe "" "i" "e" ;
affixPlGr410 : Affixe = afixe "im" "i�i" "e" ;

--subGroup 11

affixSgGr411 : Affixe = afixe "" "" "ie" ;
affixPlGr411 : Affixe = afixe "" "" "ie" ;

--subGroup 12 

affixSgGr412 : Affixe = afixe "�sc" "�ti" "�te" ;
affixPlGr412 : Affixe = afixe "�m" "��i" "�sc" ;

--subGroup 13

affixSgGr413 : Affixe = afixe "" "i" "�" ;
affixPlGr413 : Affixe = afixe "�m" "��i" "�" ;


-------------------------
--Imperfect
-------------------------

--subGroup 1,6-10
--affixSgII + affixPlII

--subGroup 2, 12-13
--affixSgI + affixPlI

--subGroups 3-5
--affixSgI2 + affixPlI2

--subGroup 11
affixSgI4 : Affixe = afixe "" "" "ia" ;
affixPlI4 : Affixe = afixe "" "" "iau" ;

------------------------
--Past Simple
------------------------
--subGroups 1-3,5-10
affixSgPS6 : Affixe = afixe "ii" "i�i" "i" ;
affixPlPS6 : Affixe = afixe "ir�m" "ir��i" "ir�" ;

--subGroup 4
affixSgPS7 : Affixe = afixe "iui" "iu�i" "iu" ;
affixPlPS7 : Affixe = afixe "iur�m" "iur��i" "iur�" ;

--subGroup 11
affixSgPS8 : Affixe = afixe "" "" "i" ;
affixPlPS8 : Affixe = afixe "" "" "ir�" ;

--subGroup 12-13
affixSgPS9 : Affixe = afixe "�i" "�i" "�" ;
affixPlPS9 : Affixe = afixe "�r�m" "�r��i" "�r�" ;

-----------------------
--Past Perfect
-----------------------
--subGroups 1-3,5 + 10
affixSgPP6 : Affixe = afixe "isem" "ise�i" "ise" ;
affixPlPP6 : Affixe = afixe "iser�m" "iser��i" "iser�" ;

--subGroup 4

affixSgPP7 : Affixe = afixe "iusem" "iuse�i" "iuse" ;
affixPlPP7 : Affixe = afixe "iuser�m" "iuser��i" "iuser�" ;

--subGroup 11
affixSgPP8 : Affixe = afixe "" "" "ise" ;
affixPlPP8 : Affixe = afixe "" "" "iser�" ;

--subGroup 12-13
affixSgPP9 : Affixe = afixe "�sem" "�se�i" "�se" ;
affixPlPP9 : Affixe = afixe "�ser�m" "�ser��i" "�ser�" ;


--subGroup 1 



mkV119 : Str -> Verbe = \povesti ->
 let root = init povesti 
 in
verbAffixes povesti (mkFromAffix root affixSgGr41 affixPlGr41) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"easc�") (mkAdjReg (root + "it"))
                    (root + "ind") (root + "e�te") ;
--subGroup 2
mkV120 : Str -> Verbe = \pustii ->
let root = init pustii
in 
verbAffixes pustii (mkFromAffix root affixSgGr41 affixPlGr41) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"asc�") (mkAdjReg (root + "it"))
                    (root + "ind") (root + "e�te") ;
--subGroup 3
mkV121 : Str -> Verbe = \locui ->
let root = init locui
in
verbAffixes locui (mkFromAffix root affixSgGr43 affixPlGr44) 
        (mkFromAffix root affixSgI2 affixPlI2) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"iasc�") (mkAdjReg (root + "it"))
                    (root + "ind") (root + "e�te") ;
--subGroup 4
mkV122 : Str -> Verbe = \sti ->
let root = init sti 
in
verbAffixes sti (mkFromAffix root affixSgGr44 affixPlGr44) 
        (mkFromAffix root affixSgI2 affixPlI2) (mkFromAffix root affixSgPS7 affixPlPS7)
             (mkFromAffix root affixSgPP7 affixPlPP7) (root +"ie") (mkAdjReg (root + "iut"))
                    (root + "iind") (variants{}) ;
--subGroup 5
mkV123 : Str -> Verbe = \sui ->
let root = init sui
in
verbAffixes sui (mkFromAffix root affixSgGr45 affixPlGr45) 
        (mkFromAffix root affixSgI2 affixPlI2) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"ie") (mkAdjReg (root + "it"))
                    (root + "ind") (sui+"e") ;

mkV124 : Str -> Verbe = \indoi ->
let root = init indoi ;
    r    = init (mkMutO indoi)
    in
verbAffixes indoi (mkAffixSpec1 root r affixSgGr45 affixPlGr45) 
        (mkFromAffix root affixSgI2 affixPlI2) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"ie") (mkAdjReg (root + "it"))
                    (root + "ind") (r+"ie") ;
                 
mkV125 : Str -> Verbe = \jupui ->
let root = init jupui ;
    r1   = genMut jupui "u" "o" ;
    r2   = genMut jupui "u" "oa"
in
verbAffixes jupui (mkTab root r1 r1 (r2+"e") (r2+"e") affixPlGr45) 
        (mkFromAffix root affixSgI2 affixPlI2) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r2 +"e") (mkAdjReg (root + "it"))
                    (root + "ind") (r2+"e") ;

--subGroup 6
mkV126 : Str -> Verbe = \fugi ->
let root = init fugi
in
verbAffixes fugi (mkFromAffix root affixSgGr468 affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"�") (mkAdjReg (root + "it"))
                    (root + "ind") fugi ;

mkV127 : Str -> Verbe = \auzi ->
let root = init auzi ;
    r    = init root + "d"
    in
verbAffixes auzi (mkTab root r auzi (r+"e") r affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") auzi ;

mkV128 : Str -> Verbe = \dormi ->
let root = init dormi ;
    r    = mkMutO root 
    in
verbAffixes dormi (mkAffixSpec2 root r affixSgGr468 affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") dormi ;
                    
mkV129 : Str -> Verbe = \muri ->
let root = init muri ;
    r1   = modU root ;
    r2   = mkStemMutO r1
         in                  
verbAffixes muri (mkTab root r1 (r1 + "i") (r2 + "e") r1  affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r2 +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r1 + "i") ;
--subGroup 7
mkV130 : Str -> Verbe = \simti ->
let root = init simti ;
    r    = init root + "t"
    in
verbAffixes simti (mkTab root r (mkStemPlReg r) (r+"e") r affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r+"e") ;
                    
mkV131 : Str -> Verbe = \sorbi ->
let root = init sorbi ;
    r    = mkMutO root 
    in
verbAffixes sorbi (mkAffixSpec2 root r affixSgGr468 affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r + "e") ;
                    
mkV132 : Str -> Verbe = \slobozi ->
let root = init slobozi ;
    rad  = init root + "d" ;
    r    = mkMutO rad 
    in
verbAffixes slobozi (mkTab root rad root (r+"e") rad affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r+"e") ;
                    
mkV133 : Str -> Verbe = \mirosi ->
let root = init mirosi ;
    r    = mkMutO root
    in
verbAffixes mirosi (mkAffixSpec2 root r  affixSgGr468 affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r+"e") ;
                    
mkV134 : Str -> Verbe = \imparti ->
let root = init imparti ;
    rad  = init root + "t" ;
    r    = genMut rad "�" "a"
    in
verbAffixes imparti (mkFromAffixes1 r root  affixSgGr468 affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r+"e") ;
                    
mkV118 : Str -> Verbe = \sari ->
let root = init sari ;
    r    = genMut root "�" "a"
    in
verbAffixes sari (mkFromAffixes2 r root  affixSgGr468 affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r+"i") ;
                    
                    
mkV135 : Str -> Verbe = \repezi ->
let root = init repezi ;
    rad  = init root + "d" ;
    r    = mkMutE rad
    in
verbAffixes repezi (mkTab root rad repezi (rad + "e") r affixPlGr468)
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (rad + "e") ;

--subGroup 8
mkV136 : Str -> Verbe = \veni ->
let root = init veni ;
    rad  = init root ;
    r    = genMut root "e" "i"
    in
verbAffixes veni (mkTab root r (init r + "i") (r + "e") r affixPlGr468) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (r +"�") (mkAdjReg (root + "it"))
                    (root + "ind") (r + "o") ;
--subGroup 9
mkV137 : Str -> Verbe = \oferi ->
let root = init oferi
in
verbAffixes oferi (mkFromAffix root affixSgGr49 affixPlGr49) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"e") (mkAdjReg (root + "it"))
                    (root + "ind") (root + "�") ;

mkV138 : Str -> Verbe = \acoperi ->
let root = init acoperi;
    r    = genMut root "e" "�" 
    in
verbAffixes acoperi (mkTab root r acoperi (root + "�") (root + "�")  affixPlGr49) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"e") (mkAdjReg (root + "it"))
                    (root + "ind") (root + "�") ;

--subGroup 10
mkV139 : Str -> Verbe = \bombani ->
let root = init bombani
in
verbAffixes bombani (mkFromAffix root affixSgGr410 affixPlGr410) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS6 affixPlPS6)
             (mkFromAffix root affixSgPP6 affixPlPP6) (root +"e") (mkAdjReg (root + "it"))
                    (root + "ind") (root + "e") ;

--subGroup 11 !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
mkV140 : Str -> Verbe = \trebui ->
let root = init trebui
in
verbAffixes trebui (mkFromAffix root affixSgGr411 affixPlGr411) 
        (mkFromAffix root affixSgI4 affixPlI4) (mkFromAffix root affixSgPS8 affixPlPS8)
             (mkFromAffix root affixSgPP8 affixPlPP8) (root +"iasc�") (mkAdjReg (root + "it"))
                    (root + "ind") nonExist ;

--subGroup 12
mkV141 : Str -> Verbe = \uri ->
let root = init uri
in
verbAffixes uri (mkFromAffix root affixSgGr412 affixPlGr412) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS9 affixPlPS9)
             (mkFromAffix root affixSgPP9 affixPlPP9) (root +"asc�") (mkAdjReg (root + "�t"))
                    (root + "�nd") (root + "�te") ;
--subGroup 13

mkV142 : Str -> Verbe = \vari ->
let root = init vari
in
verbAffixes vari (mkFromAffix root affixSgGr413 affixPlGr413) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS9 affixPlPS9)
             (mkFromAffix root affixSgPP9 affixPlPP9) (root +"e") (mkAdjReg (root + "�t"))
                    (root + "�nd") (root + "�") ;

mkV143 : Str -> Verbe = \cobori ->
let root = init cobori ;
    r    = mkMutO root
    in
verbAffixes cobori (mkAffixSpec1 root r affixSgGr413 affixPlGr413) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS9 affixPlPS9)
             (mkFromAffix root affixSgPP9 affixPlPP9) (r +"e") (mkAdjReg (root + "�t"))
                    (root + "�nd") (r + "�") ;
                 
mkV144 : Str -> Verbe = \tabari ->
let root = init tabari ;
    rad  = modAFirst root ;
    r    = mkStemPlReg rad
    in
verbAffixes tabari (mkTab root rad r (rad + "�") (rad + "�") affixPlGr413) 
        (mkFromAffix root affixSgI affixPlI) (mkFromAffix root affixSgPS9 affixPlPS9)
             (mkFromAffix root affixSgPP9 affixPlPP9) (init r +"e") (mkAdjReg (root + "�t"))
                    (root + "�nd") (rad + "�") ;


---------------------------------------
--Special verbs :

--to have :

mkV1 : Str -> Verbe = \avea ->
let root = Predef.tk 2 avea
  in
verbAffixes avea (mkTab root "am" "ai" "are" "au" affixPlGr21) 
        (mkFromAffix root affixSgII affixPlII) (mkFromAffix root affixSgPS3 affixPlPS3)
             (mkFromAffix root affixSgPP2 affixPlPP2) "aib�" (mkAdjReg (root + "ut"))
                    (root + "�nd") "ai" ;
                    
--to be :                    
{-
mkV2 : Str -> Verbe = \fi ->
let root = init fi ;
    pres : Number => Person => Str = table {Sg => table {P1 => "sunt"; P2 => "e�ti"; P3 => "este"};
                                            Pl => table {P1 => "suntem"; P2 => "sunte�i"; P3 => "sunt"} 
                                            };
    ps  : Number => Person => Str = table {Sg => table {P1 => "fusei"; P2 => "fuse�i"; P3 => "fuse"};
                                           Pl => table {P1 => "fuser�m"; P2 => "fuser��i"; P3 => "fuser�"} 
                                           };                                        
    pp : Number => Person => Str = table {Sg => table {P1 => "fusesem"; P2 => "fusese�i"; P3 => "fusese"};
                                           Pl => table {P1 => "fuseser�m"; P2 => "fuseser��i"; P3 => "fuseser�"} 
                                           }
    in
    verbAffixes fi pres (mkFromAffix "er" affixSgI affixPlI) ps pp
                                               
-}    
} ;