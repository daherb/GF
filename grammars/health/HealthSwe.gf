-- The UTF8 version currently differs from the non-UTF8 !!!

-- The difference with the UTF8 version is that 
-- operation "verbVara" doesn't need to be replaced
-- using the UTF8 encoding (because of the UTF8 problem 
-- with UTF8 resource grammars) 

-- use this path to read the grammar from the same directory

--# -path=.:../newresource/abstract:../prelude:../newresource/swedish
concrete HealthSwe of Health = open PredicationSwe, ResourceSwe, Prelude, SyntaxSwe, ExtraSwe in {

flags 
  startcat=Phr ; lexer=text ; parser=chart ; unlexer=text ;

lincat 
  Patient = patientNPCategory ;
  Body = CN ;
  Symptom = NP ;
  SymptomDegree = AP ;
  Prop = S ;
  Illness = CN ; 
  Condition = VP ;
  Specialization = CN ;
  Medicine  = CN ;

lin 
  And x y = ConjS AndConj (TwoS x y) ; 

  ShePatient = mkPronPatient hon_35 ;
  TheyPatient = mkPronPatient de_38 ;
  IPatientHe = mkPronPatient jag_32 ;

  Influenza = n2n (extCommNoun NoMasc (sApa "influens")) ** {lock_CN = <>} ; 
  Malaria = n2n (extCommNoun NoMasc (sApa "malari")) ** {lock_CN = <>} ; 
  Head = n2n (extCommNoun NoMasc (sHus "huvud")) ** {lock_CN = <>} ;
  Leg = n2n (extCommNoun NoMasc (sHus "ben")) ** {lock_CN = <>} ;
  Dentist  = n2n (extCommNoun Masc (sKikare "tandl�kar")) ** {lock_CN = <>} ;
  PainKiller = n2n (extCommNoun NoMasc (sBil "sm�rtstillande")) ** {lock_CN = <>} ;

  CatchCold = PosVG ( PredAP( AdjP1 (extAdjective (aGrund("f�rkyl")) ** {lock_Adj1 = <>}) ));
  Pregnant = PosVG ( PredAP( AdjP1 (extAdjective (aGrund("gravi") )** {lock_Adj1 = <>}) ));
  High = AdjP1 (extAdjective (aFin "h�g")** {lock_Adj1 = <>}) ;
  Terrible = AdjP1 (extAdjective (aFin "hemsk")** {lock_Adj1 = <>}) ;
 
  BeInCondition = PredVP ; 
  HaveIllness patient illness = predV2 (mkDirectVerb verbHava** {lock_TV =<>}) patient 
                                (DetNP (nullDet  ** {lock_Det = <>}) illness) ;
  NeedMedicine patient illness = predV2 (mkDirectVerb verbBehova** {lock_TV =<>}) patient 
                                 (DetNP (nullDet  ** {lock_Det = <>}) illness) ; 
  TakeMedicine patient illness = predV2 (mkDirectVerb verbTa** {lock_TV =<>}) patient 
                                 (DetNP (nullDet  ** {lock_Det = <>}) illness) ; 
  NeedDoctor patient illness = predV2 (mkDirectVerb verbBehova** {lock_TV =<>}) patient                                 
                                (DetNP (enDet  ** {lock_Det = <>}) illness) ;
  Fever = DetNP (nullDet  ** {lock_Det = <>}) (n2n (extCommNoun NoMasc (sFeber "feb")) ** {lock_CN = <>}) ;
  FeverMod degree = DetNP (nullDet  ** {lock_Det = <>}) (ModAdj degree (n2n (extCommNoun NoMasc (sFeber "feb")) ** {lock_CN = <>})) ;
 
  Complain = predV2 (mkDirectVerb verbHava ** {lock_TV =<>}) ;
  Broken patient head = predV2 (mkTransVerb verbHava "brutit" ** {lock_TV =<>} ) patient 
                        (defNounPhrase patient.n head ** {lock_NP =<>}) ;

  PainIn patient head = predV2 (mkDirectVerb verbHava** {lock_TV =<>}) patient 
   (
    DetNP (nullDet  ** {lock_Det = <>}) 
    ( AppFun 
       ((mkFun (extCommNoun NoMasc (sBil "ont")) "i") ** {lock_Fun = <>})
       ((defNounPhrase patient.n head)** {lock_NP = <>})
    )
   ) ;
  PainInMod patient head degree =  predV2 (mkDirectVerb verbHava** {lock_TV =<>}) patient
    (
      DetNP (nullDet  ** {lock_Det = <>}) 
      ( modCommNounPhrase degree 
           ( AppFun 
               ((mkFun (extCommNoun NoMasc (sBil "ont")) "i") ** {lock_Fun = <>}) 
               ((defNounPhrase patient.n head)** {lock_NP = <>})
           ) ** {lock_CN = <>}
      )
    ) ;

  Injured = injuredBody ;

};


