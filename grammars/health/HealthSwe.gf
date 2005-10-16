-- The UTF8 version currently differs from the non-UTF8 !!!

-- The difference with the UTF8 version is that 
-- operations "verbVara" (vbVara see ExtraSweU.gf) 
-- and "predAP" (predAP, see ExtraSweU.gf) need to be replaced
-- using the UTF8 encoding (because of the UTF8 problem 
-- with UTF8 resource grammars) 

-- use this path to read the grammar from the same directory

--# -path=.:../../lib/resource-0.6/abstract:../../lib/prelude:../../lib/resource-0.6/swedish
concrete HealthSwe of Health = open PredicationSwe, ResourceSwe, Prelude, SyntaxSwe, ExtraSwe, ParadigmsSwe, ResourceExtSwe in {

flags 
  startcat=Phr ; lexer=text ; parser=chart ; unlexer=text ;

lincat 
  Patient = patientNPCategory ;
  BodyPart = CN ;
  Symptom = NP ;
  SymptomDegree = AP ;
  Prop = S ;
  Illness = CN ; 
  Condition = VP ;
  Specialization = CN ;
  Medicine  = NP ;

lin 
  And x y = ConjS AndConj (TwoS x y) ; 

  ShePatient = mkPronPatient hon_35 ;
  TheyPatient = mkPronPatient de_38 ;
  IPatientHe = mkPronPatient jag_32 ;
  IPatientShe = mkPronPatient jag_32 ;
  HePatient = mkPronPatient han_34 ;
  WePatient = mkPronPatient vi_36 ;

  Influenza = UseN (nApa "influens") ; 
  Malaria = UseN (nApa "malari"); 
  Diarrhea = UseN (nApa "diarr�"); 
  SkinAllergy = UseN (nApa "hudallergi");  
  Heartburn = UseN (nApa "halsbr�nna");  
  Rheumatism = UseN (nBil "reumatism");  
  Cystitis = UseN (nRisk "urinv�gsinfektion");  
  Asthma = UseN (nApa "astma"); 
  Arthritis = UseN (nApa "artrit"); 
  Diabetes = UseN (nBil "diabetes"); 
  Tonsillitis = UseN (nBil "halsfluss"); 
  Constipation = UseN (nBil "f�rstoppning"); 
  
  Dentist  = UseN (nKikare "tandl�kare") ;
  Gynecologist = UseN (nRisk "gynekolog"); 
  Urologist= UseN (nRisk "urolog"); 
  Pediatrician = UseN (nKikare "barnl�kare"); 
  Physician = UseN (nKikare "l�kare"); 
  Dermatologist = UseN (nKikare "hudl�kare"); 
  Cardiologist = UseN (nRisk "kardiolog"); 
  Neuropathologist = UseN (nRisk "neurolog"); 
  Ophthalmologist = UseN (nKikare "�g�nl�kare"); 
  Surgeon = UseN (nRisk "kirurg"); 

  SleepingPeels = IndefManyNP (UseN (nRisk "s�mntablett")) ;
  Sedative = IndefOneNP (UseN (nPapper "lugnande")) ;
  Vitamins = IndefManyNP (UseN (nPapper "vitaminpiller")) ;
  EyeDrops = IndefManyNP (UseN (nPojke "�gondroppe")) ;
  Antibiotics = IndefManyNP (UseN (nPapper "antibiotika")) ;
  Viagra = MassNP (UseN (nBil "viagra")) ;
  Laxative = IndefOneNP (UseN (nPapper "laxer")) ;
  Insulin = MassNP (UseN (nRep "insulin")) ;
  Antidepressant = IndefOneNP ( ModAdj (AdjP1 (adjReg "antidepressiv")) (UseN (nRep "l�kemedel"))) ;
  PainKiller = IndefOneNP (UseN (nBil "sm�rtstillande")) ;

  CatchCold = PosVG ( PredAP( AdjP1 (extAdjective (aGrund("f�rkyl")) ** {lock_Adj1 = <>}) ));
  Pregnant = PosVG ( PredAP( AdjP1 (extAdjective (aGrund("gravi") )** {lock_Adj1 = <>}) ));
 
  BeInCondition = PredVP ; 
  HaveIllness patient illness = predV2 (mkDirectVerb verbHa** {lock_TV =<>}) patient 
                                (DetNP (nullDet  ** {lock_Det = <>}) illness) ;

  NeedMedicine = predV2 (mkDirectVerb verbBehova** {lock_TV =<>}) ; 
  TakeMedicine = predV2 (mkDirectVerb verbTa** {lock_TV =<>}) ;
 
  NeedDoctor patient illness = predV2 (mkDirectVerb verbBehova** {lock_TV =<>}) patient                                 
                                (DetNP (enDet  ** {lock_Det = <>}) illness) ;
  Fever = DetNP (nullDet  ** {lock_Det = <>}) (UseN (nRisk "feber")) ;
 
  Complain = predV2 (mkDirectVerb verbHa ** {lock_TV =<>}) ;
  Broken patient head = predV2 (mkTransVerb verbHa "brutit" ** {lock_TV =<>} ) patient 
                        (defNounPhrase patient.n head ** {lock_NP =<>}) ;

  PainIn patient head = predV2 (mkDirectVerb verbHa** {lock_TV =<>}) patient 
   (
    DetNP (nullDet  ** {lock_Det = <>}) 
    ( AppFun 
       ((mkFun (nBil "ont") "i") ** {lock_Fun = <>})
       ((defNounPhrase patient.n head)** {lock_NP = <>})
    )
   ) ;

  Head = UseN (nRep "huvud") ;
  Leg = UseN (nRep "ben") ;
  Stomac = UseN  (nPojke "mage")  ;
  Throat = UseN  (nBil "hals") ;
  Ear = UseN  (mkN "�ra" "�rat" "�ron" "�ronen" neutrum nonmasculine) ;
  Chest = UseN (nRep "br�st") ;
  Foot = UseN  (mkN "fot" "foten" "f�tter" "f�tterna" utrum nonmasculine) ;
  Arm = UseN  (mkN "hand" "handen" "h�nder" "h�nderna" utrum nonmasculine) ;
  Back = UseN  (nBil "rygg") ;
  Shoulder = UseN  (nNyckel "axel") ;

--  High = AdjP1 (adjReg "h�g") ;
--  Terrible = AdjP1 (adjReg "hemsk") ;
--  FeverMod degree = DetNP (nullDet  ** {lock_Det = <>}) (ModAdj degree (UseN (nKikare "feb") ) ;
--  PainInMod patient head degree =  predV2 (mkDirectVerb verbHa** {lock_TV =<>}) patient
--    (
--      DetNP (nullDet  ** {lock_Det = <>}) 
--      ( modCommNounPhrase degree 
--           ( AppFun 
--               ((mkFun (extCommNoun nonmasculine (sBil "ont")) "i") ** {lock_Fun = <>}) 
--               ((defNounPhrase patient.n head)** {lock_NP = <>})
--           ) ** {lock_CN = <>}
--      )
--    ) ;

  Injured = injuredBody ;

};


