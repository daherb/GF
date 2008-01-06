--# -path=.:alltenses

resource Verbal = ResFin ** 
  open MorphoFin,Declensions,Conjugations,CatFin,Prelude in {

  flags optimize=noexpand ;

  oper

  mkV = overload {
    mkV : (huutaa : Str) -> V = mk1V ;
    mkV : (huutaa,huusi : Str) -> V = \s,t -> mk2V <s,t> ;
  } ;

  showV : V -> Utt = \v -> ss (
   v.s ! Inf Inf1 ++
   v.s ! Presn  Sg P1 ++
   v.s ! Presn  Sg P3 ++
   v.s ! Presn  Pl P3 ++
   v.s ! Imper Pl ++
   v.s ! Pass True ++
   v.s ! Impf   Sg P1 ++
   v.s ! Impf   Sg P3 ++
   v.s ! Condit Sg P3 ++
   v.s ! PastPartAct (AN (NCase Sg Nom)) ++
   v.s ! PastPartPass (AN (NCase Sg Nom))
   ) ** {lock_Utt = <>} ;

  mk1V : Str -> V = \s -> vforms2V (vForms1 s) ;
  mk2V : (_ : Str * Str) -> V = \st -> 
    vforms2V (vForms2 st.p1 st.p2) ;

  vForms1 : Str -> VForms = \ottaa ->
    let
      a = last ottaa ;
      otta = init ottaa ; 
      ott  = init otta ;
      ots  = init ott + "s" ;
      ota  = weakGrade otta ;
      otin = init (Declensions.strongGrade (init ott)) + "elin" ;
      ot   = init ota ;
    in
    case ottaa of {
      _ + ("e" | "i" | "o" | "u" | "y" | "�") + ("a" | "�") =>
        cHukkua ottaa (ota + "n") ;
      _ + ("l" | "n" | "r") + ("taa" | "t��") => 
        cOttaa ottaa (ota + "n") (ots + "in") (ots + "i") ;
      ("" | C_) + ("a" | "e" | "i") + _ + "aa" => 
        cOttaa ottaa (ota + "n") (ot + "oin") (ott + "oi") ;
      _ + ("aa" | "��") => 
        cOttaa ottaa (ota + "n") (ot + "in") (ott + "i") ;
      _ + ("ella" | "ell�") => 
        cKuunnella ottaa otin ;
      _ + ("osta" | "�st�") => 
        cJuosta ottaa (init ott + "ksen") ;
      _ + ("st" | "nn" | "ll" | "rr") + ("a" | "�") => 
        cJuosta ottaa (ott + "en") ;
      _ + ("ita" | "it�") => 
        cHarkita ottaa ;
      _ + ("eta" | "et�" | "ota" | "ata" | "uta" | "yt�" | "�t�" | "�t�") => 
        cPudota ottaa (Declensions.strongGrade ott + "si") ;
      _ + ("da" | "d�") => 
        cJuoda ottaa ;
      _ => Predef.error (["expected infinitive, found"] ++ ottaa) 
    } ;   

  vForms2 : (_,_ : Str) -> VForms = \huutaa,huusi ->
    let
      huuda = weakGrade (init huutaa) ;
      huusin = weakGrade huusi + "n" ;
      autoin = weakGrade (init huusi) + "in" ;
    in 
    case <huutaa,huusi> of {
      <_ + ("taa" | "t��"), _ + ("oi" | "�i")> =>
        cOttaa huutaa (huuda + "n") autoin huusi ;
      <_ + ("taa" | "t��"), _ + "i"> =>
        cOttaa huutaa (huuda + "n") huusin huusi ;
      <_ + ("eta" | "et�"), _ + "eni"> =>
        cValjeta huutaa huusi ;
      <_ + ("ita" | "it�"), _ + "isi"> =>
        cPudota huutaa huusi ;
      _ => vForms1 huutaa
      } ;

}
