--# -path=../common:prelude

resource PhonoCat = open Prelude in {

--3 Elision
--
-- The phonological rule of *elision* can be defined as follows in GF.
-- In Catalan it includes both vowels and 'h'.

---TODO: L'elisi� dep�n de la tonicitat.

oper 
  vocal : Strs = strs {
    "a" ; "�" ;
	"e" ; "�" ; "�" ; "o" ; "�" ; "�" ;
	"i" ; "�" ; "�" ; "u" ; "�" ; "�" ;  "h" 
	} ;
  
  vocalForta : Strs = strs {
	"a" ; "�" ; "ha" ; "h�" ;
	"e" ; "�" ; "�" ; "he" ; "h�" ; "h�" ;
	"o" ; "�" ; "�" ; "ho" ; "h�" ; "h�" ;
	"�"  ; "�" ; "h�" ; "h�" ; 
	} ;
	
  vocalFeble : Strs = strs {
	"i" ; "�" ; "u" ; "�" ;
	"hi" ; "h�" ; "hu" ; "h�" ;
	} ;
	
	
elisDe = pre { "de" ; "d'" / vocal };
elisEl = pre { "el" ; "l'" / vocal } ;
elisLa = pre { "la" ; "l'" / vocalForta } ;
elisEm = pre { "em" ; "m'" / vocal } ;
elisEt = pre { "et" ; "t'" / vocal } ;
elisEs = pre {
			pre { "es" ; "s'" / vocal} ;
			"se" / strs { "s" } } ;

}
