
instance LexRestaurantFre of LexRestaurant = open SyntaxFre,GrammarFre,ParadigmsFre in {

	oper
		restaurant_N		= mkN "restaurant" ;
		food_N				= mkN "manger" ;
		staff_N				= mkN "personnel" ;
		wine_N				= mkN "vin" ;
		pizza_N				= mkN "pizza" feminine ;
		cheese_N			= mkN "fromage" masculine ;
		fish_N				= mkN "poisson" ;
		dish_N				= mkN "plat" ;
		drink_N				= mkN "boisson" feminine ;
		dessert_N			= mkN "dessert" ;

		recommend_V2		= mkV2 (mkV "recommander") ;

		chinese_A			= mkA "chinois" ;
		french_A			= mkA "fran�ais" ;
		italian_A			= mkA "italien" ;
		japanese_A			= mkA "japonais" ;
		mexican_A			= mkA "mexicain" ;
		thai_A				= mkA "tha�landais" ;
		expensive_A			= mkA "cher" ;
		cheap_A				= mkA ["bon march�"] ["bon march�"] ["bon march�"] ["bon march�"] ;
		nice_A				= mkA "agr�able" ;
		clean_A				= mkA "propre" ;
		dirty_A				= mkA "sale" ;
		fresh_A				= mkA "frais" "fra�che" "frais" "fra�ches" ;
		delicious_A			= mkA "d�licieux" ;
		fatty_A				= mkA "gras" "grasse" "gras" "grasses" ;
		tasteless_A			= mkA "fade";
		authentic_A			= mkA "authentique" ;
		efficient_A			= mkA "efficace" ;
		courteous_A			= mkA "poli" ;
		helpful_A			= mkA "obligeant" ;
		friendly_A			= mkA "amical" ;
		personal_A			= mkA "personnel" ;
		warm_A				= mkA "chaud" ;
		prompt_A			= mkA "rapide" ;
		attentive_A			= mkA "attentif" ;
		inefficient_A		= mkA "inefficace" ;
		rude_A				= mkA "rude" ;
		impersonal_A		= mkA "impersonnel" ;
		slow_A				= mkA "lent" ;
		unattentive_A		= mkA "inattentif" ;
		good_A				= mkA "bon" "bonne" ;
		great_A				= mkA "magnifique" ;
		excellent_A			= mkA "excellent" ;
		bad_A				= mkA "mauveux" ;
		awful_A				= mkA "affreux" ;
		horrible_A			= mkA "horrible" ;
		disgusting_A		= mkA "d�go�tant" ;
		boring_A			= mkA "ennuyeux" ;
		diverse_A			= mkA "divers" ;

		noAdv_AdV			= mkAdV "" ;
		strongly_AdV		= mkAdV "fortement" ;
		completely_AdV		= mkAdV "compl�tement";
		certainly_AdV		= mkAdV "certainement" ;
		honestly_AdV		= mkAdV "honn�tement" ;
		really_AdV			= mkAdV "vraiment" ;
		reluctantly_AdV		= mkAdV ["avec r�ticence"] ;
		hardly_AdV			= mkAdV ["� peine"] ;

--		but_Conj			= ss "mais" ** {n = Pl} ;

oper mkAdV : Str -> AdV = \s -> {s = s ; lock_AdV = <>} ;

}
