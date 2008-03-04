
instance LexEditorFre of LexEditor = open SyntaxFre, ParadigmsFre, IrregFre in {

--	flags coding = utf8 ;

        oper  ---
          mkAdV : Str -> AdV = \s -> {s = s ; lock_AdV = <>} ;
          myMkPN : N -> PN = \n -> {s = n.s ! singular ; g = n.g ; lock_PN = <>} ;

	oper
-- Sentences
		singleWordCommand_Utt verb			= mkUtt politeImpForm positivePol (mkImp verb) ;
		command_Utt verb det adj noun		= mkUtt politeImpForm positivePol (mkImp (mkVP (mkV2 verb) (mkNP det (mkCN adj noun)))) ;
		randomlyCommand_Utt verb det noun	= mkUtt politeImpForm positivePol (mkImp (mkVP (mkAdV "al�atoirement") (mkVP (mkV2 verb) (mkNP det noun)))) ;
		label_Utt noun						= mkUtt (mkNP (myMkPN noun)) ;
		errorMessage_Utt adj noun			= mkUtt (mkS negativePol (mkCl (mkNP indefPlDet (mkCN adj noun)))) ;

-- Verbs
		undo_V			= d�faire_V2 ;
		redo_V			= refaire_V2 ;
		cut_V			= mkV "couper" ;
		copy_V			= mkV "copier" ;
		paste_V			= mkV "coller" ;
		delete_V		= d�truire_V2 ;
		refine_V		= mkV "raffiner" ;
		replace_V		= mkV "remplacer" ;
		wrap_V			= mkV "emballer" ;
		select_V		= mkV "selectionner" ;
		enter_V			= mkV "ajouter" ;
		show_V			= mkV "montrer" ;

-- Nouns
		language_N		= mkN "langue" ;
		node_N			= mkN "noeud" ;
		tree_N			= mkN "arbre" masculine ;
		refinement_N	= mkN "raffinement" ;
		wrapper_N		= mkN "emballage" masculine ;
		string_N		= mkN "cha�ne" ;
		page_N			= mkN "page" ;
		danish_N		= mkN "danois" ;
		english_N		= mkN "anglais" ;
		finnish_N		= mkN "finnois" ;
		french_N		= mkN "fran�ais" ;
		german_N		= mkN "allemand" ;
		italian_N		= mkN "italien" ;
		norwegian_N		= mkN "norv�gien" ;
		russian_N		= mkN "russe" ;
		spanish_N		= mkN "espagnol" ;
		swedish_N		= mkN "su�dois" ;

-- Adjectives
		noAdj_A			= mkA "" "" "" "" ;
		available_A		= mkA "disponible" ;
		next_A			= mkA "prochaine" ;
		previous_A		= mkA "pr�c�dent" ;

-- Determiners
		defSg_Det		= defSgDet ;
		defPl_Det		= defPlDet ;
		indefSg_Det		= indefSgDet ;
		indefPl_Det		= indefPlDet ;
		this_Det		= mkDet this_QuantSg ;

}
