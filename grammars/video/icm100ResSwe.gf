resource icm100ResSwe = {

  param RefPol = Pos | Neg | Inter ;
  param RefLev = Per | Sem | Und | Acc ;

  oper ex1 : RefPol => RefLev => Str = table {
	Pos => table {
		Per => ["jag h�rde"];	
		Sem => [""];
		Und => [""];
		Acc => ["okej"]
		};	

	Neg => table {
		Per => ["urs�kta jag h�rde inte alls vad du sa"];	
		Sem => ["jag f�rst�r inte vad du menar"];
		Und => ["jag f�rst�r inte riktigt vad du menar"];
		Acc => ["tyv�rr kan inte hantera"]
		};	
	
	Inter => table {
		Per => (variants{});	
	     	Sem => (variants{});
--		Und => ["st�mmer det"]; --hack!
		Und => (variants{});
		Acc => (variants{})
		}
	};

}