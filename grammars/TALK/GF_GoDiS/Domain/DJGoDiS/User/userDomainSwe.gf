--# -path=.:../:../../:../Shared/:../../../Resource/Media/:../../../Resource/Media/Swedish/:../../../Resorce/Media/English:../../../Resource/Numbers/:../../../Core:../../../Core/Shared/:../../../Core/User


concrete userDomainSwe of userDomain = userCoreSwe, sharedDomainSwe ** { 

flags conversion=finite;


lin

	-- CompoundedAnswers
	answerSongArtistPlay song artist = {s = variants {(song.s ++ "med" ++ artist.s)
					; (artist.s ++ "med" ++ song.s)} };
		
	answerSongArtistAdd song artist = {s = variants {(song.s ++ "med" ++ artist.s)
					; (artist.s ++ "med" ++ song.s)} };
		

pattern
	askArtist = variants { ["vad har jag"] ; ["vilka l�tar har jag"] ; ["har jag n�gonting"]}
					++ variants {"med" ; "av"};


	askSong = ["vem har"] ++ variants {"skrivit"; "gjort"};

	askCurrent = ["vad heter"] ++ variants {["den h�r"] ; ["l�ten som spelas nu"]};


}