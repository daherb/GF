--# -path=.:../:../../../Resource/Time:../Shared:../../../Core:../../../Core/Shared:

concrete sharedDomainSwe of sharedDomain = sharedCoreSwe, DBSwe, TimeSwe, WeekdaySwe ** open SpecResSwe in{

lin
	-- ANSWERS


	makeAddEventAnswer event = {s = event.s};
	makeRemEventAnswer event = {s = event.s};
	makeCheckupAnswer event = {s = "om" ++ event.s};
	makeCheckTimeAnswer event = {s = event.s};
	makeAddInfoAnswer event = {s = "om" ++ event.s};

	makeAddEventTimeAnswer time = {s = time.s};
	makeRemEventTimeAnswer time = {s = time.s};
	makeCheckupTimeAnswer time = {s = time.s};
	makeCheckTimeTimeAnswer time = {s = time.s};
	makeAddInfoTimeAnswer time = {s = time.s};

	makeAddEventDayAnswer weekday = {s = "p�" ++ weekday.s};
	makeRemEventDayAnswer weekday = {s = "p�" ++ weekday.s};
	makeCheckupDayAnswer weekday = {s = "p�" ++ weekday.s};
	makeCheckTimeDayAnswer weekday = {s = "p�" ++ weekday.s};
	makeAddInfoDayAnswer weekday = {s = "p�" ++ weekday.s};

	makeCheckAnswer location = {s = location.s};
	makeAddInfoLocAnswer location = {s = "om" ++ location.s};
	makeCheckTimeLocAnswer location = {s = location.s};

-- LEXICON

pattern
	addEntry = varaints {["l�gga till"] ; ["anteckna"] ; ["g�ra en anteckning om"]};
	removeEntry = variants{ ["ta bort"] ; ["radera en anteckning"]};
	changeEntry = ["�ndra en anteckning om"];
	augmentEntry = ["l�gga till mer information"];
	checkupEntry = ["kolla tiden f�r"];

	checkup = ["vad har jag uppskrivet"];	

}