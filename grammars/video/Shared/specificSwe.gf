--# -path=.:../Time:../Channel:../Weekday

concrete specificSwe of specific = generalSwe, weekdaySwe, timeSwe, channelSwe ** {

lin
indTime t = {s = t.s} ;
indChannel c = {s = c.s} ;
indWeekday w = {s = w.s} ;

delete_rec_job = {s = ["ta bort inspelning"]} ;
delAction dact = {s = dact.s };


startTimeToStore st = {s = "fr�n" ++ st.s } ; 
endTimeToStore et = {s = "till" ++ et.s } ; 
channelToStore ch = {s = "p�" ++ ch.s } ; 
weekdayToStore wd = {s = "p�" ++  wd.s } ; 

vcr_add_rec_job_no_args = {s = ["spela in"]} ; ----
}
