--# -path=.:..:../Shared:../Weekday:../Time:../Channel

-- File name System/specific.Swe.gf

concrete specSystemSwe of specSystem = specificSwe, genSystemSwe ** {

lin
-- Confirm recording job
confirmRecJob act = {s = ["bekr�ftar"] ++ act.s } ;

q_lambdaActionDel dact = {s = ["vilket programnummer vill du ta bort"]};

---- vcr_add_rec_job_no_args = {s = ["spela in"]} ; -- hack!!!

--- Time in question
startTimeToStoreQ st = {s = "fr�n" ++ st.s } ; 
endTimeToStoreQ et = {s = "till" ++ et.s } ; 

--- Channel and Weekday in question
channelToStoreQ ch = {s = "p�" ++ ch.s } ; 
weekdayToStoreQ wd = {s = "p�" ++  wd.s } ; 

--- WHQuestions --- Lambdas
q_lambdaWeekday wdts = {s = ["vilken dag vill du spela in p�"]};
q_lambdaChannel chts = {s = ["vilken kanal vill du spela in fr�n"]};
q_lambdaStartTime stts = {s = ["vilken tid vill du p�b�rja inspelningen"]};
q_lambdaEndTime etts = {s = ["vilken tid vill du avsluta inspelningen"]};


--- Constructions for ynquestions
lin
ynQuST y = {s = y.s} ;
ynQuET y = {s = y.s} ;
ynQuCH y = {s = y.s} ;
ynQuWD y = {s = y.s} ;

lin
--- Props
startTimeToStoreProp st = {s = st.s } ; 
endTimeToStoreProp et = {s = et.s } ; 
channelToStoreProp chst = {s = chst.s } ; 
weekdayToStoreProp wdts = {s = wdts.s } ; 

channelListing chs = {s = chs.s } ; 
channels1 ch = {s = ch.s } ; 
channels2 ch chs = {s = ch.s ++ "," ++ chs.s } ; 
channelListAction ch = {s = ch.s } ; 
channelListActionDMove ch = {s = ch.s } ; 
}
