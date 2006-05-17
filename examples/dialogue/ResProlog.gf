resource ResProlog = open Prelude in {

  oper
    bracket : Str -> Str = \s -> "[" ++ s ++ "]" ;

    app1 : Str -> Str -> Str = \f,x -> f ++ paren x ;
    app2 : Str -> Str -> Str -> Str = \f,x,y -> f ++ paren (x ++ "," ++ y) ;

    apps : Str -> SS -> SS = \f,x -> ss (app1 f x.s) ;

    op1 : (s,x : Str) -> {s,x : Str} = \s,x -> {s = s ; x = x} ;
    op2 : (s,x,y : Str) -> {s,x,y : Str} = \s,x,y -> {s = s ; x = x ; y = y} ;

    request : Str -> Str = app1 "request" ;
    answer  : Str -> Str = app1 "answer" ;

    req_ans : Str -> Str -> Str -> Str = \f,t,k ->
      bracket (request f ++ "," ++ answer (app1 t k)) ;

}

-- [request(add_event), answer(event_to_store(meeting))]
