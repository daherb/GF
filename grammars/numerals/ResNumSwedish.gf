resource ResNumSwedish = {
  param DForm = ental | ton | tiotal ;
  oper mkTal : Str -> Str -> Str -> {
    s : DForm => Str 
  }
  = \ tv� -> \ tolv -> \ tjugo -> {
    s = table {
      ental => tv� ;
      ton => tolv ;
      tiotal => tjugo 
    }
    } ;
  oper regTal : Str -> {
    s : DForm => Str 
  }
  = \ fem -> mkTal fem (fem + "ton")(fem + "tio");
  oper ss : Str -> {
    s : Str 
  }
  = \ s -> {
    s = s 
  } ;
  }
