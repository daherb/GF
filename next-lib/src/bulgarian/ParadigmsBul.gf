resource ParadigmsBul = MorphoFunsBul ** open
  Predef,
  Prelude,
  MorphoBul,
  CatBul
  in {
  flags coding=cp1251 ;

oper
  mkN001 : Str -> N ;
  mkN001 base = let v0 = base
                in mkNoun (v0)
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN002 : Str -> N ;
  mkN002 base = let v0 = tk 2 base;
                    v1 = last (base)
                in mkNoun (v0+"�"+v1)
                          (v0+"�"+v1+"���")
                          (v0+"�"+v1+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN002a : Str -> N ;
  mkN002a base = let v0 = tk 2 base;
                     v1 = last (base)
                 in mkNoun (v0+"�"+v1)
                           (v0+"�"+v1+"���")
                           (v0+"�"+v1+"�")
                           (v0+"-")
                           Masc
                           Inanimate ;
  mkN003 : Str -> N ;
  mkN003 base = let v0 = tk 3 base;
                    v1 = last (base)
                in mkNoun (v0+"��"+v1)
                          (v0+"��"+v1+"���")
                          (v0+"��"+v1+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN004 : Str -> N ;
  mkN004 base = let v0 = tk 4 base
                in mkNoun (v0+"����")
                          (v0+"������")
                          (v0+"�����")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN005 : Str -> N ;
  mkN005 base = let v0 = base
                in mkNoun (v0)
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN006 : Str -> N ;
  mkN006 base = let v0 = base
                in mkNoun (v0)
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN007 : Str -> N ;
  mkN007 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN007b : Str -> N ;
  mkN007b base = let v0 = base
                 in mkNoun (v0)
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Masc
                           Inanimate ;
  mkN007a : Str -> N ;
  mkN007a base = let v0 = base
                 in mkNoun (v0)
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Masc
                           Animate ;
  mkN008 : Str -> N ;
  mkN008 base = let v0 = tk 2 base;
                    v1 = last (base)
                in mkNoun (v0+"�"+v1)
                          (v0+v1+"�")
                          (v0+"�"+v1+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN008a : Str -> N ;
  mkN008a base = let v0 = tk 2 base
                 in mkNoun (v0+"��")
                           (v0+"��")
                           (v0+"-")
                           (v0+"���")
                           Masc
                           Inanimate ;
  mkN009 : Str -> N ;
  mkN009 base = let v0 = tk 2 base;
                    v1 = last (base)
                in mkNoun (v0+"�"+v1)
                          (v0+v1+"�")
                          (v0+"�"+v1+"�")
                          (v0+v1+"�")
                          Masc
                          Inanimate ;
  mkN009a : Str -> N ;
  mkN009a base = let v0 = tk 2 base
                 in mkNoun (v0+"��")
                           (v0+"����")
                           (v0+"���")
                           (v0+"-")
                           Masc
                           Inanimate ;
  mkN010 : Str -> N ;
  mkN010 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN011 : Str -> N ;
  mkN011 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN012 : Str -> N ;
  mkN012 base = let v0 = tk 3 base
                in mkNoun (v0+"���")
                          (v0+"����")
                          (v0+"-")
                          (v0+"����")
                          Masc
                          Inanimate ;
  mkN013 : Str -> N ;
  mkN013 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"���")
                          (v0+"-")
                          (v0+"���")
                          Masc
                          Inanimate ;
  mkN014 : Str -> N ;
  mkN014 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN014a : Str -> N ;
  mkN014a base = let v0 = tk 1 base
                 in mkNoun (v0+"�")
                           (v0+"��")
                           (v0+"��")
                           (v0+"��")
                           Masc
                           Inanimate ;
  mkN015 : Str -> N ;
  mkN015 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN016 : Str -> N ;
  mkN016 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN017 : Str -> N ;
  mkN017 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN018 : Str -> N ;
  mkN018 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"�")
                          (v0+"-")
                          (v0+"���")
                          Masc
                          Inanimate ;
  mkN018a : Str -> N ;
  mkN018a base = let v0 = tk 2 base;
                     v1 = last (base)
                 in mkNoun (v0+"�"+v1)
                           (v0+"�")
                           (v0+"-")
                           (v0+"-")
                           Masc
                           Inanimate ;
  mkN019 : Str -> N ;
  mkN019 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          Masc
                          Inanimate ;
  mkN019a : Str -> N ;
  mkN019a base = let v0 = tk 2 base
                 in mkNoun (v0+"��")
                           (v0+"���")
                           (v0+"���")
                           (v0+"-")
                           Masc
                           Inanimate ;
  mkN020 : Str -> N ;
  mkN020 base = let v0 = tk 3 base;
                    v1 = last (tk 2 base)
                in mkNoun (v0+v1+"��")
                          (v0+"�"+v1+"��")
                          (v0+"-")
                          (v0+v1+"���")
                          Masc
                          Inanimate ;
  mkN021 : Str -> N ;
  mkN021 base = let v0 = tk 3 base
                in mkNoun (v0+"���")
                          (v0+"��")
                          (v0+"-")
                          (v0+"����")
                          Masc
                          Inanimate ;
  mkN022 : Str -> N ;
  mkN022 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN023 : Str -> N ;
  mkN023 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"�")
                          (v0+"-")
                          (v0+"���")
                          Masc
                          Inanimate ;
  mkN024a : Str -> N ;
  mkN024a base = let v0 = tk 1 base
                 in mkNoun (v0+"�")
                           (v0+"��")
                           (v0+"-")
                           (v0+"��")
                           Masc
                           Inanimate ;
  mkN024 : Str -> N ;
  mkN024 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Masc
                          Animate ;
  mkN025 : Str -> N ;
  mkN025 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"-")
                          (v0+"�")
                          Masc
                          Animate ;
  mkN026 : Str -> N ;
  mkN026 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�����")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN027 : Str -> N ;
  mkN027 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"����")
                          (v0+"���")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN028 : Str -> N ;
  mkN028 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN028a : Str -> N ;
  mkN028a base = let v0 = tk 1 base
                 in mkNoun (v0+"�")
                           (v0+"����")
                           (v0+"�")
                           (v0+"-")
                           Masc
                           Inanimate ;
  mkN029 : Str -> N ;
  mkN029 base = let v0 = base
                in mkNoun (v0)
                          (v0+"����")
                          (v0+"-")
                          (v0+"��")
                          Masc
                          Inanimate ;
  mkN030 : Str -> N ;
  mkN030 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"�����")
                          (v0+"���")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN031 : Str -> N ;
  mkN031 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN031a : Str -> N ;
  mkN031a base = let v0 = base
                 in mkNoun (v0)
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Masc
                           Animate ;
  mkN032 : Str -> N ;
  mkN032 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN032a : Str -> N ;
  mkN032a base = let v0 = tk 1 base
                 in mkNoun (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Masc
                           Animate ;
  mkN033 : Str -> N ;
  mkN033 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN034 : Str -> N ;
  mkN034 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN035 : Str -> N ;
  mkN035 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN035a : Str -> N ;
  mkN035a base = let v0 = base
                 in mkNoun (v0)
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Masc
                           Animate ;
  mkN036 : Str -> N ;
  mkN036 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN037 : Str -> N ;
  mkN037 base = let v0 = base
                in mkNoun (v0)
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN038 : Str -> N ;
  mkN038 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          (v0+"�")
                          Masc
                          Animate ;
  mkN039 : Str -> N ;
  mkN039 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          (v0+"-")
                          Masc
                          Inanimate ;
  mkN040 : Str -> N ;
  mkN040 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"����")
                          (v0+"-")
                          (v0+"�")
                          Masc
                          Inanimate ;
  mkN040a : Str -> N ;
  mkN040a base = let v0 = base
                 in mkNoun (v0)
                           (v0+"-")
                           (v0+"-")
                           (v0+"-")
                           Masc
                           Inanimate ;
  mkN041 : Str -> N ;
  mkN041 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN041a : Str -> N ;
  mkN041a base = let v0 = tk 1 base
                 in mkNoun (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Fem
                           Inanimate ;
  mkN041b : Str -> N ;
  mkN041b base = let v0 = tk 1 base
                 in mkNoun (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           Fem
                           Inanimate ;
  mkN042 : Str -> N ;
  mkN042 base = let v0 = base
                in mkNoun (v0)
                          (v0)
                          (v0)
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN043 : Str -> N ;
  mkN043 base = let v0 = tk 3 base;
                    v1 = last (tk 1 base)
                in mkNoun (v0+"�"+v1+"�")
                          (v0+"�"+v1+"�")
                          (v0+"�"+v1+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN043a : Str -> N ;
  mkN043a base = let v0 = tk 4 base;
                     v1 = last (tk 2 base)
                 in mkNoun (v0+"�"+v1+"��")
                           (v0+"�"+v1+"��")
                           (v0+"�"+v1+"��")
                           (v0+"-")
                           Fem
                           Inanimate ;
  mkN044 : Str -> N ;
  mkN044 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN045 : Str -> N ;
  mkN045 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN046 : Str -> N ;
  mkN046 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN047 : Str -> N ;
  mkN047 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN048 : Str -> N ;
  mkN048 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          Fem
                          Inanimate ;
  mkN049 : Str -> N ;
  mkN049 base = let v0 = base
                in mkNoun (v0)
                          (v0+"�")
                          (v0+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN050 : Str -> N ;
  mkN050 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN051 : Str -> N ;
  mkN051 base = let v0 = tk 2 base;
                    v1 = last (base)
                in mkNoun (v0+"�"+v1)
                          (v0+v1+"�")
                          (v0+v1+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN052 : Str -> N ;
  mkN052 base = let v0 = tk 5 base
                in mkNoun (v0+"�����")
                          (v0+"������")
                          (v0+"������")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN052a : Str -> N ;
  mkN052a base = let v0 = tk 6 base
                 in mkNoun (v0+"������")
                           (v0+"�������")
                           (v0+"�������")
                           (v0+"-")
                           Fem
                           Inanimate ;
  mkN053 : Str -> N ;
  mkN053 base = let v0 = tk 3 base;
                    v1 = last (base)
                in mkNoun (v0+"��"+v1)
                          (v0+"��"+v1+"�")
                          (v0+"��"+v1+"�")
                          (v0+"-")
                          Fem
                          Inanimate ;
  mkN054 : Str -> N ;
  mkN054 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN055 : Str -> N ;
  mkN055 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN056 : Str -> N ;
  mkN056 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN057 : Str -> N ;
  mkN057 base = let v0 = tk 3 base;
                    v1 = last (tk 1 base)
                in mkNoun (v0+"�"+v1+"�")
                          (v0+"�"+v1+"�")
                          (v0+"�"+v1+"�")
                          (v0+"�"+v1+"�")
                          Neut
                          Inanimate ;
  mkN057a : Str -> N ;
  mkN057a base = let v0 = tk 4 base
                 in mkNoun (v0+"����")
                           (v0+"����")
                           (v0+"����")
                           (v0+"����")
                           Neut
                           Inanimate ;
  mkN058 : Str -> N ;
  mkN058 base = let v0 = tk 3 base
                in mkNoun (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          Neut
                          Inanimate ;
  mkN059 : Str -> N ;
  mkN059 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"���")
                          (v0+"���")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN060 : Str -> N ;
  mkN060 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"���")
                          (v0+"���")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN061 : Str -> N ;
  mkN061 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN062 : Str -> N ;
  mkN062 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN063 : Str -> N ;
  mkN063 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          Neut
                          Inanimate ;
  mkN064 : Str -> N ;
  mkN064 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          Neut
                          Inanimate ;
  mkN065 : Str -> N ;
  mkN065 base = let v0 = base
                in mkNoun (v0)
                          (v0+"��")
                          (v0+"��")
                          (v0)
                          Neut
                          Inanimate ;
  mkN066 : Str -> N ;
  mkN066 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN067 : Str -> N ;
  mkN067 base = let v0 = tk 2 base
                in mkNoun (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          Neut
                          Inanimate ;
  mkN068 : Str -> N ;
  mkN068 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN069 : Str -> N ;
  mkN069 base = let v0 = base
                in mkNoun (v0)
                          (v0+"��")
                          (v0+"��")
                          (v0)
                          Neut
                          Inanimate ;
  mkN070 : Str -> N ;
  mkN070 base = let v0 = base
                in mkNoun (v0)
                          (v0+"��")
                          (v0+"��")
                          (v0)
                          Neut
                          Inanimate ;
  mkN071 : Str -> N ;
  mkN071 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN072 : Str -> N ;
  mkN072 base = let v0 = tk 1 base
                in mkNoun (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          Neut
                          Inanimate ;
  mkN073 : Str -> N ;
  mkN073 base = let v0 = base
                in mkNoun (v0)
                          (v0+"��")
                          (v0+"��")
                          (v0)
                          Neut
                          Inanimate ;
  mkN074 : Str -> N ;
  mkN074 base = let v0 = tk 1 base
                in mkNoun (v0+"-")
                          (v0)
                          (v0)
                          (v0+"-")
                          Neut
                          Inanimate ;
  mkN075 : Str -> N ;
  mkN075 base = let v0 = tk 1 base
                in mkNoun (v0+"-")
                          (v0)
                          (v0)
                          (v0+"-")
                          Neut
                          Inanimate ;
  mkA076 : Str -> A ;
  mkA076 base = let v0 = base
                in mkAdjective (v0)
                               (v0+"��")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���") ;
  mkA077 : Str -> A ;
  mkA077 base = let v0 = base
                in mkAdjective (v0)
                               (v0+"��")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���") ;
  mkA078 : Str -> A ;
  mkA078 base = let v0 = tk 1 base
                in adjAdv (mkAdjective (v0+"�")
                                       (v0+"��")
                                       (v0+"���")
                                       (v0+"�")
                                       (v0+"���")
                                       (v0+"�")
                                       (v0+"���")
                                       (v0+"�")
                                       (v0+"���")) (v0+"�") ;
  mkA079 : Str -> A ;
  mkA079 base = let v0 = tk 2 base
                in mkAdjective (v0+"��")
                               (v0+"���")
                               (v0+"����")
                               (v0+"��")
                               (v0+"����")
                               (v0+"��")
                               (v0+"����")
                               (v0+"��")
                               (v0+"����") ;
  mkA080 : Str -> A ;
  mkA080 base = let v0 = tk 2 base;
                    v1 = last (base)
                in mkAdjective (v0+"�"+v1)
                               (v0+v1+"��")
                               (v0+v1+"���")
                               (v0+v1+"�")
                               (v0+v1+"���")
                               (v0+v1+"�")
                               (v0+v1+"���")
                               (v0+v1+"�")
                               (v0+v1+"���") ;
  mkA081 : Str -> A ;
  mkA081 base = let v0 = tk 2 base;
                    v1 = last (base)
                in mkAdjective (v0+"�"+v1)
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"���")
                               (v0+"�"+v1+"�")
                               (v0+"�"+v1+"���")
                               (v0+"�"+v1+"�")
                               (v0+"�"+v1+"���")
                               (v0+"�"+v1+"�")
                               (v0+"�"+v1+"���") ;
  mkA082 : Str -> A ;
  mkA082 base = let v0 = tk 3 base;
                    v1 = last (base)
                in mkAdjective (v0+"��"+v1)
                               (v0+"��"+v1+"��")
                               (v0+"��"+v1+"���")
                               (v0+"��"+v1+"�")
                               (v0+"��"+v1+"���")
                               (v0+"��"+v1+"�")
                               (v0+"��"+v1+"���")
                               (v0+"��"+v1+"�")
                               (v0+"��"+v1+"���") ;
  mkA082a : Str -> A ;
  mkA082a base = let v0 = tk 5 base
                 in mkAdjective (v0+"�����")
                                (v0+"������")
                                (v0+"�������")
                                (v0+"�����")
                                (v0+"�������")
                                (v0+"�����")
                                (v0+"�������")
                                (v0+"�����")
                                (v0+"�������") ;
  mkA083 : Str -> A ;
  mkA083 base = let v0 = tk 4 base;
                    v1 = last (tk 2 base)
                in mkAdjective (v0+"�"+v1+"��")
                               (v0+"�"+v1+"���")
                               (v0+"�"+v1+"����")
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"����")
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"����")
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"����") ;
  mkA084 : Str -> A ;
  mkA084 base = let v0 = tk 4 base;
                    v1 = last (tk 2 base)
                in mkAdjective (v0+"�"+v1+"��")
                               (v0+"�"+v1+"���")
                               (v0+"�"+v1+"����")
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"����")
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"����")
                               (v0+"�"+v1+"��")
                               (v0+"�"+v1+"����") ;
  mkA084a : Str -> A ;
  mkA084a base = let v0 = tk 5 base
                 in mkAdjective (v0+"�����")
                                (v0+"������")
                                (v0+"�������")
                                (v0+"�����")
                                (v0+"�������")
                                (v0+"�����")
                                (v0+"�������")
                                (v0+"�����")
                                (v0+"�������") ;
  mkA085 : Str -> A ;
  mkA085 base = let v0 = tk 2 base
                in mkAdjective (v0+"��")
                               (v0+"����")
                               (v0+"�����")
                               (v0+"���")
                               (v0+"�����")
                               (v0+"���")
                               (v0+"�����")
                               (v0+"���")
                               (v0+"�����") ;
  mkA086 : Str -> A ;
  mkA086 base = let v0 = base
                in mkAdjective (v0)
                               (v0+"��")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"��")
                               (v0+"����")
                               (v0+"�")
                               (v0+"���") ;
  mkA087 : Str -> A ;
  mkA087 base = let v0 = tk 1 base
                in mkAdjective (v0+"�")
                               (v0+"��")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���") ;
  mkA088 : Str -> A ;
  mkA088 base = let v0 = tk 1 base
                in mkAdjective (v0+"�")
                               (v0+"��")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���")
                               (v0+"�")
                               (v0+"���") ;
  mkA089 : Str -> A ;
  mkA089 base = let v0 = tk 1 base
                in mkAdjective (v0+"-")
                               (v0+"��")
                               (v0+"���")
                               (v0+"-")
                               (v0+"���")
                               (v0+"-")
                               (v0+"���")
                               (v0+"-")
                               (v0+"���") ;
  mkA089a : Str -> A ;
  mkA089a base = let v0 = base
                 in mkAdjective (v0)
                                (v0)
                                (v0)
                                (v0)
                                (v0)
                                (v0)
                                (v0)
                                (v0)
                                (v0) ;
  mkV142 : Str -> VTable ;
  mkV142 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"�")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"-")
                          (v0+"����") ;
  mkV143 : Str -> VTable ;
  mkV143 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"��")
                          (v0+"����")
                          (v0+"��")
                          (v0+"����")
                          (v0+"-")
                          (v0+"����")
                          (v0+"���") ;
  mkV144 : Str -> VTable ;
  mkV144 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"-")
                          (v0+"-") ;
  mkV145 : Str -> VTable ;
  mkV145 base = let v0 = tk 2 base;
                    v1 = last (tk 1 base)
                in mkVerb (v0+v1+"�")
                          (v0+v1+"�")
                          (v0+v1+"��")
                          (v0+v1+"��")
                          (v0+"�")
                          (v0+v1+"��")
                          (v0+v1+"��")
                          (v0+v1+"��")
                          (v0+v1+"�") ;
  mkV145a : Str -> VTable ;
  mkV145a base = let v0 = tk 3 base;
                     v1 = last (tk 2 base)
                 in mkVerb (v0+v1+"��")
                           (v0+v1+"��")
                           (v0+v1+"���")
                           (v0+v1+"���")
                           (v0+v1+"���")
                           (v0+v1+"���")
                           (v0+v1+"���")
                           (v0+v1+"���")
                           (v0+v1+"��") ;
  mkV145b : Str -> VTable ;
  mkV145b base = let v0 = tk 2 base
                 in mkVerb (v0+"��")
                           (v0+"��")
                           (v0+"���")
                           (v0+"���")
                           (v0+"��")
                           (v0+"���")
                           (v0+"-")
                           (v0+"���")
                           (v0+"��") ;
  mkV146 : Str -> VTable ;
  mkV146 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"-")
                          (v0+"��") ;
  mkV146a : Str -> VTable ;
  mkV146a base = let v0 = tk 3 base
                 in mkVerb (v0+"���")
                           (v0+"���")
                           (v0+"����")
                           (v0+"����")
                           (v0+"���")
                           (v0+"����")
                           (v0+"-")
                           (v0+"-")
                           (v0+"���") ;
  mkV147 : Str -> VTable ;
  mkV147 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"-")
                          (v0+"-")
                          (v0+"��") ;
  mkV148 : Str -> VTable ;
  mkV148 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"��") ;
  mkV149 : Str -> VTable ;
  mkV149 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"-")
                          (v0+"���") ;
  mkV150 : Str -> VTable ;
  mkV150 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"�") ;
  mkV150a : Str -> VTable ;
  mkV150a base = let v0 = tk 1 base
                 in mkVerb (v0+"�")
                           (v0+"�")
                           (v0+"��")
                           (v0+"��")
                           (v0+"��")
                           (v0+"��")
                           (v0+"-")
                           (v0+"-")
                           (v0+"�") ;
  mkV151 : Str -> VTable ;
  mkV151 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV152 : Str -> VTable ;
  mkV152 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"�") ;
  mkV152a : Str -> VTable ;
  mkV152a base = let v0 = tk 4 base
                 in mkVerb (v0+"����")
                           (v0+"����")
                           (v0+"�����")
                           (v0+"�����")
                           (v0+"�����")
                           (v0+"�����")
                           (v0+"�����")
                           (v0+"-")
                           (v0+"����") ;
  mkV153 : Str -> VTable ;
  mkV153 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"-")
                          (v0+"���") ;
  mkV154 : Str -> VTable ;
  mkV154 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV155 : Str -> VTable ;
  mkV155 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"���")
                          (v0+"��") ;
  mkV156 : Str -> VTable ;
  mkV156 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"��") ;
  mkV157 : Str -> VTable ;
  mkV157 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"���") ;
  mkV158 : Str -> VTable ;
  mkV158 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"��") ;
  mkV159 : Str -> VTable ;
  mkV159 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"��") ;
  mkV160 : Str -> VTable ;
  mkV160 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"��")
                          (v0+"���")
                          (v0+"��")
                          (v0+"���")
                          (v0+"��") ;
  mkV160a : Str -> VTable ;
  mkV160a base = let v0 = tk 2 base
                 in mkVerb (v0+"��")
                           (v0+"��")
                           (v0+"��")
                           (v0+"���")
                           (v0+"��")
                           (v0+"���")
                           (v0+"��")
                           (v0+"���")
                           (v0+"��") ;
  mkV161 : Str -> VTable ;
  mkV161 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"�")
                          (v0+"��")
                          (v0+"�")
                          (v0+"��")
                          (v0+"�") ;
  mkV161a : Str -> VTable ;
  mkV161a base = let v0 = tk 1 base
                 in mkVerb (v0+"�")
                           (v0+"�")
                           (v0+"�")
                           (v0+"��")
                           (v0+"�")
                           (v0+"��")
                           (v0+"�")
                           (v0+"��")
                           (v0+"�") ;
  mkV162 : Str -> VTable ;
  mkV162 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          (v0+"�") ;
  mkV163 : Str -> VTable ;
  mkV163 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"�")
                          (v0+"��")
                          (v0+"�")
                          (v0+"��")
                          (v0+"�") ;
  mkV164 : Str -> VTable ;
  mkV164 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"��")
                          (v0+"���")
                          (v0+"��")
                          (v0+"���")
                          (v0+"��") ;
  mkV165 : Str -> VTable ;
  mkV165 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          (v0+"�") ;
  mkV166 : Str -> VTable ;
  mkV166 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"���")
                          (v0+"-") ;
  mkV167 : Str -> VTable ;
  mkV167 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"��") ;
  mkV168 : Str -> VTable ;
  mkV168 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"�")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"�") ;
  mkV169 : Str -> VTable ;
  mkV169 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"�")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"�") ;
  mkV170 : Str -> VTable ;
  mkV170 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���") ;
  mkV171 : Str -> VTable ;
  mkV171 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"�")
                          (v0+"���")
                          (v0+"�")
                          (v0+"���")
                          (v0+"�")
                          (v0+"-")
                          (v0+"��") ;
  mkV172 : Str -> VTable ;
  mkV172 base = let v0 = tk 4 base
                in mkVerb (v0+"����")
                          (v0+"����")
                          (v0+"���")
                          (v0+"�����")
                          (v0+"���")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"����") ;
  mkV173 : Str -> VTable ;
  mkV173 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV174 : Str -> VTable ;
  mkV174 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV175 : Str -> VTable ;
  mkV175 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV176 : Str -> VTable ;
  mkV176 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV177 : Str -> VTable ;
  mkV177 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"�") ;
  mkV178 : Str -> VTable ;
  mkV178 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          (v0+"�") ;
  mkV179 : Str -> VTable ;
  mkV179 base = let v0 = tk 4 base
                in mkVerb (v0+"����")
                          (v0+"����")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"�����")
                          (v0+"���") ;
  mkV180 : Str -> VTable ;
  mkV180 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          (v0+"�") ;
  mkV181 : Str -> VTable ;
  mkV181 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"��")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"-")
                          (v0+"�") ;
  mkV182 : Str -> VTable ;
  mkV182 base = let v0 = tk 1 base
                in mkVerb (v0+"�")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"-")
                          (v0+"��")
                          (v0+"�") ;
  mkV183 : Str -> VTable ;
  mkV183 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"����")
                          (v0+"���") ;
  mkV184 : Str -> VTable ;
  mkV184 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���") ;
  mkV185 : Str -> VTable ;
  mkV185 base = let v0 = tk 3 base
                in mkVerb (v0+"���")
                          (v0+"���")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���")
                          (v0+"����")
                          (v0+"���") ;
  mkV186 : Str -> VTable ;
  mkV186 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��") ;
  mkV187 : Str -> VTable ;
  mkV187 base = let v0 = tk 2 base
                in mkVerb (v0+"��")
                          (v0+"�")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��")
                          (v0+"��") ;

  adjAdv : A -> Str -> A =
    \a,adv -> {s = a.s; adv = adv; lock_A=<>} ;
}