[library(sgml)].
load(Tree) :-
    load_xml_file('lewis/lewis.xml',Tree).

find_element(Name,[element(Name,Attrs,Kinder)|_],element(Name,Attrs,Kinder)).
find_element(Name,[element(_,_,Kinder)|_],Element) :-
    find_element(Name,Kinder,Element).
find_element(Name,[_|T],Element) :-
    find_element(Name,T,Element).

find_attr_value(Name,[Name=Value|_],Value).
find_attr_value(Name,[_|T],Value) :-
    find_attr_value(Name,T,Value).

%transform(Element,_Trans) :-
%    Element = element(_Name,Attrs,_Kinder),
%    find_attr_value(gramGrp,Attrs,Grammatik),

%get_word_type(pos('adj.'),'Adjective').
%
%get_word_type(pos('adv.'),'Adverb').
%
%get_word_type([itype(I),gen(G)], 'Noun') :-
%    member(G,[m, f, n]).
%
%get_word_type(itype(
    
        
get_all_entries(Tree,Elements) :-
    bagof(Es,find_element(entry,Tree,Es),Elements).

write_all_entries(Tree) :-
    tell('plain.txt'),
    loop_entries(Tree).

loop_entries(Tree) :-
    find_element(entry,Tree,E),
 %   transform(E,TE),
    write(E),
    nl,
    fail.

loop_entries(_) :-
    told.
