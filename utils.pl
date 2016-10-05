:- module(utils,
         [prettyTRS/1,
          writeRules/1]).

prettyTRS(ctrs(V,R)) :-
  writeln(V),
  R =.. [rules|Rs],
  writeRules(Rs).
  
writeRules([]).  
writeRules([R|Rs]) :-
  writeln(R),
  writeRules(Rs).

pos(_,[]).
pos(cons(_,X), [P|Ps]) :-
  nth1(P,X,T),
  pos(T,Ps).
pos(funs(_,X), [P|Ps]) :-
  nth1(P,X,T),
  pos(T,Ps).

