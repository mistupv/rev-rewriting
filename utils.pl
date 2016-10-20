:- module(utils,
         [pretty/1,
          writeRules/1]).
  
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

pretty(ctrs(_,R)) :-
  pretty(R),
  nl.
pretty(rules(Rs)) :-
  pretty(Rs).
pretty([]).
pretty([R|Rs]) :-
  pretty(R),
  pretty(Rs).
pretty(rule(B,L,R,C)) :-
  pretty(B),
  format(" : "),
  pretty(L),
  format(" -> "),
  pretty(R),
  pretty_conds(C),
  nl.
pretty(beta(N)) :-
  format("B_~d",[N]).
pretty(cond(L,R)) :-
  pretty(L),
  format(" ->> "),
  pretty(R).
pretty(fun(N,[])) :-
  format("~s()",[N]).
pretty(fun(N,[T|Ts])) :-
  format("~s(",[N]),
  pretty_args([T|Ts]),
  format(")").
pretty(cons(N,[])) :-
  format("~s",[N]).
pretty(cons(N,[T|Ts])) :-
  format("~s(",[N]),
  pretty_args([T|Ts]),
  format(")").
pretty(var(N,_)) :-
  format("~s",[N]).
pretty(TupleArgs) :-
  TupleArgs =.. [tuple|Args],
  format("<"),
  pretty_args(Args),
  format(">").

pretty_args([]).
pretty_args([A|As]) :-
  pretty(A),
  pretty_commas(As).

pretty_commas([]).
pretty_commas([A|As]) :-
  format(", "),
  pretty(A),
  pretty_commas(As).

pretty_conds([]).
pretty_conds([C|Cs]) :-
  format(" <= "),
  pretty_args([C|Cs]).
