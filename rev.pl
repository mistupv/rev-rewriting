:- use_module(utils).
:- use_module(parser).

:- use_module(library(tokenize)).

:- dynamic(vars/1).
:- dynamic(rule/3).
:- dynamic(fun/1).


parse(PT) :- 
  tokenize_file('example.trs',Tokens,[cased(true),spaces(false),to(strings)]),
  lists:subtract(Tokens,[cntrl("\n")],CleanToks),
  %write(CleanToks). % for tokenizer debugging
  phrase(program(T),CleanToks),
  vars(T,Vs),
  funs(T,Fs),
  post(T,Vs,Fs,PT).
%  prettyTRS(X),
%  assertTRS(X).
  
assertTRS(ctrs(V,R)) :-
  R =.. [rules|Rs],
  assertVars(V),
  assertRules(Rs).

assertVars(V) :- assertz(V).

assertRules([]).
assertRules([R|Rs]) :-
  assertz(R),
  assertRules(Rs).

vars(ctrs(vars(Vs),_),Vs).

funs(ctrs(_,rules(Rs)),Fs) :-
  funs(Rs,Ls),
  list_to_set(Ls,Fs).
funs([],[]).
funs([rule(term(_),_,_)|Rs],Fs) :-
  funs(Rs,Fs).
funs([rule(term(F,_),_,_)|Rs],[F|Fs]) :-
  funs(Rs,Fs).

post([],_,_,[]).
post(ctrs(X,Y),Vs,Fs,ctrs(X,Y2)) :-
  post(Y,Vs,Fs,Y2).
post(rules(X),Vs,Fs,rules(X2)) :-
  post(X,Vs,Fs,X2).
post([R|Rs],Vs,Fs,[R2|Rs2]) :-
  post(R,Vs,Fs,R2),
  post(Rs,Vs,Fs,Rs2).
post(rule(X,Y,Z),Vs,Fs,rule(X2,Y2,Z2)) :-
  post(X,Vs,Fs,X2),
  post(Y,Vs,Fs,Y2),
  post(Z,Vs,Fs,Z2).
post(term(X),Vs,_,vars(X)) :-
  member(X,Vs).
post(term(X),Vs,_,ground(X)) :-
  \+ member(X,Vs).
post(term(X,Y),Vs,Fs,funs(X,Z)) :-
  member(X,Fs),
  post(Y,Vs,Fs,Z).
post(term(X,Y),Vs,Fs,cons(X,Z)) :-
  \+ member(X,Fs),
  post(Y,Vs,Fs,Z).
post(cond(X,Y),Vs,Fs,cond(X2,Y2)) :-
  post(X,Vs,Fs,X2),
  post(Y,Vs,Fs,Y2).
  
