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
%  assertTRS(PT).
%  prettyTRS(X),
%  assertTRS(X).
  
assertTRS(ctrs(_,R)) :-
  R = rules(Rs),
%  assertVars(V),
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
funs([rule(_,term(F,_),_,_)|Rs],[F|Fs]) :-
  funs(Rs,Fs).

% post/4
post([],_,_,[]).
post(ctrs(X,Y),Vs,Fs,ctrs(X,Y2)) :-
  post(Y,Vs,Fs,Y2).
post(rules(X),Vs,Fs,rules(X2)) :-
  post(X,Vs,Fs,X2,1).
post([R|Rs],Vs,Fs,[R2|Rs2]) :-
  post(R,Vs,Fs,R2),
  post(Rs,Vs,Fs,Rs2).
post(term(X,Y),Vs,Fs,var(X,Z)) :-
  member(X,Vs),
  post(Y,Vs,Fs,Z).
post(term(X,Y),Vs,Fs,fun(X,Z)) :-
  member(X,Fs),
  post(Y,Vs,Fs,Z).
post(term(X,Y),Vs,Fs,cons(X,Z)) :-
  \+ member(X,Vs),
  \+ member(X,Fs),
  post(Y,Vs,Fs,Z).
post(cond(X,Y),Vs,Fs,cond(X2,Y2)) :-
  post(X,Vs,Fs,X2),
  post(Y,Vs,Fs,Y2).

% post/5
post([],_,_,[],_).
post(beta(void),_,_,beta(N),N).
post([R|Rs],Vs,Fs,[R2|Rs2],N1) :-
  N2 is N1 + 1,
  post(R,Vs,Fs,R2,N1),
  post(Rs,Vs,Fs,Rs2,N2).
post(rule(B,X,Y,Z),Vs,Fs,rule(B2,X2,Y2,Z2),N) :-
  post(X,Vs,Fs,X2),
  post(Y,Vs,Fs,Y2),
  post(Z,Vs,Fs,Z2),
  post(B,Vs,Fs,B2,N).

%flatten(Rule,Flatrule) :-
%  \+ is_flat(Rule),
%  flatten_rule(Rule,Flatrule).
%
%flatten(Rule,Rule) :-
%  is_flat(Rule).

%is_flat(rule(_,_,R,C)) :-
%  (is_basic(R);is_cons(R)),

%flatten_rule(rule(B,L,R,C),rule(B,L2,R2,C2)) :-
%  flatten_

is_basic(rule(_,_,R,C)) :-
  is_basic(R),
  is_basic(C).
is_basic(cond(L,R)) :-
  is_basic(L),
  is_basic(R).
is_basic(fun(_,Ts)) :-
  is_cons(Ts).
is_basic(cons(_,Ts)) :-
  is_cons(Ts).
is_basic(var(_,_)).

is_cons([]).
is_cons([T|Ts]) :-
  is_cons(T),
  is_cons(Ts).
is_cons(cons(_,[])).
is_cons(cons(_,Ts)) :-
  is_cons(Ts).
is_cons(var(_,_)).
