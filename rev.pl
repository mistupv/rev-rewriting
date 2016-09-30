:- use_module(utils).
:- use_module(parser).

:- use_module(library(tokenize)).

:- dynamic(vars/1).
:- dynamic(rule/3).


parse :- 
  tokenize_file('example.trs',Tokens,[cased(true),spaces(false)]),
  lists:subtract(Tokens,[cntrl('\n')],CleanToks),
  %write(CleanToks), % for tokenizer debugging
  phrase(program(X),CleanToks),
  prettyTRS(X),
  assertTRS(X).
  
assertTRS(ctrs(V,R)) :-
  R =.. [rules|Rs],
  assertVars(V),
  assertRules(Rs).

assertVars(V) :- assertz(V).

assertRules([]).
assertRules([R|Rs]) :-
  assertz(R),
  assertRules(Rs).

