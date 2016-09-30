:- module(parser,
         [program/3]).

:- use_module(library(dcg/basics)).
:- use_module(library(tokenize)).

program(X) -->
  decl_ast(Y),
  {X =.. [ctrs|Y]}.

decl_ast([]) --> [].
decl_ast([H|T]) -->
  decl(H),
  decl_ast(T).

decl(X) -->
  [punct('(')],
  [word('VAR')],
  id_ast(Y),
  [punct(')')],
  {X =.. [vars|Y]}.
decl(X) -->
  [punct('(')],
  [word('RULES')],
  rule_ast(Y),
  [punct(')')],
  {X =.. [rules|Y]}.
id_ast([]) --> [].
id_ast([H|T]) --> 
  id(H),
  id_ast(T).

id(X) -->
  [word(X)].

%decl --> ('VAR',id_ast); ('THEORY',thdecl_ast); ('RULES',rule);
%         ('STRATEGY',strategydecl); (id,anylist_opt).

condlist(X) -->
  cond(H),
  cond_ast(T),
  {X =.. [conds|[H|T]]}.

cond_ast([]) --> [].
cond_ast([H|T]) --> 
  [punct(',')],
  cond(H),
  cond_ast(T).

cond(cond(X,Y)) --> 
  term(X),
  [punct('-'),punct('>')],
  term(Y).
cond(cond(X,Y)) --> 
  term(X),
  [punct('-'),punct('>'),punct('<'),punct('-')],
  term(Y).

rule_ast([]) --> [].
rule_ast([H|T]) --> rule(H),rule_ast(T).

rule(rule(X,Y,conds())) -->
  term(X),
  [punct('-')],
  [punct('>')],
  term(Y).

rule(rule(X,Y,Z)) -->
  term(X),
  [punct('-')],
  [punct('>')],
  term(Y),
  [punct('|')],
  condlist(Z).

term(X) --> id(X).
term(X) -->
  id(X),
  [punct('(')],
  [punct(')')].
term(X) -->
  id(H),
  [punct('(')],
  termlist(T),
  [punct(')')],
  {X =.. [H|T]}.

termlist([H|T]) -->
  term(H),
  term_ast(T).

term_ast([]) --> [].
term_ast([H|T]) -->
  [punct(',')],
  term(H),
  term_ast(T).
%
%anylist_opt --> []; anylist.
%anylist_ast --> []; (',',anylist,anylist_ast).
%anylist --> any,anylist_ast.
%any --> id; string; ('(',anylist,')').
%thdecl --> id_ast; ('EQUATIONS',equation_ast).
%equation_ast --> []; (equation, equation_ast).
%thdecl_ast --> []; (thdecl,thdecl_ast).
%equation --> (term,'==',term).
%stratedecl --> 'INNERMOST'; ('CONTEXTSENSITIVE',replacements_ast).
%replacements_ast --> []; (replacement,replacements_ast).
%replacement --> '(',id,int_ast,')'.
%int_ast --> []; (int,int_ast).
%
%
