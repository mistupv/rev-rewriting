:- use_module(utils).
:- use_module(parser).

:- use_module(library(tokenize)).

parse :- 
  tokenize_file('example.trs',Tokens,[cased(true),spaces(false)]),
  lists:subtract(Tokens,[cntrl('\n')],CleanToks),
  %write(CleanToks), % for tokenizer debugging
  phrase(program(X),CleanToks),
  prettyTRS(X).
  
