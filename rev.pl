:- use_module(utils).
:- use_module(parser).

:- use_module(library(tokenize)).

:- dynamic(vars/1).
:- dynamic(rule/3).
:- dynamic(fun/1).
:- dynamic(fresh_vars/1).


parse(FT) :- 
  tokenize_file('example.trs',Tokens,[cased(true),spaces(false),to(strings)]),
  lists:subtract(Tokens,[cntrl("\n")],CleanToks),
  %write(CleanToks). % for tokenizer debugging
  phrase(program(T),CleanToks),
  vars(T,Vs),
  funs(T,Fs),
  post(T,Vs,Fs,PT),
  pretty(PT),
  flatten_ctrs(PT,FT),
  pretty(FT).%,
  % convert to basic c-DCTRS,
  %pretty(CT),
  
assertTRS(ctrs(_,R)) :-
  R = rules(Rs),
%  assertVars(V),
  assertRules(Rs).

assertVars(V) :- assertz(V).

assertRules([]).
assertRules([R|Rs]) :-
  assertz(R),
  assertRules(Rs).

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

flatten_ctrs(ctrs(V,rules(R)),ctrs(V,rules(R2))) :-
  flatten_rules(R,R2).

flatten_rules([],[]).
flatten_rules([R|Rs],[R2|Rs2]) :-
  flatten_rule(R,R2),
  flatten_rules(Rs,Rs2).

flatten_rule(rule(B,L,R,C),rule(B,L,R2,C3)) :-
  flatten_rhs(R,R2,NewCs),
  append(C,NewCs,C2),
  flatten_conds(C2,C3).

flatten_rhs(T,T2,Cs) :-
  flatten_top(T,T2,Cs).

flatten_top(T,T,[]) :-
  T = fun(_,_),
  is_basic(T).
flatten_top(T,T,[]) :-
  T = cons(_,_),
  is_cons(T).
flatten_top(T,T,[]) :-
  T = var(_,_),
  is_cons(T).
flatten_top(T,T2,Cs) :-  
  T = fun(N,Ts),
  \+ is_basic(T),
  flatten_bot(Ts,Ts2,Cs),
  T2 = fun(N,Ts2).
flatten_top(T,T2,Cs) :-  
  T = cons(N,Ts),
  \+ is_cons(T),
  flatten_bot(Ts,Ts2,Cs),
  T2 = cons(N,Ts2).


flatten_bot([],[],[]).
flatten_bot([T|Ts],[T|Ts2],Cs) :-
  is_cons(T),
  flatten_bot(Ts,Ts2,Cs).
flatten_bot([T|Ts],[T2|Ts2],[C|Cs2]) :-
  \+ is_cons(T),
  flatten_bot(T,T2,C),
  flatten_bot(Ts,Ts2,Cs2).
flatten_bot(T,T2,C) :-
  T = fun(_,_),
  \+ is_cons(T),
  fresh_var(T2),
  C = cond(T,T2).
flatten_bot(T,T2,C) :-
  T = cons(_,_),
  \+ is_cons(T),
  fresh_var(T2),
  C = cond(T,T2).
flatten_bot(T,T,[]) :-
  T = var(_,_).

inj_ctrs(ctrs(V,R),ctrs(V,R2)) :-
  inj_rules(R,R2).

inj_rules([],[]).
inj_rules([R|Rs],[R2,Rs2]) :-
  inj_rule(R,R2),
  inj_rules(Rs,Rs2).

inj_rule(rule(B,L,R,C),rule(B,L,R2,C2)) :-
  erased_vars(L,R,C,EVars),
  inj_conds(C,C2,NVars),
  inj_rhs(R,B,EVars,NVars,R2).

inj_conds([],[],[]).
inj_conds([C|Cs],[C2|Cs2],[V|Vs]) :-
  inj_cond(C,C2,V),
  inj_conds(Cs,Cs2,Vs).

inj_cond(cond(L,R),cond(L,tuple(R,Var)),Var) :-
  fresh_var(Var).

inj_rhs(R,beta(N),EVars,NVars,tuple(R,cons(Label,Vars))) :-
  number_string(N,NStr),
  string_concat("B_",NStr,Label),
  append(EVars,NVars,Vars).
  
erased_vars(L,R,C,EVars) :-
  erased_lhs_vars(L,R,C,ELVars),
  erased_cond_vars(R,C,ECVars).
  append(ELVars,ECVars,EVars).

erased_lhs_vars(L,R,C,ELVars) :-
  vars_from(L,VarsL),
  vars_from(R,VarsR),
  vars_from_ls(C,VarsC),
  append(VarsR,VarsC,VarsRC),
  subtract(VarsL,VarsRC,ELVars).

erased_cond_vars(R,C,ECVars) :-
  vars_next_array(C,SVars),
  vars_from(R,RVars),
  append(SVars,RVars,SRVars),
  reverse(SRVars,RSVars),
  erased_cond_lhs(C,RSVars,ECVars).

vars_next_array([],[]).
vars_next_array([C|Cs],Vs) :-
  vars_array(Cs,[],Vs).
  
vars_array([],_,[]).
vars_array([cond(_,R)|Cs],AccVars,[NAccVars|NextVars]).
  vars_from(R,RVars),
  append(AccVars,RVars,NAccVars),
  vars_array(Cs,NAccVars,NextVars).

erased_cond_lhs([],[]).
erased_cond_lhs([cond(L,_)|Cs],[RVars|NRVars],[EVars|NEVars]) :-
  vars_from(L,LVars),
  substract(LVars,RVars,EVars),
  erased_cond_lhs(Cs,NRVars,NEVars).

fresh_var(Var) :-
  \+ fresh_vars(_),
  Nvar = "X_0",
  Var = var(Nvar,[]),
  assertz(fresh_vars([Nvar])).

fresh_var(Var) :-
  fresh_vars(Ls),
  last(Ls,NLastVar),
  split_fresh(NLastVar,NStr),
  number_string(N,NStr),
  N1 is N + 1,
  number_string(N1,N1Str),
  split_fresh(NNewVar,N1Str),
  Var = var(NNewVar,[]),
  append(Ls,[NNewVar],NewLs),
  retract(fresh_vars(_)),
  assertz(fresh_vars(NewLs)).

split_fresh(Str,N) :-
  string_concat("X_",N,Str).

flatten_conds([],[]).
flatten_conds([C|Cs],Cs4) :-
  flatten_cond(C,C2,NewCs),
  flatten_conds(NewCs,NewCs2),
  flatten_conds(Cs,Cs3),
  append(NewCs2,[C2],NewCs3),
  append(NewCs3,Cs3,Cs4).

flatten_cond(cond(X,Y),cond(X2,Y2),Cs) :-
  flatten_top(X,X2,NewCs),
  flatten_top(Y,Y2,NewCs2),
  append(NewCs,NewCs2,Cs).

is_basic(fun(_,Ts)) :-
  is_cons_list(Ts).

is_cons_list([]).
is_cons_list([T|Ts]) :-
  is_cons(T),
  is_cons_list(Ts).

is_cons(var(_,_)).
is_cons(cons(_,[])).
is_cons(cons(_,[T|Ts])) :-
  is_cons_list([T|Ts]).
