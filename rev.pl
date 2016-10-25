:- use_module(library(tokenize)).

:- use_module(utils).
:- use_module(parser).
:- use_module(trs).

:- dynamic(fresh_vars/1).


%% fscd(filename)
%% fscd is the main rule of this package
%% filename must be an atom containing the name of a .trs file
%% fscd performs the following computations:
%%   * extracts the list of tokens (Tokens) from the file
%%     (with help from tokenizer.pl)
%%   * removes unwanted tokens from Tokens (CleanTokens)
%%   * generates the data structure (T, a CTRS) by parsing
%%      (phrase) the list of tokens with the DCG specified in parser.pl
%%   * performs a post-processing of the parsed structured, labeling
%%      terms as defined symbols, constructors or variables (PT)
%%   * applies a flattening step to PT so that the DCTRS becomes a
%%     basic DCTRS (more details at "flatten_ctrs" rule)
%%   * applies a normalization step to FT so that the basic DCTRS  
%%     becomes a basic c-DCTRS (more details at "cons_ctrs" rule)
%%   * performs the injectivization transformation, which embeds the
%%     history of computation into the rules on the system
%%   * executes the inversion transformation, resulting in a system that
%%     performs backward computation steps w.r.t. the injectivized one
%%
%% the resulting systems are (pretty-)printed at each step

fscd(File) :- 
  tokenize_file(File,Tokens,[cased(true),spaces(false),to(strings)]),
  lists:subtract(Tokens,[cntrl("\n")],CleanToks),
  %write(CleanToks). % for tokenizer debugging
  phrase(program(T),CleanToks),
  vars_ctrs(T,Vs),
  funs_ctrs(T,Fs),
  post(T,Vs,Fs,PT),
  is_3ctrs(PT),
  is_cons_ctrs(PT),
  is_dctrs(PT),
  pretty(PT),
  format("Flattened TRS:"),nl,
  flatten_ctrs(PT,FT),
  pretty(FT),
  format("Constructor TRS:"),nl,
  cons_ctrs(FT,CT),
  pretty(CT),
  format("Injectivized TRS:"),nl,
  inj_ctrs(CT,InjT),
  pretty(InjT),
  format("Inverted TRS:"),nl,
  inv_ctrs(InjT,InvT),
  pretty(InvT).

assertTRS(ctrs(_,R)) :-
  R = rules(Rs),
%  assertVars(V),
  assertRules(Rs).

assertVars(V) :- assertz(V).

assertRules([]).
assertRules([R|Rs]) :-
  assertz(R),
  assertRules(Rs).

vars_ctrs(ctrs(vars(Vs),_),Vs).

funs_ctrs(ctrs(_,rules(Rs)),Fs) :-
  funs_ctrs(Rs,Ls),
  list_to_set(Ls,Fs).
funs_ctrs([],[]).
funs_ctrs([rule(_,term(F,_),_,_)|Rs],[F|Fs]) :-
  funs_ctrs(Rs,Fs).

%% post(in_trs,[var_name],[sym_name],out_trs)
%% performs the post-processing of a CTRS
%% var_name and sym_name are the defined variables and function symbols
%% these are used to correctly label terms as variables, functions or
%% (else) constructors

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

%% post(in_rule,[var_name],[sym_name],out_rule,integer)
%% same as post/4, but limits its application to rules
%% this allows us to label the system rules (beta)

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

%% flatten_ctrs(input_trs,output_trs)
%% applies a flattening step to a given CTRS

flatten_ctrs(ctrs(V,rules(R)),ctrs(V,rules(R2))) :-
  flatten_rules(R,R2).

flatten_rules([],[]).
flatten_rules([R|Rs],[R2|Rs2]) :-
  flatten_rule(R,R2),
  flatten_rules(Rs,Rs2).

% new conditions from flattening the rhs of the
% rule are appended to the rest of conditions
flatten_rule(rule(B,L,R,C),rule(B,L,R2,C3)) :-
  flatten_rhs(R,R2,NewCs),
  append(C,NewCs,C2),
  flatten_conds(C2,C3).

flatten_rhs(T,T2,Cs) :-
  flatten_top(T,T2,Cs).

%% flatten_top(in_exp,out_exp,out_conds)
%% starts the flattening of an expression and returns
%% the resulting expression and conditions
%% the expression should be flattened only if needed

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

%% flatten_bot(in_exp,out_exp,out_conds)
%% applies a flattening step on the arguments of an expression
%% this way, non-flattened expression will be replaced variables
%% as soon as they are found (i.e., we don't go deeper in the
%% expression)

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

%% flatten_conds(in_conds,out_conds)
%% when flattening a set of conditions, the new conditions
%% must be inserted before the generating conditions, and
%% these new conditions should be flattened as well

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


%% cons_ctrs(in_trs,out_trs)
%% applies a normalization step to a CTRS,
%% converting a basic CTRS into a basic c-CTRS
%% this ensures that lhs of the conditions are basic

cons_ctrs(ctrs(V,rules(R)),ctrs(V,rules(R2))) :-
  cons_rules(R,R2).

cons_rules([],[]).
cons_rules([R|Rs],[R2|Rs2]) :-
  cons_rule(R,R2,success),!,
  cons_rules(Rs,Rs2).
cons_rules([R|Rs],Rs2) :-
  cons_rule(R,_,failure),
  cons_rules(Rs,Rs2).

% For each condition with a nonbasic term on the
% lhs of the condition, we try to unify both parts
% of the condition and:
%   * if we fail, we remove the whole rule
%   * if we are succesful, we remove the condition
%     and apply the mgu to the rest of the rule
cons_rule(rule(B,L,R,C),rule(B,L,R,C),success) :-
  replace_conds(C,C,success([])).
cons_rule(rule(B,L,R,C),rule(B,L3,R3,C4),Res2) :-
  replace_conds(C,C2,success(Subs)),
  substitute(Subs,L,L2),
  substitute(Subs,R,R2),
  substitute_conds(Subs,C2,C3),
  cons_rule(rule(B,L2,R2,C3),rule(B,L3,R3,C4),Res2).
cons_rule(rule(_,_,_,C),_,failure) :-
  replace_conds(C,_,failure).

replace_conds([],[],success([])).
replace_conds([cond(L,R)|Cs],[cond(L,R)|Cs2],Res) :-
  is_basic(L),
%  is_cons(R),
  replace_conds(Cs,Cs2,Res).

replace_conds([cond(L,R)|_],_,failure) :-
  \+ is_basic(L),
%  is_cons(R),
  unify([(L,R)],failure).

replace_conds([cond(L,R)|Cs],Cs,success(Subs)) :-
  \+ is_basic(L),
%  is_cons(R),
  unify([(L,R)],success(Subs)).

substitute_conds(_,[],[]).
substitute_conds(Subs,[cond(L,R)|Cs],[cond(L2,R2)|Cs2]) :-
  substitute(Subs,L,L2),
  substitute(Subs,R,R2),
  substitute_conds(Subs,Cs,Cs2).

%% inj_ctrs(in_trs,out_trs)
%% applies the injectivization transformation a basic c-DCTRS

inj_ctrs(ctrs(V,rules(R)),ctrs(V,rules(R2))) :-
  inj_rules(R,R2).

inj_rules([],[]).
inj_rules([R|Rs],[R2|Rs2]) :-
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
  erased_cond_vars(R,C,ECVars),
  append(ELVars,ECVars,EVars).

erased_lhs_vars(L,R,C,ELVars) :-
  vars_from(L,VarsL),
  vars_from(R,VarsR),
  vars_from_conds(C,VarsC),
  append(VarsR,VarsC,VarsRC),
  subtract(VarsL,VarsRC,ELVars).

%% erased_cond_vars(rhs,[cond],erased_vars)
%% This method computes the erased variables from the conditions
%% in an efficient way (i.e., it doesn't compute Var(\ol{s_{i+1,n}})
%% on each condition, but only once)

erased_cond_vars(_,[],[]).
erased_cond_vars(R,C,ECVars) :-
  vars_from(R,RVars),       % Var(r)  
  vars_next_array(C,SVars), % [Var(s_2),Var(s_3),...]
  append([RVars],SVars,RSVars), % [Var(r),Var(s_2),Var(s_3),...]
  acc_vars(RSVars,[],RSMVars), % [Var(r),Var(r,s_2),Var(r,s_2,s_3),...]
  reverse(RSMVars,SRMVars), % [...,Var(r,s_2,s_3),Var(r,s_2),Var(r)]
  erased_cond_lhs(C,SRMVars,ECVars).

vars_next_array([],[]).
vars_next_array([_|Cs],Vs) :-
  vars_array(Cs,Vs).
  
vars_array([],[]).
vars_array([cond(S,_)|Cs],[SVars|Vs]) :-
  vars_from(S,SVars),
  vars_array(Cs,Vs).

acc_vars([],_,[]).
acc_vars([V|Vs],AccVars,[CurVars|NextVars]) :-
  append(V,AccVars,CurVars),
  acc_vars(Vs,CurVars,NextVars).

erased_cond_lhs([],[],[]).
erased_cond_lhs([cond(_,T)|Cs],[SRVars|NSRVars],REVars) :-
  vars_from(T,TVars),
  subtract(TVars,SRVars,EVars),
  erased_cond_lhs(Cs,NSRVars,NEVars),
  append(EVars,NEVars,REVars).

%% inv_ctrs(in_trs,out_trs)
%% applies the inversion transformation a basic c-DCTRS

inv_ctrs(ctrs(V,rules(R)),ctrs(V,rules(R2))) :-
  inv_rules(R,R2).

inv_rules([],[]).
inv_rules([R|Rs],[R2|Rs2]) :-
  inv_rule(R,R2),
  inv_rules(Rs,Rs2).

inv_rule(rule(B,L,R,C),rule(B,IL,IR,IC)) :-
  swap_equation((L,R),(IL,IR)),
  inv_conds(C,IC).

inv_conds(Cs,ICs) :-
  swap_conds(Cs,SCs),
  reverse(SCs,ICs).

swap_conds([],[]).
swap_conds([cond(L,R)|Cs],[cond(IL,IR)|Cs2]) :-
  swap_equation((L,R),(IL,IR)),
  swap_conds(Cs,Cs2).
  
swap_equation((L,R),(IL,IR)) :-
  extract_from_tuple(R,RArgs),
  push_into_args(L,LArgs,RArgs,IL),
  IR =.. [tuple|LArgs].
 
push_into_args(fun(N,OArgs),OArgs,NArgs,fun(N,NArgs)).

extract_from_tuple(tuple(T1,T2),T3) :-
  append([T1],[T2],T3).

fresh_var(Var) :-
  \+ fresh_vars(_),!,
  Nvar = "x_0",
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
  retract(fresh_vars(Ls)),
  assertz(fresh_vars(NewLs)).

split_fresh(Str,N) :-
  string_concat("x_",N,Str).

%% is_basic(exp)
%% true if expression is basic
is_basic(fun(_,Ts)) :-
  is_cons_list(Ts).

%% is_cons(exp)
%% true if expression is constructor
is_cons(var(_,_)).
is_cons(cons(_,[])).
is_cons(cons(_,[T|Ts])) :-
  is_cons_list([T|Ts]).

is_cons_list([]).
is_cons_list([T|Ts]) :-
  is_cons(T),
  is_cons_list(Ts).

