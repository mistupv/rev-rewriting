:- module(trs,
         [unify/2,
          substitute/3,
          vars_from/2,
          vars_from_conds/2,
          is_3ctrs/1,
          is_cons_ctrs/1,
          is_dctrs/1]).

%% is_3ctrs(ctrs)
%% checks if ctrs is a 3-CTRS

is_3ctrs(ctrs(_,rules(R))) :-
  is_3ctrs_rules(R).

is_3ctrs_rules([]).
is_3ctrs_rules([R|Rs]) :-
  is_3ctrs_rule(R),
  is_3ctrs_rules(Rs).

is_3ctrs_rule(rule(_,L,R,C)) :-
  vars_from(L,LVars),
  vars_from(R,RVars),
  vars_from_conds(C,CVars),
  append(LVars,CVars,LCVars),
  included(RVars,LCVars).

%% is_cons_ctrs(ctrs)
%% checks if ctrs is constructor

is_cons_ctrs(ctrs(_,rules(R))) :-
  is_cons_rules(R).

is_cons_rules([]).
is_cons_rules([R|Rs]) :-
  is_cons_rule(R),
  is_cons_rules(Rs).

is_cons_rule(rule(_,L,_,_)) :-
  is_basic(L).

%% is_dctrs(ctrs)
%% checks if ctrs is deterministic

is_dctrs(ctrs(_,rules(R))) :-
  is_dctrs_rules(R).

is_dctrs_rules([]).
is_dctrs_rules([R|Rs]) :-
  is_dctrs_rule(R),
  is_dctrs_rules(Rs).

is_dctrs_rule(rule(_,L,_,C)) :-
  vars_from(L,LVars),
  is_dctrs_conds(C,LVars).

is_dctrs_conds([],_).
is_dctrs_conds([cond(L,R)|Cs],AccVars) :-
  vars_from(L,LVars),
  included(LVars,AccVars),
  vars_from(R,RVars),
  append(AccVars,RVars,NewAccVars),
  is_dctrs_conds(Cs,NewAccVars).

%% unify([equation_pair],unif_result)
%% tries to unify the equation pairs from a list
%% and returns the mgu if unification is possible

unify([],success([])).

unify([(var(N,_),var(N,_))|Rest],L) :- 
	!, unify(Rest,L).

unify([(Expr,var(N,Args))|Rest],L) :- 
  \+ Expr = var(_,_),
  !, unify([(var(N,Args),Expr)|Rest],L).

unify([(var(N,Args),Expr)|Rest],L) :- 
  !, substituteEqList((var(N,Args),Expr),Rest,Rest1),
  unify(Rest1,L1),
  compose(success([(var(N,Args),Expr)]),L1,L).

unify([(fun(N,Args),fun(N,Args1))|Rest],L) :- 
  length(Args, Len1),
  length(Args1,Len2),
  Len1 =:= Len2,
	!, zip(Args,Args1,L1),
	append(L1,Rest,L2),
	unify(L2,L).

unify([(fun(_,_),fun(_,_))|_],failure).

unify([(cons(N,Args),cons(N,Args1))|Rest],L) :-
	!, zip(Args,Args1,L1),
	append(L1,Rest,L2),
  unify(L2,L).
	
unify([(cons(_,_),cons(_,_))|_],failure).

%% compose(result1,result2,comp_result)
%% compose two unification results

compose(success(_),failure,failure).
compose(success(H),success(T),success(HT)) :-
  compose_subs(H,T,HT).


compose_subs([],S,S).
compose_subs([(X1,Y1)|Rest],Subs,[(X1,Y1subs)|L]) :- 
	substitute(Subs,Y1,Y1subs),
	compose_subs(Rest,Subs,L).

%% substitute(subs,exp,exp)
%% applies a substitution to a given expression
%% and returns the resulting expression

substitute(S,var(N,Args),Expr) :-
	memberchk((var(N,Args),Expr),S),!.

substitute(_,var(N,Args),var(N,Args)).
substitute(_,cons(F,[]),cons(F,[])) :- !.
substitute(S,cons(F,Args),cons(F,ArgsS)) :-
	substitute_argsargs(S,Args,ArgsS).

substitute(_,fun(F,[]),fun(F,[])) :- !.
substitute(S,fun(F,Args),fun(F,ArgsS)) :-
	substitute_argsargs(S,Args,ArgsS).

substitute_argsargs(_,[],[]).
substitute_argsargs(S,[A|R],[AS|RS]) :-
	substitute(S,A,AS),
	substitute_argsargs(S,R,RS).

%% substituteVar(binding,exp,exp)
%% applies a binding to a given expression
%% and returns the resulting expression

substituteVar((var(N,Args),Expr),var(N,Args),Expr) :- !.
substituteVar((var(_,_),_),var(M,Args),var(M,Args)).
substituteVar(Bind,cons(F,Args),cons(F,VArgs)) :- 
	substituteVar_args(Bind,Args,VArgs).
substituteVar(Bind,fun(F,Args),fun(F,VArgs)) :- 
	substituteVar_args(Bind,Args,VArgs).
	

substituteVar_args(_,[],[]).
substituteVar_args(Bind,[E|R],[VE|VR]) :-
	substituteVar(Bind,E,VE),
	substituteVar_args(Bind,R,VR).

%% substituteEqList(binding,[equation_pair],[equation_pair])
%% applies a binding to a list of equation pairs

substituteEqList(_,[],[]).
substituteEqList(Var,[Exp|Rest],[VExp|VRest]) :-
	substituteEq(Var,Exp,VExp),
	substituteEqList(Var,Rest,VRest).

substituteEq(Bind,(Exp1,Exp2),(BExp1,BExp2)) :-
	substituteVar(Bind,Exp1,BExp1),
	substituteVar(Bind,Exp2,BExp2).

%% vars(exp,list)
%% returns the variables in expression
%% returns [] if expression is a variable

vars(var(_,_),[]).
vars(Expr,Vs) :-
  \+ Expr = var(_,_),
  vars_in(Expr,Vs).

vars_in(var(N,_),N).
vars_in(cons(_,Args),Vs) :-
  vars_in_args(Args,Vs).
vars_in(fun(_,Args),Vs) :-
  vars_in_args(Args,Vs).

vars_in_args([],[]).
vars_in_args([A|As],[V|Vs]) :-
  vars_in(A,V),
  vars_in_args(As,Vs).

%% vars_from(exp,list)
%% similar to vars, but returns the variable
%% if expression is a variable

vars_from_ls([],[]).
vars_from_ls([A|As],Vars) :-
  vars_from(A,V),
  vars_from_ls(As,Vs),
  append(V,Vs,Vars).

vars_from(var(N,Args),[var(N,Args)]).
vars_from(fun(_,Args),VarsLs) :-
  vars_from_ls(Args,VarsLs).
vars_from(cons(_,Args),VarsLs) :-
  vars_from_ls(Args,VarsLs).

vars_from_cond(cond(L,R),CVars) :-
  vars_from(L,LVars),
  vars_from(R,RVars),
  append(LVars,RVars,CVars).

vars_from_conds([],[]).
vars_from_conds([C|Cs],Vars) :-
  vars_from_cond(C,CVars),
  vars_from_conds(Cs,CsVars),
  append(CVars,CsVars,Vars).

%% zip(list1,list2,zip_list)
%% creates a list of pairs of elements from two lists

zip([],[],[]).
zip([H1|T1],[H2|T2],[(H1,H2)|Rest]) :-
  zip(T1,T2,Rest).

%% included(set1,set2)
%% Checks if the elements from set1 are included in set2

included([],_).
included([Elem|Rest],Set) :-
  member(Elem,Set),
  included(Rest,Set).
