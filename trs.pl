:- module(trs,
         [unify/2,
          substitute/3,
          vars_from/2,
          vars_from_conds/2]).

unify([],success([])).

unify([(var(N,_),var(N,_))|Rest],L) :- 
	!, unify(Rest,L).

% orient
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

compose(success(_),failure,failure).
compose(success(H),success(T),success(HT)) :-
  compose_subs(H,T,HT).

compose_subs([],S,S).
compose_subs([(X1,Y1)|Rest],Subs,[(X1,Y1subs)|L]) :- 
	substitute(Subs,Y1,Y1subs),
	compose_subs(Rest,Subs,L).

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

substituteEqList(_,[],[]).
substituteEqList(Var,[Exp|Rest],[VExp|VRest]) :-
	substituteEq(Var,Exp,VExp),
	substituteEqList(Var,Rest,VRest).

substituteEq(Bind,(Exp1,Exp2),(BExp1,BExp2)) :-
	substituteVar(Bind,Exp1,BExp1),
	substituteVar(Bind,Exp2,BExp2).

vars_in_args([],[]).
vars_in_args([A|As],[V|Vs]) :-
  vars_in(A,V),
  vars_in_args(As,Vs).

vars_in(var(N,_),N).
vars_in(cons(_,Args),Vs) :-
  vars_in_args(Args,Vs).
vars_in(fun(_,Args),Vs) :-
  vars_in_args(Args,Vs).
 
vars(var(_,_),[]).
vars(Expr,Vs) :-
  \+ Expr = var(_,_),
  vars_in(Expr,Vs).

zip([],[],[]).
zip([H1|T1],[H2|T2],[(H1,H2)|Rest]) :-
  zip(T1,T2,Rest).

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

