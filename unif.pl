:- begin_tests(unif).
:- use_module(trs).

test(unif1) :- 
  unify([(cons("a",[]),cons("a",[]))],
        success([])).

test(unif2) :-
  unify([(cons("a",[]),cons("b",[]))],
        failure).

test(unif3) :-
  unify([(var("x",[]),var("x",[]))],
        success([])).

test(unif4,[nondet]) :-
  unify([(var("x",[]),cons("a",[]))],
        success([(var("x",[]),cons("a",[]))])).

test(unif5,[nondet]) :-
  unify([(var("x",[]),var("y",[]))],
        success([(var("x",[]), var("y",[]))])).

test(unif6,[nondet]) :-
  unify([(fun("f",[cons("a",[]),var("x",[])]),fun("f",[cons("a",[]),cons("b",[])]))],
        success([(var("x",[]),cons("b",[]))])).

test(unif7,[nondet]) :-
  unify([(fun("f",[cons("a",[])]),fun("g",[cons("a",[])]))],
        failure).

test(unif8,[nondet]) :-
  unify([(fun("f",[var("x",[])]),fun("f",[var("y",[])]))],
        success([(var("x",[]),var("y",[]))])).

test(unif9,[nondet]) :-
  unify([(fun("f",[var("x",[])]),fun("g",[var("y",[])]))],
        failure).

test(unif10,[nondet]) :-
  unify([(fun("f",[var("x",[])]),fun("f",[var("y",[]),var("z",[])]))],
        failure).

test(unif11,[nondet]) :-
  unify([(fun("f",[fun("g",[var("x",[])])]),fun("f",[var("y",[])]))],
        success([(var("y",[]),fun("g",[var("x",[])]))])).

test(unif12,[nondet]) :-
  unify([(fun("f",[fun("g",[var("x",[])]),var("x",[])]),fun("f",[var("y",[]),cons("a",[])]))],X),
  member(X,[success([(var("y", []),fun("g",[cons("a",[])])),(var("x",[]),cons("a",[]))]),
            success([(var("x",[]),cons("a",[]))],(var("y", []),fun("g",[cons("a",[])])))]).

% This test may not be passed by other unify implementations
test(unif13,[nondet]) :-
  unify([(var("x",[]),fun("f",[var("x",[])]))],
        success([(var("x",[]),fun("f",[var("x",[])]))])).

test(unif14,[nondet]) :-
  unify([(var("x",[]),var("y",[])),(var("y",[]),cons("a",[]))],X),
  member(X,[success([(var("x",[]), cons("a",[])), (var("y",[]), cons("a",[]))]),
            success([(var("x",[]), var("y",[])), (var("y",[]), cons("a",[]))]),
            success([(var("y",[]), var("x",[])), (var("x",[]), cons("a",[]))]),
            success([(var("y",[]), cons("a",[])), (var("x",[]), cons("a",[]))])]).

test(unif15,[nondet]) :-
  unify([(cons("a",[]),var("y",[])),(var("x",[]),var("y",[]))],X),
  member(X,[success([(var("x",[]), cons("a",[])), (var("y",[]), cons("a",[]))]),
            success([(var("x",[]), var("y",[])), (var("y",[]), cons("a",[]))]),
            success([(var("y",[]), var("x",[])), (var("x",[]), cons("a",[]))]),
            success([(var("y",[]), cons("a",[])), (var("x",[]), cons("a",[]))])]).

test(unif16,[nondet]) :-
  unify([(var("x",[]),cons("a",[])),(cons("b",[]),var("x",[]))],
        failure).

:- end_tests(unif).
