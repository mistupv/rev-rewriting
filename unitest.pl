unify([(cons("a",[]),cons("a",[]))],success([])).
unify([(cons("a",[]),cons("b",[]))],failure).
unify([(var("x",[]),var("x",[]))],success([])).
unify([(var("x",[]),cons("a",[]))],success([(var("x",[]),cons("a",[]))])).
unify([(var("x",[]),var("y",[]))],success([(var("x",[]), var("y",[]))])).
unify([(fun("f",[cons("a",[]),var("x",[])]),fun("f",[cons("a",[]),cons("b",[])]))],success([(var("x",[]),cons("b",[]))])).
unify([(fun("f",[cons("a",[])]),fun("g",[cons("a",[])]))],failure).
unify([(fun("f",[var("x",[])]),fun("f",[var("y",[])]))],success([(var("x",[]),var("y",[]))])).
unify([(fun("f",[var("x",[])]),fun("g",[var("y",[])]))],failure).
unify([(fun("f",[var("x",[])]),fun("f",[var("y",[]),var("z",[])]))],failure).
unify([(fun("f",[fun("g",[var("x",[])])]),fun("f",[var("y",[])]))],success([(var("y",[]),fun("g",[var("x",[])]))])).
unify([(fun("f",[fun("g",[var("x",[])]),var("x",[])]),fun("f",[var("y",[]),cons("a",[])]))],success([(var("y", []),fun("g",[cons("a",[])])),(var("x",[]),cons("a",[]))])).
unify([(var("x",[]),fun("f",[var("x",[])]))],success([(var("x",[]),fun("f",[var("x",[])]))])).
unify([(var("x",[]),var("y",[])),(var("y",[]),cons("a",[]))],success([(var("x",[]),cons("a",[])),(var("y",[]),cons("a",[]))])).
unify([(cons("a",[]),var("y",[])),(var("x",[]),var("y",[]))],success([ (var("x", []), cons("a", [])), (var("y", []), cons("a", []))])).
unify([(var("x",[]),cons("a",[])),(cons("b",[]),var("x",[]))],failure).
