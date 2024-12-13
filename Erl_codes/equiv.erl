-module(equiv).
-compile(export_all).

exp1() ->
  E1 = 1+ 2,
  E2 = 1 + 2,
  E3 = 1 + 2, 
  case 5 + 5 of
    true -> E2;
    _    -> E3
  end.

exp2() ->
  E1 = 1+ 2,
  E2 = 1 + 2,
  E3 = 1 + 2, 
  if 5 + 5   -> E2;
     true -> E3
  end.

clause1(X, E1, E2) when length(X) == 0 -> E1;
clause1(X, E1, E2) -> E2.

clause2([], E1, E2) -> E1;
clause2(X, E1, E2) -> E2.

