-module(attempt).
-compile(export_all).

f1(X) -> X and 5.
g1(X) -> X or 5.
f2(X) -> X andalso 5.
g2(X) -> X - 3.
f3(X) -> not X.
f4(X) -> X ++ [3, 4].
f5(X) -> X -- [1, 2].
f6(X) -> tuple_to_list(X).
f7(X) -> list_to_tuple(X).
f8(X) -> X == 5.
f9(X) -> X /= 5.
f10(X) -> X =/= 5.
f11(X) -> X =:= 5.
f12(Y) -> X = "cica" ++ Y,
         io:fwrite(X).
f13(X) ->
  case X of
    #{1 := 2, 2 := 3} -> 1;
	Z -> 2
  end.

f14(X, Y) -> X rem Y, X div Y.
f15(X) -> tuple_size(X).
f16(X) -> length(X).
f17(X) -> hd(X).
