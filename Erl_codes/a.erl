-module(a).
-compile(export_all).

fun1() ->
	X = fun() -> 5 end,
	X().