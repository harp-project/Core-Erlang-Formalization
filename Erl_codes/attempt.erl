-module(attempt).
-compile(export_all).

ex2() ->
  {F = fun() -> 5 end},
  F(). 

list_ex() -> sums (X = 5, 3,X = 6),
			X,
			ex2().

sums(A, B, C) -> A + (B + C).

f() -> {}.
g() -> #{5 => "asd"}.

hello() -> "Hello world\n".

letexpr() -> 
     {X, Y} = {4,5}.

tuplemod() -> X = 4, 5, 6.

case_match() ->
   case X = 4 of
     3 -> Y = 5;
	 4 -> Y = 4
   end,
   Y.
 
fact(0) -> 1;
fact(N) -> io:frwrite("sad")  ,N * fact (N - 1).

f1() -> 5.
f1(X) -> 6.

f2(X) ->
	case X of
		3 -> Y = fun(X) -> X end;
		4 -> Y = fun(X) -> X + 1 end
	end,
	Y(X).

f3(X) -> X + 1.

f4(Q) -> f3(Y = Q + 1), Y.

f5() -> {io:format("Hello") , 1/0, io:format("world")}.