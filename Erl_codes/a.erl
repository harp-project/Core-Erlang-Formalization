-module(a).
-compile(export_all).

fun1(X) ->
	if X == 4 -> 5;
	true -> io:fwrite("12")
	end.

sword(1) -> throw(slice);
sword(2) -> erlang:error(cut_arm);
sword(3) -> exit(cut_leg);
sword(4) -> throw(punch);
sword(5) -> exit(cross_bridge).
 
black_knight(Attack) when is_function(Attack, 0) ->
try Attack() of
_ -> "None shall pass."
catch
throw:slice -> "It is but a scratch.";
error:cut_arm -> "I've had worse.";
exit:cut_leg -> "Come on you pansy!";
_:_ -> "Just a flesh wound."
end.

length0(L) when length(L) == 0 -> 1;
length0(_) -> 2.

length02([]) -> 1;
length02(_) -> 2.

% From the "Erlang programming" book
double([X|T], Buffer) ->
  double(T, Buffer ++ [X*2]);
double([], Buffer) ->
  Buffer.

double2([X|T], Buffer) ->
  double2(T, [X*2|Buffer]);
double2([], Buffer) ->
  lists:reverse(Buffer).
