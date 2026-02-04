-module(even_odd).
-export([even/1, odd/1, even2/1, odd2/1, main/1]).

even(0) ->
    true;
even(N) when N > 0 ->
    odd(N - 1);
even(_) ->
    false.

odd(1) ->
    true;
odd(N) when N > 1 ->
    even(N - 1);
odd(_) ->
    false.




even2(0) ->
    true;
even2(1) ->
    false;
even2(N) when N > 1 ->
    even2(N - 2);
even2(_) ->
    false.

odd2(0) ->
    false;
odd2(1) ->
    true;
odd2(N) when N > 1 ->
    odd2(N - 2);
odd2(_) ->
    false.

main([]) ->
    [even(5), odd(5), even2(5), odd2(5)].
