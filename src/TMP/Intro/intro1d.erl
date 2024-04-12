-module(intro1d).
-export([collatz/1]).


collatz(1) -> [];
collatz(X) when (0 < X) and (0 == (X rem 2)) -> [X|collatz(X div 2)];
collatz(X) when (0 < X) -> [X|collatz(3 * X + 1)].