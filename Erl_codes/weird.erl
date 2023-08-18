-module(weird).
-compile(export_all).

f() ->
  self() ! 1,
  self() ! 2,
  self() ! 3,
  receive
    2 when 1 / 0 -> "You got me"
  after 0 -> [receive X -> X after 0 -> "No more values" end, receive X -> X after 0 -> "No more values" end, receive X -> X after 0 -> "No more values" end]
  end.

flush() ->
  receive
    X -> io:format("Process ~p got: ~p~n", [self(), X]), flush()
  after
    0 -> ok
  end.

g(X) ->
  case X of
    true -> spawn(weird, slave, [self()]);
    false -> ok
  end,
  receive
    1 when false -> ok;
    2 when false -> ok;
    7 -> finished
  after
    10 -> flush(), g(false)
  end.

slave(Pid) ->
  Pid ! 1,
  Pid ! 2,
  timer:sleep(10),
  Pid ! 3,
  Pid ! 4,
  timer:sleep(10),
  Pid ! 5,
  Pid ! 6,
  timer:sleep(10),
  Pid ! 7.

recurse() -> recurse().
