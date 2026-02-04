-module(weird).
-compile(export_all).
-include_lib("eqc/include/eqc.hrl").

f() ->
  self() ! 1,
  self() ! 2,
  self() ! 3,
  receive
    2 when 1 / 0 -> "You got me"
  after 0 -> [receive X -> X after 0 -> "No more values" end, receive X -> X after 0 -> "No more values" end, receive X -> X after 0 -> "No more values" end]
  end.

% Sometimes this terminates, sometimes it does not
start() -> g(true).


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
    0 -> flush(), g(false)
  end.

slave(Pid) ->
  Pid ! 1,
  Pid ! 2,
%  timer:sleep(10),
  Pid ! 3,
  Pid ! 4,
%  timer:sleep(10),
  Pid ! 5,
  Pid ! 6,
%  timer:sleep(10),
  Pid ! 7,
  timer:sleep(1000),
  case is_process_alive(Pid) of
    true -> exit(Pid, kill);
    _ -> ok
  end.


start_messaging() ->
  Jake = spawn(weird, jake, []),
  Susan = spawn(weird, susan, []),
  Susan ! Jake,
  timer:sleep(6000).

jake() ->
  receive
    {Msg, Pid} -> io:format("Jake: Nice, Susan gave me her number: ~p ~p ~n", [Msg, Pid]),
                  Pid ! "Hi, I'm Jake!"
  after
    1000 -> flush(), jake()
  end.
susan() ->
  Jake = receive X -> X end,
  Jake ! "Hi",
  timer:sleep(1000),
  Jake ! "Heeey",
  timer:sleep(1000),
  Jake ! "Hellooo?",
  timer:sleep(1000),
  Jake ! {"Call me please, my number is XXX", self()},
  io:format("Susan: I'm waiting: ~p~n", [self()]),
  receive
    Msg -> io:format("Susan: I got: ~s ~n", [Msg])
  after
    3000 -> exit(Jake, kill), io:format("Susan: I leave~n")
%    0 -> exit(Jake, kill), io:format("Susan: I leave~n")
  end.

lazy_and(X, Y) ->
  if X -> Y;
     true -> false
  end.

prop_lazy_and1() ->
  ?FORALL(B1, bool(),
    ?FORALL(B2, bool(), lazy_and(B1, B2) == (B1 andalso B2))).

prop_lazy_and2() ->
  ?FORALL(B1, int(),
    ?FORALL(B2, int(), lazy_and(B1, B2) == (B1 andalso B2))).


flush() ->
  receive
    X -> io:format("Jake ignored: ~p~n", [X]), flush()
  after
    0 -> ok
  end.


test() ->
  spawn(fun() -> self() ! "p1" end),
  spawn(fun() -> self() ! "p2" end),
  receive
    X -> io:format("I got: ~p~n", [X])
  end,
  timer:sleep(1000),
  receive
    X -> ok
  after
    0 -> ok
  end.

test1() ->
  MyPID = self(),
  spawn(fun() -> MyPID ! "p1" end),
  spawn(fun() -> MyPID ! "p2" end),
  receive
    X -> io:format("I got: ~p~n", [X])
  end,
  timer:sleep(1000),
  receive
    X -> ok
  after
    0 -> ok
  end.

test2() ->
  MyPID = self(),
  spawn(fun() -> timer:sleep(0), MyPID ! "p1" end),
  spawn(fun() -> MyPID ! "p2" end),
  receive
    X -> io:format("I got: ~p~n", [X])
  end,
  timer:sleep(1000),
  receive
    _ -> ok
  after
    0 -> ok
  end.


start_example() ->
  Fpid = spawn(weird, fun1, []),
  Gpid = spawn(weird, fun2, []),
  Gpid ! Fpid,
  timer:sleep(2000).

fun1() ->
  receive
    {X, _} -> io:format("Received: ~p~n", [X])
  after 1000 -> flush(), fun1()
  end.

fun2() ->
  Fpid = receive X -> X end,
  timer:sleep(1000),
  Fpid ! "Hello",
  timer:sleep(1000),
  Fpid ! {"Hello", ok},
  timer:sleep(1000),
  exit(Fpid, kill).


recurse() -> recurse().
