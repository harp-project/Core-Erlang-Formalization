-module(execute_interp).
-export([evaluate/1, suite/0]).

%% evaluate(ErlFile) evaluates the entry point of the given Erlang module twice
%% (`main/0`, or `start/0` if the module has no `main/0`):
%%   1) as an ordinary Erlang function,
%%   2) as Core Erlang, with the (sequential) interpreter extracted from Rocq:
%%      Erlang file --compile to_core--> Core Erlang --pretty_print_fs_ghc--> TestProgram.hs
%%      TestProgram.hs + RunProgram.hs --ghc--> binary, whose output is parsed.
%% Both results have the same format, so they can be compared directly:
%%   {ok, Value} | {exception, Class, Reason}   (or {error, Output} if the
%%   Haskell side did not produce a result, e.g. compilation failure)

%% All paths are relative to this directory (test/), which is the expected working directory.
-define(HSDIR, "../src/Interpreter/HaskellSrc/exe").  % RocqExtraction.hs, SequentialInterpreter.hs, RunProgram.hs
-define(WORKDIR, "./generated/").     % generated files; shared, so RocqExtraction is compiled only once
-define(TESTDIR, "../atomvm/tests/erlang_tests").     % AtomVM submodule
-define(REPORTDIR, "./generated/reports/").
-define(BLACKLIST, "./blacklist.txt").  % tests of ?TESTDIR to skip
-define(HS_TIMEOUT, "60").  % seconds a generated Haskell program may run

mktmpdir() ->
    TimeInSeconds = erlang:system_time(second),
    %Date = calendar:system_time_to_rfc3339(TimeInSeconds),
    DirPath = io_lib:format("~ssemantic-tester-~p/", [?REPORTDIR, TimeInSeconds]),
    filelib:ensure_dir(DirPath),
    io:format("Report Directory created: ~s~n", [DirPath]),
    DirPath.

report(ModuleName, ReportDirectory, Result, Success) ->
    misc:write_to_file(ReportDirectory ++ ModuleName ++ ".result", io_lib:format("Result:~n~p~nVerdict: ~p~n", [Result, Success]), write),
    case Success of
       false -> 
         case Result of
           {erl_fail, R} -> io:format("Erlang failed: ~s with reason: ~p~n", [ModuleName, R]);
                            %io:format("X");
           {hs_fail, R}  -> io:format("Semantics failed: ~s with reason: ~p~n", [ModuleName, R]);
                            % io:format("X");
           R             -> io:format("Failed: ~s with reason: ~p~n", [ModuleName, R])
                            % io:format("X")
         end;
       true  -> ok %io:format(".")
    end.

evaluate(File) ->
    try eval_erl(File) of
        {ok, ErlResult} ->
            try eval_hs(File) of
                {ok, CoqResult} -> {ErlResult == CoqResult, {ErlResult, CoqResult}};
                Other           -> {false, {hs_fail, Other}}
            catch _Class:Reason -> {false, {hs_fail, Reason}}
            end;
        Other           -> {false, {erl_fail, Other}}
    catch _Class:Reason -> {false, {erl_fail, Reason}}
    end.

test_case(File, ReportDir) ->
    BaseName = misc:remove_extension(File),
    ModuleName = misc:remove_directory(BaseName),
    {Success, Result} = evaluate(File),
    report(ModuleName, ReportDir, Result, Success),
%    io:format("~s: ~p~n", [filename:basename(File), Result]),
    {ModuleName, Success, Result}.

%% Applies evaluate_and_check to every .erl file of the AtomVM test suite.
%% Returns [{File, true | false | {crash, Class, Reason}}]; a file that crashes
%% (e.g. it does not compile, or needs AtomVM-specific functions) is reported
%% and does not stop the run.
evaluate_test_suite(Files) ->
    ReportDir = mktmpdir(),
    lists:map(fun(File) -> test_case(File, ReportDir) end, Files).

%% One test name per line; everything after a '%' (the reason for the
%% blacklisting) is a comment, blank lines are ignored.
read_blacklist() ->
    {ok, Bin} = file:read_file(?BLACKLIST),
    Lines = string:lexemes(binary_to_list(Bin), "\n"),
    [Name || Line <- Lines,
             [Code | _] <- [string:split(Line, "%")],
             Name <- [string:trim(Code)],
             Name =/= ""].

% TODO: make this concurrent for more efficiency - if needed
suite() ->
    Blacklist = read_blacklist(),
    Files = [File || File <- filelib:wildcard(filename:join(?TESTDIR, "*.erl")),
                     not lists:member(filename:basename(File, ".erl"), Blacklist)],
    [ModName || {ModName, false, _} <- evaluate_test_suite(Files)].



%% ---------------------------------------------------------------------
%% Erlang

eval_erl(File) ->
    {ok, Mod, Bin} = compile:file(File, [binary]),
    {module, Mod} = code:load_binary(Mod, File, Bin),
    Entry = case erlang:function_exported(Mod, main, 0) of
                true  -> main;
                false -> start
            end,
    Result = try {ok, Mod:Entry()}
             catch Class:Reason -> {exception, Class, Reason}
             end,
    code:purge(Mod),
    code:delete(Mod),
    Result.

%% ---------------------------------------------------------------------
%% Haskell

eval_hs(File) ->
    {ok, _, CST} = compile:file(File, [to_core, binary, no_copt, {parse_transform, own_calls}]),
    filelib:ensure_dir(?WORKDIR),
    Bin = ?WORKDIR ++ "program",
    file:delete(Bin),
    BaseName = misc:remove_extension(File),
    ModuleName = misc:remove_directory(BaseName),
    ok = file:write_file(?WORKDIR ++ "TestProgram.hs", pretty_print_fs_ghc:pp_module(CST, ModuleName)),
    
    os:cmd("ghc -O0 -i" ++ ?HSDIR ++ " -i" ++ ?WORKDIR ++ " -outputdir " ++ ?WORKDIR ++ "build"
           ++ " -o " ++ Bin ++ " " ++ ?HSDIR ++ "/RunProgram.hs"),
    
    case filelib:is_regular(Bin) of
        true  -> parse_hs(os:cmd("timeout " ++ ?HS_TIMEOUT ++ " " ++ Bin ++ "; [ $? -eq 124 ] && echo __timeout"));
        false -> {error, "ghc failed"}
    end.

%% The output of RunProgram.hs: the result (or exception) as an Erlang term
parse_hs(Output) ->
    case string:find(Output, "__timeout") of
        nomatch -> parse_hs_result(Output);
        _       -> {error, timeout}
    end.

parse_hs_result(Output) ->
    case string:split(Output, "__coqresult:") of
        [_, Term] ->
            {ok, parse_term(Term)};
        _ ->
            case string:split(Output, "__exceptioncoqresult:") of
                [_, Term] -> {Class, Reason, _Details} = parse_term(Term),
                             {exception, Class, Reason};
                _         -> {error, Output}
            end
    end.

parse_term(Str) ->
    {ok, Tokens, _} = erl_scan:string(string:trim(Str) ++ "."),
    {ok, Term} = erl_parse:parse_term(Tokens),
    Term.
