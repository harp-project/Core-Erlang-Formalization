-module(test_gen).
-export([gen/3, generate_all/0]).

%% =============================================================================
%% USAGE & EXPLANATION
%% =============================================================================
%%
%% PURPOSE:
%%   This erlang module runs the Erlang functions given in the tests section against a specific target module 
%%   (configured below) and outputs the results in Coq format.
%%   It generates "Goal" and "Proof" statements verifying that the Coq 
%%   implementation behaves identically to the Erlang implementation.
%%
%% CONFIGURATION:
%%   Change the ?TARGET_MODULE macro below to point to the module you want to test.
%%     - lists     : The Erlang standard library (for baseline comparison)
%%
%% HOW TO RUN:
%%   1. Compile:
%%      $ erlc test_gen.erl target_module.erl
%%
%%   2. Run and print to console:
%%      $ erl -noshell -pa . -s test_gen generate_all -s init stop
%%
%%   3. Run and save to file (tests.v):
%%      $ erl -noshell -pa . -s test_gen generate_all -s init stop > tests.v
%%
%% ADDING TESTS:
%%   Add new entries to the `Tests` list in generate_all/0.
%%   Format: {FunctionName, [Arg1, Arg2, ...]}
%%
%% =============================================================================

%% ==========================================================
%% USER CONFIGURATION
%% ==========================================================

%% The module containing the functions we want to execute/test.
-define(TARGET_MODULE, lists). 

%% ==========================================================
%% AST BUILDER HELPERS
%% ==========================================================

with_ast(Real, Ast) -> {with_ast, Real, Ast}.

ast_fun(Arity, Body) -> {ast_fun, Arity, Body}.
ast_call(Mod, Fun, Args) -> {ast_call, Mod, Fun, Args}.
ast_var(Idx) -> {ast_var, Idx}.
ast_int(I) -> {ast_int, I}.
ast_atom(A) -> {ast_atom, A}.
ast_tuple(List) -> {ast_tuple, List}.
ast_cons(H, T) -> {ast_cons, H, T}.
ast_nil() -> {ast_nil}.

%% ==========================================================
%% MAIN GENERATOR
%% ==========================================================

generate_all() ->
    %% ==========================================================
    %% AST DEFINITIONS
    %% Structure: Name = with_ast(RealFun, AstRepresentation).
    %% AST Note:  Variables are De Bruijn indices (ast_var(0) is the innermost argument).
    %% Example:   fun(X) -> X > 0 end  ==  ast_fun(1, ast_call(..., [ast_var(0), ...]))
    %% ==========================================================

    FunGt0 = with_ast(fun(X) -> X > 0 end, 
        ast_fun(1, ast_call("erlang", ">", [ast_var(0), ast_int(0)]))),

    FunGt2 = with_ast(fun(X) -> X > 2 end, 
        ast_fun(1, ast_call("erlang", ">", [ast_var(0), ast_int(2)]))),

    FunEqB = with_ast(fun(X) -> X == b end, 
        ast_fun(1, ast_call("erlang", "=:=", [ast_var(0), ast_atom(b)]))),

    FunEven = with_ast(fun(X) -> X rem 2 == 0 end, 
        ast_fun(1, ast_call("erlang", "=:=", [ast_call("erlang", "rem", [ast_var(0), ast_int(2)]), ast_int(0)]))),

    FunWrapTrue = with_ast(fun(X) -> {true, X} end, 
        ast_fun(1, ast_tuple([ast_atom(true), ast_var(0)]))),

    FunDupList = with_ast(fun(X) -> [X, X] end, 
        ast_fun(1, ast_cons(ast_var(0), ast_cons(ast_var(0), ast_nil())))),

    FunPair = with_ast(fun(A, B) -> {A, B} end, 
        ast_fun(2, ast_tuple([ast_var(0), ast_var(1)]))),
    
    Tests = [
        {all,       [FunGt0, [1, 2, 3]]},
        {any,       [FunGt2, [1, 2, 3]]},
        {member,    [b, [a, b, c]]},
        {search,    [FunEqB, [a, b, c]]},
        {append,    [[1, 2], [3, 4]]},            %% append/2
        {append,    [[[1, 2], [3, 4], [5]]]},     %% append/1
        {concat,    [[[1, 2], [3], []]]},
        {delete,    [2, [1, 2, 3, 2]]},
        {droplast,  [[1, 2, 3]]},
        {dropwhile, [FunGt2, [4, 3, 2, 1]]},
        {duplicate, [3, x]},
        {enumerate, [[a, b, c]]},
        {filter,    [FunEven, [1, 2, 3, 4]]},
        {filtermap, [FunWrapTrue, [1, 2, 3]]}, 
        {flatlength,[[1, [2, 3], [], [4]]]},
        {flatmap,   [FunDupList, [1, 2]]},
        {flatten,   [[1, [2, [3]], 4]]},
        {join,      [x, [a, b, c]]},
        {last,      [[1, 2, 3]]},
        {nth,       [2, [a, b, c]]},
        {nthtail,   [2, [a, b, c, d]]},
        {partition, [FunGt2, [1, 2, 3, 4]]},
        {prefix,    [[1, 2], [1, 2, 3, 4]]},
        {reverse,   [[1, 2, 3]]},
        {split,     [2, [1, 2, 3, 4]]},
        {splitwith, [FunGt2, [4, 3, 2, 1]]},
        {sublist,   [[a, b, c, d], 2, 2]},        %% sublist/3
        {sublist,   [[a, b, c, d], 2]},           %% sublist/2
        {subtract,  [[1, 2, 3, 4], [2, 4]]},
        {suffix,    [[3, 4], [1, 2, 3, 4]]},
        {sum,       [[1, 2, 3, 4]]},
        {takewhile, [FunGt2, [4, 3, 2, 1]]},
        {uniq,      [[1, 2, 1, 3, 2]]},
        {unzip,     [[{1, a}, {2, b}]]},
        {unzip3,    [[{1, a, x}, {2, b, y}]]},
        {zip,       [[1, 2], [a, b]]},
        {zip3,      [[1, 2], [a, b], [x, y]]},
        {zipwith,   [FunPair, [1, 2], [a, b]]},
        {map,       [with_ast(fun(X) -> {ok, X} end, ast_fun(1, ast_tuple([ast_atom(ok), ast_var(0)]))), [1, 2]]},
        {foldl,     [with_ast(fun(X, Acc) -> Acc - X end, ast_fun(2, ast_call("erlang", "-", [ast_var(1), ast_var(0)]))), 10, [1, 2, 3]]},
        {foldr,     [with_ast(fun(X, Acc) -> X - Acc end, ast_fun(2, ast_call("erlang", "-", [ast_var(0), ast_var(1)]))), 0, [1, 2, 3]]},
        {seq,       [1, 5]},
        {keydelete, [b, 1, [{a, 1}, {b, 2}]]},
        {keyfind,   [b, 1, [{a, 1}, {b, 2}]]},
        {keymember, [b, 1, [{a, 1}, {b, 2}]]},
        {sort,      [[3, 1, 4, 2]]},
        {merge,     [[1, 3, 5], [2, 4, 6]]}
    ],

    io:format("%% Running tests against module: ~p~n", [?TARGET_MODULE]),

    lists:foreach(fun({Fn, Args}) -> 
        gen(Fn, Args, ?TARGET_MODULE) 
    end, Tests).


%% ==========================================================
%% TEST EXECUTION & PRINTING
%% ==========================================================

gen(Func, Args, Module) ->
    RealArgs = lists:map(fun
        ({with_ast, Real, _}) -> Real;
        (Other) -> Other
    end, Args),

    try apply(Module, Func, RealArgs) of
        Result ->
            Arity = length(Args),
            %% Use ~ts here because names might theoretically be complex, but usually ~s is fine.
            CoqFuncName = lists:flatten(io_lib:format("~p_~p", [Func, Arity])),
            
            CoqArgs = string:join([val_to_exp(A) || A <- Args], " "),
            CoqResult = val_to_result(Result),
            
            %% Using ~ts for safety on the final print
            io:format("(** Test ~p - inputs: ~p *)~n", [Func, strip_funs(RealArgs)]),
            io:format("Goal ⟨[], ~ts ~ts⟩~n", [CoqFuncName, CoqArgs]),
            io:format("    -->* RValSeq [~ts].~n", [CoqResult]),
            io:format("Proof. auto_proove_subst_semantics. Qed.~n~n")
    catch
        _:E ->
            io:format("(* Skipped ~p: ~p *)~n", [Func, E])
    end.

%% ==========================================================
%% VALUE CONVERTERS
%% ==========================================================

%% 1. Input Side (Exp)
val_to_exp({with_ast, _, Ast}) -> 
    %% AST -> String -> Wrap
    "(°" ++ ast_to_string(Ast) ++ ")";

val_to_exp(Val) ->
    %% Raw -> String -> Wrap
    "(˝" ++ val_to_raw(Val) ++ ")".

%% 2. AST Printer (Uses simple concatenation to avoid format crashes)
ast_to_string({ast_fun, Arity, Body}) -> 
    "EFun " ++ integer_to_list(Arity) ++ " (" ++ ast_to_string(Body) ++ ")";
ast_to_string({ast_call, M, F, Args}) ->
    ArgStr = string:join([ast_to_string(A) || A <- Args], "; "),
    "°ECall (˝VLit \"" ++ M ++ "\") (˝VLit \"" ++ F ++ "\") [" ++ ArgStr ++ "]";
ast_to_string({ast_var, Idx}) -> 
    "˝VVar " ++ integer_to_list(Idx);
ast_to_string({ast_int, I}) -> 
    "˝VLit (Integer " ++ integer_to_list(I) ++ "%Z)";
ast_to_string({ast_atom, A}) -> 
    "˝VLit \"" ++ atom_to_list(A) ++ "\"";
ast_to_string({ast_tuple, Args}) ->
    ArgStr = string:join([ast_to_string(A) || A <- Args], "; "),
    "°ETuple [" ++ ArgStr ++ "]";
ast_to_string({ast_cons, H, T}) ->
    "°ECons (" ++ ast_to_string(H) ++ ") (" ++ ast_to_string(T) ++ ")";
ast_to_string({ast_nil}) ->
    "˝VNil".

%% 3. Raw Value Printer (Recursive - uses ++ instead of fmt)
val_to_raw(I) when is_integer(I) -> 
    "VLit " ++ integer_to_list(I) ++ "%Z";
val_to_raw(A) when is_atom(A) -> 
    "VLit \"" ++ atom_to_list(A) ++ "\"";
val_to_raw([]) -> 
    "VNil";
val_to_raw([H|T]) -> 
    "VCons (" ++ val_to_raw(H) ++ ") (" ++ val_to_raw(T) ++ ")";
val_to_raw(T) when is_tuple(T) ->
    Es = [val_to_raw(E) || E <- tuple_to_list(T)],
    "VTuple [" ++ string:join(Es, "; ") ++ "]";
val_to_raw({true, Val}) -> 
    "VTuple [VLit \"true\"; " ++ val_to_raw(Val) ++ "]";
val_to_raw(_) -> "VLit \"UNKNOWN\"".

val_to_result(Val) -> val_to_raw(Val).

strip_funs(Args) -> [case is_function(A) of true -> 'FUN'; false -> A end || A <- Args].