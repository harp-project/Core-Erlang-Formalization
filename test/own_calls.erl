-module(own_calls).
-export([parse_transform/2]).

parse_transform(Forms, _Opts) ->
    [{attribute, _, module, Mod}] = [F || F = {attribute, _, module, _} <- Forms],
    [erl_syntax:revert(erl_syntax_lib:map(fun(N) -> localize(N, Mod) end, F)) || F <- Forms].

%% Mod:f(Args) -> f(Args), fun Mod:f/A -> fun f/A (for the current module Mod)
localize(Node, Mod) ->
    case erl_syntax:type(Node) of
        application ->
            Op = erl_syntax:application_operator(Node),
            case erl_syntax:type(Op) =:= module_qualifier andalso is_mod(erl_syntax:module_qualifier_argument(Op), Mod) of
                true  -> erl_syntax:copy_pos(Node, erl_syntax:application(erl_syntax:module_qualifier_body(Op), erl_syntax:application_arguments(Node)));
                false -> Node
            end;
        implicit_fun ->
            Name = erl_syntax:implicit_fun_name(Node),
            case erl_syntax:type(Name) =:= module_qualifier andalso is_mod(erl_syntax:module_qualifier_argument(Name), Mod) of
                true  -> erl_syntax:copy_pos(Node, erl_syntax:implicit_fun(erl_syntax:module_qualifier_body(Name)));
                false -> Node
            end;
        _ -> Node
    end.

is_mod(N, Mod) -> erl_syntax:type(N) =:= atom andalso erl_syntax:atom_value(N) =:= Mod.
