-module(pretty_print_fs_ghc).
-export([pp/2, pp_module/2]).
-include_lib("compiler/src/core_parse.hrl").

%% Same structure as pretty_print_fs.erl, but the AST is printed in Haskell
%% syntax (as the data types of the Haskell code extracted from Rocq), so it
%% can be evaluated without going through Rocq:
%%   - list elements are separated by "," instead of ";"
%%   - strings do not have the "%string" suffix
%%   - the clauses of a case are ((patterns, guard), body), since a Coq triple
%%     (a, b, c) is the nested pair ((a, b), c)
%%   - the NonVal -> Exp coercion needs to be explicit (EExp)

stringformat([$~,$s|F], [P|Ps]) -> P ++ stringformat(F, Ps);
stringformat([C|Fs], Ps) -> [C|stringformat(Fs, Ps)];
stringformat([], _) -> [].

%% Extend naming scheme
add_name(Var, Names) ->
  NewNames = maps:map(fun(_, V) -> V + 1 end, Names),
  VarName = case Var of
              #c_var{name={N, A}} -> {N, A};
              #c_var{name=N} -> N;
              N -> N
            end,
  maps:put(VarName, 0, NewNames).


add_names(Vars, Names) ->
  lists:foldr(fun add_name/2, Names, Vars).

%% Wrapper for pretty-printing - start with the empty naming environment
pp(E) ->
  pp(E, #{}).

%% Adding module functions to letrec

pp_expr(#c_values{es=Es}, Names) ->
  "(EExp (EValues [" ++ pp_list(Es, ",", fun(E) -> pp(E, Names) end) ++ "]))";
pp_expr(E, Names) -> pp(E, Names).

%% NOTE: the entry point (`main/0`, or `start/0` if there is no `main/0`) is a function
%% without parameters, so it is called with arity 0 and without arguments.
-define(hs_template,
"module TestProgram where

import RocqExtraction

test :: NonVal
test = ELetRec [~s] (EExp (EApp (VVal (VFunId (~s, 0))) []))
").

% NOTE: to handle recursive calls, the funnames should be bound to 0, 1, ..., k while the fun args to k+1, k+2, ...
% Therefore, we cannot create a new naming scheme here, pp_rec_fun_defs handles that
% TODO: ModuleName is required to turn call ModuleName:Fun(v1, ..., vn) into apply Fun(v1, ..., vn) to solve the issue
% of the missing module system
pp_module(#c_module{defs=Ds}, Names, ModuleName) ->
  {Ns, _} = lists:unzip(Ds),
  % the elements are indented, otherwise the layout rule of Haskell would start a new declaration
  HsDefs = pp_list(Ds,",\n  ", fun(D) -> pp_rec_fun_defs(D, Ns, Names) end),
  ModFuns = add_names(Ns, #{}),
  Entry = case maps:is_key({main, 0}, ModFuns) of
            true  -> {main, 0};
            false -> {start, 0}
          end,
  stringformat(?hs_template, [HsDefs, integer_to_list(maps:get(Entry, ModFuns))]);
pp_module(M, _, ModuleName) ->
  io:format("Not a module: ~p", [M]),
  throw(badarg).
pp_module(M, ModuleName) ->
  pp_module(M, #{}, ModuleName).

%% Pretty Printing Expressions

pp(#c_primop{name=N, args=As}, Names) ->
  stringformat("(EExp (EPrimOp ~s [~s]))", [pp_atom(N), pp_list(As,",", fun(E) -> pp_expr(E, Names) end)]);

pp(#c_case{arg=A, clauses=Cs}, Names) ->
  stringformat("(EExp (ECase ~s [~s]))", [pp_expr(A, Names), pp_list(Cs, ",", fun(C) -> pp(C, Names) end)]);

pp(#c_clause{pats=Ps, guard=G, body=B}, Names) ->
  {PatStr, PatVars} = pp_pattern_list(Ps, ",", fun(P) -> pp_pattern(P, Names) end),
  NewNames = add_names(PatVars, Names),
  stringformat("(([~s], ~s), ~s)", [PatStr, pp_expr(G, NewNames), pp_expr(B, NewNames)]);

pp(#c_apply{op=O, args=As}, Names) ->
  stringformat("(EExp (EApp ~s [~s]))", [pp_expr(O, Names), pp_list(As,",", fun(E) -> pp_expr(E, Names) end)]);

%% TODO: these might need to be mapped to Val and not Exp!
pp(#c_literal{val=V}, Names) when is_list(V) ->
  pp_cons(V, Names);
pp(#c_literal{val=V}, _) when is_atom(V) ->
  "(VVal (VLit (Atom " ++ hs_string(atom_to_list(V)) ++ ")))";
pp(#c_literal{val=V}, _) when is_integer(V) ->
  "(VVal (VLit (Integer (" ++ integer_to_list(V) ++ "))))";

pp(#c_literal{val=V}, Names) when is_map(V) ->
  stringformat("(EExp (EMap [~s]))", [pp_list(maps:to_list(V), ",", fun(E) -> pp_pair(E, Names) end)]);
pp(#c_literal{val=T}, Names) when is_tuple(T) ->
  stringformat("(EExp (ETuple [~s]))", [pp_list(tuple_to_list(T),",", fun(E) -> pp_expr(E, Names) end)]);
pp(#c_literal{val=V}, _) when is_bitstring(V) ->
  pp_bitstring(V);
%% END OF TODO


pp(#c_var{name={N, A}}, Names) ->
  stringformat("(VVal (VFunId (~s, ~s)))", [integer_to_list(maps:get({N, A}, Names)), integer_to_list(A)]);
pp(#c_var{name=N}, Names) -> %when is_atom(N) ->
  "(VVal (VVar " ++ integer_to_list(maps:get(N, Names)) ++ "))";

pp(#c_fun{vars=Vs, body=B}, Names) ->
  stringformat("(EExp (EFun ~s ~s))", [integer_to_list(length(Vs)), pp_expr(B, add_names(Vs, Names))]);

pp(#c_let{vars=Vs, arg=A, body=B}, Names) ->
  stringformat("(EExp (ELet ~s ~s ~s))", [integer_to_list(length(Vs)), pp_expr(A, Names), pp_expr(B, add_names(Vs, Names))]);

pp(#c_letrec{defs=Ds, body=B}, Names) ->
  {Ns, _} = lists:unzip(Ds),
  NewNames = add_names(Ns, Names),
  % The naming scheme for the (mutually) recursive fundefs is created individually for each fundef in pp_rec_fun_defs to ensure
  % the property outlined in the definition of pp for #c_module above
  stringformat("(EExp (ELetRec [~s] ~s))", [pp_list(Ds, ",", fun(D) -> pp_rec_fun_defs(D, Ns, Names) end), pp_expr(B, NewNames)]);

pp(#c_cons{hd=Hd,tl=Tl}, Names) ->
  pp_cons([Hd|Tl], Names);

pp(#c_call{name=N, module=M, args=Es}, Names) ->
  stringformat("(EExp (ECall ~s ~s [~s]))", [pp_expr(M, Names), pp_expr(N, Names), pp_list(Es,",", fun(E) -> pp_expr(E, Names) end)]);

pp(#c_tuple{es=Es}, Names) ->
  stringformat("(EExp (ETuple [~s]))", [pp_list(Es,",", fun(E) -> pp_expr(E, Names) end)]);

pp(#c_map{arg=_, es=Es,is_pat=_}, Names) ->
  stringformat("(EExp (EMap [~s]))",[pp_list(Es,",", fun(E) -> pp(E, Names) end)]);

pp(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}, Names) ->
  stringformat("(~s, ~s)",[pp_expr(K, Names),pp_expr(V, Names)]);

pp(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}, Names) ->
  stringformat("(~s, ~s)",[pp_expr(K, Names),pp_expr(V, Names)]);

pp(#c_seq{arg=A, body=B}, Names) ->
  stringformat("(EExp (ESeq ~s ~s))",[pp_expr(A, Names),pp_expr(B, Names)]);


pp(#c_try{arg=A, vars=Vs, body=B, evars=Evs, handler=H}, Names) when length(Evs) == 2 ->
	stringformat("(EExp (ETry ~s ~s ~s ~s ~s))",[pp_expr(A, Names),
	                                             integer_to_list(length(Vs)) , pp_expr(B, add_names(Vs, Names)),
	                                             "3", pp_expr(H, add_names(Evs ++ ["unused"], Names))]); % trick to handle 2-argument try expressions -> make them 3-argument try expressions in the semantics
pp(#c_try{arg=A, vars=Vs, body=B, evars=Evs, handler=H}, Names) when length(Evs) == 3 ->
	stringformat("(EExp (ETry ~s ~s ~s ~s ~s))",[pp_expr(A, Names),
	                                             integer_to_list(length(Vs)) , pp_expr(B, add_names(Vs, Names)),
	                                             integer_to_list(length(Evs)), pp_expr(H, add_names(Evs, Names))]);
pp(#c_binary{segments=Ss}, Names) ->
  stringformat("(EExp (EBin [~s]))", [pp_list(Ss,",", fun(Seg) -> pp_segment(Seg, Names) end)]);



pp(I, _) when is_integer(I) ->
  "(VVal (VLit (Integer (" ++ integer_to_list(I) ++ "))))";
pp(A, _) when is_atom(A) ->
  "(VVal (VLit (Atom " ++ hs_string(atom_to_list(A)) ++ ")))";
pp(V, Names) when is_list(V) ->
  pp_cons(V, Names);
pp(V, Names) when is_map(V) ->
  stringformat("(EExp (EMap [~s]))", [pp_list(maps:to_list(V), ",", fun(E) -> pp_pair(E, Names) end)]);
pp(T, Names) when is_tuple(T) ->
  stringformat("(EExp (ETuple [~s]))", [pp_list(tuple_to_list(T),",", fun(E) -> pp_expr(E, Names) end)]);
pp(V, _) when is_bitstring(V) -> pp_bitstring(V);

pp(X, _) ->
  throw({unsupported_case, X}).

%% PP helpers for expressions

pp_atom(#c_var{name=N}) when is_atom(N) ->
  hs_string(atom_to_list(N));
pp_atom(#c_var{name=N}) when is_integer(N) ->
  hs_string("_" ++ integer_to_list(N));
pp_atom(#c_literal{val=V}) ->
  hs_string(atom_to_list(V)).

%% A Haskell string literal denoting exactly the characters of Cs: quotes,
%% backslashes, control and non-ASCII characters are escaped, so atoms survive
%% unchanged, and the generated file is plain ASCII.
hs_string(Cs) -> "\"" ++ lists:flatmap(fun hs_char/1, Cs) ++ "\"".

hs_char($")  -> "\\\"";
hs_char($\\) -> "\\\\";
hs_char(C) when C >= 32, C =< 126 -> [C];
hs_char(C)  -> "\\" ++ integer_to_list(C) ++ "\\&".   % \& ends the numeric escape

pp_list(Es, S, F) -> string:join(lists:map(F, Es), S).


pp_rec_fun_defs({A, B}, NewFunNames, Names) ->
  stringformat("(~s, ~s)", [pp_rec_fun_sign(A),pp_rec_fun_body(B, NewFunNames, Names)]).
pp_rec_fun_sign(#c_var{name={_, A}}) -> % We throw away the name, it becomes a dB index
  stringformat("~s", [integer_to_list(A)]).
pp_rec_fun_body(#c_fun{vars=Vs, body=B}, NewFunNames, Names) ->
  stringformat("~s", [pp_expr(B, add_names(NewFunNames ++ Vs, Names))]).

pp_cons([], _) ->
  "(VVal VNil)";
pp_cons([A|B], Names) ->
  stringformat("(EExp (ECons ~s ~s))", [pp_expr(A, Names),pp_expr(B, Names)]).

pp_pair({A, B}, Names) -> stringformat("(~s,~s)", [pp_expr(A, Names),pp_expr(B, Names)]).


pp_bitstring(Bits) ->
  N = bit_size(Bits),
  <<V:N>> = Bits,
  stringformat("(VVal (VBitstring (Bv_to_bvn (of_nat ~s) ~s)))", [integer_to_list(N), integer_to_list(V)]).

pp_segment_attrs(#c_bitstr{unit=U, type=T, flags=Fs}) ->
  Flags = cerl:concrete(Fs),
  Unit = integer_to_list(cerl:concrete(U)),
  Type = case cerl:concrete(T) of
           integer   -> "IntType";
           float     -> "FloatType";
           binary    -> "BinaryType";
           bytes     -> "BinaryType";
           bitstring -> "BitstringType";
           bits      -> "BitstringType";
           utf8      -> "Utf8Type";
           utf16     -> "Utf16Type";
           utf32     -> "Utf32Type"
         end,
  Sign = case lists:member(signed, Flags) of
           true  -> "Signed";
           false -> "Unsigned"
         end,
  Endian = case lists:member(little, Flags) of
             true  -> "LittleEndian";
             false -> case lists:member(native, Flags) of
                        true  -> "NativeEndian";
                        false -> "BigEndian"
                      end
           end,
  {Unit, Type, Sign, Endian}.

pp_segment(#c_bitstr{val=V, size=Sz} = S, Names) ->
  {Unit, Type, Sign, Endian} = pp_segment_attrs(S),
  stringformat("(EExp (ESeg (Build_Segment ~s ~s ~s ~s ~s ~s)))",
               [pp_expr(V, Names), pp_expr(Sz, Names), Unit, Type, Sign, Endian]).



%% Pretty Printing Patterns
%% This function returns the used variables
%% NOTE: Names is the naming environment *outside* of the pattern. It is only needed for the
%% sizes of binary segments, which are values in the scope of the enclosing expression.
pp_pattern(#c_literal{val=V}, _) when is_integer(V) ->
  {"(PLit (Integer (" ++ integer_to_list(V) ++ ")))", []};
pp_pattern(#c_literal{val=V}, _) when is_atom(V) ->
  {"(PLit (Atom " ++ hs_string(atom_to_list(V)) ++ "))", []};
pp_pattern(#c_literal{val=V}, _) when is_bitstring(V) ->
  pp_pattern_bitstring(V);
pp_pattern(#c_var{name=N}, _) -> % when is_atom(N) ->
  {"PVar", [N]};
pp_pattern(#c_literal{val=L}, Names) when is_list(L) ->
  pp_pattern_cons(L, Names);
pp_pattern(#c_literal{val=T}, Names) when is_tuple(T) ->
  {Str, Ns} = pp_pattern_list(tuple_to_list(T),",", fun(P) -> pp_pattern(P, Names) end),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(#c_cons{hd=A,tl=B}, Names) ->
  {StrA, NA} = pp_pattern(A, Names),
  {StrB, NB} = pp_pattern(B, Names),
  {stringformat("(PCons ~s ~s)", [StrA, StrB]), NA ++ NB};
pp_pattern(#c_tuple{es=Es}, Names) when is_tuple(Es) ->
  {Str, Ns} = pp_pattern_list(tuple_to_list(Es),",", fun(P) -> pp_pattern(P, Names) end),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(#c_tuple{es=Es}, Names) when is_list(Es) ->
  {Str, Ns} = pp_pattern_list(Es,",", fun(P) -> pp_pattern(P, Names) end),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(#c_map{arg=_, es=Es,is_pat=_}, Names) ->
  {Str, Ns} = pp_pattern_list(Es,",", fun(P) -> pp_pattern(P, Names) end),
  {stringformat("(PMap [~s])", [Str]), Ns};
pp_pattern(#c_map_pair{op=#c_literal{val=assoc}, key=K, val=V}, Names) ->
  {StrK, NK} = pp_pattern(K, Names),
  {StrV, NV} = pp_pattern(V, Names),
  {stringformat("(~s, ~s)",[StrK, StrV]), NK ++ NV};
pp_pattern(#c_map_pair{op=#c_literal{val=exact}, key=K, val=V}, Names) ->
  {StrK, NK} = pp_pattern(K, Names),
  {StrV, NV} = pp_pattern(V, Names),
  {stringformat("(~s, ~s)",[StrK, StrV]), NK ++ NV};
pp_pattern(#c_binary{segments=Ss}, Names) ->
  {Str, Ns} = pp_pattern_list(Ss, ",", fun(S) -> pp_pattern_segment(S, Names) end),
  {stringformat("(PBin [~s])", [Str]), Ns};
pp_pattern(I, _) when is_integer(I) ->
  {"(PLit (Integer (" ++ integer_to_list(I) ++ ")))", []};
pp_pattern(A, _) when is_atom(A) ->
  {"(PLit (Atom " ++ hs_string(atom_to_list(A)) ++ "))", []};
pp_pattern(B, _) when is_bitstring(B) ->
  pp_pattern_bitstring(B);
pp_pattern(V, Names) when is_list(V) ->
  pp_pattern_cons(V, Names);
pp_pattern(M, Names) when is_map(M) ->
  {Str, Ns} = pp_pattern_list(maps:to_list(M), ",", fun(P) -> pp_pattern_map(P, Names) end),
  {stringformat("(PMap [~s])", [Str]), Ns};
pp_pattern(T, Names) when is_tuple(T) ->
  {Str, Ns} = pp_pattern_list(tuple_to_list(T),",", fun(P) -> pp_pattern(P, Names) end),
  {stringformat("(PTuple [~s])", [Str]), Ns};
pp_pattern(V, _) -> io_lib:format("~p", [V]), throw({unsupported_case, V}).

%% Helpers for pp_pattern
%% pp_pattern_list is almost the same as pp_list, but it also accumulates variable names
pp_pattern_list(Ps, S, F) ->
  {Strs, Nss} = lists:unzip(lists:map(F, Ps)),
  {string:join(Strs, S), lists:concat(Nss)}.


pp_pattern_cons([], _) ->
  {"PNil", []};
pp_pattern_cons([A|B], Names) ->
  {StrA, NA} = pp_pattern(A, Names),
  {StrB, NB} = pp_pattern(B, Names),
  {stringformat("(PCons ~s ~s)", [StrA, StrB]), NA ++ NB}.

pp_pattern_map({A, B}, Names) ->
  {StrA, NA} = pp_pattern(A, Names),
  {StrB, NB} = pp_pattern(B, Names),
  {stringformat("(~s,~s)", [StrA, StrB]), NA ++ NB}.

%% Binary patterns
%% A literal bitstring is matched as one big-endian unsigned integer segment of the same width.
pp_pattern_bitstring(Bits) ->
  case bit_size(Bits) of
    0 -> {"(PBin [])", []};
    N -> <<V:N>> = Bits,
         {stringformat("(PBin [(Build_Segment (PLit (Integer (~s))) (VLit (Integer (~s))) 1 IntType Unsigned BigEndian)])",
                       [integer_to_list(V), integer_to_list(N)]), []}
  end.

pp_pattern_segment(#c_bitstr{val=V, size=Sz} = S, Names) ->
  {Unit, Type, Sign, Endian} = pp_segment_attrs(S),
  {PatStr, PatVars} = pp_pattern(V, Names),
  {stringformat("(Build_Segment ~s ~s ~s ~s ~s ~s)", [PatStr, pp_segment_size(Sz, Names), Unit, Type, Sign, Endian]),
   PatVars}.

%% The size of a pattern segment is a value: an integer, the atom `all`/`undefined`, or a variable.
%% The variable must be bound outside of the pattern: a size that depends on an earlier segment
%% of the same pattern (e.g. <<Len:8, Data:Len/binary>>) is not supported by the Rocq syntax.
pp_segment_size(#c_literal{val=I}, _) when is_integer(I) ->
  "(VLit (Integer (" ++ integer_to_list(I) ++ ")))";
pp_segment_size(#c_literal{val=A}, _) when is_atom(A) ->
  "(VLit (Atom " ++ hs_string(atom_to_list(A)) ++ "))";
pp_segment_size(#c_var{name=N}, Names) ->
  case maps:find(N, Names) of
    {ok, I} -> "(VVar " ++ integer_to_list(I) ++ ")";
    error   -> throw({unsupported_case, segment_size_bound_in_same_pattern, N})
  end.
