-module(cst_to_ast).
-export([from_core/2, from_erl/2]).
-include_lib("compiler/src/core_parse.hrl").

-define(frameStack,"~s").

-define(functional_limit, 1000000).


from_erl(Path, OutFile)  -> write_to_file(OutFile, do_pp(compile:file(Path, [           to_core, binary, no_copt]))).
from_core(Path, OutFile) -> write_to_file(OutFile, do_pp(compile:file(Path, [from_core, to_core, binary, no_copt]))).

do_pp(V) ->
  case V of
    {ok, _, CST     } -> io_lib:format(?frameStack, [pretty_print_fs:pp_module(CST)]);
    {ok, _, CST, _Ws} -> io_lib:format(?frameStack, [pretty_print_fs:pp_module(CST)]);
     error            -> error;
    {error, _Es, _Ws} -> error
  end.

write_to_file(Filename, Content) ->
    write_to_file(Filename, Content, write).

write_to_file(Filename, Content, Mode) ->
    case file:open(Filename, [Mode]) of
        {ok, Fd} ->
            file:write(Fd, Content),
            file:close(Fd);
        {Status, Msg} ->
            io:format("Error opening file ~s: ~s", [Status, Msg])
    end.



