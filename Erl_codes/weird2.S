{module, weird2}.  %% version = 0

{exports, [{f,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 22}.


{function, f, 0, 2}.
  {label,1}.
    {line,[]}.
    {func_info,{atom,weird2},{atom,f},0}.
  {label,2}.
    {allocate_heap,6,{alloc,[{words,0},{floats,0},{funs,1}]},0}.
    {init_yregs,{list,[{y,0},{y,1},{y,2},{y,3},{y,4},{y,5}]}}.
    {make_fun3,{f,21},0,0,{x,0},{list,[]}}.
    {call_ext,1,{extfunc,erlang,spawn,1}}.
    {bif,self,{f,0},[],{x,0}}.
    {move,{integer,1},{x,1}}.
    send.
    {bif,self,{f,0},[],{x,0}}.
    {move,{integer,2},{x,1}}.
    send.
    {bif,self,{f,0},[],{x,0}}.
    {move,{integer,3},{x,1}}.
    send.
    {'try',{y,5},{f,6}}.
  {label,3}.
    {loop_rec,{f,5},{x,0}}.
    {test,is_eq_exact,{f,4},[{x,0},{integer,3}]}.
    {fmove,{float,1.0},{fr,0}}.
    {fmove,{float,0.0},{fr,1}}.
    {bif,fdiv,{f,0},[{fr,0},{fr,1}],{fr,0}}.
  {label,4}.
    {loop_rec_end,{f,3}}.
  {label,5}.
    {wait,{f,3}}.
  {label,6}.
    {try_case,{y,5}}.
    {move,{x,2},{y,2}}.
    {move,{x,1},{y,3}}.
    {move,{x,0},{y,4}}.
  {label,7}.
    {wait_timeout,{f,7},{integer,10}}.
    timeout.
    {loop_rec,{f,8},{x,0}}.
    remove_message.
    {move,{x,0},{y,5}}.
    {jump,{f,9}}.
  {label,8}.
    timeout.
    {move,{atom,noval},{y,5}}.
  {label,9}.
    {loop_rec,{f,10},{x,0}}.
    remove_message.
    {move,{x,0},{y,1}}.
    {jump,{f,11}}.
  {label,10}.
    timeout.
    {move,{atom,noval},{y,1}}.
  {label,11}.
    {loop_rec,{f,12},{x,0}}.
    remove_message.
    {move,{x,0},{y,0}}.
    {jump,{f,13}}.
  {label,12}.
    timeout.
    {move,{atom,noval},{y,0}}.
  {label,13}.
    {loop_rec,{f,14},{x,0}}.
    remove_message.
    {jump,{f,15}}.
  {label,14}.
    timeout.
    {move,{atom,noval},{x,0}}.
  {label,15}.
    {test_heap,10,1}.
    {put_tuple2,{x,0},{list,[{y,5},{y,1},{y,0},{x,0}]}}.
    {put_tuple2,{x,0},{list,[{y,4},{y,3},{y,2},{x,0}]}}.
    {deallocate,6}.
    return.


{function, module_info, 0, 17}.
  {label,16}.
    {line,[]}.
    {func_info,{atom,weird2},{atom,module_info},0}.
  {label,17}.
    {move,{atom,weird},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 19}.
  {label,18}.
    {line,[]}.
    {func_info,{atom,weird2},{atom,module_info},1}.
  {label,19}.
    {move,{x,0},{x,1}}.
    {move,{atom,weird},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.


{function, '-f/0-anonymous-0-', 0, 21}.
  {label,20}.
    {line,[]}.
    {func_info,{atom,weird2},{atom,'-f/0-anonymous-0-'},0}.
  {label,21}.
    {move,{literal,"o"},{x,0}}.
    {call_ext_only,1,{extfunc,io,fwrite,1}}.
