{module, weird}.  %% version = 0

{exports, [{f,0},{module_info,0},{module_info,1}]}.

{attributes, []}.

{labels, 19}.


{function, f, 0, 2}.
  {label,1}.
    {line,[]}.
    {func_info,{atom,weird},{atom,f},0}.
  {label,2}.
    {allocate,6,0}.
    {init_yregs,{list,[{y,0},{y,1},{y,2},{y,3},{y,4},{y,5}]}}.
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
    {test,is_eq_exact,{f,4},[{x,0},{integer,2}]}.
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
    {loop_rec,{f,7},{x,0}}.
    remove_message.
    {move,{x,0},{y,5}}.
    {jump,{f,8}}.
  {label,7}.
    timeout.
    {move,{atom,noval},{y,5}}.
  {label,8}.
    {loop_rec,{f,9},{x,0}}.
    remove_message.
    {move,{x,0},{y,1}}.
    {jump,{f,10}}.
  {label,9}.
    timeout.
    {move,{atom,noval},{y,1}}.
  {label,10}.
    {loop_rec,{f,11},{x,0}}.
    remove_message.
    {move,{x,0},{y,0}}.
    {jump,{f,12}}.
  {label,11}.
    timeout.
    {move,{atom,noval},{y,0}}.
  {label,12}.
    {loop_rec,{f,13},{x,0}}.
    remove_message.
    {jump,{f,14}}.
  {label,13}.
    timeout.
    {move,{atom,noval},{x,0}}.
  {label,14}.
    {test_heap,10,1}.
    {put_tuple2,{x,0},{list,[{y,5},{y,1},{y,0},{x,0}]}}.
    {put_tuple2,{x,0},{list,[{y,4},{y,3},{y,2},{x,0}]}}.
    {deallocate,6}.
    return.


{function, module_info, 0, 16}.
  {label,15}.
    {line,[]}.
    {func_info,{atom,weird},{atom,module_info},0}.
  {label,16}.
    {move,{atom,weird},{x,0}}.
    {call_ext_only,1,{extfunc,erlang,get_module_info,1}}.


{function, module_info, 1, 18}.
  {label,17}.
    {line,[]}.
    {func_info,{atom,weird},{atom,module_info},1}.
  {label,18}.
    {move,{x,0},{x,1}}.
    {move,{atom,weird},{x,0}}.
    {call_ext_only,2,{extfunc,erlang,get_module_info,2}}.
