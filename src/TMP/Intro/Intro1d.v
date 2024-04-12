From CoreErlang.FrameStack Require SubstSemantics.


Open Scope string_scope.


Module FrameStack.


Import FrameStack.SubstSemantics.


Import ListNotations.


(* Define the following function in Core Erlang! To compile a Core Erlang file
   use the "from_core" option of the standard compiler/interpreter.
   For examples, we refer to the language specification:
   https://www.it.uu.se/research/group/hipe/cerl/doc/core_erlang-1.0.3.pdf
   You can also check example codes in the Erl_codes folder.
   Instead of the letrec expression, define it as a top level function *)
Definition collatz (e : Exp) : Exp :=
  ELetRec [
    (1, °ECase (˝VVar 1)
     [
       ([PLit 1%Z], ˝ttrue, ˝VNil);
       ([PVar],
          °ECall (˝erlang) (˝VLit "and") [
            °ECall (˝erlang) (˝VLit "<") [˝VLit 0%Z; ˝VVar 0];
            °ECall (˝erlang) (˝VLit "=") [
              ˝VLit 0%Z;
              °ECall (˝erlang) (˝VLit "rem") [˝VVar 0; ˝VLit 2%Z]
            ]
          ],
         °ECons (˝VVar 0) (EApp (˝VFunId (1,1)) [
           °ECall (˝erlang) (˝VLit "div") [˝VVar 0; ˝VLit 2%Z]
         ])
       );
       ([PVar], °ECall (˝erlang) (˝VLit "<") [˝VLit 0%Z; ˝VVar 0],
         °ECons (˝VVar 0) (EApp (˝VFunId (1,1)) [
           °ECall (˝erlang) (˝VLit "+")
             [°ECall (˝erlang) (˝VLit "*") [˝VLit 3%Z; ˝VVar 0];
              ˝VLit 1%Z]
         ])
       )
     ])
  ]
  (EApp (˝VFunId (0, 1)) [e]).

(*
'collatz'/1 =
    ( fun(X) ->
     	( case <X> of
        	<1> when 'true' 
				-> []
        	<Z> when call 'erlang':'and' (call 'erlang':'<' (0,  Z), call 'erlang':'==' (0,  call 'erlang':'rem' (Z, 2)))
  				-> let <Y> = apply ‘collatz’/1(call 'erlang':'div' (Z, 2))
					in [Z|Y]
       		<Z> when call 'erlang':'<' (0,  Z)
  				-> let <Y> = apply ‘collatz’/1(call 'erlang':'+' (call 'erlang':'*' (3, Z), 1))
					in [Z|Y] )
    -| [{'function',{'collatz',1}}] )
*)

End FrameStack.