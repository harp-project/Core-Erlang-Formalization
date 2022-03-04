
Require Core_Erlang_Semantics.
Require Core_Erlang_Functional_Big_Step.

Import Core_Erlang_Syntax.Syntax.
Export Core_Erlang_Environment.Environment.
Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Functional_Big_Step.Functional_Big_Step.


Module ModuleHelper.



Import ListNotations.


(* Tests *)
Definition X : string := "X"%string.
Definition Y : string := "Y"%string.


Definition m1 : ErlModule := (
    "a"%string,
    [("fun0"%string, 0)],
    [],
    [( ("fun0"%string, 0) , EFun [] (ELit (Integer 10)))]

).
(* TODO: Check: Same function name with different paramters *)
Definition m2 : ErlModule :=  ("b"%string , 
                        [
                            ("fun0"%string, 0);
                            ("fun1"%string, 1);
                            ("test1"%string, 2);
                            ("+"%string, 2)
                            
                        ],
                        [],
                        [
                            ( ("fun0"%string, 0) , EFun [] (ELit (Integer 4)));
                            (("fun1"%string, 1) , EFun [X] (EVar X));
                            (("test1"%string, 2), EFun [X;Y] (EVar Y) );
                            (("+"%string, 2), EFun [X;Y] (EVar Y) )
                        ])
.

Definition modules := [m1; m2].


(* Example: ECall "b" "fun0" [] *)
Definition app : Expression := EApp (EFun [X] (EVar X)) [ELit (Integer 5)]. (* Az ECall "b" "fun1" [ELit (Integer 4)] -nek is ezt *)

Definition call : Expression := ECall "b" "fun1" [ELit (Integer 5)].

Definition that := fbs_expr 10 [] modules 0 app [] .
Definition this := fbs_expr 10 [] modules 0 call [] .

Compute that.
Compute this.

(* Call tests *)
Definition call1 : Expression := ECall "b" "test1" [(ELit (Integer 4))].
Compute fbs_expr 10 [] modules 0 call1 [] .


Definition call2 : Expression := ECall "erlang" "+" [(ELit (Integer 4)) ;(ELit (Integer 12))].
Compute fbs_expr 10 [] modules 0 call2 [] .

Compute fbs_expr 1000 [] modules 1 (ECall "erlang" "+" [ELit (Integer 5); ETuple []]) [].


    
End ModuleHelper.

