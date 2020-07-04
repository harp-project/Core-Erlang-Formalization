Require Core_Erlang_Environment.

(** The side-effects of Core Erlang *)
Module Side_Effects.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Syntax.Syntax.
(* Import Core_Erlang_Closures. *)

Inductive SideEffectId : Set :=
| Input
| Output
.

Definition SideEffectList : Type := list (SideEffectId * list Value).

Definition concatn (def : SideEffectList) (l : list SideEffectList) (n : nat) : SideEffectList :=
   def ++ concat (firstn n l).


Compute concatn [(Input, [VLit (Atom "a"%string)] )] 
                [ [(Input, [VLit (Atom "a"%string)] )];
                  [(Input, [VLit (Atom "b"%string)] )]; 
                  [(Input, [VLit (Atom "c"%string)] )] ] 
                0.

End Side_Effects.