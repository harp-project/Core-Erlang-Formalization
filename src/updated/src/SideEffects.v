(* Require Core_Erlang_Environment. *)
Require Export ExpSyntax.

(** The side-effects of Core Erlang *)
Module Side_Effects.

(*Export Core_Erlang_Helpers.Helpers.*)

Import ListNotations.

Inductive SideEffectId : Set :=
| Input
| Output
.

Definition SideEffectList : Type := list (SideEffectId * list ValueExpression).

End Side_Effects.