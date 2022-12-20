From CoreErlang Require Export Syntax.

(** The side-effects of Core Erlang *)
Import ListNotations.

Inductive SideEffectId : Set :=
| Input
| Output
.

Definition SideEffectList : Type := list (SideEffectId * list Val).
