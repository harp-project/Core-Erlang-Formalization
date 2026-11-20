(** This file defines side-effect traces: input and output logs, and logs of
    atom creation. These side effects are produced by the built-in functions
    (see `Auxiliaries.v`), and are traced by the labeled frame stack semantics
    (see `FrameStack/SubstSemanticsLabeled.v`).
*)

From CoreErlang Require Export Syntax.

Import ListNotations.

(** The kinds of side effects:
    - `Input`: reading from the input (`io:fread`); its log contains the
      arguments of the call.
    - `Output`: writing to the output (`io:fwrite`); its log contains the
      arguments of the call.
    - `AtomCreation`: creation of a new atom at run time (e.g., by
      `list_to_atom`); its log contains the created atom. *)
Inductive SideEffectId : Set :=
| Input
| Output
| AtomCreation
.

(** A side effect: its kind, and the values logged with it. *)
Definition SideEffect : Set := SideEffectId * list Val.

(** Side-effect traces. *)
Definition SideEffectList : Set := list SideEffect.
