
(*
  Things to think about:
  - PID-compatibility - bijectivity between the refered and taken PIDs in a system
    - (refered PIDs -- taken PIDs) <- does this give the context?
  - Does db-indexing PIDs make sense?
  -

*)

From CoreErlang Require Import Concurrent.NodeSemantics.

Import ListNotations.

(* Definition dom (Π : ProcessPool) (l : list PID) : Prop :=
  forall ι, ((Π ι <> None)%type -> In ι l) /\
            (Π ι = None -> ~In ι l). *)

Definition isUnTaken (ι : PID) (Π : ProcessPool) : Prop :=
  Π ι = None.

Definition isPreCompatible (Π₁ Π₂ : ProcessPool) : Prop :=
  forall ι, isUnTaken ι Π₁ -> isUnTaken ι Π₂.

(* Definition isCompatible (Π₁ Π₂ : ProcessPool) : Prop :=
  isPreCompatible Π₁ Π₂ /\ isPreCompatible Π₂ Π₁. *)


(** This is needed to ensure that a process is not spawned with a wrong PID
    in the equivalence. *)
Definition PIDOf (a : Action) : option PID :=
  match a with
  | ASpawn ι _ _ => Some ι
  | _ => None
  end.

(* TODO: do this with Applicative/Monad *)
Fixpoint PIDsOf (l : list (Action * PID)) : list PID :=
  match l with
  | [] => []
  | (a, _) :: xs =>
    match PIDOf a with
    | Some ι => [ι]
    | None => []
    end ++ PIDsOf xs
  end.

Definition isPreCompatibleReductions
  (n1 n2 : Node) l
  : Prop :=
  isPreCompatible (snd n1) (snd n2) /\
  Forall (fun ι' => isUnTaken ι' (snd n2)) (PIDsOf l).

(* Definition isCompatibleReduction
  {Π₁ Π₂ Π₁' Π₂' : ProcessPool} {e1 e2 e1' e2' : Ether} {l l'}
  (red1 : (e1, Π₁) -[l]ₙ->* (e1', Π₁'))
  (red2 : (e2, Π₂) -[l']ₙ->* (e2', Π₂'))
  : Prop :=
  isPreCompatibleReductions red1 red2 /\
  isPreCompatibleReductions red2 red1. *)

(* This does not say anything about the equivalence of actions *)
Definition simulates (S : Node -> Node -> Prop) :=
  forall n₁ n₁' n₂ a ι (pf : S n₁ n₂) (red : n₁ -[a | ι]ₙ-> n₁'),
    exists n₂' l, n₂ -[l]ₙ->* n₂' /\ isPreCompatibleReductions n₁ n₂ l /\ S n₁' n₂'.
