
(*
  Lessons learned:
  - PIDsOf cannot be defined for the co-inductive version
  - using functions for process pools is
    - simple for the definitions
    - hard, if its properties (e.g., dom) is needed
  - Bisimulations
    - Playing with bisimulation in Erlang -> this paper only considers ethers
      and defines observations based on the "dangling" messages
    - The usual notion of bisimulations involves checking equality on actions, 
      however, in this case we could not reason about systems using different 
      PIDs.
    - Bisimulations + bijective function on the PIDs? Drawback: we have to 
      somehow rename all PIDs in signals/messages, which might be impossible
      for closure values (because they include a body expression which could
      contain e.g., "self()" calls, where the PID is not syntactically there).
        ^---- would be enough to observe the "type" of these actions?
      - How "deep" action parameters should be investigated? Should they
        be equivalent, or check only the type, or nothing?
      - Could we rename PIDs in the bisimilar systems for the first time,
        so that PID bijection is not needed (the currently existing PIDs
        of the system), and then suppose that the processes spawn with the same
        PIDs? <- probably not
      - Observable behaviour: signals exiting the system, but not the internal
        signals and communication -> unTaken PIDs should be observed in the ether
    - Strong bisimulation: the two systems have to do the same steps
      - I don't see besides equality a relation that could satisfy this
    - Weak bisimulation: the two systems have to do the same communication steps
      - Too restrictive to reason about systems that use a different number of
        communication steps (e.g., server that catches errors vs server that is
        re-created when errors occur)
    - "Barbed bisimulation": the two systems should produce the same signals to
      the outside world + the evolution of the systems should preserve the relation
      - Too many soft definitions in the papers - e.g., "used PID"
        - Does it include only dangling signals, or all used pids?

      - Does Lemma 1 of Playing with Bisimulation in Erlang hold for us? e.g.,
        (ether, ι ↦ ι' ! 'cat') -[arrive(exit, ι)]-> (ether, ι ↦ deadproc)
        (ether, ι ↦ ι' ! 'cat') -[send('cat', ι')]-> (ether ∪ {(ι, ι', 'cat')}, ι ↦ 'cat')
*)

From CoreErlang Require Import Concurrent.InductiveNodeSemantics.

Import ListNotations.

(* Definition dom (Π : ProcessPool) (l : list PID) : Prop :=
  forall ι, ((Π ι <> None)%type -> In ι l) /\
            (Π ι = None -> ~In ι l). *)

(* This is wrong: it should also contain that ι is used in Π, but it is
   not associated with a process *)
Definition isUnTaken (ι : PID) (Π : ProcessPool) : Prop :=
  Π ι = None.

Definition isPreCompatible (Π₁ Π₂ : ProcessPool) : Prop :=
  forall ι, isUnTaken ι Π₁ -> isUnTaken ι Π₂.

(* Definition isCompatible (Π₁ Π₂ : ProcessPool) : Prop :=
  isPreCompatible Π₁ Π₂ /\ isPreCompatible Π₂ Π₁. *)
Goal
  isPreCompatible
    (0 ↦ inl ([], RExp (`VNil), ([], []), [], false) ∥ 1 ↦ inl ([], RExp (`VNil), ([], []), [], false) ∥ nullpool)
    (0 ↦ inl ([], RExp (`VNil), ([], []), [], false) ∥ 1 ↦ inr [] ∥ nullpool).
Proof.
  unfold isPreCompatible, isUnTaken in *.
  intros.
  destruct ι; cbn in *.
  congruence.
  destruct ι; cbn in *.
  congruence.
  assumption.
Qed.

Goal
  isPreCompatible
    (10 ↦ inl ([], RExp (`VNil), ([], []), [], false) ∥ 13 ↦ inl ([], RExp (`VNil), ([], []), [], false) ∥ nullpool)
    (13 ↦ inl ([], RExp (`VNil), ([], []), [], false) ∥ 10 ↦ inr [] ∥ nullpool).
Proof.
  unfold isPreCompatible, isUnTaken in *.
  intros.
  destruct (Nat.eq_dec ι 13).
  * subst. cbn in *. congruence.
  * destruct (Nat.eq_dec ι 10).
    - subst. cbn in *. congruence.
    - rewrite update_next. rewrite update_next. all: auto.
Qed.

(* Definition isPreCompatibleReductions
  (n1 n2 : Node) l
  : Prop :=
  isPreCompatible (snd n1) (snd n2) /\
  Forall (fun ι' => isUnTaken ι' (snd n2)) (PIDsOf l). *)

(* Definition isCompatibleReduction
  {Π₁ Π₂ Π₁' Π₂' : ProcessPool} {e1 e2 e1' e2' : Ether} {l l'}
  (red1 : (e1, Π₁) -[l]ₙ->* (e1', Π₁'))
  (red2 : (e2, Π₂) -[l']ₙ->* (e2', Π₂'))
  : Prop :=
  isPreCompatibleReductions red1 red2 /\
  isPreCompatibleReductions red2 red1. *)

(* This does not say anything about the equivalence of actions
   TODO: this definition does not include the equivalence of ethers, which
   is included in Lanese et al. Playing with bisimulation in Erlang
*)
(* Definition simulates (S : Node -> Node -> Prop) :=
  forall n₁ n₁' n₂ a ι (pf : S n₁ n₂) (red : n₁ -[a | ι]ₙ-> n₁'),
    exists n₂' l, n₂ -[l]ₙ->* n₂' /\ isPreCompatibleReductions n₁ n₂ l /\ S n₁' n₂'. *)
