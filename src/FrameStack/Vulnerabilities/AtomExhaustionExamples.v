(**
  This file contains example programs which are vulnerable to atom
  exhaustion, together with proofs of their vulnerability, based on the
  definitions of `AtomExhaustion.v` (see also the paper
  https://dl.acm.org/doi/10.1145/3759161.3763045). The examples are:
  - a single call of `list_to_atom`;
  - `infinite_atom_g`, an infinite loop creating a new atom in each
    iteration, including a discussion of why atom exhaustion is proved
    through GALNUA instead of directly;
  - `sum_example`, a recursive sum function creating an atom for each
    number it visits; for this, the vulnerability is proved for arbitrary
    atom limits (`sum_is_vulnerable`).
*)

From Stdlib Require Import DecimalFacts.
From Stdlib Require Import DecimalPos.

From CoreErlang.FrameStack Require Import SubstSemanticsLabeledLemmas.
From stdpp Require Import gmap sets.

From CoreErlang.FrameStack.Vulnerabilities Require Import AtomExhaustion.
Import Notations.

Open Scope string_scope.

Module AtomExhaustionExamples.

Import ListNotations.
Import AtomExhaustion.

(** * A single atom creation *)

(** `list_to_atom("hello")` *)
Definition call_of_list_to_atom: Exp :=
  ECall (˝VLit "erlang") (˝VLit "list_to_atom")
    [˝VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil)))))].

(** Takes one step of a GALNUA derivation: finishes it with
    `generates_terminal`, or takes a step creating a new atom, or takes
    any other step. *)
Ltac apply_proper_constr :=
  eapply generates_terminal || (
  (eapply generates_step_true_unique; simpl;
    [econstructor; reflexivity
    |set_solver 
    |]) || (
  eapply generates_step_false; simpl;
    [econstructor; try (reflexivity || scope_solver || congruence)
    |simpl]
)).

(** `list_to_atom("hello")` creates a new atom. *)
Local Example list_to_atom_galnua :
  generates_at_least_n_unique_atoms [] call_of_list_to_atom ∅ 1.
Proof.
  unfold call_of_list_to_atom.
  repeat apply_proper_constr.
Qed.

(** * An infinite loop creating atoms *)

(** `g(N) -> list_to_atom([$a, N]), g(N + 1).` applied to `e` *)
Definition infinite_atom_g (e : Exp) : Exp :=
  ELetRec
    [(1, °ELet 1
      (˝VCons (VLit 97%Z) (VCons (VVar 1) (VNil)))
      (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom") [˝VVar 0])
             (°ELet 1
                (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit 1%Z])
                (EApp (˝VFunId (2, 1)) [˝VVar 0]))))]
    (EApp (˝VFunId (0, 1)) [e]).

(** Takes `n` steps of a labeled multi-step evaluation. *)
Ltac do_n_do_step n :=
lazymatch goal with
| [ |- ⟨_ , _⟩ -[_, _]->ₗ ⟨_ , _⟩] => 
  match n with
  | 0 => idtac "reached zero"
  | S ?n' =>
      eapply SubstSemanticsLabeled.step_trans;
      [econstructor;(scope_solver || auto)
      |simpl;do_n_do_step n'
      |simpl;try auto;try cbn]
  end
| _ => idtac "failed to match"
end.

Goal atom_exhaustion (infinite_atom_g (˝VLit (Integer 0))) 20.
Proof.
  unfold atom_exhaustion, atom_exhaustion_aux.
  (* First obstacle: if we don't know the exact end destination
     FrameStack and Redex, as well as the list of SideEffects, that
     have produced, then we cannot apply 'exists' tactic *)
  do 3 eexists. split.
  - eexists.
    (* Second obstacle: since we need to construct a relation of
       step_rt, we can do it in two ways. By applying step_refl (which
       we can do at any point) or by applying step_trans constructor.

       As it was said, step_refl can be applied at ANY point of the proof.
       And it is also the default behavior of the constructor tactic. *)
    constructor.
    (* But obviously, the resulting statement in this case is unprovable,
       since the sufficient amount of atoms is not produced in the assumed
       l, which was fixed by solving the previous goal. *)
  -
Set Warnings "-undo-batch-mode".
Restart.
Set Warnings "+undo-batch-mode".
  unfold atom_exhaustion, atom_exhaustion_aux.
  do 3 eexists. split.
  - eexists.
    (* This behavior obviously presents some problems for implementing 
       automatisation tactics. *)
    do_step_labeled. do_step_labeled. do_step_labeled.
    (* Third obstacle: as you may see in the environment tab, by using
       step_trans constructor, the number of goals will get inadvertently
       bloated (due to the design of the step_trans constructor), which
       decreases readability and efficiency. *)
Set Warnings "-undo-batch-mode".
Restart.
Set Warnings "+undo-batch-mode".
  unfold atom_exhaustion, atom_exhaustion_aux.
  do 3 eexists. split.
  - eexists. eapply transitive_eval_labeled.
    (* Fourth obstacle: it can be observed, that until the -[?k, ?l]->
       is constructed and closed with step_refl, the data structures a
       proof engineer deals with to store the amassed SideEffects are
       simple lists. That presents a challenge: we want to apply step_refl
       when the number of the unique atoms in the resulting, but it is
       hard to reason about this, when one's only have lists, which may
       contain duplicates. *)
    +
    (* Notice how we will only see ?l in the last goal. But what if we have
       100 applications of SubstSemanticsLabeledLemmas.transitive_eval? Will
       a proof engineer have to unfocus his current subgoal and scroll down
       to the end of the list every time he wants to see the current progress? *)
Abort. (* That's not an option *)

(** `g(0)` creates at least 10 new atoms. *)
Theorem inf_atom_g: generates_at_least_n_unique_atoms []
  (infinite_atom_g (˝VLit (Integer 0))) ∅ 10.
Proof.
  unfold infinite_atom_g.
  repeat apply_proper_constr.
  (* This, however, is much more elegant, albeit slow *)
Qed.

(** * A recursive function creating atoms *)

(** `sum(0) -> 0; sum(N) -> list_to_atom([$a | integer_to_list(N)]),
    N + sum(N - 1).` applied to `e` *)
Definition sum_example (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 0%Z));
      ([PVar], ˝ttrue,
        (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom")
                  [°ECons (˝VLit 97%Z) (°ECall (˝VLit "erlang") (˝VLit "integer_to_list") [˝VVar 0])])
               (°ELet 1 (EApp (˝VFunId (1, 1))
                  [°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VLit 1%Z]])
                  (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 1; ˝VVar 0])))
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e]).

(** `sum(3)` creates at least 3 new atoms. *)
Theorem sum_atom_g : exists e,
  generates_at_least_n_unique_atoms [] (sum_example e) ∅ 3.
Proof.
  exists (˝VLit (Integer 3)).
  unfold sum_example.
  do 9 apply_proper_constr.
  (* Technical caveat of the tactic due to econstructor on match *)
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  do 42 apply_proper_constr.
  replace (3 - 1)%Z with 2%Z by lia.
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  do 42 apply_proper_constr. replace (2 - 1)%Z with 1%Z by lia.
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  repeat apply_proper_constr.
Qed.

(** Simplifies `avs ∪ ∅` to `avs` in the goal. *)
Ltac inf_atom_helper_avs:=
match goal with
| [|- context [?avs ∪ ∅]] =>
    replace (avs ∪ ∅) with avs by set_solver
end.

(** Simplifies `n - size s` in the goal, where `s` is a singleton set, as
    in the iterations of `infinite_atom_g`, which create one atom each. *)
Ltac inf_atom_helper_size :=
match goal with
| [|- context [?n - size (?s)]] =>
    cbn; replace (size s) with 1 by set_solver; cbn; simpl
end.

(** `g(0)` creates more than 10 atoms; proved by composing the evaluations
    of single iterations (`Reach`) with `GALNUA_multistep_rev_alt`. *)
Local Example infinite_atom_g_AE_10 : atom_exhaustion
  (infinite_atom_g (˝VLit (Integer 0))) 10.
Proof.
  (* ----------------------------------------------------------- *)
  remember (˝ VClos
  [(0, 1,
    ° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
    (° ESeq (° ECall (˝ VLit "erlang") (˝ VLit "list_to_atom") [˝ VVar 0])
      (° ELet 1 (° ECall (˝ VLit "erlang") (˝ VLit "+") [˝ VVar 2; ˝ VLit 1%Z])
      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0]))))] 0 1
  (° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
    (° ESeq (° ECall (˝ VLit "erlang") (˝ VLit "list_to_atom") [˝ VVar 0])
      (° ELet 1 (° ECall (˝ VLit "erlang") (˝ VLit "+") [˝ VVar 2; ˝ VLit 1%Z])
      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0]))))) as closRedex.
  (* ----------------------------------------------------------- *)
  assert (forall (z: Z), (0 <= z <= 255)%Z -> ⟨[FApp1 [˝ VLit z]], closRedex⟩
    -[[(AtomCreation, [VLit (String (ascii_of_nat (Z.to_nat 97))
       (String (ascii_of_nat (Z.to_nat z)) ""))])]]->ₗ*
      ⟨[FApp1 [˝ VLit (z + 1)%Z]], closRedex⟩) as Reach.
  { subst. intros z Hz. eexists.
    assert (Hb : ((0 <=? z)%Z && (z <=? 255)%Z) = true).
    { apply andb_true_intro. split; apply Z.leb_le; lia. }
    do_n_do_step 16.
    (* list_to_atom only accepts character codes in 0..255 *)
    eapply SubstSemanticsLabeled.step_trans.
    - econstructor. cbn. rewrite Hb. reflexivity.
    - simpl. do_n_do_step 14. apply SubstSemanticsLabeled.step_refl.
    - simpl. reflexivity. }
  subst.
  (* ----------------------------------------------------------- *)
  apply soundness. simpl.
  do 2 apply_proper_constr.
  do 11 (eapply GALNUA_multistep_rev_alt;
    [apply Reach; lia|]; inf_atom_helper_size; inf_atom_helper_avs).
  apply_proper_constr.
Qed.

(** The side-effect trace of `sum(n)`: the atoms `an`, ..., `a1`. *)
Fixpoint mk_sum_atom_list (n: nat) :=
match n with
| O => []
| S n' => ((AtomCreation, [(VLit
  (String (ascii_of_nat 97) (NilZero.string_of_int (Z.to_int (Z.of_nat n)))))]):SideEffect)
  :: mk_sum_atom_list n'
end.

(** The atoms of `mk_sum_atom_list n` are pairwise distinct. *)
Lemma mk_sum_atom_list_size m :
  size (mk_atom_set (mk_sum_atom_list m)) = m.
Proof.
  induction m; simpl. set_solver.
  rewrite mk_atom_set_union.
  rewrite size_union. rewrite IHm. rewrite size_singleton. lia.
  apply disjoint_singleton_l.
  clear.
  apply not_elem_of_list_to_set.
  intro.
  apply list_elem_of_omap in H as [[id vl] [H0 H]].
  destruct id; try congruence.
  destruct vl as [|v vl]; try congruence.
  destruct v; try congruence.
  destruct l; try congruence.
  destruct vl; try congruence.
  inv H.
  rewrite Pos.of_nat_succ in H0.
  assert (S m > m) by lia.
  remember (S m) as k. clear Heqk.
  generalize dependent k.
  induction m; intros; simpl in *.
  - set_solver.
  - apply elem_of_cons in H0 as [].
    + inversion H0 as [Hs].
      clear - Hs H.
      rewrite Pos.of_nat_succ in Hs.
      apply NilZero_string_of_uint_inj in Hs.
      2-3: apply Unsigned.to_uint_nonnil.
      apply Unsigned.to_uint_inj in Hs.
      apply Nat2Pos.inj in Hs; lia.
    + eapply IHm. exact H0. lia.
Qed.

(** `sum(n)` evaluates to `n * (n + 1) / 2`, producing the trace
    `mk_sum_atom_list n`. *)
Theorem sum_eval (n: nat) :
  ⟨[], sum_example (˝VLit (Z.of_nat n))⟩
    -[mk_sum_atom_list n]->ₗ*
  ⟨[], RValSeq [VLit (Z.div (Z.of_nat ((n + 1) * n)) 2%Z)]⟩.
Proof.
  unfold sum_example. induction n.
  - eexists. do_n_do_step 13. econstructor.
  - inv IHn. inv H. inv H0. simpl in H1. inv H1. inv H. inv H0. inv H.
    inv H1. inv H. inv H0. inv H. inv H1. inv H.
    inv H0. inv H. simpl in H9. inv H9. eexists.
    (* ---------------------------------------------------------- *)
    do_n_do_step 9. eapply SubstSemanticsLabeled.step_trans.
    eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
    do_n_do_step 22.
    do_step_labeled. {
      clear H1. cbn.
      rewrite string_to_vcons_mk_ascii_list.
      cbn. rewrite string_of_list_ascii_of_string.
      reflexivity.
    }
    do_n_do_step 17.
    eapply transitive_eval_labeled.
    replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n)%Z by lia.
    { eapply (frame_indep_nil_labeled _ _ _ _ _ H1). }
    all: clear H1. do_n_do_step 11. unfold eval_arith. simpl.
    (* ---------------------------------------------------------- *)
    + replace 2%Z with (Z.of_nat 2) by lia.
      rewrite <- Nat2Z.inj_div, <- Nat2Z.inj_add, <- Nat2Z.inj_div.
      replace (S (n+(n+1) * S n)) with ((S n * 2) + ((n+1)*n)) by lia.
      rewrite Nat.div_add_l; auto. econstructor.
    + replace (Z.to_nat 97) with 97 by lia.
      replace (Z.to_nat (Z.of_nat (S n))) with (S n) by lia.
      rewrite app_nil_r. reflexivity.
    + simpl in *. subst. reflexivity.
Qed.

(** `sum(11)` creates more than 10 atoms. *)
Local Example sum_AE_10 : exists e, atom_exhaustion (sum_example e) 10.
Proof.
  exists (˝VLit (Integer 11)). apply soundness; simpl.
  pose proof sum_eval. eapply GALNUA_multistep_rev_alt.
  replace 11%Z with (Z.of_nat 11) by lia. apply H. clear H.
  rewrite difference_empty_L, mk_sum_atom_list_size. apply_proper_constr.
Qed.

(** `sum(n + 1)` creates more than `n` atoms. *)
Lemma sum_general_AE : forall n, atom_exhaustion (sum_example (˝VLit (Z.of_nat (S n)))) n.
Proof.
  intros. apply soundness; simpl.
  pose proof sum_eval. eapply GALNUA_multistep_rev_alt.
  apply H. clear H.
  rewrite difference_empty_L, mk_sum_atom_list_size.
  replace (n + 1 - S n) with 0 by lia. apply_proper_constr.
Qed.

(** `sum` is vulnerable to atom exhaustion for any atom limit. *)
Lemma sum_is_vulnerable :
  forall atom_limit, exists m,
    atom_exhaustion (sum_example (˝VLit (Z.of_nat m))) atom_limit.
Proof.
  eexists. apply sum_general_AE.
Qed.

End AtomExhaustionExamples.