From CoreErlang.FrameStack Require Import SubstSemanticsLabeledLemmas.
From stdpp Require Import gmap sets.
Require Import AtomExhaustion.
Require Import List.

Open Scope string_scope.

Module AtomExhaustionExamples.

Import ListNotations.

Definition call_of_list_to_atom: Exp :=
  ECall (˝VLit "erlang") (˝VLit "list_to_atom")
    [˝VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil)))))].

Ltac apply_proper_constr := 
  eapply generates_terminal || (
  eapply generates_step_true_unique; simpl;
    [econstructor; reflexivity
    |set_solver 
    |] || (
  eapply generates_step_false; simpl;
    [econstructor; try (reflexivity || scope_solver || congruence)
    |simpl]
)).

Goal generates_at_least_n_unique_atoms [] call_of_list_to_atom ∅ 1.
Proof.
  unfold call_of_list_to_atom.
  repeat apply_proper_constr.
Qed.

Definition infinite_atom_g (e : Exp) : Exp :=
  ELetRec
    [(1, °ELet 1
      (˝VCons (VLit 97%Z) (VCons (VVar 1) (VNil)))
      (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom") [˝VVar 0])
             (°ELet 1
                (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit 1%Z])
                (EApp (˝VFunId (2, 1)) [˝VVar 0]))))]
    (EApp (˝VFunId (0, 1)) [e]).

Ltac do_step :=
  eapply SubstSemanticsLabeled.step_trans; [econstructor;auto|simpl|simpl].

Ltac do_n_do_step n :=
lazymatch goal with
| [ |- ⟨_ , _⟩ -[_, _]-> ⟨_ , _⟩] => 
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

       As it ws said, step_refl can be applied at ANY point of the proof.
       And it is also the default behavior of the constructor tactic. *)
    constructor.
    (* But obviously, the resulting statement in this case is unprovable,
       since the sufficient amount of atoms is not produced in the assumed
       l, which was fixed by solving the previous goal. *)
Restart.
  unfold atom_exhaustion, atom_exhaustion_aux.
  do 3 eexists. split.
  - eexists.
    (* This behavior obviously presents some problems for implementing 
       automatisation tactics. *)
    do_step. do_step. do_step.
    (* Third obstacle: as you may see in the environment tab, by using
       step_trans constructor, the number of goals will get inadvertently
       bloated (due to the design of the step_trans constructor), which
       descreases readability and efficiency. *)
Restart.
  unfold atom_exhaustion, atom_exhaustion_aux.
  do 3 eexists. split.
  - eexists. eapply SubstSemanticsLabeledLemmas.transitive_eval.
    (* Fourth obstacle: it can be observed, that until the -[?k, ?l]->
       is constructed and closed with step_refl, the data structures a
       proof engineer deals with to store the amassed SideEffects are
       simple lists. That presents a challenge: we want to apply step_refl
       when the number of the unique atoms in the resulting, but it is
       hard to reason about this, when one's only have lists, which may
       conatin duplicates. *)
    +
    (* Notice how we will only see ?l in the last goal. But what if we have
       100 applications of SubstSemanticsLabeledLemmas.transitive_eval? Will
       a proof engineer have to unfocus his current subgoal and scroll down
       to the end of the list every time he wants to see the current progress? *)
Abort. (* That's BS *)

Theorem inf_atom_g: generates_at_least_n_unique_atoms []
  (infinite_atom_g (˝VLit (Integer 0))) ∅ 10.
Proof.
  unfold infinite_atom_g.
  repeat apply_proper_constr.
  (* This, however, is much more elegant, albeit slow *)
Qed.

Definition sum_example (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 0%Z));
      ([PVar], ˝ttrue,
        (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom")
                  [˝VCons (VLit 97%Z) (VCons (VVar 0) (VNil))])
               (°ELet 1 (EApp (˝VFunId (1, 1))
                  [°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VLit 1%Z]])
                  (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 1; ˝VVar 0])))
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e]).

Theorem sum_atom_g : exists e,
  generates_at_least_n_unique_atoms [] (sum_example e) ∅ 3.
Proof.
  exists (˝VLit (Integer 3)).
  unfold sum_example.
  do 9 apply_proper_constr.
  (* Technical caveat of the tactic due to econstructor on match *)
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  do 31 apply_proper_constr. replace (3 - 1)%Z with 2%Z by lia.
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  do 31 apply_proper_constr. replace (2 - 1)%Z with 1%Z by lia.
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  repeat apply_proper_constr.
Qed.

Ltac inf_atom_helper :=
match goal with
| [|- context [?n - size (?s)]] =>
    cbn; replace (size s) with 1 by set_solver; cbn; simpl
end.

Goal atom_exhaustion
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
  assert (forall (z: Z), ⟨[FApp1 [˝ VLit z]], closRedex⟩
    -[[(AtomCreation, [VLit (String (ascii_of_nat (Z.to_nat 97))
       (String (ascii_of_nat (Z.to_nat z)) ""))])]]->*
      ⟨[FApp1 [˝ VLit (z + 1)%Z]], closRedex⟩) as Reach.
  { subst. intros. eexists. do_n_do_step 31.
    apply SubstSemanticsLabeled.step_refl. }
  subst.
  (* ----------------------------------------------------------- *)
  apply soundness. simpl.
  do 2 apply_proper_constr.
  do 11 (eapply galnua_multistep_rev_alt;
    [apply Reach|]; inf_atom_helper). apply_proper_constr.
Qed.

Fixpoint mk_sum_atom_list (n: nat) :=
match n with
| O => []
| S n' => ((AtomCreation, [(VLit
  (String (ascii_of_nat 97)
  (String (ascii_of_nat n) "")))]):SideEffect)
  :: mk_sum_atom_list n'
end.

Theorem sum_eval (n: nat) :
  ⟨[], sum_example (˝VLit (Z.of_nat n))⟩
    -[mk_sum_atom_list n]->*
  ⟨[], RValSeq [VLit (Z.div (Z.of_nat ((n + 1) * n)) 2%Z)]⟩.
Proof.
  unfold sum_example. induction n.
  - eexists. do_n_do_step 13. econstructor.
  - inv IHn. inv H. inv H0. simpl in H1. inv H1. inv H. inv H0. inv H.
    clear H4. inv H1. inv H. inv H0. inv H. clear H10. inv H1. inv H.
    clear H4. inv H0. inv H. simpl in H9. inv H9. eexists.
    (* ---------------------------------------------------------- *)
    do_n_do_step 9. eapply SubstSemanticsLabeled.step_trans.
    eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
    do_n_do_step 29.
    eapply SubstSemanticsLabeledLemmas.transitive_eval.
    replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n)%Z by lia.
    { eapply (SubstSemanticsLabeledLemmas.frame_indep_nil _ _ _ _ _ H1). }
    all: clear H1. do_n_do_step 11. unfold eval_arith. simpl.
    (* ---------------------------------------------------------- *)
    + replace 2%Z with (Z.of_nat 2) by lia.
      rewrite <- Nat2Z.inj_div, <- Nat2Z.inj_add, <- Nat2Z.inj_div.
      replace (S (n+(n+1) * S n)) with ((S n * 2) + ((n+1)*n)) by lia.
      rewrite Nat.div_add_l; auto. econstructor.
    + replace (Z.to_nat 97) with 97 by lia.
      replace (Z.to_nat (Z.of_nat (S n))) with (S n) by lia.
      rewrite app_nil_r. reflexivity.
Qed.

Goal exists e, atom_exhaustion (sum_example e) 10.
Proof.
  exists (˝VLit (Integer 11)). apply soundness; simpl.
  pose proof sum_eval. eapply galnua_multistep_rev_alt.
  replace 11%Z with (Z.of_nat 11) by lia. apply H. clear H.
  assert ((size ((mk_atom_set (mk_sum_atom_list 11)) ∖ ∅)) = 11).
  { set_solver. } rewrite H. apply_proper_constr.
Qed.