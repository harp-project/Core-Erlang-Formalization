From CoreErlang.FrameStack Require Import SubstSemanticsLabeledLemmas.
From stdpp Require Import gmap sets.
Require Import AtomExhaustion.
From Ltac2 Require Import Ltac2.
From Ltac2 Require Option.
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
  repeat ltac1:(apply_proper_constr).
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
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(scope_solver).
    (* Third obstacle: as you may see in the environment tab, by using
       step_trans constructor, the number of goals get inadvertently
       bloated (due to the design of the step_trans constructor), which
       descreases readability and efficiency. *)
    Fail do 2 ltac1:(do_step). (* and for some reason, I can't do this *)
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
    + admit.
    (* Notice how we will only see ?l in the last goal. But what if we have
       100 applications of SubstSemanticsLabeledLemmas.transitive_eval? Will
       a proof engineer have to unfocus his current subgoal and scroll down
       to the end of the list every time he wants to see the current progress? *)
Abort. (* That's BS *)

Theorem inf_atom_g: generates_at_least_n_unique_atoms []
  (infinite_atom_g (˝VLit (Integer 0))) ∅ 10.
Proof.
  unfold infinite_atom_g.
  repeat ltac1:(apply_proper_constr).
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
  do 9 ltac1:(apply_proper_constr).
  (* Technical caveat of the tactic due to econstructor on match *)
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  do 31 ltac1:(apply_proper_constr). ltac1:(replace (3 - 1)%Z with 2%Z by lia).
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  do 31 ltac1:(apply_proper_constr). ltac1:(replace (2 - 1)%Z with 1%Z by lia).
  eapply generates_step_false.
  eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
  repeat ltac1:(apply_proper_constr).
Qed.

Goal exists fs r l, ⟨[], infinite_atom_g (˝VLit 0%Z)⟩
    -[l]->*
  ⟨fs, r⟩.
Proof.
  do 4 eexists. unfold infinite_atom_g.
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(scope_solver).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(scope_solver).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
  ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
Abort.

(* Ltac inf_atom_helper :=
match goal with
| |- generates_at_least_n_unique_atoms [FApp1 [˝ VLit (z + 1)%Z]]
    _ avs (n - size _) =>

  replace (mk_atom_set [(AtomCreation, [VLit
    (String (ascii_of_nat (Z.to_nat 97))
      (String (ascii_of_nat (Z.to_nat z)) ""))])]) with
    (({[(String (ascii_of_nat (Z.to_nat 97))
      (String (ascii_of_nat (Z.to_nat z)) ""))]}):gset string)
    by set_solver;
  replace (size {[String (ascii_of_nat (Z.to_nat 97))
   (String (ascii_of_nat (Z.to_nat z)) "")]} ∖ avs) with 1 by set_solver *)
(* end. *)
(* generates_at_least_n_unique_atoms [FApp1 [˝ VLit (0 + 1)%Z]]
  (˝ VClos
       [(0, 1,
         ° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
             (° ESeq
                  (° ECall (˝ VLit "erlang") (˝ VLit "list_to_atom")
                       [˝ VVar 0])
                  (° ELet 1
                       (° ECall (˝ VLit "erlang") 
                            (˝ VLit "+") [˝ VVar 2; ˝ VLit 1%Z])
                       (° EApp (˝ VFunId (2, 1)) [˝ VVar 0]))))] 0 1
       (° ELet 1 (˝ VCons (VLit 97%Z) (VCons (VVar 1) VNil))
            (° ESeq
                 (° ECall (˝ VLit "erlang") (˝ VLit "list_to_atom")
                      [˝ VVar 0])
                 (° ELet 1
                      (° ECall (˝ VLit "erlang") (˝ VLit "+")
                           [˝ VVar 2; ˝ VLit 1%Z])
                      (° EApp (˝ VFunId (2, 1)) [˝ VVar 0])))))
  (∅
   ∪ mk_atom_set
       [(AtomCreation,
         [VLit
            (String (ascii_of_nat (Z.to_nat 97))
               (String (ascii_of_nat (Z.to_nat 0)) ""))])])
  (11 -
   size
     (mk_atom_set
        [(AtomCreation,
          [VLit
             (String (ascii_of_nat (Z.to_nat 97))
                (String (ascii_of_nat (Z.to_nat 0)) ""))])] ∖ ∅))
 *)
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
  { subst. intros. eexists.
    ltac1:(do_step). ltac1:(scope_solver).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). apply SubstSemanticsLabeled.step_refl. all:auto. }
  subst.
  (* ----------------------------------------------------------- *)
  apply soundness. simpl.
  do 2 ltac1:(apply_proper_constr).
  ltac1:(eapply galnua_multistep_rev_alt; [apply Reach|]).
  ltac1:(replace (mk_atom_set [(AtomCreation, [VLit
    (String (ascii_of_nat (Z.to_nat 97))
      (String (ascii_of_nat (Z.to_nat 0)) ""))])]) with
    (({[(String (ascii_of_nat (Z.to_nat 97))
      (String (ascii_of_nat (Z.to_nat 0)) ""))]}):gset string)
    by set_solver).
  ltac1:(replace ({[String (ascii_of_nat (Z.to_nat 97))
    (String (ascii_of_nat (Z.to_nat 0)) "")]} ∖ ∅) with
    ({[String (ascii_of_nat (Z.to_nat 97))
      (String (ascii_of_nat (Z.to_nat 0)) "")]}:gset string)
    by set_solver).
  ltac1:(replace (size {[String (ascii_of_nat (Z.to_nat 97))
   (String (ascii_of_nat (Z.to_nat 0)) "")]}) with 1 by set_solver).
  simpl.
Admitted.

Fixpoint mk_sum_atom_list (n: nat) :=
match n with
| O => []
| S n' => ((AtomCreation, [(VLit
  (String (ascii_of_nat 97)
  (String (ascii_of_nat n) "")))]):SideEffect)
  :: mk_sum_atom_list n'
end.

Search Z "div".

Theorem sum_eval (n: nat) :
  ⟨[], sum_example (˝VLit (Z.of_nat n))⟩
    -[mk_sum_atom_list n]->*
  ⟨[], RValSeq [VLit (Z.div (Z.of_nat ((n + 1) * n)) 2%Z)]⟩.
Proof.
  unfold sum_example. induction n.
  - eexists.
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(scope_solver).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). econstructor. all: auto.
  - ltac1:(inv IHn). ltac1:(inv H). ltac1:(inv H0). simpl in H1.
    ltac1:(inv H1). ltac1:(inv H). ltac1:(inv H0). ltac1:(inv H).
    clear H4. ltac1:(inv H1). ltac1:(inv H). ltac1:(inv H0). ltac1:(inv H).
    clear H10. ltac1:(inv H1). ltac1:(inv H). clear H4. ltac1:(inv H0).
    ltac1:(inv H). simpl in H9. ltac1:(inv H9). eexists.
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(scope_solver).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). eapply SubstSemanticsLabeled.step_trans.
    eapply SubstSemanticsLabeled.eval_step_case_not_match. reflexivity.
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(scope_solver).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step).
    eapply SubstSemanticsLabeledLemmas.transitive_eval.
    ltac1:(replace (Z.of_nat (S n) - 1)%Z with (Z.of_nat n)%Z by lia).
    { eapply (SubstSemanticsLabeledLemmas.frame_indep_nil _ _ _ _ _ H1). }
    all: clear H1.
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). ltac1:(do_step).
    ltac1:(do_step). ltac1:(do_step). ltac1:(do_step). unfold eval_arith.
    simpl.
    assert ((Z.of_nat (S n) + Z.of_nat ((n + 1) * n) `div` 2)%Z
      = (Z.of_nat (S (n + (n + 1) * S n)) `div` 2)%Z).
    { admit. } rewrite H. econstructor. all: auto.
    ltac1:(replace (Z.to_nat 97) with 97 by lia).
    ltac1:(replace (Z.to_nat (Z.of_nat (S n))) with (S n) by lia).
    rewrite app_nil_r. reflexivity.
Admitted.

Goal exists e, atom_exhaustion (sum_example e) 10.
Proof.
  exists (˝VLit (Integer 11)). apply soundness; simpl.
  ltac1:(pose proof sum_eval).
  eapply galnua_multistep_rev_alt.
  ltac1:(replace 11%Z with (Z.of_nat 11) by lia).
  apply H. clear H.
  assert ((size ((mk_atom_set (mk_sum_atom_list 11)) ∖ ∅)) = 11).
  { ltac1:(set_solver). } rewrite H. ltac1:(apply_proper_constr).
Qed.