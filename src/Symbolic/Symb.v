From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.

Import ListNotations.

Fixpoint Exp_list_eqb (le1 le2 : list Exp) : bool :=
  match le1, le2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | e1 :: le1', e2 :: le2' => andb (Exp_eqb_strict e1 e2) (Exp_list_eqb le1' le2')
  end.

Fixpoint Val_list_eqb (lv1 lv2 : list Val) : bool :=
  match lv1, lv2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | v1 :: lv1', v2 :: lv2' => andb (Val_eqb_strict v1 v2) (Val_list_eqb lv1' lv2')
  end.

Fixpoint Pat_list_eqb (lp1 lp2 : list Pat) : bool :=
  match lp1, lp2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | p1 :: lp1', p2 :: lp2' => andb (Pat_eqb p1 p2) (Pat_list_eqb lp1' lp2')
  end.

Fixpoint FCase1_eqb (l1 l2 : list (list Pat * Exp * Exp)) : bool :=
  match l1, l2 with
  | [], [] => true
  | [], _ :: _ => false
  | _ :: _, [] => false
  | (lp1, e1, e1') :: l1', (lp2, e2, e2') :: l2' => 
      andb (Pat_list_eqb lp1 lp2) (andb (Exp_eqb_strict e1 e2) (andb (Exp_eqb_strict e1' e2') (FCase1_eqb l1' l2')))
  end.

Print FrameIdent.
Definition FrameIdent_eqb (fi1 fi2 : FrameIdent) : bool :=
  match fi1, fi2 with
  | IValues, IValues => true
  | ITuple, ITuple => true
  | IMap, IMap => true
  | ICall v1 v1', ICall v2 v2' => andb (Val_eqb_strict v1 v2) (Val_eqb_strict v1' v2')
  | IPrimOp s1, IPrimOp s2 => String.eqb s1 s2
  | IApp v1, IApp v2 => Val_eqb_strict v1 v2
  | _, _ => false
  end.

Definition Frame_eqb (f1 f2 : Frame) : bool :=
  match f1, f2 with
  | FCons1 e1, FCons1 e2 => Exp_eqb_strict e1 e2
  | FCons2 v1, FCons2 v2 => Val_eqb_strict v1 v2
  | FParams fi1 vl1 el1, FParams fi2 vl2 el2 => 
      andb (FrameIdent_eqb fi1 fi2) (andb (Val_list_eqb vl1 vl2) (Exp_list_eqb el1 el2))
  | FApp1 el1, FApp1 el2 => Exp_list_eqb el1 el2
  | FCallMod e1 el1, FCallMod e2 el2 => andb (Exp_eqb_strict e1 e2) (Exp_list_eqb el1 el2)
  | FCallFun v1 el1, FCallFun v2 el2 => andb (Val_eqb_strict v1 v2) (Exp_list_eqb el1 el2)
  | FCase1 l1, FCase1 l2 => FCase1_eqb l1 l2
  | FCase2 vl1 e1 l1, FCase2 vl2 e2 l2 => 
      andb (Val_list_eqb vl1 vl2) (andb (Exp_eqb_strict e1 e2) (FCase1_eqb l1 l2))
  | FLet n1 e1, FLet n2 e2 => andb (Nat.eqb n1 n2) (Exp_eqb_strict e1 e2)
  | FSeq e1, FSeq e2 => Exp_eqb_strict e1 e2
  | FTry n1 e1 n1' e1', FTry n2 e2 n2' e2' => 
      andb (Nat.eqb n1 n2) (andb (Exp_eqb_strict e1 e2) (andb (Nat.eqb n1' n2') (Exp_eqb_strict e1' e2')))
  | _, _ => false
  end.

Fixpoint FrameStack_prefix (fs1 fs2 : FrameStack) : bool :=
  match fs1, fs2 with
  | [], _ => true
  | f1 :: fs1', f2 :: fs2' => andb (Frame_eqb f1 f2) (FrameStack_prefix fs1' fs2')
  | _, _ => false
  end.

Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 1%Z));
      ([PVar], ˝ttrue,
        °ELet 1 (EApp (˝VFunId (1, 1))
          [°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z]])
          (°ECall (˝VLit "erlang"%string) (˝VLit "*"%string) [˝VVar 1; ˝VVar 0])
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e])
   (* Write the definition here *)
.

Fixpoint sequentialStepMaxK (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match n with
    | 0 => (fs, r)
    | S n' => sequentialStepMaxK fs' r' n'
    end
  end.

Fixpoint sequentialStepMaxKNoSimpl (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match n with
    | 0 => (fs, r)
    | S n' => sequentialStepMaxKNoSimpl fs' r' n'
    end
  end.

Fixpoint sequentialStepK (fs : FrameStack) (r : Redex) (n : nat) : option (FrameStack * Redex) :=
  match n with
  | 0 => Some (fs, r)
  | S n' =>
    match sequentialStepFunc fs r with
    | Some (fs', r') => sequentialStepK fs' r' n'
    | None => None
    end
  end.

Arguments sequentialStepMaxK !_ !_ !_ /.
Arguments sequentialStepMaxKNoSimpl : simpl never.
Arguments sequentialStepK !_ !_ !_ /.

Definition canRec (fs : FrameStack) (r : Redex) : bool :=
  match fs with
  | FParams (IApp (VClos (_ :: _) _ _ _)) _ _ :: _ => 
    match r with
    | RValSeq _ => true
    | _ => false
    end
  | _ => false
  end.

Fixpoint sequentialStepCanRec (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match canRec fs r with
  | true => (fs, r)
  | false =>
    match sequentialStepFunc fs r with
    | None => (fs, r)
    | Some (fs', r') =>
      match n with
      | 0 => (fs, r)
      | S n' => sequentialStepCanRec fs' r' n'
      end
    end
  end.

Lemma maxKZeroRefl:
  forall (fs : FrameStack) (r : Redex),
  sequentialStepMaxK fs r 0 = (fs, r).
Proof.
  intros. unfold sequentialStepMaxK.
  destruct (sequentialStepFunc fs r).
  1:destruct p. all:reflexivity.
Qed.

Lemma canRecRefl:
  forall (fs : FrameStack) (r : Redex),
  sequentialStepCanRec fs r 0 = (fs, r).
Proof.
  intros. unfold sequentialStepCanRec.
  destruct (canRec fs r). 2:destruct (sequentialStepFunc fs r).
  2:destruct p. all:reflexivity.
Qed.

Lemma maxKForwardOne:
  forall (fs : FrameStack) (r r' : Redex),
  is_result r' ->
  (exists n, sequentialStepMaxK fs r (S n) = ([], r')) <->
  exists n, sequentialStepMaxK fs r n = ([], r').
Proof.
  intros. split; intro.
  * destruct H0. exists (S x). auto.
  * destruct H0. destruct x.
    + exists 0.
      rewrite maxKZeroRefl in H0. inv H0.
      inv H. all:auto.
    + exists x. auto.
Qed.

Lemma maxKOverflow:
  forall (fs : FrameStack) (r r' : Redex) (n m : nat),
  is_result r' ->
  n <= m ->
  sequentialStepMaxK fs r n = ([], r') ->
  sequentialStepMaxK fs r m = ([], r').
Proof.
  intros fs r r' n. revert fs r r'.
  induction n; intros.
  * destruct m.
    + auto.
    + rewrite maxKZeroRefl in H1. inv H1.
      inv H. all:auto.
  * destruct m.
    + inv H0.
    + unfold sequentialStepMaxK in H1|-*.
      destruct (sequentialStepFunc fs r).
      1:destruct p; fold sequentialStepMaxK.
      all:fold sequentialStepMaxK in H1.
      - apply IHn; auto. lia.
      - auto.
Qed.

Lemma maxKForwardThousand:
  forall (fs : FrameStack) (r r' : Redex),
  is_result r' ->
  (exists n, sequentialStepMaxK fs r (1000 + n) = ([], r')) <->
  exists n, sequentialStepMaxK fs r n = ([], r').
Proof.
  intros. split; intro.
  * destruct H0. exists (1000 + x). auto.
  * destruct H0. 
    exists x.
    apply (maxKOverflow _ _ _ x); auto. lia.
Qed.

Lemma maxKEquivK:
  forall (fs fs' : FrameStack) (r r' : Redex),
  (exists n, sequentialStepK fs r n = Some (fs', r')) <->
  (exists n, sequentialStepMaxK fs r n = (fs', r')).
Proof.
  intros. split;intro.
  * destruct H. exists x.
    revert H. revert fs r.
    induction x; intros.
    + unfold sequentialStepK in *. inv H.
      rewrite maxKZeroRefl. auto.
    + unfold sequentialStepMaxK.
      unfold sequentialStepK in H.
      destruct (sequentialStepFunc fs r).
      1:destruct p.
      all:fold sequentialStepMaxK. all:fold sequentialStepK in H.
      all:auto. inv H.
  * destruct H. revert H. revert fs r.
    induction x; intros.
    + rewrite maxKZeroRefl in H. inv H. exists 0.
      unfold sequentialStepK. reflexivity.
    + unfold sequentialStepMaxK in H.
      destruct (sequentialStepFunc fs r) eqn:Hssf; fold sequentialStepMaxK in H.
      - destruct p.
        apply IHx in H. destruct H. exists (S x0).
        unfold sequentialStepK. rewrite Hssf. fold sequentialStepK.
        auto.
      - inv H. exists 0. unfold sequentialStepK. reflexivity.
Qed.

Lemma kEquiv:
  forall (fs fs' : FrameStack) (r r' : Redex) (k : nat),
  ⟨ fs, r ⟩ -[k]-> ⟨ fs', r' ⟩ <-> sequentialStepK fs r k = Some (fs', r').
Proof.
  intros. split;revert fs fs' r r'.
  * induction k; intros.
    + inv H. unfold sequentialStepK. auto.
    + inv H. unfold sequentialStepK.
      apply sequentialStepEquiv in H1. rewrite H1.
      fold sequentialStepK. auto.
  * induction k; intros.
    + unfold sequentialStepK in H. inv H. constructor.
    + unfold sequentialStepK in H.
      destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. fold sequentialStepK in H.
        apply sequentialStepEquiv in Hssf.
        econstructor; eauto.
      - inv H.
Qed.

Theorem RTCEquiv:
  forall (fs : FrameStack) (r r' : Redex),
  is_result r' ->
  ⟨ fs, r ⟩ -->* r' <-> exists n, sequentialStepMaxK fs r n = ([], r').
Proof.
  intros fs r r' Hres. split; intros.
  * inv H. destruct H0.
    apply kEquiv in H0.
    apply maxKEquivK.
    exists x. auto.
  * apply maxKEquivK in H.
    destruct H. econstructor. split;[auto|].
    apply kEquiv. eauto.
Qed.

Lemma maxKNoSimplEquiv:
  forall (fs : FrameStack) (r : Redex) (n : nat),
  sequentialStepMaxK fs r n = sequentialStepMaxKNoSimpl fs r n.
Proof. reflexivity. Qed.

Lemma maxKTransCanRec:
  forall (fs fs': FrameStack) (r r' r'': Redex) (k : nat),
  is_result r'' ->
  sequentialStepCanRec fs r k = (fs', r') ->
  (exists n, sequentialStepMaxK fs' r' n = ([], r'')) ->
  (exists n, sequentialStepMaxK fs r n = ([], r'')).
Proof.
  intros.
  destruct H1. revert H0 H1. revert x fs fs' r r'.
  induction k; intros.
  + rewrite canRecRefl in H0. inv H0. exists x. auto.
  + unfold sequentialStepCanRec in H0.
    destruct (canRec fs r) eqn:HCanRec.
    - inv H0. eapply IHk; eauto.
      destruct k; unfold sequentialStepCanRec; rewrite HCanRec; auto.
    - destruct (sequentialStepFunc fs r) eqn:Hssf.
      fold sequentialStepCanRec in H0.
      ** destruct p.
         setoid_rewrite <- maxKForwardOne;[|auto].
         unfold sequentialStepMaxK. rewrite Hssf. fold sequentialStepMaxK.
         eapply IHk; eauto.
      ** inv H0. exists x. auto.
Qed.

Lemma maxKInsertCanRec:
  forall (fs : FrameStack) (r r'' : Redex),
  is_result r'' ->
  (exists n, (let (fs', r') := sequentialStepCanRec fs r 1000 in sequentialStepMaxK fs' r' n) = ([], r'')) <->
  (exists n, sequentialStepMaxK fs r n = ([], r'')).
Proof.
  intros. split; intros.
  * destruct (sequentialStepCanRec fs r 1000) eqn:Hsscr.
    eapply maxKTransCanRec; eauto.
  * destruct H0. 
    destruct (sequentialStepCanRec fs r 1000) eqn:Hsscr.
    remember 1000 as k. clear Heqk.
    revert H0 Hsscr. revert fs r f r0 k.
    induction x; intros.
    + rewrite maxKZeroRefl in H0. inv H0. inv H.
      all:simpl in Hsscr. all:destruct k.
      all:inv Hsscr. all:exists 0; auto.
    + unfold sequentialStepMaxK in H0.
      destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. fold sequentialStepMaxK in H0.
        destruct k.
        ** rewrite canRecRefl in Hsscr. inv Hsscr.
           exists (S x). unfold sequentialStepMaxK. rewrite Hssf.
           fold sequentialStepMaxK. auto.
        ** unfold sequentialStepCanRec in Hsscr.
           destruct (canRec fs r) eqn:HCanRec.
           ++ inv Hsscr. exists (S x).
              unfold sequentialStepMaxK. rewrite Hssf.
              fold sequentialStepMaxK. auto.
           ++ rewrite Hssf in Hsscr. fold sequentialStepCanRec in Hsscr.
              eapply IHx; eauto.
      - inv H0.
        destruct k.
        ** rewrite canRecRefl in Hsscr. inv Hsscr. exists 0. inv H; auto.
        ** unfold sequentialStepCanRec in Hsscr. inv H; simpl in Hsscr; inv Hsscr.
           all:exists 0; auto.
Qed.

Theorem frame_indep_core_func:
  forall (fs fs' : FrameStack) (r r' : Redex),
  (exists n, sequentialStepMaxK fs r n = (fs', r')) ->
  forall (fsapp : FrameStack), (exists n, sequentialStepMaxK (fs ++ fsapp) r n = (fs' ++ fsapp, r')).
Proof.
  intros.
  apply maxKEquivK. apply maxKEquivK in H.
  destruct H. apply kEquiv in H.
  exists x. apply kEquiv. apply frame_indep_core. auto.
Qed.

Theorem maxKTransitive:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex),
  (exists n, sequentialStepMaxK fs r n = (fs', r')) ->
  (exists n, sequentialStepMaxK fs' r' n = (fs'', r'')) ->
  (exists n, sequentialStepMaxK fs r n = (fs'', r'')).
Proof.
  setoid_rewrite <- maxKEquivK. setoid_rewrite <- kEquiv. intros.
  destruct H, H0. exists (x + x0).
  eapply transitive_eval; eauto.
Qed.

Lemma maxKDone:
  forall (r r' : Redex),
  is_result r' ->
  (exists n : nat, ([] : FrameStack, r') = ([], r)) <->
  (exists n, sequentialStepMaxK [] r' n = ([], r)).
Proof.
  intros. split;intro.
  * destruct H0. inv H0. setoid_rewrite <- RTCEquiv;[|auto].
    econstructor. split. auto. constructor.
  * destruct H0. destruct x.
    + rewrite maxKZeroRefl in H0. exists 0. auto.
    + inv H; simpl in H0; exists 0; auto.
Qed.

Lemma Z_eqb_eq_corr : forall (z1 z2 : Z), (z1 =? z2)%Z = true -> z1 = z2. Proof. lia. Qed.
Lemma Z_eqb_neq_corr: forall (z1 z2 : Z), (z1 =? z2)%Z = false-> z1 <>z2. Proof. lia. Qed.

Ltac case_innermost_term t :=
  lazymatch t with
  | context[match ?x with _ => _ end] =>
      first [ case_innermost_term x
            | let H := fresh "Heq" in
              destruct x eqn:H;
              first [apply Z_eqb_eq_corr in H
                    |apply Z_eqb_neq_corr in H
                    | idtac]]
  | _ => fail "No match subterm found"
  end.

Ltac case_innermost :=
  match goal with
  | |- ?g => case_innermost_term g
  end.

Ltac case_innermost_in H :=
  let T := type of H in
  case_innermost_term T.

Tactic Notation "case_innermost" :=
  case_innermost.

Tactic Notation "case_innermost" ident(H) :=
  case_innermost_in H.


Ltac toRec :=
match goal with
| |- context[exists n : nat, sequentialStepMaxK _ _ n = _] => 
        try (setoid_rewrite <- maxKInsertCanRec;[|constructor]);simpl;
        try (setoid_rewrite <- maxKDone;[|constructor])
| _ => idtac "nothing to do"
end.

Ltac stepOne :=
match goal with
| |- context[exists n : nat, sequentialStepMaxK _ _ n = _] =>
        try (setoid_rewrite <- maxKForwardOne;[|constructor]);simpl
| _ => idtac "nothing to do"
end.

Ltac stepThousand :=
match goal with
| |- context[exists n : nat, sequentialStepMaxK _ _ n = _] =>
        try (setoid_rewrite <- maxKForwardThousand;[|constructor]);simpl
| _ => idtac "nothing to do"
end.

Ltac toNextRec := stepOne; toRec.

Lemma NatZSuccPred:
  forall (n : nat), (Z.of_nat (S n) - 1)%Z = Z.of_nat n.
Proof. lia. Qed.

Theorem maxKTransitive':
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex) (P : Prop),
  (exists n, sequentialStepMaxK fs r n = (fs', r')) ->
  ((exists n, sequentialStepMaxK fs' r' n = (fs'', r'')) /\ P) ->
  ((exists n, sequentialStepMaxK fs r n = (fs'', r'')) /\ P).
Proof.
  setoid_rewrite <- maxKEquivK. setoid_rewrite <- kEquiv. intros.
  destruct H, H0, H0.
  split;auto.
  exists (x + x0).
  eapply transitive_eval; eauto.
Qed.

Ltac solve_final_state := 
  eexists;
    [auto| (* This is for the step number, which is always irrelevant (|- nat) when this tactic is called *)
     first [ auto (* The program indeed terminated at ([], r) where is_result r *)
           | idtac "Unexpected end state 
                    (can be due to an exception in the Erlang program,
                     a result when an exception was expected,
                     non-termination in the given depth or
                     an impossible input that was not ruled out)"
           ]].

Ltac solve_final_postcond :=
  first [ nia
        | idtac "Could not solve postcondition"
        ].

Ltac solve_terminated :=
  lazymatch goal with
  | |- context[sequentialStepMaxK] => fail "The program has not yet terminated"
  | |- _ =>
    lazymatch goal with
    | |- ex _ => eexists;solve_terminated
    | |- _ /\ _ => split;[solve_final_state|solve_final_postcond]
    | |- _ => idtac
    end
  end.

Ltac give_steps_if_needed_using steptac :=
  first [ progress simpl
        | steptac
        ].

Ltac match_with_backfall backfall :=
  lazymatch goal with
  | |- context[match ?x with _ => _ end] =>
         case_innermost;
         try nia;
         backfall
  | |- _ => fail "Match expression not found"
  end.

Ltac able_to_ind :=
  lazymatch goal with
  | |- context[sequentialStepMaxK ?fs ?r] => 
       let b := eval compute in (canRec fs r) in
         lazymatch b with
         | true => idtac
         | false => fail
         end
  | |- _ => fail
  end.

Ltac base_case :=
  stepThousand;
  first [ solve_terminated
        | match_with_backfall base_case
        | base_case].

Ltac solve_IH_precond IH:=
  lazymatch (type of IH) with
  | ?A -> _ => 
      let proof := fresh "IHPrec" in
      assert A as proof by lia;
      specialize (IH proof);
      clear proof
  | _ => idtac
  end.

Ltac framestack_is_prefix IH :=
  lazymatch goal with
  | |- context[sequentialStepMaxK ?fs _] =>
         lazymatch (type of IH) with
         | context[sequentialStepMaxK ?fsIH _] =>
             let b := eval compute in (FrameStack_prefix fsIH fs) in
             lazymatch b with
             | true => idtac
             | false => fail "Framestack in induction hypothesis is not a prefix"
             end
         | _ => fail "No step left in induction hypothesis, or symbolic variable inside framestack"
         end
  | |- _ => fail "No steps left in goal"
  end.

Ltac redex_matches IH :=
  lazymatch goal with
  | |- context[sequentialStepMaxK _ ?r] =>
         lazymatch (type of IH) with
         | context[sequentialStepMaxK _ ?rIH] => constr_eq r rIH
         | _ => fail "No step left in induction hypothesis"
         end
  | |- _ => fail "No steps left in goal"
  end.

Ltac destruct_until_conj IH :=
  lazymatch (type of IH) with
  | _ /\ _ => idtac
  | ex _ => 
    let x := fresh "x" in
    destruct IH as [x IH]; destruct_until_conj IH
  | _ => idtac
  end.

Ltac eexists_until_conj :=
  lazymatch goal with
  | |- _ /\ _ => idtac
  | |- ex _ => eexists; eexists_until_conj
  | |- _ => idtac
  end.

Ltac try_rectify_IH_redex IH kval :=
  specialize (IH kval);
  setoid_rewrite Z2Nat.id in IH; try lia;
  solve_IH_precond IH;
  
  framestack_is_prefix IH;
  redex_matches IH.

Ltac try_rectify_induction IH :=
  framestack_is_prefix IH;
  lazymatch goal with
  | |- context[sequentialStepMaxK _ ?r] => 
         lazymatch r with
         | context[VLit (Integer ?k)] => try_rectify_IH_redex IH (Z.to_nat k)
         | _ => idtac "did not find k"
         end
  | |- _ => idtac "Redex value not found" (* we need to continue... *)
  end.

Ltac solve_by_induction IH := 
  (* This tactic only gets called, if the framestack in IH is the prefix of the one in the goal,
     and the redexes are syntactically the same. So these should always work... *)
  destruct_until_conj IH;
  let IHExp := fresh "IHExp" in
  let IHPostcond := fresh "IHPostcond" in
  destruct IH as [IHExp IHPostcond];
  let IHExp_fic := fresh "IHExp_fic" in
  pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic; simpl in IHExp_fic;
  eexists_until_conj;
  eapply maxKTransitive';[apply IHExp_fic|];
  base_case.

Ltac ind_case IH := 
  let back_call := stepOne;ind_case IH in
  toRec;cbn;
  first [ solve_terminated
        | match_with_backfall ind_case
        | try_rectify_induction IH; solve_by_induction IH
        | back_call].

Ltac induction_head symb :=
  let n := fresh "n" in
  let IH := fresh "IH" in
  induction symb as [n IH] using lt_wf_ind;
  let Hn := fresh "Hn" in
  destruct n eqn:Hn;
  [base_case|stepOne;ind_case IH].

Ltac solve_to_rec symb :=
  toRec;
  first [ solve_terminated
        | able_to_ind; induction_head symb
        | match_with_backfall solve_to_rec
        | solve_to_rec].

Ltac solve_symbolically symb :=
  first [ intros; setoid_rewrite RTCEquiv;[|constructor]; solve_to_rec symb
        | fail "Could not solve goal symbolically"
        ].

Theorem fact_eval_ex:
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ ((Z.of_nat z) <= y /\ y >= 1)%Z.
Proof.
  intros.
  setoid_rewrite RTCEquiv;[|constructor].
  
  toRec.

  induction z using lt_wf_ind.
  destruct z.
  * repeat stepThousand.

    solve_terminated. exact 0.
  * toNextRec.

    cbn.
    
    specialize (H (Z.to_nat (Z.of_nat (S z) - 1)%Z)).
    setoid_rewrite Z2Nat.id in H; try lia.
    assert (Z.to_nat (Z.of_nat (S z) - 1) < S z) by lia.
    specialize (H H0). clear H0.

    destruct H as [y [IHExp IHPostcond]].

    pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
    simpl in IHExp_fic.
    
    eexists.
    eapply maxKTransitive'. auto.
    repeat stepThousand. solve_terminated.
Qed.

(* Require Import SMTCoq.Tactics.

Lemma Z_of_nat_O : Z.of_nat 0 = 0%Z.  Proof. reflexivity. Qed.
Lemma Z_of_nat_S n : Z.of_nat (S n) = (Z.of_nat n + 1)%Z.  Proof. lia. Qed.

Add_lemmas Z_of_nat_0 Z_of_nat_S. *)

Theorem fact_eval_ex':
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ ((Z.of_nat z) <= y /\ y >= 1)%Z.
Proof.
  solve_symbolically z.
Qed.

Theorem fact_eval_ex'':
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact z))%Z.
Proof.
  solve_symbolically z.

  subst x.
  rewrite <- Nat2Z.inj_mul. f_equal.
  assert (1%Z = Z.of_nat (Z.to_nat 1)) by lia. rewrite H. clear H.
  rewrite <- Nat2Z.inj_sub;[|lia].
  rewrite Nat2Z.id. simpl. rewrite Nat.sub_0_r. reflexivity.
Qed.

Theorem fact_eval : forall n,
  ⟨[], fact_frameStack (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.
  intros.
  pose proof fact_eval_ex'' n.
  destruct H. destruct H. subst x. auto.
Qed.

(*
  Let "e" and "d" be parameter expressions.

  letrec 'fact'/2 =
    fun(X, A) ->
      case <X> of
        <0> when 'true' -> A
        <Z> when 'true' -> apply 'fact'/2(call 'erlang':'-'(Z, 1), call 'erlang':'*'(Z, A))
    in
      apply 'fact'/2(e, d)

  Define the above expression!
 *)
Definition tailrec_fact (e d : Exp) : Exp :=
  ELetRec [
    (2, °ECase (˝VVar 1) [
        ([PLit (Integer 0%Z)], ˝ttrue, ˝VVar 2);
        ([PVar], ˝ttrue,
          (°EApp (˝VFunId (1, 2)) 
            [°ECall (˝erlang) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z];
             °ECall (˝erlang) (˝VLit "*"%string) [˝VVar 0; ˝VVar 3]
            ]))
      ]
    )
  ] (EApp (˝VFunId (0, 2)) [e; d]) 
.

Theorem tailrec_fact_eval : forall n,
  ⟨[], tailrec_fact (˝VLit (Z.of_nat n)) (˝VLit 1%Z)⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof. Abort.


Theorem tailrec_fact_eval_ex:
  forall (z : nat) (z' : Z), (0 <= z')%Z ->
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit (Z.of_nat z)) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact z) * z')%Z.
Proof.
  intros z.
  setoid_rewrite RTCEquiv;[|constructor].
  do 8 stepOne. stepOne.

  induction z using lt_wf_ind; intros.
  destruct z.
  * repeat stepThousand.

    solve_terminated. exact 0.
  * do 32 stepOne. cbn.

    specialize (H (Z.to_nat (Z.of_nat (S z) - 1)%Z)).
    setoid_rewrite Z2Nat.id in H; try lia.
    assert (Z.to_nat (Z.of_nat (S z) - 1) < S z) by lia.
    specialize (H H1). clear H1.
    specialize (H (Z.of_nat (S z) * z')%Z).
    assert (0 ≤ Z.of_nat (S z) * z')%Z by lia.
    specialize (H H1). clear H1.

    destruct H as [y [IHExp IHPostcond]].

    pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
    simpl in IHExp_fic.
    
    eexists.
    eapply maxKTransitive'. auto.
    repeat stepThousand. solve_terminated.
    subst y.
    Search Z.of_nat "_ * _".
    Search Z.of_nat Z.to_nat.
    rewrite <- (Z2Nat.id z' H0).
    repeat rewrite <- Nat2Z.inj_mul. f_equal.
    rewrite <- (Z2Nat.id 1);[|lia].
    rewrite <- Nat2Z.inj_sub. rewrite Nat2Z.id. 2:lia.
    simpl. rewrite Nat.sub_0_r. lia.
Qed.

Theorem tailrec_fact_eval_ex':
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit (Z.of_nat z)) (˝VLit 1%Z)) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact z))%Z.
Proof.
  intros z.
  setoid_rewrite RTCEquiv;[|constructor].
  toRec. toNextRec.
  
  induction z using lt_wf_ind; intros.
  destruct z; intros.
  * repeat stepThousand.

    solve_terminated. exact 0.
  * toNextRec. toNextRec. cbn.
    (* This can not be solved with simple induction, because even with just intoint z,
       the hypothesis H is still not general enough. It wants the accumulator to be 1. *)
Abort.

Theorem tailrec_fact_eval_ex'':
  forall (z : nat) (z' : Z), (0 <= z')%Z ->
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit (Z.of_nat z)) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact z) * z')%Z.
Proof.
  intros z.
  setoid_rewrite RTCEquiv;[|constructor].
  
  unfold tailrec_fact.
  do 8 stepOne.
Abort.

Lemma jesus_christ:
  forall xs res ident v vl,
  (⟨FParams ident (vl ++ [v]) [] :: xs, RBox⟩ -->* res) ->
  ⟨FParams ident vl [] :: xs, RValSeq [v]⟩ -->* res.
Proof.
  intros. inv H. destruct H0. inv H0. inv H1.
  econstructor. split;auto.
  econstructor. econstructor. eauto. eauto.
Qed.

Lemma jesus_christ_backwards:
  forall xs res ident v vl,
  ident <> IMap ->
  ⟨FParams ident vl [] :: xs, RValSeq [v]⟩ -->* res ->
  (⟨FParams ident (vl ++ [v]) [] :: xs, RBox⟩ -->* res).
Proof.
  intros. inv H0. destruct H1. inv H1. inv H2.
  econstructor. split;auto.
  econstructor. econstructor. auto. eauto. eauto.
Qed.

Lemma jesus_christ':
  forall xs res ident v vl,
  ident <> IMap -> is_result res ->
  (exists n, sequentialStepMaxK (FParams ident (vl ++ [v]) [] :: xs) RBox n = ([], res)) <->
  (exists n, sequentialStepMaxK (FParams ident vl [] :: xs) (RValSeq [v]) n = ([], res)).
Proof.
  intros.
  setoid_rewrite <- RTCEquiv; auto.
  split. apply jesus_christ. apply jesus_christ_backwards. auto.
Qed.

Ltac test IH :=
  lazymatch (type of IH) with
  | context[sequentialStepMaxK ?fs _] => idtac "found it!"
  | _ => idtac "did not find it"
  end.

Theorem tailrec_fact_eval_ex''':
  forall (z : nat) (z' : Z), (*(0 <= z')%Z ->*)
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit (Z.of_nat z)) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact z) * z')%Z.
Proof.
  intros z.
  setoid_rewrite RTCEquiv;[|constructor].
  
  unfold tailrec_fact.
  do 8 stepOne. setoid_rewrite <- jesus_christ';auto. simpl.
  
  induction z using lt_wf_ind; intros.
  destruct z.
  * repeat stepThousand. solve_terminated. exact 0.
  * toNextRec. toNextRec. cbn.
    test H.
    Print frame_indep_core_func.
    
    setoid_rewrite <- jesus_christ';auto. simpl.
    specialize (H (Z.to_nat ((Z.of_nat (S z) - 1)%Z))).
    assert (Z.to_nat ((Z.of_nat (S z) - 1)%Z) < S z) by lia.
    specialize (H H0). clear H0.
    setoid_rewrite Z2Nat.id in H;[|lia].
    specialize (H (Z.of_nat (S z) * z')%Z).
    
    destruct H as [y [IHExp IHPostcond]].
    Print frame_indep_core_func.
    pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
    simpl in IHExp_fic.
    
    eexists. Print maxKTransitive'.
    eapply maxKTransitive'. auto.
    repeat stepThousand. solve_terminated.
    subst y.
    Search Z.of_nat "_ * _".
    Search Z.of_nat Z.to_nat.
    rewrite Z.mul_assoc. f_equal.
    rewrite <- Nat2Z.inj_mul. f_equal.
    rewrite <- (Z2Nat.id 1);[|lia].
    rewrite <- Nat2Z.inj_sub. rewrite Nat2Z.id. 2:lia.
    simpl. rewrite Nat.sub_0_r. lia.
Qed.

Definition canRecNew (fs : FrameStack) (r : Redex) : bool :=
  match fs with
  | FParams (IApp (VClos (_ :: _) _ _ _)) _ [] :: _ => 
    match r with
    | RValSeq _ => true
    | RBox => true
    | _ => false
    end
  | _ => false
  end.

Definition lastParamRBox (fs : FrameStack) (r : Redex) : (FrameStack * Redex) :=
  match fs, r with
  | FParams ident vl ex :: fs', RValSeq [v] => (FParams ident (vl ++ [v]) ex :: fs', RBox)
  | FParams ident vl ex :: fs', RBox => (FParams ident vl ex :: fs', RBox)
  | fs', r => (fs', r)
  end.

Fixpoint sequentialStepCanRecNew (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match canRecNew fs r with
  | true => lastParamRBox fs r
  | false =>
    match sequentialStepFunc fs r with
    | None => (fs, r)
    | Some (fs', r') =>
      match n with
      | 0 => (fs, r)
      | S n' => sequentialStepCanRecNew fs' r' n'
      end
    end
  end.

Lemma last_param_box_equiv:
  forall xs ident v vl fs' r',
  ident <> IMap ->
  (exists k, ⟨FParams ident (vl ++ [v]) [] :: xs, RBox⟩ -[S k]-> ⟨ fs', r' ⟩) <->
  exists k, ⟨FParams ident vl [] :: xs, RValSeq [v]⟩ -[S k]-> ⟨ fs', r' ⟩.
Proof.
  intros.
  split;intro.
  * destruct H0. inv H0. inv H2.
    exists x. econstructor. econstructor. eauto. auto.
  * destruct H0. inv H0. inv H2.
    exists x. econstructor. econstructor. auto. eauto. auto. 
Qed.

Lemma maxKTransCanRecNew:
  forall (fs fs': FrameStack) (r r' r'': Redex) (k : nat),
  is_result r'' ->
  sequentialStepCanRecNew fs r k = (fs', r') ->
  (exists n, sequentialStepMaxK fs' r' n = ([], r'')) ->
  (exists n, sequentialStepMaxK fs r n = ([], r'')).
Proof.
  intros.
  destruct H1. revert H0 H1. revert x fs fs' r r'.
  induction k; intros.
  + unfold sequentialStepCanRecNew in H0.
    destruct (canRecNew fs r) eqn:HCanRec.
    - unfold canRecNew in HCanRec.
      destruct fs; try discriminate.
      destruct f; try discriminate.
      destruct ident; try discriminate.
      destruct v; try discriminate.
      destruct ext; try discriminate.
      destruct el; try discriminate.
      destruct r; try discriminate.
      ** simpl in H0. destruct vs.
         ++ inv H0. exists x. auto.
         ++ destruct vs.
            -- inv H0. destruct x.
               *** rewrite maxKZeroRefl in H1. inv H1.
               *** exists (S x).
                   simpl in H1. simpl.
                   destruct (params =? length (vl ++ [v]));auto.
            -- inv H0. exists x. auto.
      ** simpl in H0. inv H0. exists x. auto.
    - destruct (sequentialStepFunc fs r) eqn:Hssf. 1:destruct p. all:inv H0. all:eexists;eauto.
  + simpl in H0.
    destruct (canRecNew fs r) eqn:HCanRec.
    - unfold canRecNew in HCanRec.
      destruct fs; try discriminate.
      destruct f; try discriminate.
      destruct ident; try discriminate.
      destruct v; try discriminate.
      destruct ext; try discriminate.
      destruct el; try discriminate.
      destruct r; try discriminate.
      ** simpl in H0. destruct vs.
         ++ inv H0. exists x. auto.
         ++ destruct vs.
            -- inv H0. destruct x.
               *** rewrite maxKZeroRefl in H1. inv H1.
               *** exists (S x).
                   simpl in H1. simpl.
                   destruct (params =? length (vl ++ [v]));auto.
            -- inv H0. exists x. auto.
      ** simpl in H0. inv H0.
         exists x. auto.
    - destruct (sequentialStepFunc fs r) eqn:Hssf.
      ** destruct p. specialize (IHk _ _ _ _ _ H0 H1).
         destruct IHk. exists (S x0). unfold sequentialStepMaxK. rewrite Hssf.
         fold sequentialStepMaxK. auto.
      ** inv H0.
         destruct x.
         ++ rewrite maxKZeroRefl in H1. inv H1. exists 0. apply maxKZeroRefl.
         ++ unfold sequentialStepMaxK in H1. rewrite Hssf in H1. inv H1.
            exists 0. apply maxKZeroRefl.
Qed.

Goal forall o, o = "true"%string -> o = "true"%string \/ o = "false"%string. Proof. auto. Qed.

Lemma maxKInsertCanRecNew:
  forall (fs : FrameStack) (r r'' : Redex),
  is_result r'' ->
  (exists n, (let (fs', r') := sequentialStepCanRecNew fs r 1000 in sequentialStepMaxK fs' r' n) = ([], r'')) <->
  (exists n, sequentialStepMaxK fs r n = ([], r'')).
Proof.
  intros. split; intros.
  * destruct (sequentialStepCanRecNew fs r 1000) eqn:Hsscr.
    eapply maxKTransCanRecNew; eauto.
  * destruct H0. 
    destruct (sequentialStepCanRecNew fs r 1000) eqn:Hsscr.
    remember 1000 as k. clear Heqk.
    revert H0 Hsscr. revert fs r f r0 k.
    induction x; intros.
    + rewrite maxKZeroRefl in H0. inv H0. inv H.
      all:destruct k.
      all:inv Hsscr. all:exists 0; auto.
    + unfold sequentialStepMaxK in H0.
      destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. fold sequentialStepMaxK in H0.
        destruct k.
        ** simpl in Hsscr.
           destruct (canRecNew fs r) eqn:HCanRec.
           ++ unfold canRecNew in HCanRec.
              destruct fs; try discriminate.
              destruct f1; try discriminate.
              destruct ident; try discriminate.
              destruct v; try discriminate.
              destruct ext; try discriminate.
              destruct el; try discriminate. destruct r; try discriminate.
              -- simpl in Hsscr. destruct vs.
                 *** inv Hsscr.
                 *** destruct vs.
                     +++ inv Hsscr.
                         exists (S x). simpl.
                         simpl in Hssf.
                         destruct (params =? length (vl ++ [v])); inv Hssf; auto.
                     +++ inv Hsscr.
              -- simpl in Hsscr. inv Hsscr.
                 exists (S x). unfold sequentialStepMaxK.
                 rewrite Hssf. fold sequentialStepMaxK. auto.
           ++ rewrite Hssf in Hsscr. inv Hsscr. exists (S x).
              unfold sequentialStepMaxK. rewrite Hssf. fold sequentialStepMaxK. auto.
        ** simpl in Hsscr.
           destruct (canRecNew fs r) eqn:HCanRec.
           ++ unfold canRecNew in HCanRec.
              destruct fs; try discriminate.
              destruct f1; try discriminate.
              destruct ident; try discriminate.
              destruct v; try discriminate.
              destruct ext; try discriminate.
              destruct el; try discriminate.
              destruct r; try discriminate.
              -- simpl in Hsscr. destruct vs.
                 *** inv Hsscr.
                 *** destruct vs.
                     +++ inv Hsscr.
                         exists (S x). unfold sequentialStepMaxK. simpl. simpl in Hssf.
                         rewrite Hssf. fold sequentialStepMaxK. auto.
                     +++ inv Hsscr.
              -- simpl in Hsscr. inv Hsscr. exists (S x).
                 unfold sequentialStepMaxK. rewrite Hssf. fold sequentialStepMaxK. auto.
           ++ rewrite Hssf in Hsscr.
              specialize (IHx _ _ _ _ _ H0 Hsscr). auto.
      - inv H0.
        destruct k.
        ** unfold sequentialStepCanRecNew in Hsscr.
           destruct (canRecNew [] r'') eqn:HCanRec.
           ++ simpl in HCanRec. discriminate.
           ++ rewrite Hssf in Hsscr. inv Hsscr. exists 0. apply maxKZeroRefl.
        ** unfold sequentialStepCanRec in Hsscr. inv H; simpl in Hsscr; inv Hsscr.
           all:exists 0; auto.
Qed.

Theorem tailrec_fact_eval_ex'''':
  forall (z : Z) (z' : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z)) * z')%Z.
Proof.
  setoid_rewrite RTCEquiv;[|constructor].
  toRec. do 2 stepOne. setoid_rewrite <- jesus_christ';auto. simpl.
  intros z z' IHPreCond.
  assert (0 <= z)%Z by lia. revert z'. revert IHPreCond.
  apply Zlt_0_ind with (x := z);auto. clear H z. intros z. intros IH. intros a. intros.
  destruct z;try nia.
  * repeat stepThousand. solve_terminated. exact 0.
  * stepOne. toRec. cbn. do 11 stepOne. cbn. setoid_rewrite <- jesus_christ';auto. simpl.
    specialize (IH (Z.pos p - 1)%Z).
    assert (0 <= Z.pos p - 1 < Z.pos p)%Z by lia.
    specialize (IH H). clear H.
    assert  (0 <= Z.pos p - 1)%Z by lia.
    specialize (IH H). clear H.
    
    destruct H as [y [IHExp IHPostcond]].

    pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
    simpl in IHExp_fic.
    
    eexists.
    eapply maxKTransitive'. auto.
    repeat stepThousand. solve_terminated. exact 0.
    
    
    
    subst y.
    rewrite Z.mul_assoc. f_equal.
    rewrite <- positive_nat_Z at 2.
    rewrite <- Nat2Z.inj_mul.
    f_equal.
    rewrite Z2Nat.inj_sub;try nia.
    assert (Z.to_nat 1%Z = 1) by lia. rewrite H. clear H.
    rewrite Z2Nat.inj_pos.
    Search Pos.to_nat "_ - _".
    assert (1 = Pos.to_nat (Pos.of_nat 1)) by lia.
    rewrite H. clear H.
    destruct p.
    + rewrite <- Pos2Nat.inj_sub; try lia.
      assert (Pos.of_nat 1 = 1%positive) by lia. rewrite H. clear H.
      rewrite Pos.sub_1_r.
      assert (Pos.pred p~1 = p~0)%positive by lia. rewrite H. clear H.
      remember (Pos.to_nat p~0) as k.
      assert (Pos.to_nat p~1 = S k) by lia. rewrite H. clear H. clear Heqk.
      unfold fact at 2. fold fact. rewrite Nat.mul_comm. reflexivity.
    + rewrite <- Pos2Nat.inj_sub; try lia.
      assert (Pos.of_nat 1 = 1%positive) by lia. rewrite H. clear H.
      rewrite Pos.sub_1_r.
      remember (Pos.to_nat (Pos.pred p~0)) as k.
      assert (Pos.to_nat p~0 = S k) by lia. rewrite H. clear H.
      unfold fact at 2. fold fact. rewrite Nat.mul_comm. reflexivity.
    + simpl. nia.
Qed.

Theorem fact_eval_ex''':
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (z <= y /\ y >= 1)%Z.
Proof.
  setoid_rewrite RTCEquiv;[|auto].
  toRec. setoid_rewrite <- jesus_christ';auto. simpl.
  intros z HPreCond.
  assert (0 <= z)%Z by lia. revert HPreCond.
  Print Zlt_0_ind.
  apply Zlt_0_ind with (x := z);try nia.
  intros.
  destruct x; try nia.
  * repeat stepThousand. solve_terminated. exact 0.
  * stepOne. toRec. setoid_rewrite <- jesus_christ';auto. simpl.
    specialize (H0 (Z.pos p - 1)%Z).
    assert (0 ≤ Z.pos p - 1 < Z.pos p)%Z by lia. specialize (H0 H2). clear H2.
    (* specialize H0 by the rest of the symb vars... *)
    assert (0 ≤ Z.pos p - 1)%Z by lia. specialize (H0 H2). clear H2.
    
    destruct H0 as [y [IHExp IHPostcond]].

    pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
    simpl in IHExp_fic.
    
    eexists.
    eapply maxKTransitive'. auto.
    repeat stepThousand. solve_terminated. exact 0.
Qed.

Definition timestwo (e : Exp) : Exp :=
  ELetRec [
      (1, °ECall (˝erlang) (˝VLit "*"%string) [˝VVar 1; ˝VLit 2%Z]
      
      )
    ] (EApp (˝VFunId (0, 1)) [e]).

Definition timestwo' (e : Exp) : Exp :=
  °ECall (˝erlang) (˝VLit "*"%string) [e; ˝VLit 2%Z].

Theorem timestwo_ex:
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (timestwo (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Theorem timestwo'_ex:
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (timestwo' (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_simple (e : Exp) : Exp :=
  (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "*"%string))) [e;(VVal (VLit (Integer (2))))])).

Theorem times_two_simple_ex:
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (times_two_simple (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_rec (e : Exp) : Exp := ELetRec [
(1, (EExp (ECase (VVal (VVar 1)) 
[
  ([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))));
  ([PVar], (VVal (VLit (Atom "true"%string))), 
    (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) 
    (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(EExp (EApp (VVal (VFunId (2, 1))) [(VVal (VVar 0))]));(VVal (VLit (Integer (2))))])))))])))] 

(EApp (VVal (VFunId (0, 1))) [e]).

Theorem times_two_rec_ex:
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (times_two_rec (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition plus_nums_simple (e f : Exp) : Exp :=
(EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [e;f])).

Theorem plus_nums_simple_ex:
  forall (z : nat) (z' : nat),
  exists (y : Z),
  ⟨ [], (plus_nums_simple (˝VLit (Z.of_nat z)) (˝VLit (Z.of_nat z'))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z + Z.of_nat z')%Z.
Proof.
  solve_symbolically z.
Qed.

Definition plus_nums_rec (e f : Exp) : Exp :=
ELetRec [
(2, (EExp (ECase (VVal (VVar 1)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VVar 2)));([PVar], (VVal (VLit (Atom "true"%string))), (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(EExp (EApp (VVal (VFunId (2, 2))) [(VVal (VVar 0));(VVal (VVar 8))]));(VVal (VLit (Integer (1))))])))))])))
] (EApp (VVal (VFunId (0, 2))) [e;f]).

Theorem plus_nums_rec_ex:
  forall (z : nat) (z' : nat),
  exists (y : Z),
  ⟨ [], (plus_nums_rec (˝VLit (Z.of_nat z)) (˝VLit (Z.of_nat z'))) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z + Z.of_nat z')%Z.
Proof.
  setoid_rewrite RTCEquiv;[|constructor].
  toRec.
  
  induction z using lt_wf_ind; intros.
  destruct z.
  * repeat stepThousand. solve_terminated.
  * admit.
Admitted.

Definition isitzero_atom (e : Exp) : Exp :=
(EExp (ECase (e) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "true"%string))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "false"%string))))])).

Theorem isitzero_atom_ex:
  forall (z : nat),
  exists (y : string),
  ⟨ [], (isitzero_atom (˝VLit (Z.of_nat (S z)))) ⟩ -->* RValSeq [VLit y] /\ (y = "false"%string)%Z.
Proof.
  solve_symbolically z. auto.
Qed.

Definition isitzero_num (e : Exp) : Exp :=
(EExp (ECase (e) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (1)))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))))])).

Theorem isitzero_num_ex:
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (isitzero_num (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ ((y = 0)%Z \/ (y = 1)%Z).
Proof.
  setoid_rewrite RTCEquiv;[|constructor].
  intros z.
  stepOne. stepOne. stepOne.
  case_innermost.
  * stepThousand. solve_terminated.
  * stepThousand. solve_terminated.
  
  (*solve_symbolically z.*)
Qed.

Definition isitzero_num_app (e : Exp) : Exp :=
EExp ( EApp ( EFun 1 (EExp (ECase (VVal (VVar 0)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (1)))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))))]))) [e]).

Theorem isitzero_num_app_ex:
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (isitzero_num_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ ((y = 0)%Z \/ (y = 1)%Z).
Proof.
  setoid_rewrite RTCEquiv;[|constructor].
  intros z.
  stepOne. stepOne. stepOne. stepOne. stepOne. stepOne. stepOne. stepOne. stepOne.
  case_innermost.
  * stepOne. stepOne. stepOne. stepOne. solve_terminated. exact 0.
  * stepOne. stepOne. stepOne. stepOne. stepOne. solve_terminated. exact 0.
  
  (*solve_symbolically z.*)
Qed.

Definition isitzero_atom_app (e : Exp) : Exp :=
EExp ( EApp ( EFun 1(EExp (ECase (VVal (VVar 0)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "true"%string))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "false"%string))))]))) [e]).

Theorem isitzero_atom_app_ex:
  forall (z : Z), (z > 0)%Z ->
  exists (y : string),
  ⟨ [], (isitzero_atom_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = "false"%string).
Proof.
  setoid_rewrite RTCEquiv;[|constructor].
  intros. unfold isitzero_atom_app.
  stepOne. stepOne. stepOne. stepOne. stepOne. stepOne. stepOne. stepOne. stepOne.
  case_innermost.
  * lia.
  * stepOne. stepOne. stepOne. stepOne. stepOne. solve_terminated. exact 0. auto.
Qed.

Theorem timestwo_ex':
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (times_two_simple (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  setoid_rewrite RTCEquiv;[|constructor]. unfold times_two_simple.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  intros. solve_terminated. exact 0.
Qed.

Print EFun.

Definition times_two_simple_app (e : Exp) : Exp :=
  EExp (EApp (EExp (EFun 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "*"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (2))))])))) [e]).

Theorem timestwo_ex'':
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (times_two_simple_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  setoid_rewrite RTCEquiv;[|constructor]. unfold times_two_simple_app.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne. cbn.
  stepOne.
  intros. solve_terminated. exact 0.
Qed.

Theorem timestwo_ex''':
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (times_two_rec (˝VLit (Z.of_nat z))) ⟩ -->* RValSeq [VLit y] /\ (y = (Z.of_nat z) * 2)%Z.
Proof.
  setoid_rewrite RTCEquiv;[|constructor]. unfold times_two_rec.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne. setoid_rewrite <- jesus_christ';auto. simpl.
  induction z using lt_wf_ind.
  destruct z.
  * do 7 stepOne. do 1 stepOne. solve_terminated. exact 0.
  * do 30 stepOne. setoid_rewrite <- jesus_christ';auto. simpl.
    specialize (H z). assert (z < S z) by lia. apply H in H0. clear H.
    destruct H0. destruct H.
    eapply frame_indep_core_func with (fsapp := [FParams (ICall (VLit "erlang"%string) (VLit "+"%string)) [] [˝ VLit 2%Z]]) in H. simpl in H.
    eexists. eapply maxKTransitive'. assert (Z.of_nat (S z) - 1 = Z.of_nat z)%Z by lia. rewrite H1. eauto.
    
    do 3 stepOne. cbn. admit.
  
(*   stepOne.
  stepOne.
  stepOne.
  stepOne. intros z. case_innermost. repeat stepThousand. solve_terminated. exact 0.
  do 29 stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
  stepOne.
   *)
Abort.

Ltac my_tac args :=
  lazymatch args with
  | (?a, ?rest) =>
        (* first argument is a *)
        (* rest is the remaining arguments *)
        (* do something with a ... *)
        revert rest;
        my_tac a
  | (?only) => revert only
  end.

Theorem asd: forall (a s d f : nat), (a = a) /\ (s = s) /\ (d = d) /\ (f = f) /\ True.
Proof.
intros.
Compute (a,s,d,f).
my_tac (a,s,d,f). auto. Qed.

Theorem timestwo_ex''':
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (plus_nums_rec (˝VLit (Z.of_nat z)) (˝VLit 0%Z)) ⟩ -->* RValSeq [VLit y] /\ (y = (Z.of_nat z))%Z.
Proof.
  setoid_rewrite RTCEquiv;[|constructor].
  do 8 stepOne.
Admitted.


Definition plus_nums_rec' (e f : Exp) := ELetRec [(2, (EExp (ECase (VVal (VVar 1)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VVar 2)));([PVar], (VVal (VLit (Atom "true"%string))), (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(VVal (VVar 4));(VVal (VLit (Integer (1))))])) (EExp (EApp (VVal (VFunId (3, 2))) [(VVal (VVar 1));(VVal (VVar 0))])))))))])))] (EApp (VVal (VFunId (0, 2))) [e;f]).

Theorem plus_nums_rec_ex':
  forall (z : nat),
  exists (y : Z),
  ⟨ [], (plus_nums_rec' (˝VLit (Z.of_nat z)) (˝VLit 0%Z)) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat z)%Z.
Proof.
setoid_rewrite RTCEquiv;[|constructor].
do 8 stepOne. setoid_rewrite <- jesus_christ'; auto. simpl.
induction z using lt_wf_ind.
destruct z. stepThousand. solve_terminated. exact 0.
do 38 stepOne. setoid_rewrite <- jesus_christ'; auto. simpl.
Admitted.

Theorem helper:
  forall fs fs'












