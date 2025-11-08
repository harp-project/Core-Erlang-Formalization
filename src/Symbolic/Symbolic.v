From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.

Open Scope string_scope.
Import ListNotations.

Print positive.

Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 1%Z));
      ([PVar], ˝ttrue,
        °ELet 1 (EApp (˝VFunId (1, 1))
          [°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VLit 1%Z]])
          (°ECall (˝VLit "erlang") (˝VLit "*") [˝VVar 1; ˝VVar 0])
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e])
   (* Write the definition here *)
.

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

Fixpoint ssmkInner (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match n with
    | 0 => (fs, r)
    | S n' => ssmkInner fs' r' n'
    end
  end.

Definition isEnd (fs : FrameStack) (r : Redex) : bool :=
  match fs, r with
  | [], RValSeq _ => true
  | _, _ => false
  end.

Fixpoint ssmk (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
match isEnd fs r with
| true => (fs, r)
| false =>
  match n with
  | 0 => (fs, r)
  | S n' => 
    let (fs', r') := ssmkInner fs r 1000 in
    ssmk fs' r' n'
  end
end.

Arguments ssmkInner !_ !_ !_ /.
Arguments ssmk !_ !_ !_ /.

Ltac simpl_and_try_solve :=
  simpl;                                          (* simplify the goal *)
  lazymatch goal with
  | [ |- context[ssmk] ] => try lia              (* eval not done: is the case impossible? *)
  | _ => try (eexists; split;[reflexivity|nia])   (* eval done: the result exists & postcond holds *)
  end.


Ltac solve_forward :=
  repeat (simpl_and_try_solve; case_innermost).


Theorem fact_eval_example:
  forall (z : Z), (0 <= z < 10)%Z -> exists (y : Z), ssmk [] (fact_frameStack (˝VLit z)) 1000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
Qed.

Theorem fact_eval_example':
  forall (z : Z), (0 <= z < 30)%Z -> exists (y : Z), ssmk [] (fact_frameStack (˝VLit z)) 1000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros; unfold fact_frameStack.
  solve_forward.
Qed.

Theorem fact_eval_example_rec0:
  forall (z : Z), (0 <= z)%Z -> 
  exists (y : Z), ssmk [] (fact_frameStack (˝VLit z)) 1000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
Abort.

Lemma ssmkInnerTrans:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex) (n n' : nat),
  ssmkInner fs r n = (fs', r') -> ssmkInner fs' r' n' = (fs'', r'') -> ssmkInner fs r (n + n') = (fs'', r'').
Proof.
  intros fs fs' fs'' r r' r'' n. revert fs fs' fs'' r r' r''.
  induction n; intros.
  * simpl. unfold ssmkInner in H. destruct (sequentialStepFunc fs r); try destruct p; inv H; auto.
  * simpl. unfold ssmkInner. unfold ssmkInner in H.
    destruct (sequentialStepFunc fs r) eqn:Hssf.
    + destruct p. fold ssmkInner in *. eapply IHn; eauto.
    + inv H.
      destruct n'.
      - unfold ssmkInner in H0. rewrite Hssf in H0. auto.
      - unfold ssmkInner in H0. rewrite Hssf in H0. auto.
Qed.

Lemma ssmkInnerLet:
  forall (fs: FrameStack) (r: Redex) (n n' : nat),
  ssmkInner fs r (n + n') = let (fs', r') := ssmkInner fs r n in ssmkInner fs' r' n'.
Proof.
  intros. revert fs r n'. induction n; intros.
  * simpl. destruct (ssmkInner fs r 0) eqn:HssmkInner.
    unfold ssmkInner in HssmkInner.
    destruct (sequentialStepFunc fs r) eqn:Hssf.
    1:destruct p. all:inv HssmkInner. all:auto.
  * simpl.
    unfold ssmkInner. destruct (sequentialStepFunc fs r) eqn:Hssf.
    1:destruct p. all:fold ssmkInner.
    + auto.
    + destruct n'.
      all:unfold ssmkInner.
      all:rewrite Hssf.
      all:auto.
Qed.

Theorem ssmkEquiv:
  forall (fs : FrameStack) (r : Redex) (n : nat),
  ssmk fs r n = ssmkInner fs r (n * 1000).
Proof.
  intros fs r n. revert fs r.
  induction n; intros.
  + simpl. unfold ssmk, ssmkInner.
    destruct (isEnd fs r).
    all:destruct (sequentialStepFunc fs r).
    1,3:destruct p. all:reflexivity.
  + rewrite Nat.mul_succ_l.
    unfold ssmk. destruct (isEnd fs r) eqn:HisEnd.
    - unfold isEnd in *. destruct fs; try discriminate. destruct r; try discriminate.
      rewrite Nat.add_comm. simpl. reflexivity.
    - fold ssmk.
      destruct (ssmkInner fs r 1000) eqn:Hssmk.
      rewrite Nat.add_comm.
      rewrite ssmkInnerLet. rewrite Hssmk. auto.
Qed.

Lemma ssmkTrans:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex) (n n' : nat),
  ssmk fs r n = (fs', r') -> ssmk fs' r' n' = (fs'', r'') -> ssmk fs r (n + n') = (fs'', r'').
Proof.
  setoid_rewrite ssmkEquiv.
  intros.
  assert ((n + n') * 1000 = (n * 1000 + n' * 1000)) by lia.
  rewrite H1. clear H1.
  eapply ssmkInnerTrans; eauto.
Qed.

Lemma backOneInner:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex) (n n' : nat),
  ssmkInner fs r 1 = (fs', r') ->
  (let (fs0, r0) := ssmkInner fs' r' n in ssmk fs0 r0 n' = (fs'', r'')) ->
  let (fs0, r0) := ssmkInner fs r (S n) in ssmk fs0 r0 n' = (fs'', r'').
Proof.
  intros.
  destruct (ssmkInner fs' r' n) eqn:HssmkInner.
  rewrite ssmkEquiv in H0.
  destruct (ssmkInner fs r (S n)) eqn:HssmkInner0.
  rewrite ssmkEquiv.
  assert (S n = 1 + n) by lia.
  rewrite H1 in HssmkInner0. clear H1.
  rewrite ssmkInnerLet in HssmkInner0.
  rewrite H in HssmkInner0.
  rewrite HssmkInner0 in HssmkInner. inv HssmkInner. auto.
Qed.

Lemma advanceOneInner:
  forall (fs fs'' : FrameStack) (r r'' : Redex) (n n' : nat),
  (let (fs0, r0) := ssmkInner fs r (S n) in ssmk fs0 r0 n' = (fs'', r'')) ->
  exists (fs' : FrameStack) (r' : Redex),
    ssmkInner fs r 1 = (fs', r') /\
    (let (fs0, r0) := ssmkInner fs' r' n in ssmk fs0 r0 n' = (fs'', r'')).
Proof.
  intros.
  destruct (ssmkInner fs r (S n)) eqn:HssmkInner.
  rewrite ssmkEquiv in H.
  assert (S n = 1 + n) by lia.
  rewrite H0 in HssmkInner. clear H0.
  rewrite ssmkInnerLet in HssmkInner.
  destruct (ssmkInner fs r 1) eqn:HssmkInner0.
  do 2 eexists. split. eauto.
  rewrite HssmkInner.
  rewrite ssmkEquiv. auto.
Qed.

Lemma backOnePivot:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex) (n : nat),
  ssmkInner fs r 1 = (fs', r') ->
  ssmk fs' r' n = (fs'', r'') ->
  let (fs0, r0) := ssmkInner fs r 1 in ssmk fs0 r0 n = (fs'', r'').
Proof.
  intros. rewrite H. auto.
Qed.

Lemma advanceOnePivot:
  forall (fs fs'' : FrameStack) (r r'' : Redex) (n : nat),
  (let (fs0, r0) := ssmkInner fs r 1 in ssmk fs0 r0 n = (fs'', r'')) ->
  exists (fs' : FrameStack) (r' : Redex),
    ssmkInner fs r 1 = (fs', r') /\
    ssmk fs' r' n = (fs'', r'').
Proof.
  intros. setoid_rewrite ssmkEquiv.
  destruct (ssmkInner fs r 1) eqn:HssmkInner.
  rewrite ssmkEquiv in H.
  do 2 eexists. split. eauto. auto.
Qed.

Lemma backOneChange:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex) (n : nat),
  ssmkInner fs r 1 = (fs', r') ->
  (let (fs0, r0) := ssmkInner fs' r' 999 in ssmk fs0 r0 n = (fs'', r'')) ->
  ssmk fs r (S n) = (fs'', r'').
Proof.
  intros.
  rewrite ssmkEquiv.
  destruct (ssmkInner fs' r' 999) eqn:HssmkInner.
  rewrite ssmkEquiv in H0.
  assert (S n * 1000 = 1 + (999 + n * 1000)) by lia.
  rewrite H1. clear H1.
  rewrite ssmkInnerLet. rewrite H.
  rewrite ssmkInnerLet. rewrite HssmkInner. auto.
Qed.

Lemma advanceOneChange:
  forall (fs fs'' : FrameStack) (r r'' : Redex) (n : nat),
  ssmk fs r (S n) = (fs'', r'') ->
  exists (fs' : FrameStack) (r' : Redex),
    ssmkInner fs r 1 = (fs', r') /\
    (let (fs0, r0) := ssmkInner fs' r' 999 in ssmk fs0 r0 n = (fs'', r'')).
Proof.
  intros. rewrite ssmkEquiv in H.
  assert (S n * 1000 = 1 + (999 + n * 1000)) by lia.
  rewrite H0 in H. clear H0.
  rewrite ssmkInnerLet in H.
  destruct (ssmkInner fs r 1) eqn:HssmkInner.
  rewrite ssmkInnerLet in H.
  destruct (ssmkInner f r0 999) eqn:HssmkInner0.
  do 2 eexists. split. eauto.
  rewrite HssmkInner0. rewrite ssmkEquiv. auto.
Qed.

Lemma ssmkInnerOneMore:
  forall (fs : FrameStack) (r : Redex) (v : list Val) (n : nat),
  ssmkInner fs r n = ([], RValSeq v) -> ssmkInner fs r (S n) = ([], RValSeq v).
Proof.
  intros fs r v n. revert fs r v.
  induction n; intros.
  * unfold ssmkInner in *.
    destruct (sequentialStepFunc fs r) eqn:Hssf.
    1:destruct p. all:inv H. reflexivity.
  * unfold ssmkInner. unfold ssmkInner in H.
    destruct (sequentialStepFunc fs r) eqn:Hssf. all:auto.
    destruct p. fold ssmkInner in *.
    apply IHn in H.
    unfold ssmkInner in H. destruct (sequentialStepFunc f r0) eqn:Hssf0.
    1:destruct p. 1:fold ssmkInner in H. all:auto.
Qed.

Theorem ssmkInnerMore:
  forall (fs : FrameStack) (r : Redex) (v : list Val) (n n' : nat),
  n <= n' ->
  ssmkInner fs r n = ([], RValSeq v) -> ssmkInner fs r n' = ([], RValSeq v).
Proof.
  intros fs r v n. revert fs r v.
  induction n; intros.
  * destruct n'.
    all:unfold ssmkInner in *.
    all:destruct (sequentialStepFunc fs r) eqn:Hssf.
    1,3:destruct p.
    all:auto. inv H0.
  * destruct n'.
    + inv H.
    + assert (n <= n') by lia.
      unfold ssmkInner. unfold ssmkInner in H0.
      destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. fold ssmkInner in *.
        apply IHn. lia. auto.
      - auto.
Qed.

Ltac advanceOne H :=
  first [ apply advanceOneChange in H;destruct H as [fs' [r' [Hfirst H]]];inv Hfirst
        | apply advanceOneInner in H;destruct H as [fs' [r' [Hfirst H]]];inv Hfirst
        | apply advanceOnePivot in H;destruct H as [fs' [r' [Hfirst H]]];inv Hfirst
        | idtac "Nothing to advance"].

Theorem fact_eval_rec:
  forall (z : nat), (* (0 <= z) -> *)
  forall (y : nat), ssmk [] (fact_frameStack (˝VLit (Z.of_nat z))) 1000 = ([], RValSeq [VLit (Z.of_nat y)]) ->
  (z <= y).
Proof.
  intros. unfold fact_frameStack in H.
  advanceOne H.
  advanceOne H.
  advanceOne H.
  advanceOne H.
  advanceOne H.
  advanceOne H.
  
  
  induction z.
  * simpl in H. inv H. nia.
  * (*simpl in H0. simpl in IHz.*)
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.
    advanceOne H.

    
    assert ((Z.of_nat (S z) - 1)%Z = Z.of_nat z) by lia.
    rewrite H0 in H. clear H0.
    
    
  
  


Abort.

Lemma help:
  forall (fs : FrameStack) (r r' : Redex),
  is_result r' ->
  (exists n, ssmk fs r (S n) = ([], r')) <->
  exists n, ssmk fs r n = ([], r').
Proof.
  intros. split; intro.
  * destruct H0. exists (S x). auto.
  * destruct H0. destruct x.
    + unfold ssmk in *.
      destruct (isEnd fs r) eqn:HisEnd.
      - inv H0. exists 0. reflexivity.
      - fold ssmk. inv H0.
        inv H. simpl. exists 0. simpl. reflexivity.
    + exists x. auto.
Qed.

Definition mayRec (fs : FrameStack) (r : Redex) : bool :=
  match fs with
  | FParams (IApp (VClos (_ :: _) _ _ _)) _ _ :: _ => 
    match r with
    | RValSeq _ => true
    | _ => false
    end
  | _ => false
  end.

Compute mayRec [FParams
         (IApp
            (VClos
               [(0, 1,
                 ° ECase (˝ VVar 1)
                     [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z);
                      ([PVar], ˝ VLit "true",
                       ° ELet 1
                           (° EApp (˝ VFunId (1, 1))
                                [° ECall (˝ VLit "erlang") (˝ VLit "-")
                                     [˝ VVar 0; ˝ VLit 1%Z]])
                           (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])]
               0 1
               (° ECase (˝ VVar 1)
                    [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z);
                     ([PVar], ˝ VLit "true",
                      ° ELet 1
                          (° EApp (˝ VFunId (1, 1))
                               [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]])
                          (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])))
         [] []] (RValSeq [VLit (Z.of_nat 1)]).

Fixpoint ssmkMayRec (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex * nat :=
match mayRec fs r with
| true => (fs, r, n)
| false => 
  match sequentialStepFunc fs r with
  | None => (fs, r, n)
  | Some (fs', r') =>
    match n with
    | 0 => (fs, r, n)
    | S n' => ssmkMayRec fs' r' n'
    end
  end
end.

Compute ssmkMayRec [] (fact_frameStack (˝VLit 4%Z)) 100.

Theorem ssmkRec:
  forall (fs : FrameStack) (r : Redex) (n : nat),
  ssmkInner fs r n =
  let '(fs', r', n') := ssmkMayRec fs r n in ssmkInner fs' r' n'.
Proof.
  intros. revert fs r. induction n; intros.
  * simpl. unfold ssmkInner.
    destruct (mayRec fs r).
    + reflexivity.
    + destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. rewrite Hssf. reflexivity.
      - rewrite Hssf. reflexivity.
  * simpl. unfold ssmkInner.
    destruct (mayRec fs r).
    + reflexivity.
    + destruct (sequentialStepFunc fs r) eqn:Hssf.
      - fold ssmkInner. destruct p. auto.
      - rewrite Hssf. reflexivity.
Qed.

Theorem fact_eval_example_rec0:
  forall (z : nat), (*(0 <= z) -> *)
  exists (y : nat),
  (exists (n : nat), ssmk [] (fact_frameStack (˝VLit (Z.of_nat z))) n = ([], RValSeq [VLit (Z.of_nat y)])) 
    /\ (z <= y).
Proof.
  intros. setoid_rewrite <- help;[|constructor].
  
  Opaque ssmkInner. simpl.
  setoid_rewrite ssmkRec. simpl.
  Transparent ssmkInner.

Abort.

(* Ltac toPotentialRec :=
  Opaque ssmkInner; simpl; try (setoid_rewrite ssmkRec); simpl; Transparent ssmkInner.
 *)

Fixpoint ssmkInnerNoSimpl (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match n with
    | 0 => (fs, r)
    | S n' => ssmkInnerNoSimpl fs' r' n'
    end
  end.

Arguments ssmkInnerNoSimpl : simpl never.

Lemma ssmkInnerSimplEquiv : 
  forall (fs : FrameStack) (r : Redex) (n : nat),
  ssmkInner fs r n = ssmkInnerNoSimpl fs r n.
Proof. reflexivity. Qed.

Theorem ssmkSimpl :
  forall (fs : FrameStack) (r : Redex) (n : nat),
  match isEnd fs r with
  | true => (fs, r)
  | false => let (fs', r') := ssmkInnerNoSimpl fs r 1000 in ssmk fs' r' n
  end = ssmk fs r (S n).
Proof. reflexivity. Qed.

Theorem ssmkRecNoSimpl :
  forall (fs : FrameStack) (r : Redex) (n : nat),
  ssmkInner fs r n =
  let '(fs', r', n') := ssmkMayRec fs r n in ssmkInnerNoSimpl fs' r' n'.
Proof.
  intros. rewrite ssmkRec. destruct (ssmkMayRec fs r n). destruct p. rewrite ssmkInnerSimplEquiv. reflexivity.
Qed.

Ltac toPotentialRec :=
match goal with
| |- context[ssmkInner] => idtac
| _ => try (setoid_rewrite <- ssmkSimpl); simpl
end;
  try (setoid_rewrite ssmkRecNoSimpl); simpl;
  try (setoid_rewrite <- ssmkInnerSimplEquiv).

Lemma asd:
  forall (fs : FrameStack) (r : Redex) (n : nat),
  ssmkInner fs r (S n) = let (fs', r') := ssmkInner fs r 1 in ssmkInnerNoSimpl fs' r' n.
Proof. Admitted.

Theorem fact_eval_example_rec0:
  forall (z : nat), (*(0 <= z) -> *)
  exists (y : Z),
  (exists (n : nat), ssmk [] (fact_frameStack (˝VLit (Z.of_nat z))) n = ([], RValSeq [VLit y])) 
    /\ ((Z.of_nat z) <= y)%Z.
Proof.
  intros. setoid_rewrite <- help;[|constructor].
  toPotentialRec.
  induction z.
  * simpl. eexists. split;[exists 0;reflexivity|nia].
  * setoid_rewrite asd. simpl. setoid_rewrite <- ssmkInnerSimplEquiv.
    toPotentialRec. setoid_rewrite ssmkInnerSimplEquiv. unfold eval_arith_NEW. simpl.
    remember (IApp _). clear Heqf.

Abort.

Theorem ssmkInnerOuter:
  forall (fs : FrameStack) (r r': Redex) (k : nat),
  is_result r' ->
  (exists n, (let (fs0, r0) := ssmkInner fs r k in ssmk fs0 r0 n) = ([], r')) <->
  (exists n, ssmk fs r n = ([], r')).
Proof.
  intros. split.
  * intros.
    destruct H0. destruct (ssmkInner fs r k) eqn:HssmkInner.
    setoid_rewrite ssmkEquiv.
    rewrite ssmkEquiv in H0.
    exists (x + k).
    assert ((x + k) * 1000 = k + ((x * 1000) + (k * 999))) by lia.
    rewrite H1. clear H1.
    rewrite ssmkInnerLet. rewrite HssmkInner.
    rewrite ssmkInnerLet. rewrite H0.
    inv H.
    + destruct k; simpl; reflexivity.
    + destruct k; simpl; reflexivity.
  * intros.
    destruct H0.
    (* setoid_rewrite not working backwards?? *)
    assert 
    ( (exists n : nat, (let (fs0, r0) := ssmkInner fs r k in ssmkInner fs0 r0 (n * 1000)) = ([], r')) ->
      (exists n : nat, (let (fs0, r0) := ssmkInner fs r k in ssmk fs0 r0 n) = ([], r'))).
    { intros. destruct (ssmkInner fs r k). setoid_rewrite ssmkEquiv. auto. }
    apply H1. clear H1.
    (* setoid_rewrite not working backwards again??? *)
    assert
    ( (∃ n : nat, ssmkInner fs r (k + n * 1000) = ([], r')) ->
      (∃ n : nat, (let (fs0, r0) := ssmkInner fs r k in ssmkInner fs0 r0 (n * 1000)) = ([], r'))).
    { intros. setoid_rewrite ssmkInnerLet in H1. destruct (ssmkInner fs r k). auto. }
    apply H1. clear H1.
    rewrite ssmkEquiv in H0.
    exists x.
    assert (k + x * 1000 = x * 1000 + k) by lia.
    rewrite H1. clear H1.
    rewrite ssmkInnerLet. rewrite H0.
    inv H.
    + destruct k; simpl; reflexivity.
    + destruct k; simpl; reflexivity.
Qed.

Theorem ssmkOuterIsInner:
  forall (fs : FrameStack) (r r': Redex),
  is_result r' ->
  (exists n, ssmk fs r n = ([], r')) <->
  (exists n, ssmkInner fs r n = ([], r')).
Proof.
  intros. split; intro.
  * destruct H0. exists (x * 1000). rewrite <- ssmkEquiv. auto.
  * destruct H0.
    exists x. rewrite ssmkEquiv.
    assert (x * 1000 = x + x * 999) by lia.
    rewrite H1. clear H1.
    rewrite ssmkInnerLet. rewrite H0.
    inv H.
    + destruct x; simpl; reflexivity.
    + destruct x; simpl; reflexivity.
Qed.

Print frame_indep_core.
Close Scope string_scope.

Fixpoint ssExactlyk (fs : FrameStack) (r : Redex) (n : nat) : option (FrameStack * Redex) :=
match n with
| 0 => Some (fs, r)
| S n' =>
  match sequentialStepFunc fs r with
  | Some (fs', r') => ssExactlyk fs' r' n'
  | _ => None
  end
end.

Theorem kStepEquiv:
  forall (fs fs' : FrameStack) (r r' : Redex) (k : nat),
  ⟨ fs, r ⟩ -[k]-> ⟨ fs', r' ⟩ <-> ssExactlyk fs r k = Some (fs', r').
Proof.
  intros. split.
  * revert fs fs' r r'.
    induction k; intros.
    + simpl. inv H. reflexivity.
    + simpl. destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. apply IHk.
        inv H. apply sequentialStepEquiv in H1. rewrite Hssf in H1. inv H1. auto.
      - inv H. apply sequentialStepEquiv in H1. rewrite H1 in Hssf. discriminate.
  * revert fs fs' r r'.
    induction k; intros.
    + simpl in H. inv H. constructor.
    + simpl in H. destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. apply sequentialStepEquiv in Hssf.
        econstructor. eauto. apply IHk. auto.
      - discriminate.
Qed.

Theorem kStepMaxkStep:
  forall (fs fs' : FrameStack) (r r' : Redex),
  (exists n, ssmkInner fs r n = (fs', r')) <->
  (exists n, ssExactlyk fs r n = Some (fs', r')).
Proof.
  intros. split.
  * intro. destruct H. revert H. revert fs fs' r r'.
    induction x; intros.
    + unfold ssmkInner in H. destruct (sequentialStepFunc fs r).
      - destruct p. inv H. exists 0. reflexivity.
      - inv H. exists 0. reflexivity.
    + unfold ssmkInner in H.
      destruct (sequentialStepFunc fs r) eqn:Hssf; fold ssmkInner in H.
      - destruct p. apply IHx in H. destruct H. exists (S x0). simpl. rewrite Hssf. auto.
      - inv H. exists 0. reflexivity.
  * intro. destruct H. exists x.
    revert H. revert fs fs' r r'.
    induction x; intros.
    + simpl in H. inv H. unfold ssmkInner.
      destruct (sequentialStepFunc _ _). 1:destruct p. all:reflexivity.
    + simpl in H. unfold ssmkInner.
      destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p. fold ssmkInner. apply IHx. auto.
      - inv H.
Qed.

Theorem frame_indep_core_functional:
  forall (fs fs' : FrameStack) (r r' : Redex),
  (exists n, ssmkInner fs r n = (fs', r')) ->
  forall (fsapp : FrameStack), (exists n, ssmkInner (fs ++ fsapp) r n = (fs' ++ fsapp, r')).
Proof.
  intros.
  apply kStepMaxkStep. apply kStepMaxkStep in H.
  destruct H. apply kStepEquiv in H.
  exists x. apply kStepEquiv. apply frame_indep_core. auto.
Qed.

Theorem ssmkTransitive:
  forall (fs fs' fs'' : FrameStack) (r r' r'' : Redex),
  (exists n, ssmkInner fs r n = (fs', r')) ->
  (exists n, ssmkInner fs' r' n = (fs'', r'')) ->
  (exists n, ssmkInner fs r n = (fs'', r'')).
Proof.
  setoid_rewrite kStepMaxkStep. setoid_rewrite <- kStepEquiv. intros.
  destruct H. destruct H0. exists (x + x0).
  eapply transitive_eval; eauto.
Qed.

Theorem fact_eval_example_rec0':
  forall (z : nat), (*(0 <= z) -> *)
  exists (y : Z),
  (exists (n : nat), ssmk [] (fact_frameStack (˝VLit (Z.of_nat z))) n = ([], RValSeq [VLit y])) 
    /\ ((Z.of_nat z) <= y)%Z.
Proof.
  intros.
  setoid_rewrite <- help;[|constructor].
  toPotentialRec.
  induction z.
  * simpl. eexists. split;[exists 0;reflexivity|nia].
  * setoid_rewrite asd. simpl. setoid_rewrite <- ssmkInnerSimplEquiv.
    toPotentialRec. setoid_rewrite ssmkInnerSimplEquiv. unfold eval_arith_NEW. simpl.
    remember (IApp _).
    setoid_rewrite <- ssmkInnerSimplEquiv.
    setoid_rewrite ssmkInnerOuter;[|constructor].
    setoid_rewrite ssmkOuterIsInner;[|constructor].
    setoid_rewrite ssmkInnerOuter in IHz;[|constructor].
    setoid_rewrite ssmkOuterIsInner in IHz;[|constructor].
    
    destruct IHz. destruct H.
    remember (FLet _ _) as l.
    pose proof frame_indep_core_functional.
    specialize (H1 _ _ _ _ H [l]). simpl in H1.
    
    assert ((Z.of_nat (S z) - 1)%Z = Z.of_nat z) by lia. rewrite H2. clear H2.
    
    eexists. split.
    eapply ssmkTransitive. eauto.
    subst l.
    setoid_rewrite <- ssmkOuterIsInner;[|constructor].
    setoid_rewrite <- help;[|constructor]. simpl.
    exists 0. simpl. reflexivity.
    
    (* we actually also need the info, that 0! > 0, which is surprising... *)
    setoid_rewrite <- ssmkOuterIsInner in H;[|constructor].
    setoid_rewrite <- help in H;[|constructor].
    destruct z.
    + subst f. simpl in H. destruct H. destruct x0.
      - simpl in H. inv H. lia.
      - simpl in H. inv H. lia.
    + nia.
Qed.

(* TODO
   - look into: frame_indep_core for function
   - look into: how do I use the old tactics for this method?
   - look into: how can I use the new theorems for this method?
 *)















