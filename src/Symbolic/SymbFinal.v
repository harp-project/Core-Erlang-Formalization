From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.

Import ListNotations.

(* ----- DEFINITIONS ----- *)

Fixpoint sequentialStepMaxK (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match n with
    | 0 => (fs, r)
    | S n' => sequentialStepMaxK fs' r' n'
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

Definition canRec (fs : FrameStack) (r : Redex) : bool :=
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

Fixpoint sequentialStepCanRec (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match canRec fs r with
  | true => lastParamRBox fs r
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

Arguments sequentialStepMaxK !_ !_ !_ /.
Arguments sequentialStepK !_ !_ !_ /.
Arguments sequentialStepCanRec !_ !_ !_ /.

(* ----- LEMMAS ----- *)

Lemma maxKZeroRefl:
  forall (fs : FrameStack) (r : Redex),
  sequentialStepMaxK fs r 0 = (fs, r).
Proof.
  intros. unfold sequentialStepMaxK.
  destruct (sequentialStepFunc fs r).
  1:destruct p. all:reflexivity.
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

Lemma canRecUnfold:
  forall (fs : FrameStack) (r : Redex),
  canRec fs r = true -> 
    exists ext_top ext' id params e vl fs',
    (fs = FParams (IApp (VClos (ext_top :: ext') id params e)) vl [] :: fs') /\ 
    ((exists vseq, r = RValSeq vseq) \/ (r = RBox)).
Proof.
  intros. unfold canRec in H.
  destruct fs; try discriminate. destruct f; try discriminate. destruct ident; try discriminate.
  destruct v; try discriminate. destruct ext; try discriminate. destruct el; try discriminate.
  destruct r; try discriminate.
  * do 8 eexists. 1:reflexivity. left. eexists. reflexivity.
  * do 8 eexists. 1:reflexivity. right. reflexivity.
Qed.

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
  + unfold sequentialStepCanRec in H0.
    destruct (canRec fs r) eqn:HCanRec.
    - apply canRecUnfold in HCanRec. 
      destruct HCanRec as [ext_top [ext' [id [params [e [vl [fs'' [Hcr1 [[vs Hcr2] | Hcr2]]]]]]]]].
      * subst. simpl in H0. destruct vs.
        ++ inv H0. exists x. auto.
        ++ destruct vs.
           -- inv H0. destruct x.
              ** rewrite maxKZeroRefl in H1. inv H1.
              ** exists (S x).
                 simpl in H1. simpl.
                 destruct (params =? length (vl ++ [v]));auto.
           -- inv H0. exists x. auto.
      * subst. simpl in H0. inv H0. exists x. auto.
    - destruct (sequentialStepFunc fs r) eqn:Hssf. 1:destruct p. all:inv H0. all:eexists;eauto.
  + simpl in H0.
    destruct (canRec fs r) eqn:HCanRec.
    - apply canRecUnfold in HCanRec.
      destruct HCanRec as [ext_top [ext' [id [params [e [vl [fs'' [Hcr1 [[vs Hcr2] | Hcr2]]]]]]]]].
      * subst. simpl in H0. destruct vs.
        ++ inv H0. exists x. auto.
        ++ destruct vs.
           -- inv H0. destruct x.
               ** rewrite maxKZeroRefl in H1. inv H1.
               ** exists (S x).
                  simpl in H1. simpl.
                  destruct (params =? length (vl ++ [v]));auto.
            -- inv H0. exists x. auto.
      * subst. simpl in H0. inv H0. exists x. auto.
    - destruct (sequentialStepFunc fs r) eqn:Hssf.
      ** destruct p.
         unfold sequentialStepCanRec in H0. rewrite HCanRec in H0. rewrite Hssf in H0.
         fold sequentialStepCanRec in H0.
         specialize (IHk _ _ _ _ _ H0 H1).
         destruct IHk. exists (S x0). unfold sequentialStepMaxK. rewrite Hssf.
         fold sequentialStepMaxK. auto.
      ** inv H0.
         destruct x.
         ++ rewrite maxKZeroRefl in H1. inv H1. exists 0.
            unfold sequentialStepCanRec in H3. rewrite HCanRec in H3. rewrite Hssf in H3. inv H3.
            apply maxKZeroRefl.
         ++ unfold sequentialStepMaxK in H1.
            unfold sequentialStepCanRec in H3.
            rewrite HCanRec in H3. rewrite Hssf in H3.  inv H3.
            rewrite Hssf in H1. inv H1.
            exists 0. apply maxKZeroRefl.
Qed.

Lemma maxKInsertCanRecGeneral:
  forall (fs : FrameStack) (r r'' : Redex) (k : nat),
  is_result r'' ->
  (exists n, (let (fs', r') := sequentialStepCanRec fs r k in sequentialStepMaxK fs' r' n) = ([], r'')) <->
  (exists n, sequentialStepMaxK fs r n = ([], r'')).
Proof.
  intros. split; intros.
  * destruct (sequentialStepCanRec fs r k) eqn:Hsscr.
    eapply maxKTransCanRec; eauto.
  * destruct H0. 
    destruct (sequentialStepCanRec fs r k) eqn:Hsscr.
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
           destruct (canRec fs r) eqn:HCanRec.
           ++ apply canRecUnfold in HCanRec.
              destruct HCanRec as [ext_top [ext' [id [params [e [vl [fs'' [Hcr1 [[vs Hcr2] | Hcr2]]]]]]]]].
              -- subst. simpl in Hsscr. destruct vs.
                 *** inv Hsscr.
                 *** destruct vs.
                     +++ inv Hsscr.
                         exists (S x). simpl.
                         simpl in Hssf.
                         destruct (params =? length (vl ++ [v])); inv Hssf; auto.
                     +++ inv Hsscr.
              -- subst. simpl in Hsscr. inv Hsscr.
                 exists (S x). unfold sequentialStepMaxK.
                 rewrite Hssf. fold sequentialStepMaxK. auto.
           ++ unfold sequentialStepCanRec in Hsscr. rewrite HCanRec in Hsscr.
              rewrite Hssf in Hsscr. inv Hsscr. exists (S x).
              unfold sequentialStepMaxK. rewrite Hssf. fold sequentialStepMaxK. auto.
        ** simpl in Hsscr.
           destruct (canRec fs r) eqn:HCanRec.
           ++ apply canRecUnfold in HCanRec.
              destruct HCanRec as [ext_top [ext' [id [params [e [vl [fs'' [Hcr1 [[vs Hcr2] | Hcr2]]]]]]]]].
              -- subst. simpl in Hsscr. destruct vs.
                 *** inv Hsscr.
                 *** destruct vs.
                     +++ inv Hsscr.
                         exists (S x). unfold sequentialStepMaxK. simpl. simpl in Hssf.
                         rewrite Hssf. fold sequentialStepMaxK. auto.
                     +++ inv Hsscr.
              -- subst. simpl in Hsscr. inv Hsscr. exists (S x).
                 unfold sequentialStepMaxK. rewrite Hssf. fold sequentialStepMaxK. auto.
           ++ unfold sequentialStepCanRec in Hsscr. rewrite HCanRec in Hsscr.
              rewrite Hssf in Hsscr.
              specialize (IHx _ _ _ _ _ H0 Hsscr). auto.
      - inv H0.
        destruct k.
        ** unfold sequentialStepCanRec in Hsscr.
           destruct (canRec [] r'') eqn:HCanRec.
           ++ simpl in HCanRec. discriminate.
           ++ rewrite Hssf in Hsscr. inv Hsscr. exists 0. apply maxKZeroRefl.
        ** unfold sequentialStepCanRec in Hsscr. inv H; simpl in Hsscr; inv Hsscr.
           all:exists 0; auto.
Qed.

Lemma maxKInsertCanRec:
  forall (fs : FrameStack) (r r'' : Redex),
  is_result r'' ->
  (exists n, (let (fs', r') := sequentialStepCanRec fs r 1000 in sequentialStepMaxK fs' r' n) = ([], r'')) <->
  (exists n, sequentialStepMaxK fs r n = ([], r'')).
Proof.
  intros fs r r''.
  exact (maxKInsertCanRecGeneral fs r r'' 1000).
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

(* ----- TACTICS ----- *)

Ltac contains_match :=
  lazymatch goal with
  | |- context[match _ with _ => _ end] => idtac
  | |- _ => fail
  end.

Ltac possibly_recursive :=
  lazymatch goal with
  | |- context[FParams (IApp (VClos (_ :: _) _ _ _)) _ [] :: _] => idtac
  | |- _ => fail
  end.

Ltac case_innermost_term t Heq :=
  lazymatch t with
  | context[match ?x with _ => _ end] =>
      first [ case_innermost_term x Heq
            | destruct x eqn:Heq;
              first [apply Z_eqb_eq_corr in Heq
                    |apply Z_eqb_neq_corr in Heq
                    | idtac]]
  | _ => fail "No match subterm found"
  end.

Ltac case_innermost Heq :=
  match goal with
  | |- ?g => case_innermost_term g Heq
  end.

Ltac case_innermost_in H Heq :=
  let T := type of H in
  case_innermost_term T Heq.

Tactic Notation "case_innermost" ident(Heq) :=
  case_innermost Heq.

Tactic Notation "case_innermost" ident(H) ident(Heq) :=
  case_innermost_in H Heq.

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

Ltac is_not_terminated :=
  lazymatch goal with
  | |- context[sequentialStepMaxK _ _ _] => idtac
  | |- _ => fail
  end.

Ltac solve_final_state := 
  exists 0; (* This is for the step number, which is always irrelevant (|- nat) when this tactic is called *)
     first [ auto (* The program indeed terminated at ([], r) where is_result r *)
           | idtac "Unexpected end state 
                    (can be due to an exception in the Erlang program,
                     a result when an exception was expected,
                     non-termination in the given depth or
                     an impossible input that was not ruled out)"
           ].

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

Tactic Notation "intros_tail" :=
  idtac.

Tactic Notation "intros_tail" ident_list(t) :=
  intros t.

Ltac strip_IH_precond IH :=
  (* By this point, the induction hypothesis is an implication list. Note that this tactic
     terminates at hitting a forall, even if implication is just syntactic sugar for a forall
     in Coq. 
     
     P -> Q      is equivalent to        forall _ : P, Q
     
     When hitting a forall, lia cannot go further, because it is a declaration of a symbolic
     variable. In that case 'P' is not solvable. So this is a trick, but it is intended behaviour. *)
  let TIH := type of IH in
  lazymatch TIH with
  | ?p -> _ => 
    let H := fresh "Heq" in
    try (
    assert p as H by lia; specialize (IH H); clear H;
    strip_IH_precond IH)
  | _ => idtac
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

Ltac separate_cases_mult h t :=
  (* If we find a match expression, then introduce the variable h, along with the precondition. *)
  let precond := fresh "PreCond" in
  let heq := fresh "Heq" in
  intros h; intros t; intros precond;
  (* Separate the cases, using the hypothesis name Heq... *)
  case_innermost heq; simpl;
  (* ...and eliminate sequentialStepCanRec from all branches, if it exists. *)
  try (setoid_rewrite maxKInsertCanRecGeneral;try auto);
  (* A branch might not be reachable based on PreCond and Heq, try solving using nia *)
  try nia;
  (* The branch condition is merged with the precondition. *)
  let Tp := type of precond in
  let Th := type of heq in
  let precond' := fresh "PreCond" in
  assert (Tp /\ Th) as precond' by lia;
  clear heq; clear precond;
  (* Finally, we get back to the standard goal on both branches. *)
  revert h t precond'.

(* Tactic Notation "separate_cases_mult" ident(h) ident_list(t) :=
  separate_cases_mult h t. *)

Ltac base_case_mult_inner h t :=
  (* Do a thousand reduction steps. *)
  stepThousand;
  first [ (* If we run into a match expression, separate the cases. *)
          contains_match;
          separate_cases_mult h t;
          base_case_mult_inner h t
        | (* If we do not have a match expression but we have not terminated, continue the loop. *)
          is_not_terminated;
          base_case_mult_inner h t
        | (* If we have terminated, solve the terminated state. *)
          intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated goal"
        ].

Ltac base_case_mult precond heq' h t := 
  (* We need to return h and the precondition to the goal, before the loop begins. *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  revert precond'; revert t; revert h;
  base_case_mult_inner h t.

Ltac spec_rest_of_terms IH vl :=
  match vl with
  | [] => idtac
  | VLit ?lit :: ?vl' =>
    match lit with
    | Integer ?i => specialize (IH i)
    | Atom ?a => specialize (IH a)
    end;
    spec_rest_of_terms IH vl'
  | _ => fail "Unexpected error during induction: unsupported argument type"
  end.

Ltac rec_case_mult_inner IH h t :=
  toRec;
  first [ (* If case separation is found while getting to the next recursive step,
             continue on all branches *)
          contains_match;
          separate_cases_mult h t;
          rec_case_mult_inner IH h t
        | (* If the function is possibly recursive, we can assume that we have reached the
             next point of recursion. *)
          possibly_recursive;
          intros h; intros t;
          let precond := fresh "PreCond" in
          intros precond;
          (* The list of computed parameters needs to be extracted from the goal. In this
             tactic, the parameters are either integers or atoms. *)
          lazymatch goal with
          | |- context[FParams (IApp (VClos (_ :: _) _ _ _)) ?vl [] :: _] => 
            match vl with
            (* TODO: currently only integers and atoms are supported, extend this to
                     other types, e.g. lists *)
            | VLit ?lit :: ?vl =>
              (* IH is specialized by the variable the function is doing recursion on
                 (the first argument) *)
              match lit with
              | Integer ?i => specialize (IH i)
              | Atom ?a => specialize (IH a)
              end;
              (* IH is specialized by the condition introduced by the induction itself. *)
              strip_IH_precond IH;
              (* IH is specialized by the rest of the symbolic variables. *)
              spec_rest_of_terms IH vl
            | _ => fail "Unexpected error during induction: unsupported argument type"
            end;
            (* IH is specialzed by the precondition. *)
            strip_IH_precond IH;
            (* Terminal subterms are existential, they can be separated from IH by destruct. IH is
               then separated to the termination of the recursion, and the postcondition of said
               recursion termination. *)
            destruct_until_conj IH;
            let IHExp := fresh "IHExp" in
            let IHPostcond := fresh "IHPostcond" in
            destruct IH as [IHExp IHPostcond];
            (* The functional version of the frame_indep_core lemma is applied. *)
            let IHExp_fic := fresh "IHExp_fic" in
            pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic; simpl in IHExp_fic;
            (* Existential variables are created using eexists. *)
            eexists_until_conj;
            (* The transitivity property of the frame stack semantics is used. *)
            eapply maxKTransitive';[apply IHExp_fic|];
            clear IHExp IHExp_fic;
            (* The postcondition from the recursive step can be seen as a precondition
               for the rest of the evaluation. Thus, they are merged together. *)
            let precond' := fresh "PreCond" in
            let Tp := type of precond in
            let Th := type of IHPostcond in
            assert (Tp /\ Th) as precond' by nia;
            clear precond IHPostcond;
            (* All the variables are reverted, along with the precondition. This is because the rest
               of the goal is not recursive, thus it can be solved with the same algorithm as the
               base case. *)
            revert precond'; revert t; revert h;
            base_case_mult_inner h t
          | |- _ => fail "Could not get parameter list."
          end
        | (* If we did not reach a pattern match, or a point of recursion, but the function has
             not terminated yet, then toRec (1000 steps) was not enought, so we continue. *)
          is_not_terminated;
          rec_case_mult_inner IH h t
        | (* However, if we did terminate, then solve_terminated can solve the goal. *)
          intros; solve_terminated
        ].


Ltac rec_case_mult precond heq' IH h t := 
  (* Heq' is merged with the precondition, to get a new precondition. *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  (* To get to the next recursive step, a single step needs to be made first, since the
     goal is already potentially recursive. *)
  revert precond'; revert t; revert h;
  stepOne;
  rec_case_mult_inner IH h t.

Ltac solve_induction_mult h t :=
  (* To solve using induction, first introduce the variables and the precondition. *)
  intro h; intros t;
  let precond := fresh "PreCond" in
  intros precond;
  (* IH needs to be as general as possible, but we need to know that 0 <= h, which is in the
     precondition. So we need to assert it with lia, before reverting the precondition. *)
  let heq := fresh "Heq" in
  assert (0 <= h)%Z as heq by lia;
  revert precond; revert t;
  (* Induction is performed. In the new goal, the symbolic variable h is universally quantified
     again, the introduced version is irrelevant along with Heq, thus they can be deleted when
     they are not needed anymore. *)
  apply Zlt_0_ind with (x := h);[clear heq; clear h|exact heq];
  (* Since the old h was cleared, the name can be reused for its new universally quantified
     instance. The induction hypothesis is introduced as IH. We also know that 0 <= h, this is
     given by Zlt_0_ind itself. Heq can be reused, since it was cleared. It can be cleared
     again, since it directly comes from PreCond. PreCond is introduced after Heq. *)
  intros h;
  let IH := fresh "IH" in
  intros IH; intros heq; intros t; clear heq; intros precond;
  (* Destructing h gives 3 cases, the first is a base case with 0, the second is positive,
     and the third is negative. Since we assume that the recursive function decreases on h,
     the first case will terminate (IH not needed), the second will recurse, and the third
     is impossible, because h cannot be negative. *)
  let heq' := fresh "Heq" in
  destruct h eqn:heq';
    [clear IH;base_case_mult precond heq' h t| rec_case_mult precond heq' IH h t|nia].

Ltac take_to_rec_loop_mult h t :=
  toRec;
  first [ (* If the goal might be recursive... *)
          possibly_recursive;
          idtac "trying induction...";
          solve_induction_mult h t
        | (* If we can find a match expression... *)
          contains_match;
          separate_cases_mult h t;
          solve_symbolically_internal_mult h t
        | (* If we did not hit a point of recursion, or a case separation,
             the loop needs to be continued. *)
          solve_symbolically_internal_mult h t
        ]
with
solve_symbolically_internal_mult h t :=
  first [ (* If sequentialStepMaxK is still in the goal, and we did not hit recursion yet,
             then try moving forward to a point of recursion. *)
          is_not_terminated; take_to_rec_loop_mult h t
          (* If sequentialStepMaxK is not in the goal, we have terminated. *)
        | intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated program"
        ].

(* HACK: it is way easier, to handle cases with 1 and more than 1 symbolic variables separately.
   Ltac is very peculiar with empty parameter lists, which is annoying. *)
Tactic Notation "solve_symbolically" ident(h) ne_ident_list(t) := 
  (* To start, rewrite the goal from inductive to functional *)
  setoid_rewrite RTCEquiv;[|auto];
  (* This is separate, because the loop does not need to rewrite with RTCEquiv *)
  solve_symbolically_internal_mult h t.

Ltac separate_cases_0 h :=
  (* If we find a match expression, then introduce the variable h, along with the precondition. *)
  let precond := fresh "PreCond" in
  let heq := fresh "Heq" in
  intros h; intros precond;
  (* Separate the cases, using the hypothesis name Heq... *)
  case_innermost heq; simpl;
  (* ...and eliminate sequentialStepCanRec from all branches, if it exists. *)
  try (setoid_rewrite maxKInsertCanRecGeneral;try auto);
  (* A branch might not be reachable based on PreCond and Heq, try solving using nia *)
  try nia;
  (* The branch condition is merged with the precondition. *)
  let Tp := type of precond in
  let Th := type of heq in
  let precond' := fresh "PreCond" in
  assert (Tp /\ Th) as precond' by lia;
  clear heq; clear precond;
  (* Finally, we get back to the standard goal on both branches. *)
  revert h precond'.

Ltac base_case_0_inner h :=
  (* Do a thousand reduction steps. *)
  stepThousand;
  first [ (* If we run into a match expression, separate the cases. *)
          contains_match;
          separate_cases_0 h;
          base_case_0_inner h
        | (* If we do not have a match expression but we have not terminated, continue the loop. *)
          is_not_terminated;
          base_case_0_inner h
        | (* If we have terminated, solve the terminated state. *)
          intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated goal"
        ].

Ltac base_case_0 precond heq' h := 
  (* We need to return h and the precondition to the goal, before the loop begins. *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  revert h precond';
  base_case_0_inner h.

Ltac rec_case_0_inner IH h :=
  toRec;
  first [ (* If case separation is found while getting to the next recursive step,
             continue on all branches *)
          contains_match;
          separate_cases_0 h;
          rec_case_0_inner IH h
        | (* If the function is possibly recursive, we can assume that we have reached the
             next point of recursion. *)
          possibly_recursive;
          intros h; 
          let precond := fresh "PreCond" in
          intros precond;
          (* The list of computed parameters needs to be extracted from the goal. In this
             tactic, the function has only 1 parameter, which is either an integer or an atom. *)
          lazymatch goal with
          | |- context[FParams (IApp (VClos (_ :: _) _ _ _)) ?vl [] :: _] => 
            match vl with
            | [] => fail "Too few function parameters"
            (* TODO: currently only integers and atoms are supported, extend this to
                     other types, e.g. lists *)
            | [VLit (Integer ?i)] => specialize (IH i)
            | [VLit (Atom ?a)] => specialize (IH a)
            | _ :: _ => fail "Too many function parameters"
            | _ => fail "Unexpected error during induction"
            end;
            (* IH is specialzed by the condition introduced by the induction itself, and the
               precondition. Since this version of the tactic only takes a single symbolic variable, no
               more specialization is needed. *)
            strip_IH_precond IH;
            (* Terminal subterms are existential, they can be separated from IH by destruct. IH is
               then separated to the termination of the recursion, and the postcondition of said
               recursion termination. *)
            destruct_until_conj IH;
            let IHExp := fresh "IHExp" in
            let IHPostcond := fresh "IHPostcond" in
            destruct IH as [IHExp IHPostcond];
            (* The functional version of the frame_indep_core lemma is applied. *)
            let IHExp_fic := fresh "IHExp_fic" in
            pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic; simpl in IHExp_fic;
            (* Existential variables are created using eexists. *)
            eexists_until_conj;
            (* The transitivity property of the frame stack semantics is used. *)
            eapply maxKTransitive';[apply IHExp_fic|];
            clear IHExp IHExp_fic;
            (* The postcondition from the recursive step can be seen as a precondition
               for the rest of the evaluation. Thus, they are merged together. *)
            let precond' := fresh "PreCond" in
            let Tp := type of precond in
            let Th := type of IHPostcond in
            assert (Tp /\ Th) as precond' by nia;
            clear precond IHPostcond;
            (* The variable h is reverted, along with the precondition. This is because the rest
               of the goal is not recursive, thus it can be solved with the same algorithm as the
               base case. *)
            revert h precond';
            base_case_0_inner h
          | |- _ => fail "Could not get parameter list."
          end
        | (* If we did not reach a pattern match, or a point of recursion, but the function has
             not terminated yet, then toRec (1000 steps) was not enought, so we continue. *)
          is_not_terminated;
          rec_case_0_inner IH h
        | (* However, if we did terminate, then solve_terminated can solve the goal. *)
          intros; solve_terminated
        ].

Ltac rec_case_0 precond heq' IH h := 
  (* Heq' is merged with the precondition, to get a new precondition. *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  (* To get to the next recursive step, a single step needs to be made first, since the
     goal is already potentially recursive. *)
  revert h precond';
  stepOne;
  rec_case_0_inner IH h.

Ltac solve_induction_0 h :=
  (* To solve using induction, first introduce the variable and the precondition. *)
  intro h;
  let precond := fresh "PreCond" in
  intros precond;
  (* IH needs to be as general as possible, but we need to know that 0 <= h, which is in the
     precondition. So we need to assert it with lia, before reverting the precondition. *)
  let heq := fresh "Heq" in
  assert (0 <= h)%Z as heq by lia;
  revert precond;
  (* Induction is performed. In the new goal, the symbolic variable h is universally quantified
     again, the introduced version is irrelevant along with Heq, thus they can be deleted when
     they are not needed anymore. *)
  apply Zlt_0_ind with (x := h);[clear heq; clear h|exact heq];
  (* Since the old h was cleared, the name can be reused for its new universally quantified
     instance. The induction hypothesis is introduced as IH. We also know that 0 <= h, this is
     given by Zlt_0_ind itself. Heq can be reused, since it was cleared. It can be cleared
     again, since it directly comes from PreCond. PreCond is introduced after Heq. *)
  intros h;
  let IH := fresh "IH" in
  intros IH; intros heq; clear heq; intros precond;
  (* Destructing h gives 3 cases, the first is a base case with 0, the second is positive,
     and the third is negative. Since we assume that the recursive function decreases on h,
     the first case will terminate (IH not needed), the second will recurse, and the third
     is impossible, because h cannot be negative. *)
  let heq' := fresh "Heq" in
  destruct h eqn:heq';
    [clear IH;base_case_0 precond heq' h| rec_case_0 precond heq' IH h|nia].

Ltac take_to_rec_loop_0 h :=
  toRec;
  first [ (* If the goal might be recursive... *)
          possibly_recursive;
          idtac "trying induction...";
          solve_induction_0 h
        | (* If we can find a match expression... *)
          contains_match;
          separate_cases_0 h;
          solve_symbolically_internal_0 h
        | (* If we did not hit a point of recursion, or a case separation,
             the loop needs to be continued. *)
          solve_symbolically_internal_0 h
        ]
with
solve_symbolically_internal_0 h := 
  first [ (* If sequentialStepMaxK is still in the goal, and we did not hit recursion yet,
             then try moving forward to a point of recursion. *)
          is_not_terminated; take_to_rec_loop_0 h
          (* If sequentialStepMaxK is not in the goal, we have terminated. *)
        | intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated program"
        ].

Tactic Notation "solve_symbolically" ident(h) :=
  setoid_rewrite RTCEquiv; [|auto];
  solve_symbolically_internal_0 h.

(* TODO
   - technically, symbolic evaluation without any symbolic variables (i.e. just evaluating)
     is not yet supported, because the solve_symbolically tactic needs at least one variable.
   - check this on the other functions
   - look at the difference of z and x in the tactics: am I possibly messing something up?
     
     THINK/ASK ABOUT IT:
       Am I right, is it only possible to have a function application with an empty list of
       parameters left to evaluate on the *top* of the frame stack?
*)

(* ----- EXAMPLES ----- *)

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

Theorem fact_eval_ex:
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (z <= y /\ y >= 1)%Z.
Proof.
  solve_symbolically z.
Qed.

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

Theorem fact_tailrec_eval_ex:
  forall (z : Z) (z' : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z)) * z')%Z.
Proof.
  solve_symbolically z z'.
  

Qed.
























