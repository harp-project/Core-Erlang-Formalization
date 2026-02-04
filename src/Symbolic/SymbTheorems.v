From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.

Import ListNotations.

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

