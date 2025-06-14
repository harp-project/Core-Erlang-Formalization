From CoreErlang.FrameStack Require Export Frames SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Concurrent Require Export ProcessSemantics.
From CoreErlang.Interpreter Require Export EqualityFunctions.
From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import InterpreterAuxLemmas.

Theorem step_equiv: forall fs fs' e e', REDCLOSED e ->
    ⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩ <-> step_func fs e = Some (fs', e').
Proof.
  intros fs fs' e e' HH. split.
  * intro. inversion H; try auto; unfold step_func; try rewrite <- create_result_equiv.
    + destruct ident; try reflexivity. congruence.
    + rewrite <- H1. destruct ident; try reflexivity. congruence.
    + rewrite <- H0. reflexivity.
    + rewrite H0. rewrite Nat.eqb_refl. reflexivity.
    + rewrite H0. reflexivity.
    + rewrite H0. reflexivity.
    + rewrite H0. reflexivity.
    + rewrite <- H0. rewrite Nat.eqb_refl. reflexivity.
    + destruct exc. destruct p. rewrite H0.
      destruct F; try reflexivity.
      do 4 (destruct vl2; try reflexivity). simpl.
      unfold exclass_to_value. destruct e0; destruct e3; simpl; destruct e0; discriminate.
  * intro. destruct e.
    + destruct e.
      - simpl in H. inv H. constructor. inv HH. inv H0. assumption.
      - simpl in H. destruct e; try (inv H; constructor); try reflexivity.
        destruct l eqn:Hl.
        ** inv H. constructor.
        ** destruct p. inv H. constructor.
    + simpl in H. destruct fs; try discriminate.
      destruct f; destruct vs; try discriminate.
      - destruct vs. inv H. constructor. discriminate.
      - destruct vs. inv H. constructor. discriminate.
      - destruct el; discriminate.
      - rewrite <- create_result_equiv in H. destruct el.
        ** destruct vs; try discriminate.
           destruct (create_result ident (vl ++ [v])) eqn:H'; try discriminate.
           destruct p. inv H.
           apply eval_cool_params with (l := o). rewrite H'. reflexivity.
        ** destruct vs; try discriminate. inv H. constructor.
      - destruct vs; try discriminate. inv H. constructor.
      - destruct vs; try discriminate. inv H. constructor.
      - destruct vs; try discriminate. inv H. constructor.
      - destruct l. inv H. constructor.
        destruct p. destruct p. destruct (match_pattern_list l0 []) eqn:H'.
        inv H. constructor. assumption.
        inv H. constructor. assumption.
      - destruct l. inv H. constructor.
        destruct p. destruct p. destruct (match_pattern_list l0 (v :: vs)) eqn:H'.
        inv H. constructor. assumption.
        inv H. constructor. assumption.
      - destruct v; try discriminate. destruct l; try discriminate.
        destruct (s =? "true")%string eqn:Hs.
        rewrite String.eqb_eq in Hs. rewrite Hs.
        destruct vs; try discriminate. inv H. constructor.
        destruct (s =? "false")%string eqn:Hs'.
        rewrite String.eqb_eq in Hs'. rewrite Hs'.
        destruct vs; try discriminate. inv H. constructor.
        destruct vs; try discriminate.
      - simpl in H. destruct l.
        ** inv H. constructor. reflexivity.
        ** discriminate.
      - simpl in H. destruct l. discriminate.
        destruct (Datatypes.length vs =? l) eqn:H'.
        inv H. constructor. simpl. f_equal. apply Nat.eqb_eq. assumption.
        discriminate.
      - destruct vs; try discriminate. inv H. constructor.
      - simpl in H. destruct (vl1 =? 0) eqn:H'.
        inv H. constructor. simpl. apply Nat.eqb_eq. assumption.
        discriminate.
      - simpl in H. destruct (vl1 =? S (Datatypes.length vs)) eqn:H'.
        inv H. constructor. simpl. apply Nat.eqb_eq. assumption.
        discriminate.
    + simpl in H. destruct e. destruct p. destruct fs. discriminate.
      destruct f; simpl in *; inv H; try constructor; simpl; try reflexivity.
      do 4 (destruct vl2; try discriminate). inv H1. constructor.
    + simpl in H. destruct fs; try discriminate.
      destruct f; try discriminate. destruct el.
      - destruct ident; try discriminate; simpl in H; inv H.
        ** apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** destruct m; inv H1; 
           try (apply eval_cool_params_0 with (l := None); try discriminate; try reflexivity).
           destruct l.
           ++ destruct f; inv H0;
              try (apply eval_cool_params_0 with (l := None); try discriminate; try reflexivity).
              destruct l. rewrite <- eval_equiv in H1.
              -- destruct (eval s s0 vl) eqn:H'; try discriminate. destruct p. inv H1.
                 apply eval_cool_params_0 with (l := o). discriminate.
                 simpl. rewrite H'. reflexivity.
              -- inv H1. apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
           ++ inv H0. apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** rewrite <- primop_eval_equiv in H1.
           destruct (primop_eval f vl) eqn:H'; try discriminate. destruct p. inv H1.
           apply eval_cool_params_0 with (l := o). discriminate. simpl.
           rewrite H'. reflexivity.
        ** destruct v; inv H1;
           try (apply eval_cool_params_0 with (l := None); try discriminate; try reflexivity).
           destruct (params =? Datatypes.length vl) eqn:H'.
           ++ inv H0.
              apply eval_cool_params_0 with (l := None). discriminate.
              simpl. rewrite H'. reflexivity.
           ++ inv H0.
              apply eval_cool_params_0 with (l := None). discriminate.
              simpl. rewrite H'. reflexivity.
      - destruct ident; try discriminate; simpl in H; inv H; constructor; discriminate.
Qed.

Theorem step_func_closedness: forall fs e, FSCLOSED fs -> REDCLOSED e -> forall fs' e',
    step_func fs e = Some (fs', e') -> FSCLOSED fs' /\ REDCLOSED e'.
Proof.
  intros. apply step_equiv in H1; try assumption. apply (step_closedness fs e); assumption.
Qed.

Lemma VLit_val_eq: forall v l, v =ᵥ VLit l = true -> v = VLit l.
Proof.
  intros. destruct v; simpl in H; try congruence.
  apply Lit_eqb_eq in H. rewrite H. reflexivity.
Qed.

Lemma VLit_val_neq: forall v l, v =ᵥ VLit l = false -> v <> VLit l.
Proof.
  intros. intro.
  rewrite H0 in H. rewrite Val_eqb_refl in H. discriminate.
Qed.

Theorem processLocalStepEquiv: forall p p' a, (* If p is liveProcess *)
  (forall fs e mb links flag, p = inl (fs, e, mb, links, flag) -> REDCLOSED e) ->
  p -⌈ a ⌉-> p' <-> processLocalStepFunc p a = Some p'.
Proof.
  intros p p' a Hlp. split; intro.
  * inversion H; simpl.
    + destruct (step_func fs e) eqn:H'.
      - destruct p0.
        symmetry in H1. apply Hlp in H1.
        rewrite step_equiv in H0. rewrite H' in H0. inv H0. reflexivity.
        assumption.
      - symmetry in H1. apply Hlp in H1.
        rewrite step_equiv in H0. rewrite H' in H0. discriminate. assumption.
    + reflexivity.
    + destruct H0.
      - destruct H0. destruct H4. subst. rewrite <- Nat.eqb_neq in H4.
        rewrite H4. destruct b; simpl; reflexivity.
      - destruct H0. destruct H4. subst. destruct flag.
        ** destruct (gset_elem_of_dec source links) eqn:H'.
           ++ contradiction.
           ++ rewrite <- Nat.eqb_neq in H5. rewrite H5. reflexivity.
        ** rewrite <- Nat.eqb_neq in H5. rewrite H5.
           destruct (reason =ᵥ VLit "normal"%string); try reflexivity.
           destruct (gset_elem_of_dec source links) eqn:H'; try reflexivity.
           contradiction.
    + destruct H0.
      - destruct H0. destruct H4. destruct flag; rewrite H4.
        ** rewrite H0. simpl. rewrite H5. reflexivity.
        ** destruct (dest =? source); rewrite H5, H0; simpl; reflexivity.
      - destruct H0; destruct H0; rewrite H0.
        ** destruct H4, H5, H6. destruct (dest =? source); destruct b.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- destruct (gset_elem_of_dec source links) eqn:H''. rewrite H5. reflexivity.
                 specialize (H6 eq_refl). congruence.
           ++ destruct (reason =ᵥ VLit "kill"%string) eqn:H'; try rewrite H5; try reflexivity.
              specialize (H7 eq_refl).
              clear -H7 H'. apply VLit_val_eq in H'. congruence.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- specialize (H6 eq_refl).
                 destruct (gset_elem_of_dec source links) eqn:H''; try congruence.
                 rewrite H5. reflexivity.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- specialize (H7 eq_refl). clear H'. destruct (reason =ᵥ VLit "kill"%string) eqn:H';
                 try rewrite H5; try reflexivity.
                 clear -H7 H'. apply VLit_val_eq in H'. congruence.
        ** destruct H4, H5. symmetry in H5. rewrite <- Nat.eqb_eq in H5. rewrite H5.
           rewrite H4. simpl. subst. destruct b; reflexivity.
    + destruct H0; destruct H0; rewrite H0.
      ** destruct (reason =ᵥ VLit "kill"%string) eqn:H'; try reflexivity.
         clear -H4 H'. apply VLit_val_eq in H'. congruence.
      ** destruct (gset_elem_of_dec source links) eqn:H'. reflexivity. congruence.
    + reflexivity.
    + reflexivity.
    + destruct (Val_eqb_strict v v && (ι =? ι)) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'.
        rewrite Val_eqb_strict_refl in H'. congruence.
    + destruct (Val_eqb_strict v v && (ι =? ι)) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'. 
        rewrite Val_eqb_strict_refl in H'. congruence.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (links !! ι) eqn:H'; try discriminate.
      destruct (Val_eqb_strict v reason) eqn:H''.
      reflexivity.
      inversion H1. rewrite H6 in H''. rewrite Val_eqb_strict_refl in H''. congruence.
    + reflexivity.
    + unfold processLocalStepASpawn. destruct (len l); try discriminate.
      inversion H0. rewrite Nat.eqb_refl.
      unfold plsASpawnSpawn.
      destruct (Val_eqb_strict (VClos ext id n e) (VClos ext id n e) 
                  && Val_eqb_strict l l) eqn:H'.
      reflexivity. apply andb_false_iff in H'. destruct H'.
      rewrite Val_eqb_strict_refl in H4. congruence.
      rewrite Val_eqb_strict_refl in H4. congruence.
    + unfold processLocalStepASpawn. destruct (len l); try discriminate.
      inversion H0. rewrite Nat.eqb_refl.
      unfold plsASpawnSpawnLink.
      destruct (Val_eqb_strict (VClos ext id n e) (VClos ext id n e) 
                  && Val_eqb_strict l l) eqn:H'.
      reflexivity. apply andb_false_iff in H'. destruct H'.
      rewrite Val_eqb_strict_refl in H4. congruence.
      rewrite Val_eqb_strict_refl in H4. congruence.
    + destruct mb. destruct l0 eqn:H'; simpl. unfold peekMessage in H0. discriminate.
      unfold peekMessage in H0. inversion H0. reflexivity.
    + destruct mb. destruct l0 eqn:H'; simpl. reflexivity.
      unfold peekMessage in H0. discriminate.
    + destruct mb. destruct l0 eqn:H'; simpl. unfold recvNext in H0. discriminate.
      unfold recvNext in H0. inversion H0. reflexivity.
    + destruct mb. destruct l0 eqn:H'. unfold removeMessage in H0. discriminate.
      unfold removeMessage in H0. unfold removeMessage. inversion H0. reflexivity.
    + reflexivity.
    + reflexivity.
    + destruct v eqn:H'; try auto. destruct l eqn:H''.
      - do 8 (destruct s; try reflexivity; destruct a0; 
        destruct b; try reflexivity;
        destruct b0; try reflexivity;
        destruct b1; try reflexivity;
        destruct b2; try reflexivity;
        destruct b3; try reflexivity;
        destruct b4; try reflexivity;
        destruct b5; try reflexivity;
        destruct b6; try reflexivity).
        destruct s; try reflexivity. congruence.
      - destruct x eqn:H'''; try reflexivity. congruence.
    + destruct (bool_from_lit v) eqn:H'; try discriminate. inversion H0. reflexivity.
    + destruct (bool_from_lit v) eqn:H'; try discriminate. inversion H0. reflexivity.
    + reflexivity.
    + reflexivity.
  * unfold processLocalStepFunc in H.
    destruct a.
    + unfold processLocalStepASend in H.
      destruct t eqn:Ht.
      - destruct p; try discriminate. destruct p, p, p, p. destruct f; try discriminate.
        destruct f; try discriminate. destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate.
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct v; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate. destruct vs; try discriminate.
        destruct vs; try discriminate.
        destruct (Val_eqb_strict v e && (p =? receiver)) eqn:H'; try discriminate.
        symmetry in H'. apply andb_true_eq in H'. destruct H'.
        symmetry in H1. apply Nat.eqb_eq in H1. rewrite <- H1.
        symmetry in H0. apply Val_eqb_strict_eq in H0. rewrite H0.
        inversion H. constructor.
        specialize 
          (Hlp (FParams (ICall (VLit "erlang"%string) (VLit "!"%string)) [VPid p] [] :: f0)
          (RValSeq [v]) m g p0).
        rewrite H0 in Hlp. clear -Hlp.
        pose proof (Hlp eq_refl) as Hlp. inv Hlp. inv H0. assumption.
      - unfold plsASendSExit in H. destruct b.
        ** destruct p; try discriminate. destruct (d !! receiver) eqn:H'; try discriminate.
           destruct (Val_eqb_strict v r) eqn:H''; try discriminate.
           inversion H.
           apply Val_eqb_strict_eq in H''. rewrite H'' in H'.
           constructor; try assumption. admit.
        ** destruct p; try discriminate. destruct p, p, p, p. destruct f; try discriminate.
           destruct f; try discriminate. destruct ident; try discriminate.
           destruct m0; try discriminate. destruct l; try discriminate.
           do 6 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate. destruct f; try discriminate. destruct l;
           try discriminate.
           do 4 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate. destruct vl; try discriminate.
           destruct v; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r0; try discriminate.
           destruct vs; try discriminate. destruct vs; try discriminate.
           destruct (Val_eqb_strict v r && (p =? receiver)) eqn:H'; try discriminate.
           symmetry in H'. apply andb_true_eq in H'. destruct H'.
           symmetry in H1. apply Nat.eqb_eq in H1. rewrite <- H1.
           symmetry in H0. apply Val_eqb_strict_eq in H0. rewrite H0.
           inversion H. constructor.
           pose proof (Hlp _ _ _ _ _ eq_refl) as Hlp.
           inv Hlp. inv H4. assumption.
      - destruct p; try discriminate. destruct p, p, p, p. destruct f; try discriminate.
        destruct f; try discriminate. destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 4 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate.
        destruct r; try discriminate. destruct vs; try discriminate.
        destruct v; try discriminate. destruct vs; try discriminate.
        destruct (p =? receiver) eqn:H'; try discriminate. inversion H.
        apply Nat.eqb_eq in H'. rewrite H'. constructor.
      - destruct p; try discriminate. destruct p, p, p, p.
        destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate. destruct m0; try discriminate.
        destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct v; try discriminate. destruct vs; try discriminate.
        destruct (p =? receiver) eqn:H'; try discriminate. inversion H.
        apply Nat.eqb_eq in H'. rewrite H'. constructor.
    + unfold processLocalStepAArrive in H. destruct t.
      - destruct p; try discriminate. destruct p, p, p, p. inversion H. constructor.
      - unfold plsAArriveSExit in H. destruct p; try discriminate.
        destruct p, p, p, p.
        rename p0 into flag. rename sender into source. rename receiver into dest.
        destruct flag eqn:H'.
        ** destruct b eqn:H''.
           ++ destruct (gset_elem_of_dec source g) eqn:H'''.
              -- inversion H. constructor. right. split; try reflexivity.
                 assumption.
              -- destruct (dest =? source) eqn:H''''; try discriminate. inversion H.
                 constructor. right.
                 split. assumption.
                 split. reflexivity. apply Nat.eqb_neq in H''''. assumption.
           ++ destruct (r =ᵥ VLit "kill"%string) eqn:H'''.
              -- inversion H. constructor. left.
                 split. apply VLit_val_eq in H'''. assumption.
                 split; reflexivity.
              -- inversion H. constructor. left.
                 split. reflexivity.
                 apply VLit_val_neq in H'''. assumption.
        ** destruct (dest =? source) eqn:H''.
           ++ destruct b eqn:H'''.
              -- destruct (r =ᵥ VLit "normal"%string) eqn:H''''.
                 *** inversion H. constructor. right. right.
                     split. reflexivity.
                     split. apply VLit_val_eq in H''''. assumption.
                     split. rewrite Nat.eqb_eq in H''. symmetry. assumption.
                     apply VLit_val_eq in H''''. symmetry. assumption.
                 *** destruct (gset_elem_of_dec source g) eqn:H'''''; try discriminate.
                     inversion H. constructor. right. left.
                     split. reflexivity.
                     split. apply VLit_val_neq in H''''. assumption.
                     split. reflexivity.
                     split. intro. assumption.
                     intro. discriminate.
              -- destruct (r =ᵥ VLit "kill"%string) eqn:H''''.
                 *** inversion H. constructor. left.
                     split. apply VLit_val_eq in H''''. assumption.
                     split; reflexivity.
                 *** destruct (r =ᵥ VLit "normal"%string) eqn:H'''''.
                     +++ inversion H. constructor. right. right.
                         split. reflexivity.
                         split. apply VLit_val_eq in H'''''. assumption.
                         split. apply Nat.eqb_eq in H''. symmetry. assumption.
                         reflexivity.
                     +++ inversion H. constructor. right. left.
                         split. reflexivity.
                         split. apply VLit_val_neq in H'''''. assumption.
                         split. reflexivity.
                         split. intro. discriminate.
                         intro. apply VLit_val_neq in H''''. assumption.
           ++ destruct b eqn:H'''.
              -- destruct (r =ᵥ VLit "normal"%string) eqn:H''''.
                 *** inversion H. constructor. left.
                     split. apply VLit_val_eq in H''''. assumption.
                     split. apply Nat.eqb_neq in H''. assumption.
                     reflexivity.
                 *** destruct (gset_elem_of_dec source g) eqn:H'''''.
                     +++ inversion H. constructor. right. left.
                         split. reflexivity.
                         split. apply VLit_val_neq in H''''. assumption.
                         split. reflexivity.
                         split. intro. assumption.
                         intro. discriminate.
                     +++ inversion H. constructor. right.
                         split. assumption.
                         split. reflexivity.
                         apply Nat.eqb_neq in H''. assumption.
              -- destruct (r =ᵥ VLit "normal"%string) eqn:H''''.
                 *** inversion H. constructor. left.
                     split. apply VLit_val_eq in H''''. assumption.
                     split. apply Nat.eqb_neq in H''. assumption.
                     reflexivity.
                 *** destruct (r =ᵥ VLit "kill"%string) eqn:H'''''.
                     +++ inversion H. constructor. left.
                         split. apply VLit_val_eq in H'''''. assumption.
                         split; reflexivity.
                     +++ inversion H. constructor. right. left.
                         split. reflexivity.
                         split. apply VLit_val_neq in H''''. assumption.
                         split. reflexivity.
                         split. intro. discriminate.
                         intro. apply VLit_val_neq in H'''''. assumption.
      - destruct p; try discriminate. destruct p, p, p, p. inversion H. constructor.
      - destruct p; try discriminate. destruct p, p, p, p. inversion H. constructor.
    + unfold processLocalStepASelf in H. destruct p; try discriminate. destruct p, p, p, p.
      destruct f; try discriminate. destruct f; try discriminate.
      destruct ident; try discriminate. destruct m0; try discriminate.
      destruct l; try discriminate.
      do 6 (destruct s; try discriminate;
      destruct a; try discriminate;
      destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
      destruct s; try discriminate.
      destruct f; try discriminate. destruct l; try discriminate.
      do 4 (destruct s; try discriminate;
      destruct a; try discriminate;
      destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
      destruct s; try discriminate.
      destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
      inversion H. constructor.
    + destruct t1; try discriminate. unfold processLocalStepASpawn in H.
      destruct (len t2) eqn:H''''; try discriminate.
      destruct (n =? params) eqn:H'; try discriminate.
      rename link into link_flag. destruct link_flag eqn:H''.
      - unfold plsASpawnSpawnLink in H. destruct p; try discriminate.
        destruct p, p, p, p. destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate. destruct m0; try discriminate.
        destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 10 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate. destruct vs; try discriminate.
        destruct vs; try discriminate.
        destruct (Val_eqb_strict v (VClos ext id params e) && Val_eqb_strict v0 t2) eqn:H''';
        try discriminate.
        inversion H. rewrite Nat.eqb_eq in H'. rewrite <- H'.
        apply andb_true_iff in H'''. destruct H'''.
        apply Val_eqb_strict_eq in H0. rewrite H0.
        apply Val_eqb_strict_eq in H2. rewrite H2.
        rewrite <- H'. constructor. symmetry. assumption.
      - unfold plsASpawnSpawn in H. destruct p; try discriminate. destruct p, p, p, p.
        destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 5 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (Val_eqb_strict v (VClos ext id params e) && Val_eqb_strict v0 t2) eqn:H''';
        try discriminate.
        inversion H. rewrite Nat.eqb_eq in H'. rewrite <- H'.
        apply andb_true_iff in H'''. destruct H'''.
        apply Val_eqb_strict_eq in H0. rewrite H0.
        apply Val_eqb_strict_eq in H2. rewrite H2.
        rewrite <- H'. constructor. symmetry. assumption.
    + unfold processLocalStepTau in H. destruct p; try discriminate. destruct p, p, p, p.
      pose proof (Hlp _ _ _ _ _ eq_refl) as Hlp.
      destruct (step_func f r) eqn:H'.
      destruct p. inversion H. constructor. apply step_equiv in H'; try assumption. clear H'.
      destruct f; try discriminate. destruct f; try discriminate.
      destruct ident; try discriminate.
      - destruct m0; try discriminate. destruct l; try discriminate.
        do 6 (destruct s; try discriminate; 
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate.
        do 12 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct v; try discriminate. destruct l; try discriminate.
        do 9 (destruct s; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        destruct s; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (bool_from_lit v) eqn:H''; try discriminate. inversion H.
        apply p_set_flag_exc. symmetry. assumption.
      - do 9 (destruct f; try discriminate;
        destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
        ** do 8 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct vs; try discriminate. destruct vs; try discriminate.
           destruct v; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate).
           destruct l eqn:H'.
           ++ clear H1.
              do 8
              (destruct s; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct a; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b0; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b1; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b2; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b3; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b4; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b5; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              destruct b6; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate);
              clear H1 H2 H3 H4 H5 H6 H7 H8 H9 H10).
              destruct s; inversion H; try (apply p_recv_wait_timeout_invalid; discriminate).
              destruct m. destruct l1; try discriminate.
              inversion H. apply p_recv_wait_timeout_new_message.
           ++ destruct x.
              -- inversion H. apply p_recv_wait_timeout_0.
              -- inversion H. apply p_recv_wait_timeout_invalid; discriminate.
              -- inversion H. apply p_recv_wait_timeout_invalid; discriminate.
        ** destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct (recvNext m) eqn:H''; try discriminate.
           inversion H. constructor. assumption.
        ** do 8 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct (peekMessage m) eqn:H'; try discriminate.
           inversion H. apply p_recv_peek_message_ok. assumption.
        ** do 5 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate. destruct vl; try discriminate.
           destruct el; try discriminate. destruct r; try discriminate.
           destruct (removeMessage m) eqn:H'; try discriminate.
           inversion H. constructor. assumption.
    + unfold processLocalStepEps in H. destruct p; try discriminate. destruct p, p, p, p.
      destruct f.
      - destruct r; try discriminate.
        ** destruct vs; try discriminate. destruct vs; try discriminate.
           inversion H. constructor.
        ** inversion H. constructor.
      - destruct f; try discriminate. destruct el; try discriminate.
        destruct ident; try discriminate.
        ** destruct m0; try discriminate.
           destruct l; try discriminate.
           do 6 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate.
           destruct f; try discriminate. destruct l; try discriminate.
           do 12 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate.
           destruct vl; try discriminate. destruct v; try discriminate.
           destruct l; try discriminate.
           do 9 (destruct s; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct s; try discriminate.
           destruct vl; try discriminate. destruct r; try discriminate.
           destruct vs; try discriminate. destruct vs; try discriminate.
           destruct (bool_from_lit v) eqn:H'; try discriminate.
           inversion H. constructor. symmetry. assumption.
        ** do 17 (destruct f; try discriminate;
           destruct a; try discriminate;
           destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
           destruct f; try discriminate.
           destruct vl; try discriminate. destruct r; try discriminate.
           inversion H. destruct (peekMessage m) eqn:H'; try discriminate.
           inversion H. constructor. assumption.
Admitted.