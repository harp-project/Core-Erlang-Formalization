From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang.Concurrent Require Export ProcessSemantics.
From CoreErlang.Interpreter Require Export EqualityFunctions.
From CoreErlang.Interpreter Require Import StepFunctions.

Theorem step_func_closedness: forall fs e, FSCLOSED fs -> REDCLOSED e -> forall fs' e',
    step_func fs e = Some (fs', e') -> FSCLOSED fs' /\ REDCLOSED e'.
Proof.
  intros. destruct e.
  * destruct e.
    + simpl in H1. inv H1. split; try assumption. inv H0. inv H2. constructor.
      constructor. assumption. constructor.
    + destruct e; simpl in H1; inv H1.
      - split; try assumption. inv H0. inv H2. inv H3. constructor. constructor. scope_solver.
        constructor.
      - split;[|constructor]. constructor.
        ** constructor. scope_solver. constructor.
           ++ inv H0. inv H2. inv H3. induction el; constructor.
              -- specialize (H2 0). simpl in H2. apply H2. apply Nat.lt_0_succ.
              -- apply IHel. intros. specialize (H2 (S i)).
                 simpl in H2. apply H2. apply Nat.succ_lt_mono in H0. assumption.
           ++ discriminate.
        ** inv H. constructor. constructor; assumption.
      - split. scope_solver.
        ** inv H0. inv H2. inv H3. assumption.
        ** inv H; constructor; assumption.
        ** inv H0. inv H2. inv H3. constructor. assumption.
      - split;[|constructor]. constructor.
        ** inv H0. inv H2. inv H3. constructor; try constructor.
           ++ clear -H2. induction l. constructor.
              constructor. specialize (H2 0). simpl in H2.
              specialize (H2 (Nat.lt_0_succ _)). assumption.
              apply IHl. simpl in H2. intros.
              specialize (H2 (S i)). simpl in H2. apply H2.
              apply Nat.succ_lt_mono in H. assumption.
           ++ discriminate.
        ** inv H; constructor; assumption.
      - split.
        ** inv H0. inv H2. inv H4. destruct l eqn:H'.
           ++ inv H3. assumption.
           ++ destruct p. inv H3. constructor.
              -- scope_solver.
                 *** specialize (H5 0). simpl in H5. apply H5. apply Nat.lt_0_succ.
                 *** induction l0. constructor.
                     simpl. destruct a.
                     constructor. specialize (H1 1). simpl in H1. apply H1.
                     assert (0 < S (base.length l0) -> 1 < S (S (base.length l0))).
                     { intros. apply Nat.succ_lt_mono in H0. assumption. }
                     apply H0. apply Nat.lt_0_succ.
                     constructor. specialize (H5 1). simpl in H5. apply H5.
                     assert (0 < S (base.length l0) -> 1 < S (S (base.length l0))).
                     { intros. apply Nat.succ_lt_mono in H0. assumption. }
                     apply H0. apply Nat.lt_0_succ.
                     apply IHl0; intros.
                     +++ induction i.
                         --- simpl. specialize (H1 0). simpl in H1. apply H1.
                             apply Nat.lt_0_succ.
                         --- simpl. simpl in H0. specialize (H1 (S (S i))). simpl in H1.
                             apply H1. apply -> Nat.succ_lt_mono in H0. assumption.
                     +++ induction i.
                         --- simpl. specialize (H5 0). simpl in H5. apply H5.
                             apply Nat.lt_0_succ.
                         --- simpl. simpl in H0. specialize (H5 (S (S i))). simpl in H5.
                             apply H5. apply -> Nat.succ_lt_mono in H0. assumption.
                 *** intros. clear. induction l0. exists 0. reflexivity.
                     destruct a. simpl. destruct IHl0. exists (S x). simpl.
                     do 2 f_equal. rewrite H. rewrite Nat.add_0_r.
                     rewrite Nat.add_succ_r. reflexivity.
              -- inv H; constructor; assumption.
        ** inv H0. inv H2. inv H4. destruct l eqn:H'.
           ++ inv H3. scope_solver.
           ++ destruct p. inv H3.
              specialize (H1 0). simpl in H1. constructor. apply H1. apply Nat.lt_0_succ.
      - scope_solver.
        ** inv H0. inv H2. inv H3. assumption.
        ** inv H0. inv H2. inv H3. induction l; constructor.
           ++ specialize (H5 0). simpl in H5. apply H5. apply Nat.lt_0_succ.
           ++ apply IHl. intros. specialize (H5 (S i)). simpl in H5. apply H5.
              apply Nat.succ_lt_mono in H0. assumption.
        ** inv H; constructor; assumption.
        ** inv H0. inv H2. inv H3. assumption.
      - scope_solver.
        ** inv H0. inv H2. inv H3. induction l; constructor.
           ++ specialize (H2 0). simpl in H2. apply H2. apply Nat.lt_0_succ.
           ++ apply IHl. intros. specialize (H2 (S i)). simpl in H2. apply H2.
              apply Nat.succ_lt_mono in H0. assumption.
        ** discriminate.
        ** inv H; constructor; assumption.
      - scope_solver.
        ** inv H0. inv H2. inv H3. induction l; constructor.
           ++ specialize (H5 0). simpl in H5. apply H5. apply Nat.lt_0_succ.
           ++ apply IHl. intros. specialize (H5 (S i)). simpl in H5. apply H5.
              apply Nat.succ_lt_mono in H0. assumption.
        ** inv H; constructor; assumption.
        ** inv H0. inv H2. inv H3. assumption.
      - scope_solver.
        ** inv H0. inv H2. inv H3. induction l; constructor.
           ++ destruct a, p. split.
              -- specialize (H5 0). simpl in H5. rewrite Nat.add_0_r in H5. 
                 apply H5. apply Nat.lt_0_succ.
              -- specialize (H6 0). simpl in H6. rewrite Nat.add_0_r in H6. 
                 apply H6. apply Nat.lt_0_succ.
           ++ apply IHl.
              -- intros.
                 specialize (H5 (S i)). simpl in H5. apply H5.
                 apply Nat.succ_lt_mono in H0. assumption.
              -- intros.
                 specialize (H6 (S i)). simpl in H6. apply H6.
                 apply Nat.succ_lt_mono in H0. assumption.
        ** inv H; constructor; assumption.
        ** inv H0. inv H2. inv H3. assumption.
      - scope_solver.
        ** inv H0. inv H2. inv H3. rewrite Nat.add_0_r in H6. assumption.
        ** inv H; constructor; assumption.
        ** inv H0. inv H2. inv H3. assumption.
      - scope_solver.
        ** inv H0. inv H2. inv H3. assumption.
        ** inv H; constructor; assumption.
        ** inv H0. inv H2. inv H3. assumption.
      - scope_solver; try assumption.
        inv H0. inv H2. inv H3. admit. 
      - scope_solver; try assumption.
        ** inv H0. inv H2. inv H3. rewrite Nat.add_0_r in H8. assumption.
        ** inv H0. inv H2. inv H3. rewrite Nat.add_0_r in H9. assumption.
        ** inv H0. inv H2. inv H3. assumption.
  * destruct fs; try discriminate.
    destruct f; simpl in H1.
    + destruct vs; try discriminate. destruct vs; try discriminate.
      inv H1. scope_solver.
      - inv H0. inv H2. assumption.
      - inv H. assumption.
      - inv H. inv H3. assumption.
    + destruct vs; try discriminate. destruct vs; try discriminate.
      inv H1. scope_solver.
      - inv H. inv H4; constructor; assumption.
      - inv H0. inv H2. assumption.
      - inv H. inv H3. assumption.
    + destruct el.
      - destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (create_result ident (vl ++ [v])) eqn:H'; try discriminate.
        destruct p. inv H1. unfold create_result in H'.
        destruct ident; inv H'.
        ** scope_solver.
           ++ inv H. inv H3. inv H4; constructor; assumption.
           ++ induction vl; simpl.
              constructor.
              inv H0. inv H2. assumption. constructor. constructor.
              inv H. inv H3. inv H6. assumption. 
              apply IHvl. inv H. constructor.
              -- scope_solver.
                 *** inv H3. inv H6. assumption.
                 *** discriminate.
              -- inv H4; constructor; assumption.
        ** inv H. inv H3.
           split. inv H4; constructor; assumption.
           constructor. constructor; try constructor.
           intros. clear H8 H7 H5. induction vl.
           ++ induction i.
              -- simpl. inv H0. inv H2. assumption.
              -- simpl in H. apply Nat.succ_lt_mono in H. inv H.
           ++ destruct i.
              -- simpl. inv H6. assumption. 
              -- simpl. admit.
        ** admit.
        ** admit.
        ** unfold primop_eval in H2. destruct (convert_primop_to_code f) eqn:H'; try discriminate.
           ++ destruct (eval_primop_error f (vl ++ [v])) eqn:H''; try discriminate.
              inv H2. unfold eval_primop_error in H''. rewrite H' in H''.
              destruct vl; try discriminate.
              -- simpl in H''. inv H''. inv H0. inv H2. scope_solver.
                 inv H. inv H5; constructor; assumption.
              -- simpl in H''. destruct vl; simpl in H''; discriminate.
           ++ destruct (eval_primop_error f (vl ++ [v])) eqn:H''; try discriminate.
              inv H2. unfold eval_primop_error in H''. rewrite H' in H''.
              destruct vl; try discriminate. simpl in H''. destruct vl.
              -- simpl in H''. inv H''. inv H0. inv H2. inv H. inv H2. inv H7. scope_solver.
                 inv H5; constructor; assumption.
              -- simpl in H''. destruct vl; discriminate.
           ++ unfold convert_primop_to_code in H'. destruct f.
              -- inv H2. scope_solver. inv H. inv H4; constructor; assumption.
              -- admit.
        ** admit.
      - destruct vs; try discriminate. destruct vs; try discriminate. inv H1.
        split.
        ** constructor.
           ++ constructor.
              -- destruct ident; constructor; inv H; inv H3; inv H5; assumption.
              -- inv H. inv H3. inv H6.
                 *** simpl. constructor; inv H0; inv H1; assumption.
                 *** simpl. admit.
              -- admit.
              -- admit.
           ++ inv H. assumption.
        ** inv H. inv H3. inv H7. constructor. assumption.
    + destruct vs; try discriminate. destruct vs; try discriminate. inv H1. scope_solver.
      - inv H0. inv H2. assumption.
      - inv H. inv H3. assumption.
      - discriminate.
      - inv H. inv H3. assumption.
    + destruct vs; try discriminate. destruct vs; try discriminate. inv H1.
      inv H0. inv H2. inv H. inv H2. scope_solver; assumption.
    + destruct vs; try discriminate. destruct vs; try discriminate. inv H1.
      inv H. inv H3. inv H0. inv H1. scope_solver; try assumption. discriminate.
    + destruct l.
      - inv H1. scope_solver. inv H. inv H4; constructor; assumption.
      - destruct p, p. destruct (match_pattern_list l0 vs) eqn:H'.
        ** inv H1. admit.
        ** inv H1. admit.
    + destruct vs; try discriminate. destruct v; try discriminate. destruct l; try discriminate.
      
      do 4 (destruct s; try discriminate; destruct a; try discriminate;
      destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate).
      - destruct s; try discriminate; destruct a; try discriminate;
        destruct b, b0, b1, b2, b3, b4, b5, b6; try discriminate.
        destruct s; try discriminate.
        destruct vs; try discriminate. inv H1.
        scope_solver.
        ** inv H. inv H3. assumption.
        ** inv H. assumption.
        ** inv H. inv H3. inv H5. scope_solver. scope_solver. assumption.
      - destruct s; try discriminate. destruct vs; try discriminate. inv H1.
        inv H. inv H3. scope_solver.
        inv H4; constructor; assumption.
    + destruct (base.length vs =? l) eqn:H'; try discriminate.
      inv H1. split.
      - inv H. inv H4; constructor; assumption.
      - admit.
    + destruct vs; try discriminate. destruct vs; try discriminate. inv H1.
      inv H. inv H3. scope_solver. inv H4; constructor; assumption.
    + destruct (vl1 =? base.length vs) eqn:H'; try discriminate. inv H1. split.
      - inv H. inv H4; constructor; assumption.
      - admit.
  * destruct e. destruct p. simpl in H1.
    destruct fs; try discriminate. destruct f; try discriminate.
    + destruct (isPropagatable (FCons1 hd)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FCons2 tl)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FParams ident vl el)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FApp1 l)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FCallMod f l) ); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FCallFun m l)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FCase1 l)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FCase2 lv ex le)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FLet l e0)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + destruct (isPropagatable (FSeq e0)); try discriminate.
      inv H1. inv H0. scope_solver. inv H. inv H3; constructor; assumption.
    + do 4 (destruct vl2; try discriminate). inv H1.
      inv H0. scope_solver.
      inv H. inv H3; constructor; assumption.
      unfold exclass_to_value. destruct e; admit.
  * simpl in H1. destruct fs; try discriminate.
    destruct f; try discriminate. destruct el; try discriminate.
    + destruct ident; try discriminate.
      - destruct (create_result IValues vl) eqn:H'; try discriminate.
        destruct p. inv H1. unfold create_result in H'. inv H'.
        inv H. inv H3. scope_solver.
        inv H4; constructor; assumption.
      - destruct (create_result ITuple vl) eqn:H'; try discriminate.
        destruct p. inv H1. unfold create_result in H'. inv H'.
        inv H. inv H3. split.
        inv H4; constructor; assumption.
        constructor. constructor.
        admit. admit.
      - admit.
      - destruct (create_result (IPrimOp f) vl) eqn:H'; try discriminate.
        destruct p. inv H1. unfold create_result in H'. unfold primop_eval in H'.
        admit.
      - destruct (create_result (IApp v) vl) eqn:H'; try discriminate.
        destruct p. inv H1. unfold create_result in H'. admit.
    + destruct ident; try discriminate.
      - inv H1. inv H. inv H3. inv H7. scope_solver; try assumption. discriminate.
      - inv H1. inv H. inv H3. inv H7. scope_solver; try assumption. discriminate.
      - inv H1. inv H. inv H3. inv H5. inv H7. scope_solver; try assumption. discriminate.
      - inv H1. inv H. inv H3. inv H7. scope_solver; try assumption. discriminate.
      - inv H1. inv H. inv H3. inv H5. inv H7. scope_solver; try assumption. discriminate.
Admitted.

Theorem step_equiv: forall fs fs' e e', FSCLOSED fs -> REDCLOSED e ->
    ⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩ <-> step_func fs e = Some (fs', e').
Proof.
  intros fs fs' e e' HH HH0. split.
  * intro. inversion H; try auto; unfold step_func.
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
      - simpl in H. inv H. constructor. inv HH0. inv H0. assumption.
      - simpl in H. destruct e; try (inv H; constructor); try reflexivity.
        destruct l eqn:Hl.
        ** inv H. constructor.
        ** destruct p. inv H. constructor.
    + simpl in H. destruct fs; try discriminate.
      destruct f; destruct vs; try discriminate.
      - destruct vs. inv H. constructor. discriminate.
      - destruct vs. inv H. constructor. discriminate.
      - destruct el; discriminate.
      - destruct el.
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
        do 4 (destruct s; try discriminate; destruct a; try discriminate;
        destruct b; try discriminate; destruct b0; try discriminate;
        destruct b1; try discriminate; destruct b2; try discriminate;
        destruct b3; try discriminate; destruct b4; try discriminate;
        destruct b5; try discriminate; destruct b6; try discriminate).
        ** destruct s; try discriminate; destruct a; try discriminate;
           destruct b; try discriminate; destruct b0; try discriminate;
           destruct b1; try discriminate; destruct b2; try discriminate;
           destruct b3; try discriminate; destruct b4; try discriminate;
           destruct b5; try discriminate; destruct b6; try discriminate.
           destruct s; try discriminate. destruct vs; try discriminate.
           inv H. constructor.
        ** destruct s; try discriminate. destruct vs; try discriminate.
           inv H. constructor.
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
              destruct l.
              -- destruct (eval s s0 vl) eqn:H'; try discriminate. destruct p. inv H1.
                 apply eval_cool_params_0 with (l := o). discriminate.
                 simpl. rewrite H'. reflexivity.
              -- inv H1. apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
           ++ inv H0. apply eval_cool_params_0 with (l := None). discriminate. reflexivity.
        ** destruct (primop_eval f vl) eqn:H'; try discriminate. destruct p. inv H1.
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

Print Process.
Print LiveProcess.
Print DeadProcess.
Print Mailbox.
Print In.

Theorem processLocalStepEquiv': forall p p' a,
  (forall fs e mb links flag, p = inl (fs, e, mb, links, flag) ->
    FSCLOSED fs -> REDCLOSED e -> 
    forall (mb1 mb2 : list Val), mb = (mb1, mb2) ->
    (forall mb1v, In mb1v mb1 -> VALCLOSED mb1v) ->
    (forall mb2v, In mb2v mb2 -> VALCLOSED mb2v) ->
      inl (fs, e, mb, links, flag) -⌈ a ⌉-> p' <-> processLocalStepFunc p a = Some p')
  /\
  (forall pidmap, p = inr pidmap ->
    inr pidmap -⌈ a ⌉-> p' <-> processLocalStepFunc p a = Some p'). Admitted.

Theorem processLocalStepEquiv: forall p p' a, (* If p is liveProcess *)
  p -⌈ a ⌉-> p' <-> processLocalStepFunc p a = Some p'.
Proof.
  (* intros. split; intro.
  * inversion H; simpl.
    + destruct (step_func fs e) eqn:H'.
      - destruct p0. rewrite step_equiv in H0. rewrite H' in H0. inversion H0. reflexivity. admit. admit.
      - rewrite step_equiv in H0. rewrite H' in H0. discriminate. admit. admit.
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
    + destruct (bool_decide (v = v) && (ι =? ι)) eqn:H'.
      - destruct (valclosed_func v) eqn:H''; try reflexivity.
        apply valclosed_equiv in H0. rewrite H0 in H''. discriminate.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'. 
        apply bool_decide_eq_false_1 in H'. congruence.
    + destruct (bool_decide (v = v) && (ι =? ι)) eqn:H'.
      - destruct (valclosed_func v) eqn:H''; try reflexivity.
        apply valclosed_equiv in H0. rewrite H0 in H''. discriminate.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'. 
        apply bool_decide_eq_false_1 in H'. congruence.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (links !! ι) eqn:H'; try discriminate.
      destruct (bool_decide (v = reason)) eqn:H''.
      destruct (valclosed_func reason) eqn:H'''; try reflexivity.
      apply valclosed_equiv in H0. rewrite H0 in H'''. discriminate.
      inversion H1. rewrite H6 in H''. apply bool_decide_eq_false_1 in H''. congruence.
    + reflexivity.
    + unfold processLocalStepASpawn. destruct (len l); try discriminate.
      inversion H0. rewrite Nat.eqb_refl.
      unfold plsASpawnSpawn.
      destruct (bool_decide (VClos ext id n e = VClos ext id n e) && bool_decide (l = l)) eqn:H'.
      reflexivity. apply andb_false_iff in H'. destruct H'.
      apply bool_decide_eq_false_1 in H4. congruence.
      apply bool_decide_eq_false_1 in H4. congruence.
    + unfold processLocalStepASpawn. destruct (len l); try discriminate.
      inversion H0. rewrite Nat.eqb_refl.
      unfold plsASpawnSpawnLink.
      destruct (bool_decide (VClos ext id n e = VClos ext id n e) && bool_decide (l = l)) eqn:H'.
      reflexivity. apply andb_false_iff in H'. destruct H'.
      apply bool_decide_eq_false_1 in H4. congruence.
      apply bool_decide_eq_false_1 in H4. congruence.
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
      - destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
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
        destruct (bool_decide (v = e) && (p =? receiver)) eqn:H'; try discriminate.
        symmetry in H'. apply andb_true_eq in H'. destruct H'.
        symmetry in H1. apply Nat.eqb_eq in H1. rewrite <- H1.
        symmetry in H0. apply bool_decide_eq_true_1 in H0. rewrite H0.
        destruct (valclosed_func e) eqn:H'; try discriminate. inversion H. constructor.
        apply valclosed_equiv. assumption.
      - unfold plsASendSExit in H. destruct b.
        ** destruct p; try discriminate. destruct (d !! receiver) eqn:H'; try discriminate.
           destruct (bool_decide (v = r)) eqn:H''; try discriminate.
           destruct (valclosed_func r) eqn:H'''; try discriminate.
           inversion H. constructor. apply valclosed_equiv. assumption.
           rewrite H'. apply bool_decide_eq_true_1 in H''. rewrite H''. reflexivity.
        ** destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
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
           destruct (bool_decide (v = r) && (p =? receiver)) eqn:H'; try discriminate.
           symmetry in H'. apply andb_true_eq in H'. destruct H'.
           symmetry in H1. apply Nat.eqb_eq in H1. rewrite <- H1.
           symmetry in H0. apply bool_decide_eq_true_1 in H0. rewrite H0.
           destruct (valclosed_func r) eqn:H'; try discriminate. inversion H.
           constructor. apply valclosed_equiv. assumption.
      - destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
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
      - destruct p; try discriminate. destruct l, p, p, p.
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
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
      - unfold plsAArriveSExit in H. destruct p; try discriminate.
        destruct l, p, p, p.
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
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
    + unfold processLocalStepASelf in H. destruct p; try discriminate. destruct l, p, p, p.
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
        destruct l, p, p, p. destruct f; try discriminate. destruct f; try discriminate.
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
        destruct (bool_decide (v = VClos ext id params e) && bool_decide (v0 = t2)) eqn:H''';
        try discriminate.
        inversion H. rewrite Nat.eqb_eq in H'. rewrite <- H'.
        apply andb_true_iff in H'''. destruct H'''.
        apply bool_decide_eq_true_1 in H0. rewrite H0.
        apply bool_decide_eq_true_1 in H2. rewrite H2.
        rewrite <- H'. constructor. symmetry. assumption.
      - unfold plsASpawnSpawn in H. destruct p; try discriminate. destruct l, p, p, p.
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
        destruct (bool_decide (v = VClos ext id params e) && bool_decide (v0 = t2)) eqn:H''';
        try discriminate.
        inversion H. rewrite Nat.eqb_eq in H'. rewrite <- H'.
        apply andb_true_iff in H'''. destruct H'''.
        apply bool_decide_eq_true_1 in H0. rewrite H0.
        apply bool_decide_eq_true_1 in H2. rewrite H2.
        rewrite <- H'. constructor. symmetry. assumption.
    + unfold processLocalStepTau in H. destruct p; try discriminate. destruct l, p, p, p.
      destruct (step_func f r) eqn:H'.
      destruct p. inversion H. constructor. apply step_equiv in H'. assumption. clear H'.
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
    + unfold processLocalStepEps in H. destruct p; try discriminate. destruct l, p, p, p.
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
           inversion H. constructor. assumption. *)
Admitted.