From CoreErlang.FrameStack Require Export Frames SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Concurrent Require Export ProcessSemantics ClosednessLemmas.
From CoreErlang.Interpreter Require Export StepFunctions InterpreterAuxLemmas.
From CoreErlang Require Export StrictEqualities Equalities.
From stdpp Require Export option list.

Theorem sequentialStepEquiv: forall fs fs' e e', REDCLOSED e ->
    ⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩ <-> sequentialStepFunc fs e = Some (fs', e').
Proof.
  intros fs fs' e e' HH. split.
  * intro. inversion H; try auto; unfold sequentialStepFunc; try rewrite <- create_result_equiv.
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

Theorem processLocalStepEquiv: forall p p' a, PROCCLOSED p ->
  p -⌈ a ⌉-> p' <-> processLocalStepFunc p a = Some p'.
Proof.
  intros p p' a Hlp. split; intro.
  * inversion H; simpl.
    + destruct (sequentialStepFunc fs e) eqn:H'.
      - destruct p0.
        symmetry in H1. 
        unfold PROCCLOSED in Hlp. destruct p; try discriminate.
        destruct l, p, p, p, Hlp, H5.
        rewrite sequentialStepEquiv in H0. rewrite H' in H0. inv H0. reflexivity.
        inv H1. assumption.
      - symmetry in H1.
        rewrite sequentialStepEquiv in H0. rewrite H' in H0. discriminate.
        unfold PROCCLOSED in Hlp. destruct p; try discriminate.
        destruct l, p, p, p, Hlp, H5. inv H1. assumption.
    + reflexivity.
    + destruct H0.
      - destruct H0. destruct H4. subst. rewrite <- Nat.eqb_neq in H4.
        rewrite H4. destruct b; simpl; reflexivity.
      - destruct H0. destruct H4. subst. destruct flag.
        ** unfold pids_member.
           destruct (gset_elem_of_dec source links) eqn:H'.
           ++ contradiction.
           ++ rewrite <- Nat.eqb_neq in H5. rewrite H5. reflexivity.
        ** rewrite <- Nat.eqb_neq in H5. rewrite H5.
           destruct (reason =ᵥ VLit "normal"%string); try reflexivity.
           unfold pids_member.
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
              -- unfold pids_member.
                 destruct (gset_elem_of_dec source links) eqn:H''. rewrite H5. reflexivity.
                 specialize (H6 eq_refl). congruence.
           ++ destruct (reason =ᵥ VLit "kill"%string) eqn:H'; try rewrite H5; try reflexivity.
              specialize (H7 eq_refl).
              clear -H7 H'. apply VLit_val_eq in H'. congruence.
           ++ destruct (reason =ᵥ VLit "normal"%string) eqn:H'.
              -- clear -H4 H'. apply VLit_val_eq in H'. congruence.
              -- specialize (H6 eq_refl). unfold pids_member.
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
      ** unfold pids_member. destruct (gset_elem_of_dec source links) eqn:H'. reflexivity. congruence.
    + unfold pids_insert. do 4 f_equal. set_solver.
    + unfold pids_delete. reflexivity.
    + destruct (Val_eqb_strict v v && (ι =? ι)) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'.
        rewrite Val_eqb_strict_refl in H'. congruence.
    + destruct (Val_eqb_strict v v && (ι =? ι)) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. rewrite andb_true_r in H'. 
        rewrite Val_eqb_strict_refl in H'. congruence.
    + unfold pids_insert. destruct (ι =? ι) eqn:H'.
      - do 4 f_equal. set_solver.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + destruct (ι =? ι) eqn:H'.
      - reflexivity.
      - rewrite Nat.eqb_refl in H'. discriminate.
    + unfold dead_lookup.
      destruct (@lookup PID Val (@gmap PID numbers.Nat.eq_dec nat_countable Val)
      (@gmap_lookup PID numbers.Nat.eq_dec nat_countable Val) ι links) eqn:H''.
      assert (
        (@lookup PID Val DeadProcess (@gmap_lookup PID numbers.Nat.eq_dec nat_countable Val) ι links) =
        (@lookup PID Val (@gmap PID numbers.Nat.eq_dec nat_countable Val)
        (@gmap_lookup PID numbers.Nat.eq_dec nat_countable Val) ι links) 
      ) as Ha. { reflexivity. } rewrite Ha in H1. rewrite H'' in H1. clear H'' Ha.
      inversion H1. destruct (Val_eqb_strict reason reason) eqn:H'''.
      unfold dead_delete. reflexivity.
      rewrite Val_eqb_strict_refl in H'''. congruence.
      cbv in H1, H''. rewrite H'' in H1. clear H''. congruence.
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
      destruct ("erlang" =? "erlang")%string eqn:Hs.
      destruct ("spawn_link" =? "spawn_link")%string eqn:Hs'.
      destruct (Val_eqb_strict (VClos ext id n e) (VClos ext id n e) 
                  && Val_eqb_strict l l) eqn:H'. simpl.
      unfold pids_insert. do 4 f_equal. set_solver.
      do 2 rewrite Val_eqb_strict_refl in H'. simpl in H'. congruence.
      apply String.eqb_neq in Hs'. congruence.
      apply String.eqb_neq in Hs. congruence.
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
      - destruct (s =? "infinity")%string eqn:Hs.
        apply String.eqb_eq in Hs. rewrite Hs in H1. congruence. reflexivity.
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
        destruct f; try discriminate. destruct l; try discriminate. destruct vl; try discriminate.
        destruct v; try discriminate. destruct vl; try discriminate. destruct el; try discriminate.
        destruct r; try discriminate. destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
        apply String.eqb_eq in Herl. subst s. simpl in H.
        destruct (s0 =? "!")%string eqn:Hsend;[|congruence].
        apply String.eqb_eq in Hsend. subst s0.
        destruct (Val_eqb_strict v e) eqn:Hve;[|simpl in H; congruence].
        apply Val_eqb_strict_eq in Hve. subst v. simpl in H.
        destruct (p =? receiver) eqn:Hpr;[|congruence].
        apply Nat.eqb_eq in Hpr. subst p. inv H.
        constructor.
        simpl in Hlp. destruct Hlp, H0. inv H0. inv H3. assumption.
      - unfold plsASendSExit in H. destruct b.
        ** unfold dead_lookup in H.
           destruct p; try discriminate.
           destruct (@lookup PID Val (@gmap PID numbers.Nat.eq_dec nat_countable Val)
             (@gmap_lookup PID numbers.Nat.eq_dec nat_countable Val) receiver d) 
             eqn:Hlookup; try discriminate.
           destruct (Val_eqb_strict v r) eqn:Hvr;[|congruence].
           apply Val_eqb_strict_eq in Hvr. subst v.
           inv H. constructor.
           ++ simpl in Hlp.
              apply elem_of_map_to_list in Hlookup.
              apply Forall_forall with (x := (receiver, r)) in Hlp; assumption.
           ++ rewrite <- Hlookup. reflexivity.
        ** destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
           destruct f; try discriminate. destruct ident; try discriminate.
           destruct m0; try discriminate. destruct l; try discriminate.
           destruct f; try discriminate. destruct l; try discriminate. destruct vl; try discriminate.
           destruct v; try discriminate. destruct vl; try discriminate. destruct el; try discriminate.
           destruct r0; try discriminate. destruct vs; try discriminate. destruct vs; try discriminate.
           destruct (s =? "erlang")%string eqn:Herl;[|simpl in H;congruence].
           apply String.eqb_eq in Herl. subst s. simpl in H.
           destruct (s0 =? "exit")%string eqn:Hexit;[|simpl in H; congruence].
           apply String.eqb_eq in Hexit. subst s0. simpl in H.
           destruct (Val_eqb_strict v r) eqn:Hvr;[|simpl in H; congruence].
           apply Val_eqb_strict_eq in Hvr. subst v. simpl in H.
           destruct (p =? receiver) eqn:Hpr;[|congruence].
           apply Nat.eqb_eq in Hpr. subst p.
           inv H. constructor.
           simpl in Hlp.
           destruct Hlp, H0. inv H0. inv H3. assumption.
      - destruct p; try discriminate. destruct l, p, p, p. destruct f; try discriminate.
        destruct f; try discriminate. destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate.
        destruct f; try discriminate. destruct l; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate. destruct vs; try discriminate.
        destruct v; try discriminate. destruct vs; try discriminate.
        destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
        apply String.eqb_eq in Herl. subst s. simpl in H.
        destruct (s0 =? "link")%string eqn:Hlink;[|simpl in H; congruence].
        apply String.eqb_eq in Hlink. subst s0.
        destruct (p =? receiver) eqn:Hpr;[|congruence].
        apply Nat.eqb_eq in Hpr. subst p.
        inv H. unfold pids_insert.
        assert (g ∪ {[receiver]} = {[receiver]} ∪ g).
        { set_solver. }
        rewrite H. constructor.
      - destruct p; try discriminate. destruct l, p, p, p.
        destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate. destruct m0; try discriminate.
        destruct l; try discriminate. destruct f; try discriminate. destruct l; try discriminate.
        destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
        destruct vs; try discriminate. destruct v; try discriminate. destruct vs; try discriminate.
        destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
        apply String.eqb_eq in Herl. subst s. simpl in H.
        destruct (s0 =? "unlink")%string eqn:Hunlink;[|congruence].
        apply String.eqb_eq in Hunlink. subst s0.
        destruct (p =? receiver) eqn:Hpr;[|congruence].
        apply Nat.eqb_eq in Hpr. subst p.
        inv H. constructor.
    + unfold processLocalStepAArrive in H. destruct t.
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
      - unfold plsAArriveSExit in H. destruct p; try discriminate.
        destruct l, p, p, p.
        rename p0 into flag. rename sender into source. rename receiver into dest.
        destruct flag eqn:H'.
        ** destruct b eqn:H''.
           ++ unfold pids_member in H.
              destruct (gset_elem_of_dec source g) eqn:H'''.
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
                 *** unfold pids_member in H.
                     destruct (gset_elem_of_dec source g) eqn:H'''''; try discriminate.
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
                 *** unfold pids_member in H.
                     destruct (gset_elem_of_dec source g) eqn:H'''''.
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
      - destruct p; try discriminate. destruct l, p, p, p.
        unfold pids_insert in H.
        assert ({[sender]} ∪ g = g ∪ {[sender]}).
        { set_solver. }
        rewrite <- H0 in H.
        inversion H. constructor.
      - destruct p; try discriminate. destruct l, p, p, p. inversion H. constructor.
    + unfold processLocalStepASelf in H. destruct p; try discriminate. destruct l, p, p, p.
      destruct f; try discriminate. destruct f; try discriminate.
      destruct ident; try discriminate. destruct m0; try discriminate.
      destruct l; try discriminate. destruct f; try discriminate. destruct l; try discriminate.
      destruct vl; try discriminate. destruct el; try discriminate. destruct r; try discriminate.
      destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
      apply String.eqb_eq in Herl. subst s. simpl in H.
      destruct (s0 =? "self")%string eqn:Hself;[|congruence].
      apply String.eqb_eq in Hself. subst s0.
      inv H. constructor.
    + destruct t1; try discriminate. unfold processLocalStepASpawn in H.
      destruct (len t2) eqn:H''''; try discriminate.
      destruct (n =? params) eqn:H'; try discriminate.
      apply Nat.eqb_eq in H'. subst n.
      rename link into link_flag. destruct link_flag eqn:H''.
      - unfold plsASpawnSpawnLink in H. destruct p; try discriminate.
        destruct l, p, p, p. destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate. destruct m0; try discriminate.
        destruct l; try discriminate. destruct f; try discriminate. destruct l; try discriminate.
        destruct vl; try discriminate. destruct vl; try discriminate. destruct el; try discriminate.
        destruct r; try discriminate. destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
        apply String.eqb_eq in Herl. subst s. simpl in H.
        destruct (s0 =? "spawn_link")%string eqn:Hsl;[|congruence].
        apply String.eqb_eq in Hsl. subst s0.
        destruct (Val_eqb_strict v (VClos ext id params e)) eqn:Hvc;[|simpl in H; congruence].
        apply Val_eqb_strict_eq in Hvc. subst v. simpl in H.
        destruct (Val_eqb_strict v0 t2) eqn:Hv0t2;[|congruence].
        apply Val_eqb_strict_eq in Hv0t2. subst v0.
        inv H. unfold pids_insert.
        assert (g ∪ {[ι]} = {[ι]} ∪ g). { set_solver. }
        rewrite H. constructor. symmetry. assumption.
      - unfold plsASpawnSpawn in H. destruct p; try discriminate. destruct l, p, p, p.
        destruct f; try discriminate. destruct f; try discriminate.
        destruct ident; try discriminate.
        destruct m0; try discriminate. destruct l; try discriminate. destruct f; try discriminate.
        destruct l; try discriminate. destruct vl; try discriminate. destruct vl; try discriminate.
        destruct el; try discriminate. destruct r; try discriminate. destruct vs; try discriminate.
        destruct vs; try discriminate.
        destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
        apply String.eqb_eq in Herl. subst s. simpl in H.
        destruct (s0 =? "spawn")%string eqn:Hspawn;[|congruence].
        apply String.eqb_eq in Hspawn. subst s0.
        destruct (Val_eqb_strict v (VClos ext id params e)) eqn:Hvc;[|simpl in H; congruence].
        apply Val_eqb_strict_eq in Hvc. subst v. simpl in H.
        destruct (Val_eqb_strict v0 t2) eqn:Hv0t2;[|congruence].
        apply Val_eqb_strict_eq in Hv0t2. subst v0.
        inv H. constructor. symmetry. assumption.
    + unfold processLocalStepTau in H. destruct p; try discriminate. destruct l, p, p, p.
      simpl in Hlp. destruct Hlp, H1. rename H1 into Hlp. clear H0 H2.
      destruct (sequentialStepFunc f r) eqn:H'.
      destruct p. inversion H. constructor. apply sequentialStepEquiv in H'; try assumption. clear H'.
      destruct f; try discriminate. destruct f; try discriminate.
      destruct ident; try discriminate.
      - destruct m0; try discriminate. destruct l; try discriminate. destruct f; try discriminate.
        destruct l; try discriminate. destruct vl; try discriminate. destruct v; try discriminate.
        destruct l; try discriminate. destruct vl; try discriminate. destruct el; try discriminate.
        destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
        apply String.eqb_eq in Herl. subst s. simpl in H.
        destruct (s0 =? "process_flag")%string eqn:Hpf;[|simpl in H; congruence].
        apply String.eqb_eq in Hpf. subst s0. simpl in H.
        destruct (s1 =? "trap_exit")%string eqn:Hte;[|congruence].
        apply String.eqb_eq in Hte. subst s1.
        destruct r; try discriminate. destruct vs; try discriminate. destruct vs; try discriminate.
        destruct (bool_from_lit v) eqn:Hbfl; try discriminate.
        inv H. apply p_set_flag_exc. symmetry. assumption.
      - destruct vl; try discriminate. destruct el; try discriminate.
        destruct (f =? "recv_peek_message")%string eqn:Hrpm.
        apply String.eqb_eq in Hrpm. subst f.
        destruct r; try discriminate. destruct (peekMessage m) eqn:Hpm; try discriminate.
        inv H. apply p_recv_peek_message_ok. assumption.
        destruct (f =? "recv_next")%string eqn:Hrn.
        apply String.eqb_eq in Hrn. subst f.
        destruct r; try discriminate. destruct (recvNext m) eqn:Hrnm; try discriminate.
        inv H. constructor. assumption.
        destruct (f =? "remove_message")%string eqn:Hrm.
        apply String.eqb_eq in Hrm. subst f.
        destruct r; try discriminate. destruct (removeMessage m) eqn:Hrmm; try discriminate.
        inv H. constructor. assumption.
        destruct (f =? "recv_wait_timeout")%string eqn:Hrwt.
        apply String.eqb_eq in Hrwt. subst f.
        destruct r; try discriminate. destruct vs; try discriminate. destruct vs; try discriminate.
        destruct v; try discriminate.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** destruct l; try discriminate.
           ++ destruct (s =? "infinity")%string eqn:Hs.
              -- apply String.eqb_eq in Hs. subst s.
                 destruct m. destruct l0; try discriminate. inv H. apply p_recv_wait_timeout_new_message.
              -- inv H. apply p_recv_wait_timeout_invalid. congruence.
                 apply String.eqb_neq in Hs. congruence.
           ++ destruct x eqn:Hx.
              -- inv H. apply p_recv_wait_timeout_0.
              -- inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
              -- inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** inv H. apply p_recv_wait_timeout_invalid. congruence. congruence.
        ** congruence.
    + unfold processLocalStepEps in H. destruct p; try discriminate. destruct l, p, p, p.
      destruct f.
      - destruct r; try discriminate.
        ** destruct vs; try discriminate. destruct vs; try discriminate.
           inversion H. constructor.
        ** inversion H. constructor.
      - destruct f; try discriminate. destruct el; try discriminate.
        destruct ident; try discriminate.
        ** destruct m0; try discriminate. destruct l; try discriminate. destruct f; try discriminate.
           destruct l; try discriminate.
           destruct (s =? "erlang")%string eqn:Herl;[|simpl in H; congruence].
           apply String.eqb_eq in Herl. subst s. simpl in H.
           destruct (s0 =? "process_flag")%string eqn:Hpf;[|congruence].
           apply String.eqb_eq in Hpf. subst s0.
           destruct vl; try discriminate. destruct v; try discriminate. destruct l; try discriminate.
           destruct vl; try discriminate.
           destruct (s =? "trap_exit")%string eqn:Hte;[|congruence].
           apply String.eqb_eq in Hte. subst s.
           destruct r; try discriminate. destruct vs; try discriminate. destruct vs; try discriminate.
           destruct (bool_from_lit v) eqn:Hbflv;try discriminate.
           inv H. constructor. symmetry. assumption.
        ** destruct (f =? "recv_peek_message")%string eqn:Hrpm;[|congruence].
           apply String.eqb_eq in Hrpm. subst f.
           destruct vl; try discriminate. destruct r; try discriminate.
           destruct (peekMessage m) eqn:Hpm; try discriminate.
           inv H. constructor. assumption.
Qed.

Theorem interProcessStepEquiv: forall n n' a p, NODECLOSED n -> 
  n -[ a | p ]ₙ-> n' with ∅ <-> interProcessStepFunc n a p = Some n'.
Proof.
  intros. split; intro.
  * inv H0.
    + simpl. unfold pool_lookup.
      assert ((p ↦ p0 ∥ prs) !! p = (p ↦ p0 ∥ prs) !! p) by (apply eq_refl).
      setoid_rewrite lookup_insert. setoid_rewrite lookup_insert in H0 at 2. rewrite Nat.eqb_refl.
      inv H. unfold POOLCLOSED in H2.
      apply elem_of_map_to_list in H0. apply Forall_forall with (x := (p,p0)) in H2;[|auto].
      apply (processLocalStepEquiv _ _ _ H2) in H1. simpl in H1. rewrite H1.
      unfold pool_insert.
      setoid_rewrite etherAdd_equiv. f_equal. f_equal.
      setoid_rewrite insert_insert. reflexivity.
    + simpl. unfold pool_lookup.
      assert ((p ↦ p0 ∥ prs) !! p = (p ↦ p0 ∥ prs) !! p) by (apply eq_refl).
      setoid_rewrite lookup_insert. setoid_rewrite lookup_insert in H0 at 2. rewrite Nat.eqb_refl.
      rewrite etherPop_equiv in H1. rewrite H1.
      rewrite Signal_eqb_strict_refl.
      inv H. unfold POOLCLOSED in H3.
      apply elem_of_map_to_list in H0. apply Forall_forall with (x := (p, p0)) in H3;[|auto].
      apply (processLocalStepEquiv _ _ _ H3) in H2. simpl in H2. rewrite H2. unfold pool_insert.
      f_equal. f_equal. setoid_rewrite insert_insert. reflexivity.
    + simpl. unfold pool_lookup. rename Π into prs.
      assert ((p ↦ p0 ∥ prs) !! p = (p ↦ p0 ∥ prs) !! p) by (apply eq_refl).
      setoid_rewrite lookup_insert. setoid_rewrite lookup_insert in H0 at 2.
      inv H. unfold POOLCLOSED in H3.
      apply elem_of_map_to_list in H0. apply Forall_forall with (x := (p, p0)) in H3;[|auto].
      apply (processLocalStepEquiv _ _ _ H3) in H1.
      destruct H2.
      - subst a. rewrite H1. unfold pool_insert.
        do 2 f_equal. apply insert_insert.
      - destruct H.
        ** subst a. rewrite Nat.eqb_refl, H1. do 2 f_equal. unfold pool_insert. apply insert_insert.
        ** subst a. rewrite H1. do 2 f_equal. unfold pool_insert. apply insert_insert.
    + simpl. unfold pool_lookup. rename Π into prs.
      assert ((p ↦ p0 ∥ prs) !! p = (p ↦ p0 ∥ prs) !! p) by (apply eq_refl).
      setoid_rewrite lookup_insert. setoid_rewrite lookup_insert in H0 at 2. rewrite H1.
      apply usedInPoolCorrect in H3.
      apply usedInEtherCorrect in H4.
      rewrite <- (usedInPool_equiv ι' (p ↦ p0 ∥ prs)).
      rewrite <- (usedInEther_equiv ι' ether).
      rewrite H3, H4. simpl.
      rewrite create_result_equiv in H5. unfold create_result_NEW in H5. rewrite H5.
      clear H5 H4 H3.
      destruct v1. inv H6. inv H6. inv H6. inv H6. inv H6. inv H6. inv H6. inv H6.
      inv H. unfold POOLCLOSED in H3.
      apply elem_of_map_to_list in H0. apply Forall_forall with (x := (p, p0)) in H3;[|auto].
      apply (processLocalStepEquiv _ _ _ H3) in H6. simpl in H6. rewrite H6.
      unfold pool_insert, pids_singleton, pids_empty. do 3 f_equal. apply insert_insert.
  * unfold interProcessStepFunc in H0. destruct n.
    unfold pool_lookup in H0.
    destruct (p0 !! p) eqn:Hp0p;try discriminate.
    inv H. unfold POOLCLOSED in H1.
    remember Hp0p as Hp0p'. clear HeqHp0p'.
    apply elem_of_map_to_list in Hp0p'.
    apply Forall_forall with (x := (p, p1)) in H1;[|auto]. clear Hp0p'.
    apply insert_id in Hp0p. rewrite <- Hp0p.
    destruct a.
    + destruct (sender =? p) eqn:Hsp; try discriminate.
      apply Nat.eqb_eq in Hsp. subst p.
      destruct (processLocalStepFunc p1 (ASend sender receiver t)) eqn:Hpls; try discriminate.
      unfold pool_insert in H0. rewrite <- etherAdd_equiv in H0. inv H0.
      apply (processLocalStepEquiv _ _ _ H1) in Hpls.
      constructor. assumption.
    + destruct (receiver =? p) eqn:Hrp; try discriminate.
      destruct (etherPopNew sender receiver e) eqn:Hep; try discriminate.
      destruct p2.
      destruct (Signal_eqb_strict t s) eqn:Hses; try discriminate.
      apply Signal_eqb_strict_eq in Hses. subst s.
      destruct (processLocalStepFunc p1 (AArrive sender receiver t)) eqn:Hpls; try discriminate. 
      apply Nat.eqb_eq in Hrp. subst p.
      rewrite <- etherPop_equiv in Hep.
      unfold pool_insert in H0. inv H0.
      apply (processLocalStepEquiv _ _ _ H1) in Hpls.
      constructor; auto.
    + destruct (ι =? p) eqn:Hip; try discriminate.
      destruct (processLocalStepFunc p1 (ASelf ι)) eqn:Hpls; try discriminate.
      apply Nat.eqb_eq in Hip. subst p. inv H0.
      apply (processLocalStepEquiv _ _ _ H1) in Hpls.
      unfold pool_insert.
      constructor; auto.
    + destruct (mk_list t2) eqn:Hmk; try discriminate.
      destruct (usedInPoolNew ι p0 || usedInEtherNew ι e) eqn:Huip; try discriminate.
      destruct (create_result_NEW (IApp t1) l) eqn:Hcr; try discriminate.
      destruct p2. rename link into link'.
      destruct (processLocalStepFunc p1 (ASpawn ι t1 t2 link')) eqn:Hpls; try discriminate.
      unfold pool_insert, pids_empty, pids_singleton in H0. inv H0.
      apply orb_false_elim in Huip. destruct Huip.
      apply n_spawn with (l := l) (eff := o); try auto.
      - discriminate.
      - rewrite <- usedInPool_equiv in H. apply usedInPoolComplete in H. setoid_rewrite Hp0p. auto.
      - rewrite <- usedInEther_equiv in H0. apply usedInEtherComplete in H0. auto.
      - apply (processLocalStepEquiv _ _ _ H1) in Hpls. assumption.
    + destruct (processLocalStepFunc p1 τ) eqn:Ht; try discriminate.
      inv H0. unfold pool_insert.
      apply (processLocalStepEquiv _ _ _ H1) in Ht.
      constructor; auto.
    + destruct (processLocalStepFunc p1 ε) eqn:He; try discriminate.
      inv H0. unfold pool_insert.
      apply (processLocalStepEquiv _ _ _ H1) in He.
      constructor; auto.
Qed.

Theorem sequentialStepFuncClosedness: forall fs e, FSCLOSED fs -> REDCLOSED e -> forall fs' e',
    sequentialStepFunc fs e = Some (fs', e') -> FSCLOSED fs' /\ REDCLOSED e'.
Proof.
  intros. apply sequentialStepEquiv in H1; try assumption. apply (step_closedness fs e); assumption.
Qed.

Theorem processLocalStepFuncClosedness: forall p p' a, PROCCLOSED p -> ACTIONCLOSED a ->
    processLocalStepFunc p a = Some p' -> PROCCLOSED p'.
Proof.
  intros. apply processLocalStepEquiv in H1; try assumption.
  apply (processLocalStepClosedness p p' a); assumption.
Qed.

Theorem interProcessStepFuncClosedness: forall n n' pid a,
    interProcessStepFunc n a pid = Some n' -> NODECLOSED n -> NODECLOSED n'.
Proof.
  intros. apply interProcessStepEquiv in H; try assumption.
  apply (interProcessStepClosedness n n' pid a ∅); assumption.
Qed.