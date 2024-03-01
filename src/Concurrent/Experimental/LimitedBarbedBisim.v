From CoreErlang Require Export Concurrent.BarbedBisim Concurrent.Examples.

Import ListNotations.

CoInductive preBarbedBisimReceptionists (U : list PID) : Node -> Node -> Prop :=
| is_bisim (A B : Node) :
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
  (forall A' a ι,
      A -[a | ι]ₙ-> A' ->
        exists B' l,
          reductionPreCompatibility A B [(a,ι)] l /\
          reductionPreCompatibility B A l [(a,ι)] /\
          B -[l]ₙ->* B' /\ preBarbedBisimReceptionists U A' B') ->
  (* external observers: *)
  (forall source dest,
      ~In dest U ->
      dest ∉ dom A.2 ->
      exists source' l B',
      B -[l]ₙ->* B' /\
      dest ∉ dom B'.2 /\
      (* list_biforall Srel (A.1 source dest) (B'.1 source' dest) *)
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)
      (* A.1 source dest = B'.1 source' dest *)
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest)))
->
  (* receptionists *)
  (forall source dest,
    ~In source U ->
    dest ∈ dom A.2 ->
    exists dest' l B',
    B -[l]ₙ->* B' /\
    dest ∈ dom B'.2 /\
    option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source, dest')))
(* ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' ->
        exists A' l,
          reductionPreCompatibility B A [(a,ι)] l /\
          reductionPreCompatibility A B l [(a,ι)] /\
          A -[l]ₙ->* A' /\
      barbedBisim U A' B') ->
  (forall source dest,
      ~In dest U ->
      dest ∉ dom B.2 ->
      exists source' l A',
      A -[l]ₙ->* A' /\
      dest ∉ dom A'.2 /\
      (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in, as far as this relation is reflexive,
               transitive and symmetric *)
      (* B.1 source dest = A'.1 source' dest *)
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))  *) ->
  preBarbedBisimReceptionists U A B
.
Notation "A ⪯ B 'using' U" := (preBarbedBisimReceptionists U A B) (at level 70).

Axiom unsafe : forall U A B B',
  A ⪯ B using U -> A ⪯ B' using U.

Lemma bisim_congr :
  forall U Π Π' eth eth', (eth, Π) ⪯ (eth', Π') using U ->
    forall Π2, (eth, Π ∪ Π2) ⪯ (eth', Π' ∪ Π2) using U.
Proof.
  cofix IH. intros. inv H. constructor; auto; simpl in *.
  * clear -H0. destruct H0. split; unfold preCompatibleNodes in *; intros.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H in H1_1.
      assert (isUntaken ι (eth', Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
    - apply isUntaken_comp in H1 as [H1_1 H1_2].
      apply H0 in H1_1.
      assert (isUntaken ι (eth, Π2)). {
        destruct H1_1, H1_2. split; auto.
      }
      now apply isUntaken_comp.
  * intros. destruct A'.
    apply step_in_comp in H as H'. destruct H' as [[Π1' [? ?]] | [Π2' [? ?]]].
    - subst. apply H3 in H6 as H6'. destruct_hyps. destruct x as [e' Π1''].
      apply unsafe with (B' := (e', ∅)) in H10. apply IH with (Π2 := Π2) in H10.
      Guarded.
      (* (* At this point, we need renamings :( - or to know what PIDs are
         spawned by Π *)
      Print reductionPreCompatibility.
      (* spawns in x0 should be distinct from:
         - syntactically used PIDs in Π2 - for goal 3
         - ι0 -> if a = send(ι, ι0 <- destination, msg)
         - We also need a proof that (eth, Π) ~ (eth[x|->y], Π[x|->y])
      *)
      exists (e', Π1'' ∪ Π2), x0. split. 2: split. 3: split.
      4: { apply IH. assumption. }
      3: apply reductions_are_preserved_by_comp; auto.
      3: {
        intros. destruct H6 as [H6 _]. rewrite Forall_forall in H6.
        apply H6 in H9. unfold isUntaken in H9. simpl in *.
      } *)
      admit.
    - subst. exists (e, Π' ∪ Π2'), [(a, ι)]. split_and!.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
           apply isUntaken_comp; split; auto.
           (* ι0 should be Untaken wrt. eth *)
           destruct H5, H6. split; simpl in *; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π' uses ι0 *)
           (* is it okay to assume, that Π2 does not communicate to 
              PIDs in the domain of Π/Π' -> NO!

              is it okay to assume, that Π2 does not communicate to
              PIDs in ((dom Π ∪ dom Π') \ (dom Π ∩ dom Π')). Probably not.
            *)
           admit.
      + split.
        ** destruct a; auto. simpl. constructor; auto. intro.
           eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
           apply n_refl. 2: cbn; left; reflexivity.
           apply isUntaken_comp in H5 as [? ?].
           apply isUntaken_comp; split; auto.
        ** intros; simpl in *; destruct a; auto; simpl in *.
           destruct_or!; auto. split. 2: split; auto.
           subst.
           (* ISSUE: we do not know, whether Π uses ι0
              BOTTOMLINE: we should specify where can Π2 send messages?
            *)
           admit.
      + econstructor.
        apply reduction_is_preserved_by_comp_r. (* eassumption. *) admit. admit. admit. admit.
      + admit.
(*     - subst. exists (e, Π ∪ Π2'), [(a, ι)]. split_and!.
      split.
      + destruct a; auto. simpl. constructor; auto. intro.
        eapply (no_spawn_unTaken (eth, Π ∪ Π2)). eapply n_trans. eassumption.
        apply n_refl. 2: cbn; left; reflexivity.
        apply isUntaken_comp in H5 as [? ?]. apply H0 in H5.
        apply isUntaken_comp; split; auto.
        (* ι0 should be Untaken wrt. eth *)
        destruct H5, H6. split; simpl in *; auto.
      + intros; simpl in *; destruct a; auto; simpl in *.
        destruct_or!; auto. split. 2: split; auto.
        subst.
        (* ISSUE: we do not know, whether Π' uses ι0 *)
        admit.
      4: { apply IH. apply barbedBisim_refl. } *)
Abort.


(*
CoInductive barbedBisim (U : list PID) : Node -> Node -> Prop :=
| is_bisim (A B : Node) :
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
  (forall A' a ι,
      A -[a | ι]ₙ-> A' ->
        exists B' l,
          reductionPreCompatibility A B [(a,ι)] l /\
          reductionPreCompatibility B A l [(a,ι)] /\
          B -[l]ₙ->* B' /\ barbedBisim U A' B') ->
  (forall source dest,
      ~In dest U ->
      dest ∉ dom A.2 ->
      exists source' l B',
      B -[l]ₙ->* B' /\
      dest ∉ dom B'.2 /\
      (* list_biforall Srel (A.1 source dest) (B'.1 source' dest) *)
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)
      (* A.1 source dest = B'.1 source' dest *)
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' ->
        exists A' l,
          reductionPreCompatibility B A [(a,ι)] l /\
          reductionPreCompatibility A B l [(a,ι)] /\
          A -[l]ₙ->* A' /\
      barbedBisim U A' B') ->
  (forall source dest,
      ~In dest U ->
      dest ∉ dom B.2 ->
      exists source' l A',
      A -[l]ₙ->* A' /\
      dest ∉ dom A'.2 /\
      (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in, as far as this relation is reflexive,
               transitive and symmetric *)
      (* B.1 source dest = A'.1 source' dest *)
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))) ->
  barbedBisim U A B
.
Notation "A ~ B 'using' U" := (barbedBisim U A B) (at level 70).

Theorem reductionPreCompatibility_refl A A' a ι:
  A -[ a | ι ]ₙ-> A' ->
  reductionPreCompatibility A A [(a, ι)] [(a, ι)].
Proof.
  split; intros.
  * cbn. break_match_goal; auto. constructor; auto.
    intro. destruct H0. destruct a; inv Heqo. inv H.
    1: destruct H3 as [? | [? | ?]]; congruence.
    simpl in *. congruence.
  * cbn in H1. break_match_hyp; inv H1. 2: { inv H3. }
    destruct a; inv Heqo. split; auto. split; auto.
    now constructor.
Qed.

Corollary Srel_refl :
  forall s, SIGCLOSED s -> Srel s s.
Proof.
  destruct s; simpl; auto.
Qed.

Corollary Signal_eq_refl :
  forall s, s =ₛ s.
Proof.
  destruct s; cbn; try reflexivity.
  * cbn. unfold "=ₛ". simpl. apply Val_eqb_refl.
  * cbn. unfold "=ₛ". simpl. rewrite Val_eqb_refl.
    now destruct b.
Qed.

Corollary Signal_eq_sym :
  forall s s', s =ₛ s' -> s' =ₛ s.
Proof.
  destruct s eqn:ES1, s' eqn:ES2; unfold "=ₛ"; cbn; intro H; try reflexivity; try now inv H.
  * now rewrite Val_eqb_sym.
  * cbn. rewrite Val_eqb_sym.
    destruct b, b0; auto.
Qed.

Corollary Signal_eq_trans :
  forall s s' s'', s =ₛ s' -> s' =ₛ s'' -> s =ₛ s''.
Proof.
  destruct s eqn:ES1, s' eqn:ES2, s'' eqn:ES3;
    unfold "=ₛ"; cbn; intros H1 H2; try reflexivity; try now inv H1; try now inv H2.
  * erewrite Val_eqb_trans; eauto.
  * apply andb_true_iff in H1, H2. destruct_and!.
    rewrite (Val_eqb_trans _ _ _ H3 H0).
    now destruct b, b0, b1.
Qed.

Theorem barbedBisim_refl :
  forall U A, ether_wf A.1 -> A ~ A using U.
Proof.
  cofix H. intros.
  constructor.
  * unfold symClos, preCompatibleNodes.
    split; intros ι H1; apply H1.
  * assumption.
  * assumption.
  * intros. exists A', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A A' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source, [], A.
    split. constructor. split. assumption.
    apply option_biforall_refl.
    intros. apply Signal_eq_refl.
    (* (*  apply forall_biforall_refl. *) reflexivity. *)
    (* specialize (H0 source dest). rewrite Forall_forall in *.
    intros. apply Srel_refl. now apply H0. *)
  * intros. exists B', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A B' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source, [], A.
    split. constructor. split. assumption. (*  reflexivity. *) (* apply forall_biforall_refl.
    specialize (H0 source dest). rewrite Forall_forall in *.
    intros. apply Srel_refl. now apply H0. *)
    apply option_biforall_refl.
    intros. apply Signal_eq_refl.
Qed.

Theorem barbedBisim_sym :
  forall U A B, A ~ B using U -> B ~ A using U.
Proof.
  cofix IH.
  intros. inv H. constructor; auto.
  * split; apply H0.
  * clear H6 H4. intros.
    apply H5 in H. destruct_hyps.
    do 2 eexists. split. 2: split. 3: split. 3: eassumption.
    1-2: auto.
    now apply IH.
  * clear H6 H4. intros.
    apply H3 in H. destruct_hyps.
    do 2 eexists. split. 2: split. 3: split. 3: eassumption.
    1-2: auto.
    now apply IH.
Qed.

(* Lemma preCompatibleNodes_trans :
  forall A B C, preCompatibleNodes A B -> preCompatibleNodes B C ->
    preCompatibleNodes A C.
Proof.
  intros. intros ι Hi. apply H in Hi.
Qed. *)

Lemma reductionPreCompatibility_app :
  forall As Bs A B,
    reductionPreCompatibility A B As Bs ->
    reductionPreCompatibility B A Bs As ->
    forall As' Bs' A' B' B'' (* B'' A'' *),
      A -[As]ₙ->* A' ->
      (* A' -[ys]ₙ->* A'' -> *)
      B -[Bs]ₙ->* B' ->
      B' -[Bs']ₙ->* B'' ->
      reductionPreCompatibility A' B' As' Bs' ->
      reductionPreCompatibility B' A' Bs' As' ->
      reductionPreCompatibility A B (As ++ As') (Bs ++ Bs').
Proof.
  intros As Bs A B C1 C2 As' Bs' A' B' B'' D1A D1 D2 C1' C2'.
  unfold reductionPreCompatibility in *.
  destruct C1 as [C1_1 C1_2]. destruct C2 as [C2_1 C2_2].
  destruct C1' as [C1_1' C1_2']. destruct C2' as [C2_1' C2_2'].
  split.
  * clear C2_2' C1_2' C1_2 C2_2.
    unfold PIDsOf. rewrite flat_map_app. fold (PIDsOf spawnPIDOf As).
    fold (PIDsOf spawnPIDOf As'). apply Forall_app; split; auto.
    (** Proof by contradiction :
        If ι ∈ (PIDsOf spawnPIDOf ys) 
        1) were used (isUsed ι B), then it couldn't be contained in
           this list (spawn could not happen on it).
        2) were assigned in B (B.2 ι = Some proc), then spawn could
           not happen on it
    *)
    rewrite Forall_forall in *. intros. apply C1_1' in H as H'. clear C1_1'.
    intro H0.
    eapply compatibility_of_reductions in H0 as H0'. 2: eassumption.
    congruence. (* 
    destruct H0'. (* congruence. *) destruct_hyps.
    destruct H0. pose proof (isUsedEther_no_spawn _ _ _ D1 _ H3). *)
  * intros ι Ha Hin1 Hin2. unfold PIDsOf in Hin1, Hin2.
    rewrite flat_map_app in *.
    fold (PIDsOf spawnPIDOf As) in *. fold (PIDsOf spawnPIDOf As') in *.
    fold (PIDsOf sendPIDOf As) in Hin1. fold (PIDsOf sendPIDOf As') in Hin1.
    apply not_in_app in Hin2 as [Hin2_1 Hin2_2].
    apply in_app_or in Hin1 as [Hin1 | Hin1].
    - specialize (C1_2 _ Ha Hin1 Hin2_1) as [H8_1 [H8_2 H8_3]]. split; auto.
      split.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now left.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply isUsedEther_no_spawn. exact D2.
        eapply isUsedEther_after_send; eauto.
        now apply not_elem_of_dom.
    - eapply no_spawn_included in Hin2_1. 2: eassumption.
      apply not_elem_of_dom in Ha.
      rewrite Hin2_1 in Ha.
      apply not_elem_of_dom in Ha.
      specialize (C1_2' _ Ha Hin1 Hin2_2) as [H8_1 [H8_2 H8_3]]. split.
      2: split.
      + apply not_elem_of_dom. eapply processes_dont_die_None; try eassumption.
        now apply not_elem_of_dom.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now right.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply no_spawn_included_2. eassumption.
        apply not_elem_of_dom. assumption.
Qed.

Lemma barbedBisim_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ~ B using U ->
      exists B' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ~ B' using U.
Proof.
  intros A A' l IH. induction IH; rename n into A; intros.
  * exists B, []. split. 2: split. 3: split. 3: constructor. 3: assumption.
    1-2: split; constructor; auto.
  * rename n' into A'. rename n'' into A''.
    inv H0. apply H4 in H as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    clear H4 H5 H6 H7. apply IHIH in H10. destruct H10 as [B'' [l'' H10]].
    destruct_hyps.
    exists B'', (l' ++ l''). split. 2: split. 3: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
Qed.

(* Theorem reductionPreCompatibility_trans :
  forall A C B As Bs Cs,
    reductionPreCompatibility A B As Bs ->
    reductionPreCompatibility B C Bs Cs ->
    reductionPreCompatibility A C As Cs.
Proof.
  intros. destruct H, H0. split.
  * rewrite Forall_forall in *. intros.
    apply H in H3 as H3'.
Qed. *)

(* Lemma Vrel_trans :
  forall n v1 v2, Vrel n v1 v2 -> forall v3, Vrel n v2 v3 -> Vrel n v1 v3.
Proof.
  intros n v1 v2 H.
  assert (VALCLOSED v1) by now apply Vrel_closed_l in H. revert H0.
  induction H using Vrel_ind; destruct v3; intros;
    try now (try rewrite Vrel_Fix_eq in H;
             try rewrite Vrel_Fix_eq in H1;
             simpl in *; destruct_hyps; auto).
  * rewrite Vrel_Fix_eq. simpl. split. 2: split.
    1: apply H0.
    1: now apply Vrel_closed_r in H.
    rewrite Vrel_Fix_eq in H. simpl in H. destruct_hyps. subst.
    split. 2: split. 1-2: auto.
Qed. *)

(* Corollary Srel_trans :
  forall s1 s2 s3, Srel s1 s2 -> Srel s2 s3 -> Srel s1 s3.
Proof.
  intros; destruct s1, s2, s3; simpl in *; try contradiction.
  * intros. split; apply CIU_Val_compat_closed_reverse.
    - specialize (H n) as [H _]. specialize (H0 n) as [H0 _].
      apply Erel_Val_compat_closed in H, H0.
      apply Rrel_exp_compat_closed in H, H0.
      apply CIU_iff_Rrel_closed in H, H0.
Qed. *)

(** NOTE: this theorem is needed separately to prove transitivity, because
    using symmetry in the proof for transitivity breaks the guardedness
    conditions! *)
Corollary barbedBisim_many_sym :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, B ~ A using U ->
      exists B' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ B' ~ A' using U.
Proof.
  intros.
  apply barbedBisim_sym in H0.
  pose proof (barbedBisim_many _ _ _ H _ _ H0).
  destruct_hyps. exists x, x0. do 3 (split; auto).
  now apply barbedBisim_sym.
Qed.

Theorem barbedBisim_trans :
  forall U A B C,
    (A ~ B using U -> B ~ C using U -> A ~ C using U).
Proof.
  (**)
  (* intros. apply barbedBisim_sym in H as Hsym.
  apply barbedBisim_sym in H0 as H0sym.
  generalize dependent A. generalize dependent B. revert U C. *)
  (**)
  cofix IH. intros.
  pose proof (H) as AB. inv H. pose proof (H0) as BC. inv H0. constructor; auto.
  * clear -H1 H. destruct H1, H. split.
    1-2: eapply preCompatibleNodes_trans; eassumption.
  * clear H7. intros. apply H4 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    pose proof (barbedBisim_many _ _ _ H14 _ _ BC).
    destruct H16 as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H15 H19). exists C', l'.
    split. 2: split. 3: split; auto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H20 in H25. intro.
        now apply H in H26.
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H1 in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto.
  * intros.
    epose proof (H5 source dest H0 H14). destruct H15 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    pose proof (barbedBisim_many _ _ _ H15 _ _ BC) as [C' [Cs ?]]. destruct_hyps.
    pose proof H21 as B'C'. inv H21.
    specialize (H26 sourceB _ H0 ltac:(assumption)).
    destruct H26 as [sourceC [Cs' [C'' ?]]].
    destruct_hyps.
    exists sourceC, (Cs ++ Cs'), C''.
    split. 2: split.
    - eapply closureNodeSem_trans; eassumption.
    - assumption.
    - clear -H29 H17. (* rewrite <- H29. assumption. *) (* transitivity is needed here! *)
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
  * clear H7. intros. rename B' into C'. apply H12 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    (* assert (B ~ A using U) as BA by now apply barbedBisim_sym. *)
    pose proof (barbedBisim_many_sym _ _ _ H14 _ _ AB).
    destruct H16 as [A' [l']]. destruct_hyps.
    (* apply barbedBisim_sym in H15. *)
    (* specialize (IH _ _ _ _ H15 H19). *)
    epose proof (IH _ _ _ _ H19 H15) as IH2. clear IH.
    exists A', l'.
    split. 2: split. 3: split; auto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H20 in H25. intro.
        now apply H1 in H26.
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto.
  * intros.
    epose proof (H13 source dest H0 H14). destruct H15 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    assert (B ~ A using U) as BA by now apply barbedBisim_sym.
    pose proof (barbedBisim_many _ _ _ H15 _ _ BA) as [A' [As ?]]. destruct_hyps.
    pose proof H21 as B'A'. inv H21.
    specialize (H26 sourceB _ H0 ltac:(assumption)).
    destruct H26 as [sourceA [As' [A'' ?]]].
    destruct_hyps.
    exists sourceA, (As ++ As'), A''.
    split. 2: split.
    - eapply closureNodeSem_trans; eassumption.
    - assumption.
    - (* rewrite <- H29. assumption. (* transitivity is needed here! *) *)
      clear -H29 H17.
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
Qed.

CoInductive barbedExpansion (U : list PID) : Node -> Node -> Prop :=
| is_expansion A B:
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
  (forall A' a ι, A -[a | ι]ₙ-> A' -> exists B' l, 
    reductionPreCompatibility A B [(a,ι)] l /\
    reductionPreCompatibility B A l [(a,ι)] /\
    length l <= 1 /\ B -[l]ₙ->* B' /\ barbedExpansion U A' B')
  ->
  (forall B' a ι, B -[a | ι]ₙ-> B' -> exists A' l,
    reductionPreCompatibility B A [(a,ι)] l /\
    reductionPreCompatibility A B l [(a,ι)] /\
    length l >= 1 /\ A -[l]ₙ->* A' /\ barbedExpansion U A' B')
  ->
  (forall source dest,
    ~In dest U ->
    dest ∉ dom A.2 ->
    exists source', (* list_biforall Srel (A.1 source dest) (B.1 source' dest) *)
    dest ∉ dom B.2 /\
    (* (A.1 source dest) = (B.1 source' dest) *)
    option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source', dest)))
  ->
  (forall source dest,
    ~In dest U ->
    dest ∉ dom B.2 ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    dest ∉ dom A'.2 /\
    (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
    (* (B.1 source dest) = (A'.1 source' dest) *)
    option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))
->
  barbedExpansion U A B.

Notation "A ⪯ B 'using' U" := (barbedExpansion U A B) (at level 70).

Theorem barbedExpansion_implies_bisim :
  forall U A B, A ⪯ B using U -> A ~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * intros. apply H3 in H. destruct H as [B' [l H]]. destruct_hyps.
    apply IH in H10. exists B', l. now auto.
  * intros. apply (H5 source dest) in H. destruct_hyps.
    exists x, [], B. split; auto. now constructor. assumption.
  * intros. apply H4 in H. destruct H as [A' [l H]]. destruct_hyps.
    apply IH in H10. exists A', l. now auto.
Qed.

CoInductive barbedBisimUpTo (U : list PID) : Node -> Node -> Prop :=
| is_bisim_up_to A B:
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
  (forall A' a ι, A -[a | ι]ₙ-> A' ->
     exists B' A'' B'' l,
       reductionPreCompatibility A B [(a,ι)] l /\
       reductionPreCompatibility B A l [(a,ι)] /\
       B -[l]ₙ->* B' /\
       A' ⪯ A'' using U /\ B' ⪯ B'' using U /\ barbedBisimUpTo U A'' B'') ->
  (forall source dest,
    ~In dest U ->
    dest ∉ dom A.2 ->
    exists source' l B',
    B -[l]ₙ->* B' /\
    dest ∉ dom B'.2 /\
    (* list_biforall Srel (A.1 source dest) (B'.1 source' dest) *)
    (* (A.1 source dest) = (B'.1 source' dest) *)
    option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) ->
  (forall B' a ι, B -[a | ι]ₙ-> B' ->
     exists A' B'' A'' l,
       reductionPreCompatibility B A [(a,ι)] l /\
       reductionPreCompatibility A B l [(a,ι)] /\
       A -[l]ₙ->* A' /\
       A' ⪯ A'' using U /\ B' ⪯ B'' using U /\ barbedBisimUpTo U  A'' B'') ->
   (forall source dest,
    ~In dest U ->
    dest ∉ dom B.2 ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    dest ∉ dom A'.2 /\
    (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
    (* (B.1 source dest) = (A'.1 source' dest) *)
    option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))
->
  barbedBisimUpTo U A B.

Notation "A ~⪯~ B 'using' U" := (barbedBisimUpTo U A B) (at level 70).

Corollary diamond_trans :
  forall U A B A' B',
    A ~ A' using U -> B ~ B' using U -> A' ~ B' using U ->
    A ~ B using U.
Proof.
  intros ????? AA' BB' A'B'.
  eapply barbedBisim_trans. exact AA'.
  eapply barbedBisim_trans. exact A'B'.
  now apply barbedBisim_sym.
Qed.


Lemma barbedExpansion_refl :
  forall U A, ether_wf A.1 -> A ⪯ A using U.
Proof.
  cofix H. intros.
  constructor.
  * unfold symClos, preCompatibleNodes.
    split; intros ι H1; apply H1.
  * assumption.
  * assumption.
  * intros. exists A', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. slia. split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A A' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists B', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. slia. split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A B' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source.
    split. assumption.
    apply option_biforall_refl. intros. apply Signal_eq_refl.
  * intros. exists source, [], A.
    split. constructor.
    split. assumption.
    apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

Lemma barbedExpansion_is_expansion_up_to :
  forall U A B,
    A ⪯ B using U -> A ~⪯~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * intros. apply H3 in H as H'. destruct H' as [B' [l H']]. destruct_hyps.
    exists B', A', B', l. do 3 (split; auto).
    split. 2: split.
    1-2: apply barbedExpansion_refl.
    - now apply (ether_wf_preserved A A' [(a, ι)] ltac:(econstructor;[eassumption|constructor])).
    - now apply (ether_wf_preserved _ _ _ H10).
    - now apply IH.
  * intros. apply (H5 source) in H. destruct H as [sourceB H].
    exists sourceB, [], B. split. constructor. assumption. assumption.
  * intros. apply H4 in H as H'. destruct H' as [A' [l H']]. destruct_hyps.
    exists A', B', A', l. do 3 (split; auto).
    split. 2: split.
    1-2: apply barbedExpansion_refl.
    - now apply (ether_wf_preserved _ _ _ H10).
    - now apply (ether_wf_preserved B B' [(a, ι)] ltac:(econstructor;[eassumption|constructor])).
    - now apply IH.
Qed.


(* Lemma barbedBisimUpTo_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ~⪯~ B using U ->
      exists B' A'' B'' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ A'' using U /\ A'' ~⪯~ B'' using U /\ B' ⪯ B'' using U.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
Admitted.

Lemma barbedBisimUpTo_barbedBisim_helper :
  forall U A B A' B',
    A ⪯ A' using U -> A' ~⪯~ B' using U -> B ⪯ B' using U
    -> A ~⪯~ B using U.
Proof.
  cofix IH. intros. pose proof H as AA'. pose proof H1 as BB'.
  constructor; auto.
  * inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H0. eapply preCompatibleNodes_trans.
      apply H2. inv H1. apply H0.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H0. eapply preCompatibleNodes_trans.
      apply H2. inv H. apply H0.
  * now inv H.
  * now inv H1.
  * intros. rename A'0 into A0.
    inv H. apply H6 in H2 as [A'0 [l ?]]. destruct_hyps.
    clear H6 H7 H8 H9.
    eapply barbedBisimUpTo_many in H11. 2: eassumption.
    destruct H11 as [B'' [A''' [B''' [l'' H11]]]]. destruct_hyps.
    
Admitted.

Lemma barbedBisimUpTo_trans :
  forall U A B C,
    A ~⪯~ B using U -> B ~⪯~ C using U
    -> A ~⪯~ C using U.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [A'' [B'' [lB H1]]]].
    destruct_hyps.
    eapply barbedBisimUpTo_many in H9. 2: eassumption.
    destruct H9 as [C' [B''0 [C'' [lC H9]]]]. destruct_hyps.
    exists C', A'', C'', lC. split. 2: split. 3: split.
    3: assumption.
    (* - clear -H H1 H9 H13 H2 H0.
      destruct H, H1, H9, H13. split.
      + rewrite Forall_forall in *.
        intros. apply H in H9. intro.
        apply H5 in H10; auto.
        
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H1 in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto. *)
    1-2: admit.
    split. 2: split. 1-3: try assumption.
    eapply IH. 2: eassumption.
    apply barbedExpansion_implies_bisim in H15.
Abort. *)

Lemma barbedExpansion_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ⪯ B using U ->
      exists B' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ B' using U /\ length l' <= length l.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
  * exists B, []. split. 2: split. 3: split. 4: split.
    3: constructor.
    3: assumption.
    1-2: split; constructor; auto.
    lia.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H3 in H4 as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl in H12. 2: eassumption.
    destruct H12 as [B'' [l'' H12]].
    destruct_hyps.
    exists B'', (l' ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Qed.

Lemma barbedExpansion_many_sym :
  forall B B' l', B -[l']ₙ->* B' ->
    forall U A, A ⪯ B using U ->
      exists A' l,
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        A -[ l ]ₙ->* A' /\ A' ⪯ B' using U /\ length l' <= length l.
Proof.
  intros B B' l'. revert B B'. induction l'; intros; inv H.
  * exists A, []. split. 2: split. 3: split. 4: split.
    3: constructor.
    3: assumption.
    1-2: split; constructor; auto.
    lia.
  * rename B' into B''. rename n' into B'.
    inv H0. apply H5 in H4 as H'. destruct H' as [A' [l H']]. destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl' in H12. 2: eassumption.
    destruct H12 as [A'' [l'' H12]].
    destruct_hyps.
    exists A'', (l ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Qed.

Lemma barbedExpansion_trans :
  forall U A B C,
    A ⪯ B using U -> B ⪯ C using U
    -> A ⪯ C using U.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedExpansion_many in H10. 2: eassumption.
    destruct H10 as [C' [lC H10]]. destruct_hyps.
    exists C', lC. split. 2: split. 3: split. 4: split.
    4: assumption.
    4: eapply IH; eassumption.
    - inv H0.
      clear -H H1 H10 H12 H2 H16.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H16 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H5 in H12; eauto.
    - inv H0.
      clear -H H1 H10 H12 H2 H16.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H6 in H8. intro.
        now apply H2 in H9.
      + intros. apply H7 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
    - lia.
  * intros. rename B' into C'.
    inv H0. apply H6 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedExpansion_many_sym in H10. 2: eassumption.
    destruct H10 as [A' [lA H10]]. destruct_hyps.
    exists A', lA. split. 2: split. 3: split. 4: split.
    4: assumption.
    4: eapply IH; eassumption.
    - inv H.
      clear -H0 H1 H10 H12 H2 H16.
      destruct H0, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H16 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H7 in H12; eauto.
    - inv H.
      clear -H0 H1 H10 H12 H2 H16.
      destruct H0, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H4 in H8. intro.
        now apply H2 in H9.
      + intros. apply H5 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
    - lia.
  * intros. inv H. inv H0. clear H7 H6 H13 H12 H9 H15.
    specialize (H8 source dest H1 H2) as [sourceB [H8_1 H8_2]].
    specialize (H14 sourceB dest H1 H8_1) as [sourceC [H14_1 H14_2]].
    eexists. split. assumption.
    eapply option_biforall_trans; eauto.
    intros. eapply Signal_eq_trans; eassumption.
  * intros. pose proof H as AB. pose proof H0 as BC.
    inv H. inv H0. clear H7 H6 H13 H12 H8 H14.
    specialize (H15 source dest H1 H2) as [sourceB [lB [B' H14]]]. destruct_hyps.
    eapply barbedExpansion_many_sym in H0. 2: exact AB.
    destruct H0 as [A' [lA H0]]. destruct_hyps.
    inv H13.
    specialize (H21 sourceB dest H1 H6) as [sourceA [lA' [A'' H21]]]. destruct_hyps.
    do 3 eexists. split. 2: split.
    3: {
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
    }
    eapply closureNodeSem_trans; eassumption.
    assumption.
Qed.

Require Export PIDRenaming.

Definition isUsedPool (ι : PID) (Π : ProcessPool) :=
  ι ∉ map_fold (fun k v acc => usedPIDsProc v ++ acc) [] Π.

Definition barbedCongr (U V : list PID) (A B : Node) : Prop :=
  forall C : ProcessPool,
    Forall (fun p => ~isUsedPool p C) V ->
      (A.1, A.2 ∪ C) ~ (B.1, B.2 ∪ C) using U.

(* Lemma barbedBisimUpTo_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B A'' B'', A ⪯ A'' using U -> A'' ~⪯~ B'' using U -> B ⪯ B'' using U ->
      exists B' A''' B''' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ A''' using U /\ A''' ~⪯~ B''' using U /\ B' ⪯ B''' using U.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
  * exists B, A', B, []. split. 2: split. 3: split. 4: split. 5: split.
    3: constructor.
    1-2: split; constructor; auto.
    1-2: inv H3.
    2: { 
    1-2: apply barbedExpansion_refl; now inv H0.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H3 in H4 as H'. destruct H' as [B' [A''0 [B'' [lB H']]]].
    destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl in H6. Unshelve. 3: exact B'. 3: exact U.
    2: { clear -H6 H11 H12 H13.
    destruct H12 as [A'' [l'' H12]].
    destruct_hyps.
    exists A'', (l ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Admitted. *)

(* Lemma barbedBisimUpTo_barbedBisim_helper_asd :
  forall U A B C,
    A ⪯ B using U -> B ~⪯~ C using U
    -> A ~⪯~ C using U.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedBisimUpTo_many in H10. 2: eassumption.
    destruct H10 as [C' [B''0 [C'' [lC H10]]]]. destruct_hyps.
    exists C', A', C'', lC. split. 2: split. 3: split.
    3: assumption.
    1-2: shelve.
    split. 2: split. 2: assumption.
    apply barbedExpansion_refl. now inv H11.
    apply (barbedExpansion_trans _ _ _ _ H11) in H14.
    eapply IH; eassumption.
    Unshelve.
    - inv H0.
      clear -H H1 H10 H12 H2 H17.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H17 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H5 in H12; eauto.
    - inv H0.
      clear -H H1 H10 H12 H2 H17.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H6 in H8. intro.
        now apply H2 in H9.
      + intros. apply H7 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
  * 
Qed. *)

Lemma barbedBisimUpTo_barbedBisim_helper :
  forall U A B C,
    A ~ B using U -> B ~⪯~ C using U
    -> A ~⪯~ C using U.
Proof.
  cofix IH. intros. pose proof H as AB. inv H.
  pose proof H0 as BC. inv H0.
  constructor; auto.
  * split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros.
    clear H5 H6 H7 H11 H12 H13.
    apply H4 in H0. destruct H0 as [B' [l H0]]. destruct_hyps.
   (*  pose proof (barbedBisim_expansion_many _ _ _ H6 _ _ BC).
    destruct H11 as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H7 H14). exists C', l'.
    split. 2: split. 3: split; auto.
    - destruct H0, H5, H11, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H0 in H19. intro.
        now apply H in H20.
      + intros. apply H15 in H21; eauto.
        destruct_hyps. apply H17 in H23; eauto.
    - destruct H0, H5, H11, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H12 in H19. intro.
        now apply H1 in H20.
      + intros. apply H18 in H21; eauto.
        destruct_hyps. apply H16 in H23; eauto.
  * intros.
    epose proof (H5 source dest H0). destruct H14 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    pose proof (barbedBisim_expansion_many _ _ _ H14 _ _ BC) as [C' [Cs ?]]. destruct_hyps.
    pose proof H19 as B'C'. inv H19.
    specialize (H24 sourceB _ H0). destruct H24 as [sourceC [Cs' [C'' ?]]].
    destruct_hyps.
    exists sourceC, (Cs ++ Cs'), C''.
    split.
    - eapply closureNodeSem_trans; eassumption.
    - rewrite <- H24. assumption. (* transitivity is needed here! *)
  * 
  * *)
Admitted.

Lemma barbedBisimUpTo_barbedBisim_helper2 :
  forall U A B C,
    A ~⪯~ B using U -> B ~ C using U
    -> A ~⪯~ C using U.
Proof.
  
Admitted.

Theorem barbedBisimUpTo_barbedBisim :
  forall U A B, A ~⪯~ B using U -> A ~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * clear H4 H6 H5. intros. apply H3 in H as H'.
    destruct H' as [B' [A'' [B'' [l H']]]]. destruct_hyps.
    apply barbedExpansion_implies_bisim in H7, H8.
    (* apply IH in H9.
    exists B', l. do 3 (split; auto).
    eapply barbedBisim_trans. exact H7.
    eapply barbedBisim_trans. exact H9.
    now apply barbedBisim_sym. *)
    exists B', l. do 3 (split; auto).
    eapply barbedBisimUpTo_barbedBisim_helper in H9. 2: eassumption.
    apply barbedBisim_sym in H8.
    eapply barbedBisimUpTo_barbedBisim_helper2 in H9. 2: eassumption.
    now apply IH.
    (* tricks needed to fix guardedness *)
    (* eapply diamond_trans; try eassumption.
    now apply IH. Guarded. *)
    (* inv H9. *)
  * admit.
Admitted.
*)

