From CoreErlang.FrameStack Require Export LogRel SubstSemanticsLemmas.
Import ListNotations.

Lemma Vrel_Var_compat :
  forall Γ n,
  n < Γ ->
  Vrel_open Γ (VVar n) (VVar n).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; simpl; intuition.
  now rewrite Heqs, Heqs0.
Qed.

Global Hint Resolve Vrel_Var_compat : core.

(* TODO NOTE: currently, function arities are not yet checked when doing the substitution, however, this is going to change! *)
Lemma Vrel_FunId_compat :
  forall Γ n a1 a2,
  n < Γ ->
  Vrel_open Γ (VFunId (n, a1)) (VFunId (n, a2)).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; simpl; intuition.
  now rewrite Heqs, Heqs0.
Qed.

Global Hint Resolve Vrel_FunId_compat : core.

Lemma Vrel_Lit_compat_closed :
  forall m l,
  Vrel m (VLit l) (VLit l).
Proof.
  intros. rewrite Vrel_Fix_eq. unfold Vrel_rec. repeat constructor.
  now rewrite Lit_eqb_refl.
Qed.

Global Hint Resolve Vrel_Lit_compat_closed : core.

Lemma Vrel_Lit_compat :
  forall Γ l,
  Vrel_open Γ (VLit l) (VLit l).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Lit_compat : core.

(* Lemma Vrel_Pid_compat_closed :
  forall m p,
  Vrel m (EPid p) (EPid p).
Proof.
  intros. rewrite Vrel_Fix_eq. unfold Vrel_rec. repeat constructor.
Qed.

Global Hint Resolve Vrel_Pid_compat_closed : core.

Lemma Vrel_Pid_compat :
  forall Γ p,
  Vrel_open Γ (EPid p) (EPid p).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Pid_compat : core. *)

Lemma Vrel_Nil_compat_closed:
  forall m, Vrel m VNil VNil.
Proof.
  split; constructor; constructor.
Qed.

Global Hint Resolve Vrel_Nil_compat_closed : core.

Lemma Vrel_Nil_compat :
  forall Γ, Vrel_open Γ VNil VNil.
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Nil_compat : core.

Lemma Vrel_Cons_compat_closed :
  forall m v1 v1' v2 v2', Vrel m v1 v1' -> Vrel m v2 v2'
 ->
  Vrel m (VCons v1 v2) (VCons v1' v2').
Proof.
  intros. rewrite Vrel_Fix_eq. split. 2: split. 1-2: constructor.
  * apply Vrel_closed in H. apply H.
  * apply Vrel_closed in H0. apply H0.
  * apply Vrel_closed in H. apply H.
  * apply Vrel_closed in H0. apply H0.
  * intros. rewrite Vrel_Fix_eq in H. rewrite Vrel_Fix_eq in H0.
    split; [apply H | apply H0].
  Unshelve. all: lia.
Qed.

Global Hint Resolve Vrel_Cons_compat_closed : core.

Lemma Vrel_Cons_compat :
  forall Γ v1 v1' v2 v2', Vrel_open Γ v1 v1' -> Vrel_open Γ v2 v2'
 ->
  Vrel_open Γ (VCons v1 v2) (VCons v1' v2').
Proof.
  intros. unfold Vrel_open. intros. simpl.
  apply Vrel_Cons_compat_closed; [apply H | apply H0]; auto.
Qed.

Global Hint Resolve Vrel_Cons_compat : core.

Ltac simpl_convert_length :=
  match goal with
  | |- context G [Datatypes.length ((convert_to_closlist _) ++ _) ] =>
    unfold convert_to_closlist; rewrite app_length, map_length; try rewrite map_length
  | [H : context G [Datatypes.length ((convert_to_closlist _) ++ _)] |- _] =>
    unfold convert_to_closlist in H; rewrite app_length, map_length,map_length in H
  | |- context G [Datatypes.length (convert_to_closlist _) ] =>
    unfold convert_to_closlist; rewrite map_length,map_length
  | [H : context G [Datatypes.length (convert_to_closlist _)] |- _] =>
    unfold convert_to_closlist in H; rewrite map_length,map_length in H
  end.

Lemma Vrel_Clos_compat :
  forall Γ ext1 ext2 id1 id2 vl1 vl2 b1 b2,
  vl1 = vl2 ->
  Erel_open (length ext1 + vl1 + Γ) b1 b2 ->
  list_biforall (fun '(i, v, e) '(i2, v2, e2) => 
    v = v2 /\ Erel_open (length ext1 + v + Γ) e e2) ext1 ext2 ->
  Vrel_open Γ (VClos ext1 id1 vl1 b1) (VClos ext2 id2 vl2 b2).
Proof.
  unfold Vrel_open. intros. subst.
  revert H1 H0 H2.
  revert ext1 ext2 id1 id2 vl2 b1 b2 ξ₁ ξ₂.
  induction n using Wf_nat.lt_wf_ind. intros.
  subst.
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor; simpl.
    (* scope of environmental extension of closure 1 *)
    + rewrite map_length, map_map, map_map. intros.
      pose proof (biforall_forall _ _ _ (0, 0, `VNil) (0, 0, `VNil) H1 i H3).
      extract_map_fun F.
      replace 0 with (F (0, 0, `VNil)) at 1 by (now subst).
      rewrite map_nth.
      extract_map_fun G.
      replace (`VNil) with (G (0, 0, `VNil)) at 2 by (now subst).
      rewrite map_nth.
      subst F G.
      destruct (nth i ext1 (0, 0, ` VNil)), p.
      destruct (nth i ext2 (0, 0, ` VNil)), p.
      inv H4. cbn. eapply Erel_open_scope in H6 as [H6 _].
      apply -> subst_preserves_scope_exp. exact H6.
      apply upn_scope. now apply H2.
    (* scope of body of closure 1 *)
    + eapply Erel_open_scope in H0 as [H0 _]. rewrite map_length.
      apply -> subst_preserves_scope_exp. exact H0.
      apply upn_scope. now apply H2.
  - apply biforall_length in H1 as H1'. rewrite <- H1' in *.
    constructor; simpl.
  (* scope of environmental extension of closure 2 *)
    + rewrite map_length, map_map, map_map. intros.
      rewrite <- H1' in *.
      pose proof (biforall_forall _ _ _ (0, 0, `VNil) (0, 0, `VNil) H1 i H3).
      extract_map_fun F.
      replace 0 with (F (0, 0, `VNil)) at 1 by (now subst).
      rewrite map_nth.
      extract_map_fun G.
      replace (`VNil) with (G (0, 0, `VNil)) at 2 by (now subst).
      rewrite map_nth.
      subst F G.
      destruct (nth i ext1 (0, 0, ` VNil)), p.
      destruct (nth i ext2 (0, 0, ` VNil)), p.
      inv H4. cbn. eapply Erel_open_scope in H6 as [_ H6].
      apply -> subst_preserves_scope_exp. exact H6.
      apply upn_scope. now apply H2.
    (* scope of body of closure 2 *)
    + eapply Erel_open_scope in H0 as [_ H0]. rewrite map_length.
      apply -> subst_preserves_scope_exp. exact H0.
      rewrite <- H1' in *.
      apply upn_scope. now apply H2.
  - unfold Erel_open, Erel in H0.
    do 2 rewrite subst_comp_exp. epose proof (nH0 := H0 m _ _ _).
    destruct nH0 as [nCl1 [nCl2 nH0]].
    split. 2: split. exact nCl1. exact nCl2. intros. eapply nH0.
    3: exact H6.
    nia. assumption.
  Unshelve.
      subst; apply biforall_length in H4 as Hvl1vl0.
      apply biforall_length in H1 as Hext1ext2.
      split. 2: split.
      (** scopes **)
      1-2: rewrite subst_list_extend; auto;[
        |simpl_convert_length; auto].
      1-2: apply scoped_list_subscoped_eq;[
        simpl_convert_length; auto| |apply H2].
      1-2: rewrite indexed_to_forall; intros.
      1: {
        eapply nth_possibilities_alt in H3 as [[Hs Hnia]|[Hs [Hnia1 Hnia2]]];
        repeat simpl_convert_length; rewrite Hs; clear Hs.
        Unshelve.
        3-4: exact VNil.
        * unfold convert_to_closlist. rewrite map_map.
          extract_map_fun F.
          (* these "strange", big extensions are obtained from the simplification of F! If you rewrite this part, first some default value for d', and then check what is F d', next
          you can modify the chosen d' to fit the purpose of F. 
          This also applies to the other similar places in this proof ↓ *)
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (`VNil)).
          2: rewrite map_length; nia.
          replace (VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (`VNil)) with (F (0, 0, `VNil)) by now subst F.
          rewrite map_nth. destruct (nth i ext1 (0, 0, ` VNil)) eqn:P.
          destruct p. subst F. simpl.
          eapply biforall_forall with (i := i) in H1 as H1'.
          rewrite P in H1'. 2: nia. Unshelve. 2: exact (0, 0, `VNil).
          destruct (nth i ext2 (0, 0, ` VNil)) eqn:P2. destruct p.
          inv H1'. constructor.
          - intros. do 2 rewrite map_map. repeat rewrite map_length in *.
            extract_map_fun F. replace 0 with (F (0, 0, `VNil)) by now subst F.
            rewrite map_nth.
            extract_map_fun G. replace (`VNil) with (G (0, 0, `VNil)) at 3 by now subst G.
            rewrite map_nth.
            destruct (nth i0 ext1 (0, 0, ` VNil)) eqn:P3. destruct p.
            subst F G. cbn.
            eapply biforall_forall with (i := i0) in H1 as H1''. 2: nia.
            rewrite P3 in H1''.
            Unshelve. 2: exact (0, 0, `VNil).
            destruct (nth i0 ext2 (0, 0, ` VNil)). destruct p. inv H1''.
            apply Erel_open_scope in H7 as [H7 _].
            apply -> subst_preserves_scope_exp. exact H7.
            apply upn_scope. apply H2.
          - rewrite map_length. apply -> subst_preserves_scope_exp.
            apply Erel_open_scope in H5 as [H5 _]. exact H5.
            apply upn_scope. apply H2.
        * eapply biforall_forall with (i := i - length ext1) in H4. 2: nia.
          apply Vrel_closed_l in H4. exact H4.
      }
      1: {
        (* this is the symmetric version of the previous proof *)
        eapply nth_possibilities_alt in H3 as [[Hs Hnia]|[Hs [Hnia1 Hnia2]]]; rewrite Hs; clear Hs; repeat simpl_convert_length.
        Unshelve.
        3: exact VNil.
        * unfold convert_to_closlist. rewrite map_map.
          extract_map_fun F.
          (* these "strange", big extensions are obtained from the simplification of F! If you rewrite this part, first some default value for d', and then check what is F d', next
          you can modify the chosen d' to fit the purpose of F. 
          This also applies to the other similar places in this proof ↓ *)
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (`VNil)).
          2: rewrite map_length; nia.
          replace (VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (`VNil)) with (F (0, 0, `VNil)) by now subst F.
          rewrite map_nth. destruct (nth i ext1 (0, 0, ` VNil)) eqn:P.
          destruct p. subst F. simpl.
          eapply biforall_forall with (i := i) in H1 as H1'.
          rewrite P in H1'. 2: nia. Unshelve. 2: exact (0, 0, `VNil).
          destruct (nth i ext2 (0, 0, ` VNil)) eqn:P2. destruct p.
          inv H1'. constructor.
          - intros. do 2 rewrite map_map. repeat rewrite map_length in *.
            extract_map_fun F. replace 0 with (F (0, 0, `VNil)) by now subst F.
            rewrite map_nth.
            extract_map_fun G. replace (`VNil) with (G (0, 0, `VNil)) at 3 by now subst G.
            rewrite map_nth.
            destruct (nth i0 ext1 (0, 0, ` VNil)) eqn:P3. destruct p.
            subst F G. cbn.
            eapply biforall_forall with (i := i0) in H1 as H1''. 2: nia.
            rewrite P3 in H1''.
            Unshelve. 2: exact (0, 0, `VNil).
            destruct (nth i0 ext2 (0, 0, ` VNil)). destruct p. inv H1''.
            apply Erel_open_scope in H7 as [_ H7].
            apply -> subst_preserves_scope_exp. exact H7.
            cbn. rewrite Hext1ext2. apply upn_scope. apply H2.
          - rewrite map_length. apply -> subst_preserves_scope_exp.
            apply Erel_open_scope in H5 as [_ H5]. exact H5.
            rewrite Hext1ext2. apply upn_scope. apply H2.
        * eapply biforall_forall with (i := i - length ext1) in H4. 2: nia.
          apply Vrel_closed_r in H4.
          rewrite <- Hext1ext2. exact H4.
      }
      (** scopes up to this point **)
      intros.
      do 2 (rewrite substcomp_list_eq; [|simpl_convert_length; nia]).
      do 2 rewrite substcomp_id_r.
      epose proof (list_subst_get_possibilities _ _ _) as [[Hs Hnia]|[Hs Hnia]];
      epose proof (list_subst_get_possibilities _ _ _) as [[Hs2 Hnia2]|[Hs2 Hnia2]].
      * rewrite Hs, Hs2.
        eapply nth_possibilities_alt in Hnia as [[Hs3 Hnia3]|[Hs3 [Hnia31 Hnia32]]];
        eapply nth_possibilities_alt in Hnia2 as [[Hs4 Hnia4]|[Hs4 [Hnia41 Hnia42]]].
        + repeat simpl_convert_length. rewrite Hs3, Hs4.
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (`VNil)).
          2: simpl_convert_length; nia.
          unfold convert_to_closlist at 1. rewrite map_map.
          extract_map_fun F.
          replace (VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (`VNil)) with (F (0, 0, `VNil)) by now subst F.
          rewrite map_nth.
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (`VNil)).
          2: simpl_convert_length; nia.
          unfold convert_to_closlist at 1. rewrite map_map.
          extract_map_fun G.
          replace (VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (`VNil)) with (G (0, 0, `VNil)) by now subst G.
          rewrite map_nth.
          destruct (nth x ext1 (0, 0, ` VNil)) eqn:P1.
          destruct (nth x ext2 (0, 0, ` VNil)) eqn:P2.
          destruct p, p0. subst F G. simpl.
          assert (n1 = n3). {
            eapply biforall_forall with (i := x) in H1.
            rewrite P1, P2 in H1. apply H1.
            nia.
          }
          subst.
          apply H; auto.
          2: eapply Grel_downclosed; eauto.
          eapply biforall_forall with (i := x) in H1.
          rewrite P1, P2 in H1. apply H1.
          nia.
        + repeat simpl_convert_length.
          rewrite Hvl1vl0, Hext1ext2 in *. nia.
        + repeat simpl_convert_length.
          rewrite Hvl1vl0, Hext1ext2 in *. nia.
        + rewrite Hs3, Hs4. repeat simpl_convert_length.
          do 2 rewrite map_length.
          eapply biforall_forall in H4. rewrite Hext1ext2. exact H4.
          nia.
      * repeat simpl_convert_length. nia.
      * shelve. (* we prove this after the next goal *)
      * rewrite Hs, Hs2. repeat simpl_convert_length.
        rewrite app_length, map_length, map_length.
        destruct H2 as [Hss1 [Hss2 Hrel]].
        specialize (Hrel (x - (length ext1 + length vl1)) ltac:(nia)).
        rewrite Hext1ext2, Hvl1vl0 in *.
        repeat break_match_goal; trivial.
        eapply Vrel_downclosed; eassumption.
  Unshelve.
  1: exact VNil.
  1,3: nia.
  repeat simpl_convert_length. nia.
Qed.

Global Hint Resolve Vrel_Clos_compat : core.

Lemma Vrel_Tuple_compat_closed :
  forall m l l', list_biforall (Vrel m) l l'
 ->
  Vrel m (VTuple l) (VTuple l').
Proof.
  intros. induction H; rewrite Vrel_Fix_eq; simpl; intuition.
  * constructor. intros. inv H.
  * constructor. intros. inv H.
  * constructor. intros. destruct i.
    - now apply Vrel_closed_l in H.
    - simpl. apply Vrel_closed_l in IHlist_biforall. destruct_scopes.
      apply H4. simpl in H1. nia.
  * constructor. intros. destruct i.
    - now apply Vrel_closed_r in H.
    - simpl. apply Vrel_closed_r in IHlist_biforall. destruct_scopes.
      apply H4. simpl in H1. nia.
  * now rewrite <- Vrel_Fix_eq.
  * rewrite Vrel_Fix_eq in IHlist_biforall.
    apply IHlist_biforall.
Qed.

Global Hint Resolve Vrel_Tuple_compat_closed : core.

Lemma Vrel_Tuple_compat :
  forall Γ l l', list_biforall (Vrel_open Γ) l l'
->
  Vrel_open Γ (VTuple l) (VTuple l').
Proof.
  intros. unfold Vrel_open. intros. simpl.
  apply Vrel_Tuple_compat_closed.
  eapply biforall_map. exact H. intros. auto.
Qed.

Global Hint Resolve Vrel_Tuple_compat : core.

Lemma Vrel_Map_compat_closed :
  forall m l l',
  list_biforall (fun '(v1, v2) '(v1', v2') => Vrel m v1 v1' /\ Vrel m v2 v2') l l'
 ->
  Vrel m (VMap l) (VMap l').
Proof.
  intros. induction H; rewrite Vrel_Fix_eq; simpl; intuition.
  * constructor; intros; inv H.
  * constructor; intros; inv H.
  * destruct IHlist_biforall as [? [? _]]. destruct hd, hd', H.
    apply Vrel_closed_l in H. apply Vrel_closed_l in H3.
    destruct_scopes.
    constructor; intros; simpl in *; destruct i; auto.
    - apply H4. nia.
    - apply H8. nia.
  * destruct IHlist_biforall as [? [? _]]. destruct hd, hd', H.
    apply Vrel_closed_r in H. apply Vrel_closed_r in H3.
    destruct_scopes.
    constructor; intros; simpl in *; destruct i; auto.
    - apply H5. nia.
    - apply H7. nia.
  * destruct hd, hd'. do 2 rewrite <- Vrel_Fix_eq. intuition.
    rewrite Vrel_Fix_eq in IHlist_biforall.
    apply IHlist_biforall.
Qed.

Global Hint Resolve Vrel_Map_compat_closed : core.

Lemma Vrel_Map_compat :
  forall Γ l l',
  list_biforall (fun '(v1, v2) '(v1', v2') => Vrel_open Γ v1 v1' /\ Vrel_open Γ v2 v2') l l'
 ->
  Vrel_open Γ (VMap l) (VMap l').
Proof.
  intros. unfold Vrel_open. intros. simpl.
  apply Vrel_Map_compat_closed.
  eapply biforall_map. exact H. intros. destruct x, y, H1. split; auto.
Qed.

Global Hint Resolve Vrel_Map_compat : core.

#[global]
Hint Constructors list_biforall : core.

Lemma Erel_Val_compat_closed :
  forall {n v v'},
    Vrel n v v' ->
    Erel n (`v) (`v').
Proof.
  intros.
  unfold Erel, exp_rel.
  pose proof (Vrel_possibilities H).
  intuition eauto.
  * destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]].
    inv H3. 2: { inv H1. }
    eapply HD1 in H5 as [k' HDF]; [|nia|].
    eexists. constructor. exact HDF.
    now constructor.
  * do 2 unfold_hyps. subst.
    destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]].
    inv H2. 2: { inv H0. }
    eapply HD1 in H3 as [k' HDF]; [|nia|].
    eexists. constructor. exact HDF.
    now constructor.
  * do 5 unfold_hyps. subst.
    destruct H0 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H3 as [k' HDF]; [|nia|].
    eexists. constructor. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
  * do 3 unfold_hyps. subst.
    destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H3 as [k' HDF]; [|nia|].
    eexists. constructor. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
  * do 3 unfold_hyps. subst.
    destruct H0 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H3 as [k' HDF]; [|nia|].
    eexists. constructor. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
  * do 9 unfold_hyps. subst.
    destruct H0 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H3 as [k' HDF]; [|nia|].
    eexists. constructor. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
Unshelve.
  all: nia.
Qed.

Global Hint Resolve Erel_Val_compat_closed : core.

Lemma Erel_Val_compat :
  forall {Γ v v'},
    Vrel_open Γ v v' ->
    Erel_open Γ (`v) (`v').
Proof.
  intros.
  unfold Erel_open, Vrel_open in *; intros.
  simpl. now apply Erel_Val_compat_closed, H.
Qed.

Global Hint Resolve Erel_Val_compat : core.

Lemma match_pattern_Vrel : forall p v1 v2 n,
  Vrel n v1 v2 ->
  (forall l1, 
        (match_pattern p v1 = Some l1 ->
         exists l2, match_pattern p v2 = Some l2 /\ list_biforall (Vrel n) l1 l2)).
Proof.
  intros.
  assert (VALCLOSED v1) by (eapply Vrel_closed in H; apply H).
  assert (VALCLOSED v2) by (eapply Vrel_closed in H; apply H).
  generalize dependent v2. revert n. generalize dependent v1. revert l1. generalize dependent p.
  induction p using Pat_ind2 with
    (Q := Forall (fun p => 
      forall (l1 : list Val) (v1 : Val),
      match_pattern p v1 = Some l1 ->
      VALCLOSED v1 ->
      forall (n : nat) (v2 : Val),
      Vrel n v1 v2 ->
      VALCLOSED v2 ->
      exists l2 : list Val,
        match_pattern p v2 = Some l2 /\ list_biforall (Vrel n) l1 l2))
    (R := Forall (fun '(p1, p2) =>
      (forall (l1 : list Val) (v1 : Val),
      match_pattern p1 v1 = Some l1 ->
      VALCLOSED v1 ->
      forall (n : nat) (v2 : Val),
      Vrel n v1 v2 ->
      VALCLOSED v2 ->
      exists l2 : list Val,
      match_pattern p1 v2 = Some l2 /\ list_biforall (Vrel n) l1 l2) /\
      (forall (l1 : list Val) (v1 : Val),
      match_pattern p2 v1 = Some l1 ->
      VALCLOSED v1 ->
      forall (n : nat) (v2 : Val),
      Vrel n v1 v2 ->
      VALCLOSED v2 ->
      exists l2 : list Val,
      match_pattern p2 v2 = Some l2 /\ list_biforall (Vrel n) l1 l2)

    )); intros.
  7-10: auto.
  1-2,4-6: destruct v1, v2; inv H0; rewrite Vrel_Fix_eq in H; destruct H as [_ [_ ?]]; try contradiction.
  * eexists. split. reflexivity. auto.
  * do 2 break_match_hyp; try congruence. 2: contradiction.
    inv H4. apply Lit_eqb_eq in Heqb0. apply Lit_eqb_eq in Heqb. subst.
    eexists. split. simpl. rewrite Lit_eqb_refl. reflexivity. auto.
  * break_match_hyp; try congruence.
    break_match_hyp; try congruence. inv H4.
    inv H. destruct_scopes. rewrite <- Vrel_Fix_eq in H0.
    rewrite <- Vrel_Fix_eq in H3.
    eapply IHp1 in H0. eapply IHp2 in H3. all:eauto.
    do 4 unfold_hyps.
    eexists. split. simpl. rewrite H0, H. reflexivity.
    now apply biforall_app.
  * destruct_scopes. generalize dependent l0.
    generalize dependent l2. revert l1. induction l; intros.
    - destruct l0, l2; try congruence. 2: contradiction.
      inv H4. exists []. split; auto.
    - inv IHp.
      destruct l0, l2; try congruence. 1: contradiction.
      repeat break_match_hyp; try congruence. inv H4.
      unfold_hyps.
      eapply IHl in Heqo0. 4: eassumption. 2: assumption.
      2-3: intros; try apply (H3 (S i) ltac:(snia));
                       apply (H5 (S i) ltac:(snia)).
      destruct Heqo0 as [binds [Eq1 Eq2]].
      eapply H2 in Heqo as [binds0 [Eq01 Eq02]].
      3: rewrite Vrel_Fix_eq; exact H.
      2: now apply (H3 0 ltac:(snia)).
      2: now apply (H5 0 ltac:(snia)).
      simpl. simpl in Eq1. rewrite Eq01, Eq1.
      eexists. split. reflexivity. now apply biforall_app.
  * destruct_scopes. generalize dependent l0.
    generalize dependent l2. revert l1. induction l; intros.
    - destruct l0, l2; try congruence. 2: contradiction.
      inv H4. exists []. split; auto.
    - destruct_foralls. destruct a.
      destruct l0, l2; try congruence. 1: destruct p1; contradiction.
      repeat break_match_hyp; try congruence. inv H4.
      do 3 unfold_hyps.
      eapply IHl in Heqo1. 5: eassumption. all: try assumption.
      2: intros; apply (H3 (S i) ltac:(snia)).
      2: intros; apply (H6 (S i) ltac:(snia)).
      2: intros; apply (H2 (S i) ltac:(snia)).
      2: intros; apply (H7 (S i) ltac:(snia)).
      destruct Heqo1 as [binds [Eq1 Eq2]].
      eapply H0 in Heqo as [binds0 [Eq01 Eq02]].
      eapply H1 in Heqo0 as [binds1 [Eq11 Eq12]].
      3: rewrite Vrel_Fix_eq; exact H4.
      5: rewrite Vrel_Fix_eq; exact H.
      2: now apply (H7 0 ltac:(snia)).
      2: now apply (H6 0 ltac:(snia)).
      2: now apply (H2 0 ltac:(snia)).
      2: now apply (H3 0 ltac:(snia)).
      simpl. simpl in Eq1. rewrite Eq01, Eq11, Eq1.
      eexists. split. reflexivity. apply biforall_app; auto.
      now apply biforall_app.
  * simpl in *. inv H0. exists [v2]. split; auto.
Qed.

Corollary match_pattern_list_Vrel : forall pl vl1 vl2 n,
  list_biforall (Vrel n) vl1 vl2 ->
  (forall l1, 
        (match_pattern_list pl vl1 = Some l1 ->
         exists l2, match_pattern_list pl vl2 = Some l2 /\
                    list_biforall (Vrel n) l1 l2)).
Proof.
  induction pl; intros.
  * inv H. 2: inv H0. eexists. split. reflexivity.
    inv H0. now auto.
  * simpl in H0. inv H. congruence.
    repeat break_match_hyp; try congruence. inv H0.
    eapply match_pattern_Vrel in Heqo as [l2 [HH LB]].
    2: exact H1.
    eapply IHpl in Heqo0 as [l3 [HH2 LB2]]. 2: exact H2.
    eexists. split. simpl. rewrite HH, HH2. reflexivity.
    now apply biforall_app.
Qed.

Lemma nomatch_pattern_Vrel : forall p v1 v2 n,
  Vrel n v1 v2 ->
  match_pattern p v1 = None -> match_pattern p v2 = None.
Proof.
  intros.
  assert (VALCLOSED v1) by (eapply Vrel_closed in H; apply H).
  assert (VALCLOSED v2) by (eapply Vrel_closed in H; apply H).
  generalize dependent v2. revert n. generalize dependent v1.
  induction p using Pat_ind2 with
    (Q := Forall (
      fun p => forall v1 : Val,
                match_pattern p v1 = None ->
                VALCLOSED v1 ->
                forall (n : nat) (v2 : Val),
                Vrel n v1 v2 -> VALCLOSED v2 -> match_pattern p v2 = None
    ))
    (R := Forall (
      fun '(p1, p2) => 
      (forall v1 : Val,
      match_pattern p1 v1 = None ->
      VALCLOSED v1 ->
      forall (n : nat) (v2 : Val),
      Vrel n v1 v2 -> VALCLOSED v2 -> match_pattern p1 v2 = None)
      /\
      (forall v1 : Val,
      match_pattern p2 v1 = None ->
      VALCLOSED v1 ->
      forall (n : nat) (v2 : Val),
      Vrel n v1 v2 -> VALCLOSED v2 -> match_pattern p2 v2 = None)
    )); intros; auto.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition.
    do 2 break_match_hyp; try congruence. 2: contradiction.
    rewrite Lit_eqb_eq in Heqb; subst. now rewrite Heqb0.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition. destruct_scopes. proof_irr_many.
    break_match_hyp; try congruence.
    break_match_hyp; try congruence.
    - eapply IHp2 in Heqo0. rewrite Heqo0. all: auto.
      now break_match_goal.
      rewrite Vrel_Fix_eq. eassumption.
    - eapply IHp1 in Heqo. now rewrite Heqo. all: auto.
      rewrite Vrel_Fix_eq. eassumption.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition. destruct_scopes. proof_irr_many.
    generalize dependent l0. generalize dependent l1. induction l; intros.
    - destruct l1; auto. destruct l0; auto. contradiction.
    - destruct_foralls.
      destruct l0.
      + destruct l1; auto. contradiction.
      + destruct l1; auto.
        destruct (match_pattern a v) eqn:D1.
        ** break_match_goal; auto.
           unfold_hyps.
           break_match_hyp. congruence.
           eapply (IHl H6) in Heqo0. now rewrite Heqo0.
           now (intros; apply (H4 (S i) ltac:(snia))).
           eassumption.
           now (intros; apply (H3 (S i) ltac:(snia))).
        ** eapply H2 in D1. now rewrite D1.
           now apply (H3 0 ltac:(snia)).
           now (rewrite Vrel_Fix_eq; apply H5).
           now apply (H4 0 ltac:(snia)).
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition. destruct_scopes. proof_irr_many.
    generalize dependent l0. generalize dependent l1. induction l; intros.
    - destruct l1; auto. destruct l0; auto. destruct p; contradiction.
    - destruct_foralls.
      destruct l0.
      + destruct l1; auto. contradiction.
      + destruct l1; destruct a; auto.
        destruct p0, p. do 3 unfold_hyps.
        destruct (match_pattern p1 v1) eqn:D1.
        ** destruct (match_pattern p2 v2) eqn:D2.
           -- break_match_goal; auto.
              break_match_hyp. congruence.
              eapply (IHl H6) in Heqo0. rewrite Heqo0.
              now break_match_goal.
              now (intros; apply (H3 (S i) ltac:(snia))).
              now (intros; apply (H10 (S i) ltac:(snia))).
              eassumption.
              now (intros; apply (H2 (S i) ltac:(snia))).
              now (intros; apply (H11 (S i) ltac:(snia))).
           -- eapply H1 in D2. rewrite D2.
              now break_match_goal.
              now apply (H11 0 ltac:(snia)).
              now (rewrite Vrel_Fix_eq; eassumption).
              now apply (H10 0 ltac:(snia)).
        ** eapply H in D1. now rewrite D1.
           now apply (H2 0 ltac:(snia)).
           now (rewrite Vrel_Fix_eq; eassumption).
           now apply (H3 0 ltac:(snia)).
Qed.

Corollary nomatch_pattern_list_Vrel : forall pl vl1 vl2 n,
  list_biforall (Vrel n) vl1 vl2 ->
  match_pattern_list pl vl1 = None -> match_pattern_list pl vl2 = None.
Proof.
  intros pl vl1 vl2 n H. revert pl. induction H; simpl; intros.
  * now auto.
  * destruct pl.
    - now auto.
    - simpl in *. break_match_hyp.
      + break_match_hyp. congruence.
        apply IHlist_biforall in Heqo0. break_match_goal; auto.
        now rewrite Heqo0.
      + eapply nomatch_pattern_Vrel in Heqo. now rewrite Heqo. 
        eassumption. 
Qed.

Lemma Erel_Case_compat_closed : forall n e1 e1' l l',
    Erel n e1 e1' ->
    list_biforall (
      fun '(p, g, e) '(p', g', e') => p = p' /\
        forall m (Hmn : m <= n) vl vl',
        length vl = PatListScope p ->
        list_biforall (Vrel m) vl vl' ->
        Erel m g.[list_subst vl idsubst] g'.[list_subst vl' idsubst] /\ 
        Erel m e.[list_subst vl idsubst] e'.[list_subst vl' idsubst]
    ) l l' ->
    Erel n (ECase e1 l) (ECase e1' l').
Proof.
  intros.
  destruct H as [He1 [He1' HErel1]].
  apply biforall_length in H0 as Hlen.
  split. 2: split. 1-2: do 2 constructor; auto.
  (* scopes: *)
  1-4: intros; eapply biforall_forall with
     (d1 := ([]:list Pat, `VNil, `VNil))
     (d2 := ([]:list Pat, `VNil, `VNil)) in H0; [|try eassumption].
  4,6: rewrite Hlen; exact H.
  1-4: do 2 rewrite map_nth with (d := ([]:list Pat, `VNil, `VNil)).
  1-4: destruct nth, nth, p, p0, H0; cbn; subst.
  1-4: pose proof (repeat_length VNil (PatListScope l1)).
  1-4: pose proof (Forall_repeat (fun v => VALCLOSED v) VNil (PatListScope l1) ltac:(constructor)) as Fr.
  1-4: rewrite Nat.add_0_r.
  1-4: assert (list_biforall (Vrel 0) (repeat VNil (PatListScope l1)) (repeat VNil (PatListScope l1))) as H'H by
    (clear; induction (PatListScope l1); simpl; constructor; auto).
  1-4: apply H1 in H'H as [H'1 H'2]; [|lia|now rewrite repeat_length].
  1-4: apply Erel_closed in H'1 as [H'11 H'12], H'2 as [H'21 H'22].
  1-4: fold (PatListScope l1); rewrite <- H0; now apply subst_implies_list_scope.
  (* evaluation: *)
  intros.
  inv H1; try inv_val.
  eapply HErel1 in H6 as [k1 D].
  1: eexists; constructor; exact D.
  1: lia.
  (* second step *)
  clear H6 He1 He1' HErel1 e1 e1'.
  (* scopes (boiler plate, TODO: extract it to assertions): *)
  split. 2: split.
  1-2: constructor; [constructor|apply H].
  1-4: intros; eapply biforall_forall with
     (d1 := ([]:list Pat, `VNil, `VNil))
     (d2 := ([]:list Pat, `VNil, `VNil)) in H0; [|try eassumption].
  4,6: rewrite Hlen; exact H1.
  1-4: do 2 rewrite map_nth with (d := ([]:list Pat, `VNil, `VNil)).
  1-4: destruct nth, nth, p, p0, H0; cbn; subst.
  1-4: pose proof (repeat_length VNil (PatListScope l1)).
  1-4: pose proof (Forall_repeat (fun v => VALCLOSED v) VNil (PatListScope l1) ltac:(constructor)) as Fr.
  1-4: assert (list_biforall (Vrel 0) (repeat VNil (PatListScope l1)) (repeat VNil (PatListScope l1))) as H'H by
    (clear; induction (PatListScope l1); simpl; constructor; auto).
  1-4: apply H2 in H'H as [H'1 H'2]; [|lia|now rewrite repeat_length].
  1-4: apply Erel_closed in H'1 as [H'11 H'12], H'2 as [H'21 H'22].
  1-4: fold (PatListScope l1); rewrite <- H0; now apply subst_implies_list_scope.
  (* evaluation *)
  generalize dependent k.
  induction H0; split; intros.
  * inv H1. destruct H as [_ [_ [_ H]]].
    eapply H in H4. destruct H4 as [k2 D]. eexists. constructor. exact D.
    lia. unfold if_clause. split; auto. intros. split; apply Vrel_Lit_compat_closed.
  * inv H1. destruct H as [_ [_ [_ H]]].
    eapply H in H7. destruct H7 as [k2 D]. eexists. constructor. 
    congruence. exact D.
    lia. fold (Excrel k0 e1 e2). eapply Excrel_downclosed. exact H0.
    Unshelve. lia.
  * destruct hd as [p e1], hd' as [p0 e2].
    destruct p as [p1 g1], p0 as [p2 g2].
    simpl in Hlen. destruct H. subst.
    inv H3.
    - apply match_pattern_list_length in H11 as Hlen2.
      eapply match_pattern_list_Vrel in H11 as H11'. 2: exact H2.
      destruct H11' as [vs [Hvs HLB]].
      apply biforall_length in HLB as Hlen3.
      specialize (H4 (S k0) ltac:(lia) _ _ (eq_sym Hlen2) HLB)
        as [[Hclg1 [Hclg2 Hg]] [Hcle1 [Hcle2 He]]].
      eapply Hg in H12 as [k3 D]. eexists. econstructor.
      eassumption.
      exact D.
      lia.
      (* step 3, scopes again *)
      apply biforall_vrel_closed in H2 as Hcl. destruct Hcl as [HHcl1 HHcl2].
      apply biforall_vrel_closed in HLB as Hcl. destruct Hcl as [HHcl3 HHcl4].
      split. 2: split.
      1-2: constructor; [constructor | apply H1]; auto.
      2,6: eexists; eassumption.
      1,4: rewrite Hlen2.
      2: rewrite Hlen3.
      1-2: apply subst_implies_list_scope; auto.
      (* boiler plate *)
      1-4: intros; eapply biforall_forall with
        (d1 := ([]:list Pat, `VNil, `VNil))
        (d2 := ([]:list Pat, `VNil, `VNil)) in H0; [|try eassumption].
      4,6: assert (length tl = length tl') as Hlen' by lia;
           rewrite Hlen'; exact H.
      1-4: do 2 rewrite map_nth with (d := ([]:list Pat, `VNil, `VNil)).
      1-4: destruct nth, nth, p, p0, H0; cbn; subst.
      1-4: pose proof (repeat_length VNil (PatListScope l0)).
      1-4: pose proof (Forall_repeat (fun v => VALCLOSED v) VNil (PatListScope l0) ltac:(constructor)) as Fr.
      1-4: assert (list_biforall (Vrel 0) (repeat VNil (PatListScope l0)) (repeat VNil (PatListScope l0))) as H'H by
        (clear; induction (PatListScope l0); simpl; constructor; auto).
      1-4: apply H3 in H'H as [H'1 H'2]; [|lia|now rewrite repeat_length].
      1-4: apply Erel_closed in H'1 as [H'11 H'12], H'2 as [H'21 H'22].
      1-4: fold (PatListScope l0); rewrite <- H0; now apply subst_implies_list_scope.
      (* evaluation *)
      split.
      + (* valid *)
        intros. inv H3.
        ** (* true guard *)
           inv H. inv H7.
           destruct hd'; simpl in H5; destruct H5 as [_ [_ H5]];
           try contradiction.
           break_match_hyp. 2: contradiction. apply Lit_eqb_eq in Heqb.
           subst.
           rewrite H13 in H11. inv H11.
           eapply He in H14 as [k4 D]. eexists. econstructor.
           eassumption.
           exact D.
           lia.
           fold (Frel k1 F1 F2). eapply Frel_downclosed. exact H1.
           Unshelve. lia.
        ** (* false guard *)
           inv H. inv H7.
           destruct hd'; simpl in H5; destruct H5 as [_ [_ H5]];
           try contradiction.
           break_match_hyp. 2: contradiction. apply Lit_eqb_eq in Heqb.
           subst.
           eapply IHlist_biforall in H13 as [k4 D].
           eexists. constructor. exact D.
           lia.
           2: exact H1.
           1-2: lia.
           eapply biforall_impl. 2: exact H2.
           intros. eapply Vrel_downclosed. exact H3. Unshelve. lia.
      + (* exception *)
        intros. inv H3. eapply H1 in H9 as [k4 D]. eexists. constructor.
        congruence.
        exact D.
        lia.
        fold (Excrel k1 e0 e3). eapply Excrel_downclosed. exact H.
        Unshelve. lia.
    - eapply nomatch_pattern_list_Vrel in H11 as H11'. 2: exact H2.
      eapply IHlist_biforall in H12 as [k4 D].
      eexists. constructor; auto. exact D.
      lia.
      2: exact H1.
      1-2: lia.
      eapply biforall_impl; [|exact H2].
      intros; eapply Vrel_downclosed; eassumption.
      Unshelve. lia.
  * inv H3. eapply H1 in H9 as [k4 D]. eexists. constructor.
    congruence.
    exact D.
    lia.
    fold (Excrel k0 e1 e2). eapply Excrel_downclosed. exact H2.
    Unshelve. lia.
Qed.
(* lessons learned from the proof above:
    reasoning about scopes is long and repetitive.
    reasoning about the evaluation is quite simple, and nice *)

Global Hint Resolve Erel_Case_compat_closed : core.

Lemma Erel_Case_compat : forall Γ e1 e1' l l',
  Erel_open Γ e1 e1' ->
  list_biforall (
    fun '(p, g, e) '(p', g', e') =>
      p = p' /\ Erel_open (PatListScope p + Γ) g g' /\
      Erel_open (PatListScope p + Γ) e e'
  ) l l' ->
  Erel_open Γ (ECase e1 l) (ECase e1' l').
Proof.
  intros.
  unfold Erel_open.
  intros. cbn.
  apply biforall_length in H0 as Hlen.
  eapply Erel_Case_compat_closed; auto.
  apply forall_biforall with (d1 := ([], `VNil, `VNil)) (d2 := ([], `VNil, `VNil)).
  now do 2 rewrite map_length.
  rewrite map_length. intros.
  apply biforall_forall with
    (i := i) (d1 := ([], `VNil, `VNil)) (d2 := ([], `VNil, `VNil)) in H0; auto.
  extract_map_fun F.
  replace ([], `VNil, `VNil) with (F ([], `VNil, `VNil)) by now subst F.
  rewrite map_nth. (* replace does not work at position 1, its buggy *)
  extract_map_fun G.
  replace (F ([], `VNil, `VNil)) with (G ([], `VNil, `VNil)) by now subst F G.
  rewrite map_nth. subst F G. simpl.
  destruct nth, p, nth, p, H0, H3. subst.
  split. reflexivity.
  intros. repeat rewrite subst_comp_exp. split.
  * apply H3. apply Grel_list_subst; auto.
    eapply Grel_downclosed; eassumption.
  * apply H4. apply Grel_list_subst; auto.
    eapply Grel_downclosed; eassumption.
 Unshelve. all: lia.
Qed.

Global Hint Resolve Erel_Case_compat : core.


Lemma Erel_Var_compat :
  forall Γ n,
    n < Γ ->
    Erel_open Γ (`VVar n) (`VVar n).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_Var_compat : core.

(* TODO NOTE: currently, function arities are not yet checked when doing the substitution, however, this is going to change! *)
Lemma Erel_FunId_compat :
  forall Γ n a,
    n < Γ ->
    Erel_open Γ (`VFunId (n, a)) (`VFunId (n, a)).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_FunId_compat : core.

Lemma Erel_Lit_compat :
  forall Γ l,
    Erel_open Γ (`VLit l) (`VLit l).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_Lit_compat : core.

Lemma Erel_Fun_compat :
  forall Γ (vl vl' : nat) b b',
    vl = vl' ->
    Erel_open (vl + Γ) b b' ->
    Erel_open Γ (EFun vl b) (EFun vl' b').
Proof.
  intros. subst. unfold Erel_open.
  intros. split. 2: split.
  1-2: simpl; do 2 constructor.
  1-2: eapply Erel_open_scope in H0.
  1-2: apply -> subst_preserves_scope_exp; [apply H0|apply upn_scope;apply H].
  simpl; intros. inv H2. 2: { inv H3. } destruct H1 as [_ [_ [H1 _]]].
  eapply H1 in H7 as [k' HD]. eexists. constructor. exact HD.
  nia.
  constructor; auto.
  rewrite Vrel_Fix_eq. simpl.
  split. 2: split.
  1-2: constructor; simpl; try (intro; nia).
  1-2: apply Erel_open_scope in H0; apply -> subst_preserves_scope_exp.
  1,3: apply H0.
  1,2: apply upn_scope; apply H.
  intuition. unfold Erel_open, Erel in H0.
  do 2 rewrite subst_comp_exp. apply H0.
  apply Grel_list_subst; auto. eapply Grel_downclosed in H. eassumption.
  Unshelve. nia.
Qed.

Global Hint Resolve Erel_Fun_compat : core.

Lemma Erel_Let_compat_closed :
  forall n x y (e2 e2' : Exp), x = y ->
    (forall m (Hmn : m <= n) vl vl',
        length vl = x ->
        list_biforall (Vrel m) vl vl' ->
        Erel m e2.[list_subst vl idsubst]
               e2'.[list_subst vl' idsubst]) ->
    forall m (Hmn : m <= n) e1 e1',
      Erel m e1 e1' ->
      Erel m (ELet x e1 e2) (ELet y e1' e2').
Proof.
  intros n y x e2 e2' Hs. subst. intros.
  destruct (Erel_closed H0) as [IsClosed_e1 IsClosed_e2].
  unfold Erel, exp_rel.
  assert (list_biforall (Vrel 0) (repeat VNil x) (repeat VNil x)) as H'H. {
    clear. induction x; simpl; constructor; auto.
  }
  epose proof (H 0 ltac:(lia) (repeat VNil x) (repeat VNil x) _ H'H) as H'.
  Unshelve.
  2: { now rewrite repeat_length. }
  split. 2: split.
  * apply Erel_closed_l in H'. do 2 constructor; auto.
    pose proof (repeat_length VNil x). rewrite <- H1, Nat.add_0_r.
    pose proof (Forall_repeat (fun v => VALCLOSED v) VNil x ltac:(constructor)) as Fr.
    now apply subst_implies_list_scope.
  * apply Erel_closed_r in H'. do 2 constructor; auto.
    pose proof (repeat_length VNil x). rewrite <- H1, Nat.add_0_r.
    pose proof (Forall_repeat (fun v => VALCLOSED v) VNil x ltac:(constructor)) as Fr.
    now apply subst_implies_list_scope.
  * intros. destruct m0; inv H2. inv_val. subst.
    destruct H0 as [_ [_ H0]].
    eapply H0 in H5 as [x0 D]. exists (S x0). constructor. exact D.
    lia.

    apply Erel_closed_l in H' as e1H.
    apply subst_implies_list_scope in e1H. 2: apply Forall_repeat; auto.
    apply Erel_closed_r in H' as e2H.
    apply subst_implies_list_scope in e2H. 2: apply Forall_repeat; auto.
    destruct H1 as [Hcl3 [Hcl4 [H1_1 H1_2]]].
    rewrite repeat_length in e1H, e2H.
    split. 2: split. 1-2: constructor; auto; now constructor.
    split.
    - (* normal evaluation of e1 *)
      intros. inv H2.
      eapply biforall_impl in H1. 2: {
        intros. eapply Vrel_downclosed. exact H2.
      }
      eapply (H k ltac:(lia) _ _ _ H1) in H10. 2: lia.
      destruct H10 as [x1 D]. eexists. constructor.
      1: now apply biforall_length in H1.
      1: exact D.
      fold (Frel k F1 F2). eapply Frel_downclosed.
      split. 2: split. 1-2: assumption. split; eassumption.
    - (* exception e1 *)
      intros. inv H2.
      eapply H1_2 in H9 as [x0 D]. 
      1: { eexists. constructor. congruence. exact D. }
      1: lia.
      fold (Excrel k e0 e3). eapply Excrel_downclosed. apply H1.
  Unshelve.
  all: lia.
Qed.

Global Hint Resolve Erel_Let_compat_closed : core.


Lemma Erel_Let_compat :
  forall Γ x x' (e1 e1' e2 e2': Exp),
    x = x' ->
    Erel_open Γ e1 e1' ->
    Erel_open (x + Γ) e2 e2' ->
    Erel_open Γ (ELet x e1 e2) (ELet x' e1' e2').
Proof.
  intros. subst.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_Let_compat_closed; auto.
  intros.
  apply biforall_length in H3 as Hl.
  do 2 rewrite subst_comp_exp.
  rewrite subst_list_extend; auto.
  rewrite subst_list_extend. 2: now rewrite <- Hl.
  apply H1.
  apply biforall_vrel_closed in H3 as H3'. destruct H3' as [Hvl Hvl'].
  split. 2: split.
  1-2: apply scoped_list_subscoped_eq; auto; try lia; apply H.
  intros.
  assert (x < x' \/ x >= x') as [Hlia1 | Hlia2] by lia.
  - rewrite list_subst_lt, list_subst_lt. 2-3: lia.
    eapply biforall_forall in H3. exact H3. lia.
  - rewrite list_subst_ge, list_subst_ge. 2-3: lia.
    destruct H as [_ [_ H]]. rewrite Hl.
    specialize (H (x - length vl') ltac:(lia)).
    repeat break_match_goal; try contradiction.
    eapply Vrel_downclosed. eassumption.
  Unshelve.
  lia.
Qed.

Global Hint Resolve Erel_Let_compat : core.

(* TODO: 0 identifiers are going to change *)
Lemma Erel_LetRec_compat_closed :
  forall n l l' (e e' : Exp) m (Hmn : m <= n),
  (* scope of the closure lists is necessary: *)
    Forall (fun '(vl, e) => EXP length l + vl ⊢ e) l  ->
    Forall (fun '(vl, e) => EXP length l' + vl ⊢ e) l' -> 
    Erel m e.[list_subst (convert_to_closlist (map (fun '(x,y) => (0,x,y)) l)) idsubst]
           e'.[list_subst (convert_to_closlist (map (fun '(x,y) => (0,x,y)) l')) idsubst] ->
    Erel m (ELetRec l e) (ELetRec l' e').
Proof.
  intros.
  unfold Erel, exp_rel.
  (* scopes: *)
  apply Erel_closed in H1 as HH. destruct HH as [H_1 H_2].
  apply subst_implies_list_scope in H_1, H_2.
  2: {
    rewrite indexed_to_forall.
    rewrite indexed_to_forall in H0. intros.
    unfold convert_to_closlist in *. repeat rewrite map_length in *.
    apply H0 in H2 as H2'.
    instantiate (1 := VClos (map (fun '(x, y) => (0, x, y)) l') 0 0 (`VNil)).
    Unshelve. 2: exact (0, `VNil).
    rewrite map_map.
    rewrite map_nth with (d := (0, `VNil)).
    destruct nth. constructor.
    * intros. rewrite map_length in *.
      do 2 rewrite map_map. apply H0 in H3.
      do 2 rewrite map_nth with (d := (0, `VNil)). destruct nth.
      now rewrite Nat.add_0_r.
    * now rewrite map_length, Nat.add_0_r.
  }
  2: {
    rewrite indexed_to_forall.
    rewrite indexed_to_forall in H. intros.
    unfold convert_to_closlist in *. repeat rewrite map_length in *.
    apply H in H2 as H2'.
    instantiate (1 := VClos (map (fun '(x, y) => (0, x, y)) l) 0 0 (`VNil)).
    Unshelve. 2: exact (0, `VNil).
    rewrite map_map.
    rewrite map_nth with (d := (0, `VNil)).
    destruct nth. constructor.
    * intros. rewrite map_length in *.
      do 2 rewrite map_map. apply H in H3.
      do 2 rewrite map_nth with (d := (0, `VNil)). destruct nth.
      now rewrite Nat.add_0_r.
    * now rewrite map_length, Nat.add_0_r.
  }
  unfold convert_to_closlist in H_1, H_2. do 2 rewrite map_length in *.
  split. 2: split.
  1-2: do 2 constructor; [|now rewrite Nat.add_0_r].
  1-2: rewrite indexed_to_forall in H, H0; intros.
  1-2: do 2 rewrite map_nth with (d := (0, `VNil)).
  1-2: rewrite Nat.add_0_r.
  Unshelve. 4-7: exact (0, `VNil).
  1: apply H in H2.
  2: apply H0 in H2.
  1-2: now destruct nth.
  (* evaluation *)
  intros. inv H3; try inv_val.
  eapply H1 in H9 as [x D]. exists (S x). econstructor. reflexivity. exact D.
  lia.
  fold (Frel k F1 F2). eapply Frel_downclosed. eassumption.
  Unshelve.
  lia.
Qed.

Global Hint Resolve Erel_LetRec_compat_closed : core.

Lemma Vrel_Clos_compat_closed :
  forall n ext1 ext2 id1 id2 vl1 vl2 e1 e2,
  vl1 = vl2 ->
  Forall (fun '(id1, vl1, e1) => EXP length ext1 + vl1 ⊢ e1) ext1 ->
  Forall (fun '(id1, vl1, e1) => EXP length ext2 + vl1 ⊢ e1) ext2 ->
  (forall m (Hmn : m <= n) vl vl',
        length vl = vl1 ->
        list_biforall (Vrel m) vl vl' ->
        Erel m e1.[list_subst (convert_to_closlist ext1 ++ vl) idsubst]
               e2.[list_subst (convert_to_closlist ext2 ++ vl') idsubst]) ->
  Vrel n (VClos ext1 id1 vl1 e1) (VClos ext2 id2 vl2 e2).
Proof.
  intros. rewrite Vrel_Fix_eq. simpl. split. 2: split.
  1: {
    constructor.
    * intros. do 2 rewrite map_nth with (d := (0, 0, `VNil)).
      rewrite indexed_to_forall with (def := (0, 0, `VNil)) in H0.
      apply H0 in H3. destruct nth, p. cbn. now rewrite Nat.add_0_r.
    * specialize (H2 n ltac:(lia) (repeat VNil vl1) (repeat VNil vl1)).
      replace (length ext1 + vl1 + 0) with
              (length (convert_to_closlist ext1 ++ repeat VNil vl1)).
      2: { unfold convert_to_closlist.
           rewrite app_length, map_length, repeat_length. lia. }
      apply subst_implies_list_scope.
      apply Forall_app. split.
      - apply closlist_scope. intros.
        do 2 rewrite map_nth with (d := (0, 0, `VNil)).
        rewrite indexed_to_forall with (def := (0, 0, `VNil)) in H0.
        apply H0 in H3. destruct nth, p. now rewrite Nat.add_0_r.
      - now apply Forall_repeat.
      - apply Erel_closed_l in H2; auto.
        now rewrite repeat_length.
        clear. induction vl1; simpl; auto.
  }
  1: {
    constructor.
    * intros. do 2 rewrite map_nth with (d := (0, 0, `VNil)).
      rewrite indexed_to_forall with (def := (0, 0, `VNil)) in H1.
      apply H1 in H3. destruct nth, p. cbn. now rewrite Nat.add_0_r.
    * specialize (H2 n ltac:(lia) (repeat VNil vl2) (repeat VNil vl2)).
      replace (length ext2 + vl2 + 0) with
              (length (convert_to_closlist ext2 ++ repeat VNil vl2)).
      2: { unfold convert_to_closlist.
           rewrite app_length, map_length, repeat_length. lia. }
      apply subst_implies_list_scope.
      apply Forall_app. split.
      - apply closlist_scope. intros.
        do 2 rewrite map_nth with (d := (0, 0, `VNil)).
        rewrite indexed_to_forall with (def := (0, 0, `VNil)) in H1.
        apply H1 in H3. destruct nth, p. now rewrite Nat.add_0_r.
      - now apply Forall_repeat.
      - apply Erel_closed_r in H2; auto.
        now rewrite repeat_length.
        clear. induction vl2; simpl; auto.
  }
  split; auto. subst.
  intros. apply H2. lia. lia. auto.
Qed.
(*
Lemma Vrel_closlist n l1 l2 :
  list_biforall
  (fun '(_, v, e) '(_, v', e') =>
  v = v' /\
  (forall m (Hmn : m <= n) vl vl',
  length vl = v ->
  list_biforall (Vrel m) vl vl' ->
  Erel m e.[list_subst (convert_to_closlist l1 ++ vl) idsubst]
         e'.[list_subst (convert_to_closlist l2 ++ vl') idsubst])) l1 l2 ->
  Forall (fun '(id1, vl1, e1) => EXP length l1 + vl1 ⊢ e1) l1 ->
  Forall (fun '(id1, vl1, e1) => EXP length l2 + vl1 ⊢ e1) l2 ->
  list_biforall (Vrel n) (convert_to_closlist l1) (convert_to_closlist l2).
Proof.
  intros H FL1 FL2. eapply forall_biforall.
  { simpl_convert_length. now apply biforall_length in H. }
  intros. unfold convert_to_closlist in *. rewrite map_length in *.
  apply biforall_forall with (i := i) (d1 := (0, 0, `VNil)) (d2 := (0, 0, `VNil)) in H as H'; auto.
  rewrite map_nth with (d := (0, 0, `VNil)).
  rewrite map_nth with (d := (0, 0, `VNil)).
  destruct nth, nth, p, p0. destruct H'. subst.
  apply VClos_compat_closed; auto.
Qed. *)

Lemma Erel_LetRec_compat :
  forall Γ l l' (e e': Exp), length l = length l' ->
    list_biforall (fun '(v, e) '(v', e') =>
      v = v' /\ Erel_open (length l + v + Γ) e e'
    ) l l' ->
    Erel_open (length l + Γ) e e' ->
    Erel_open Γ (ELetRec l e) (ELetRec l' e').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply (Erel_LetRec_compat_closed n).
  lia.
  (* scopes: *)
  1-2: rewrite indexed_to_forall; intros; rewrite map_length in *.
  1-2: eapply biforall_forall with (i := i) (d1 := (0, `VNil)) (d2 := (0, `VNil)) in H0; try lia.
  Unshelve.
  4-5: exact (0, `VNil).
  1-2: rewrite map_nth with (d := (0, `VNil)).
  1-2: do 2 destruct nth; destruct H0; subst.
  1-2: apply Erel_open_scope in H4 as [H4_1 H4_2]; try rewrite <- H.
  1-2: apply -> subst_preserves_scope_exp; [eassumption|].
  1-2: rewrite <- (Nat.add_0_r (length l + n1)) at 2; apply upn_scope, H2.
  (* evaluation *)
  unfold Erel_open in H0.
  do 2 rewrite subst_comp_exp.
  apply H1.
  rewrite H. apply Grel_list_subst; auto.
  2: unfold convert_to_closlist; now repeat rewrite map_length.
  
  (* Doing some function magic (extensionality mostly) to be able to
     use Vrel_Clos_compat *)
  unfold convert_to_closlist. repeat rewrite map_map.
  eapply forall_biforall with
    (d1 := VClos (map (fun x : nat * Exp =>
    let
    '(x0, y) :=
     let '(n, x0) := x in (n, x0.[upn (Datatypes.length l' + n) ξ₁]) in
     (0, x0, y)) l) 0 0 (`VNil))
    (d2 := VClos (map (fun x : nat * Exp =>
    let
    '(x0, y) :=
     let '(n, x0) := x in (n, x0.[upn (Datatypes.length l' + n) ξ₂]) in
     (0, x0, y)) l') 0 0 (`VNil)).
  now do 2 rewrite map_length.
  rewrite map_length. intros.
  eapply biforall_forall with (d1 := (0, `VNil)) (d2 := (0, `VNil))
    (i := i) in H0 as H0'. 2: lia.
  do 2 rewrite map_nth with (d := (0, `VNil)). do 2 destruct nth; simpl.
  destruct H0'. subst.
  extract_map_fun F.
  remember (fun x : nat * Exp =>
  let
  '(x0, y) :=
   let '(n0, x0) := x in (n0, x0.[upn (Datatypes.length l' + n0) ξ₂]) in
   (0, x0, y)) as G.
  epose proof (Vrel_Clos_compat Γ (map (fun '(a, b) => (0, a, b)) l) (map (fun '(a, b) => (0, a, b)) l') 0 0 n1 n1 e0 e1 eq_refl _ _ _ ξ₁ ξ₂ H2). simpl in H4.
  repeat rewrite map_length in *. do 2 rewrite map_map in H4.
  repeat rewrite H in H4.
  extract_map_fun in H4 as F'.
  assert (F = F'). {
    extensionality x. subst F F'. now destruct x.
  }
  rewrite H6 in *. clear H6 F.
  assert (G = (fun x : nat * Exp =>
  let
  '(y, x0) := let '(a, b) := x in (0, a, b) in
   let
   '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length l' + ls) ξ₂]))). {
      extensionality x. subst G. now destruct x.
   }
  subst. rewrite H6.
  apply H4.
  Unshelve.
  * clear F G HeqF HeqG.
    intro. intros. apply H5.
    now rewrite map_length in H4.
  * clear F G HeqF HeqG H5 H3 i.
    eapply forall_biforall with (d1 := (0, 0, `VNil)) (d2 := (0, 0, `VNil)).
    now do 2 rewrite map_length.
    rewrite map_length. intros.
    do 2 rewrite map_nth with (d := (0, `VNil)).
    eapply biforall_forall with (d1 := (0, `VNil)) (d2 := (0, `VNil))in H0.
    2: exact H3.
    destruct nth, nth, H0; subst; split; auto.
Qed.

Global Hint Resolve Erel_LetRec_compat : core.

Lemma Erel_Cons_compat_closed :
  forall m e1 e1' e2 e2', Erel m e1 e1' -> Erel m e2 e2'
 ->
  Erel m (ECons e1 e2) (ECons e1' e2').
Proof.
  intros. destruct H as [He1 [He1' HD1]], H0 as [He2 [He2' HD2]].
  split. 2: split. 1-2: constructor; auto.
  intros. destruct H as [HF1 [HF2 [HDF1 HDF2]]].
  inv H0; try inv_val.
  eapply HD2 in H4 as [i D]. eexists. constructor. exact D.
  lia.
  split. 2: split.
  1-2: repeat constructor; auto.
  split.
  { (* normal evaluation *)
    intros. inv H0. destruct vl2. 2: destruct vl2. all: inv H. 2: inv H7.
    clear H7.
    eapply HD1 in H6 as [i D]. eexists. constructor. exact D.
    lia.
    split. 2: split.
    1-2: repeat constructor; auto.
    1-2: apply Vrel_closed in H3; apply H3.
    split.
    { (* normal evaluation *)
      intros. inv H0. destruct vl2. 2: destruct vl2. all: inv H. 2: inv H9.
      eapply HDF1 in H8 as [i D]. eexists. constructor. exact D.
      lia.
      constructor; auto.
      apply Vrel_Cons_compat_closed; eapply Vrel_downclosed; eassumption.
      Unshelve. all: lia.
    }
    { (* exception *)
      intros. inv H0.
      eapply HDF2 in H9 as [i D]. eexists. constructor. congruence. exact D.
      lia.
      eapply Excrel_downclosed. exact H. Unshelve. lia.
    }
  }
  { (* exception *)
    intros. inv H0.
    eapply HDF2 in H7 as [i D]. eexists. constructor. congruence. exact D.
    lia.
    eapply Excrel_downclosed. exact H. Unshelve. lia.
  }
Qed.

Global Hint Resolve Erel_Cons_compat_closed : core.

Lemma Erel_Cons_compat :
  forall Γ v1 v1' v2 v2', Erel_open Γ v1 v1' -> Erel_open Γ v2 v2'
 ->
  Erel_open Γ (ECons v1 v2) (ECons v1' v2').
Proof.
  unfold Erel_open. intros. simpl. apply Erel_Cons_compat_closed; [apply H | apply H0]; auto.
Qed.

Global Hint Resolve Erel_Cons_compat : core.

(* 
NOTE: does not work because of the ordering. We need to restrict it to
values that are inserted to the same position

(* Maps.v *)
Lemma map_insert_biprop :
  forall (P : Val -> Val -> Prop)
    (l l' : list (Val * Val)) (k v k' v' : Val),
      P k k' -> P v v' ->
      list_biforall (fun '(v1, v2) '(v1', v2') => P v1 v1' /\ P v2 v2') l l' ->
  list_biforall (fun '(v1, v2) '(v1', v2') => P v1 v1' /\ P v2 v2')
  (map_insert k v l) (map_insert k' v' l').
Proof.
  intros. induction H1; simpl.
  * constructor; auto.
  * destruct hd, hd'. 
Admitted. *)

Definition IRel (n : nat) (i1 i2 : FrameIdent) : Prop :=
ICLOSED i1 /\ ICLOSED i2 /\
match i1, i2 with
| IApp v, IApp v' => Vrel n v v'
| ITuple, ITuple => True
| IMap, IMap => True
| ICall f, ICall f' => f = f'
| IPrimOp f, IPrimOp f' => f = f'
| IValues, IValues => True
| _, _ => False
end.

Lemma go_is_biforall {A B : Type}: forall (P : A -> B -> Prop) l l',
(fix go l l' {struct l} : Prop :=
        match l with
        | [] => match l' with
                | [] => True
                | _ :: _ => False
                end
        | x :: xs =>
            match l' with
            | [] => False
            | y :: ys => P x y /\ go xs ys
            end
        end) l l' ->
list_biforall P l l'.
Proof.
  induction l; destruct l'; try contradiction; auto.
  * intros. constructor. apply H. apply IHl, H.
Qed.

(* NOTE: unsafe comparison of closures are exploited here
Lemma Vrel_Val_eqb m v v' :
  Vrel m v v' ->
  Val_eqb v v' = true.
Proof.
  revert v'. induction v using Val_ind_weakened with
    (Q := Forall (fun v => forall v', Vrel m v v' -> Val_eqb v v' = true))
    (R := Forall (fun '(v1, v2) =>
      (forall v', Vrel m v1 v' -> Val_eqb v1 v' = true) /\
      (forall v', Vrel m v2 v' -> Val_eqb v2 v' = true))); intros;
  try rewrite Vrel_Fix_eq in H; try destruct v', H as [Hcl1 [Hcl2 H]];
  try contradiction; auto.
  * break_match_hyp. now simpl. contradiction.
  * simpl. rewrite IHv1, IHv2; auto. 1-2: now rewrite Vrel_Fix_eq.
  * simpl. clear Hcl1 Hcl2. generalize dependent l0.
    induction IHv; destruct l0; auto; intros.
    rewrite H, IHIHv; auto.
    apply H0. rewrite Vrel_Fix_eq. apply H0.
  * simpl. clear Hcl1 Hcl2. generalize dependent l0.
    induction l; intros; destruct l0; auto.
    destruct a; auto.
    destruct a, p. inv IHv. inv H2.
    rewrite H0, H1. 2-3: rewrite Vrel_Fix_eq; apply H. simpl.
    destruct H as [_ [_ H]]. rewrite IHl; auto.
  * 
Qed. *)

(* NOTE: unsafe comparison of closures are exploited here *)
Lemma Vrel_Val_eqb m v v' :
  Vrel m v v' ->
  v <ᵥ v' = false.
Proof.
  revert v'. induction v using Val_ind_weakened with
    (Q := Forall (fun v => forall v', Vrel m v v' -> Val_ltb v v' = false))
    (R := Forall (fun '(v1, v2) =>
      (forall v', Vrel m v1 v' -> Val_ltb v1 v' = false) /\
      (forall v', Vrel m v2 v' -> Val_ltb v2 v' = false))); intros;
  try rewrite Vrel_Fix_eq in H; try destruct v', H as [Hcl1 [Hcl2 H]];
  try contradiction; auto.
  * break_match_hyp. simpl. apply Lit_eqb_eq in Heqb. subst.
    destruct l0; simpl. 2: lia.
    unfold string_ltb. break_match_goal; auto.
    apply OrderedTypeEx.String_as_OT.compare_helper_lt in Heqc.
    apply OrderedTypeEx.String_as_OT.lt_not_eq in Heqc as Heqc'.
    congruence.
    contradiction.
  * simpl. rewrite IHv1, IHv2; auto. 2-3: now rewrite Vrel_Fix_eq.
    now break_match_goal.
  * simpl. clear Hcl1 Hcl2. generalize dependent l0.
    induction IHv; destruct l0; auto; intros. contradiction.
    simpl. rewrite H. 2: now rewrite Vrel_Fix_eq.
    destruct H0.
    apply go_is_biforall in H1 as H1'. apply biforall_length in H1'.
    apply IHIHv in H1.
    rewrite H1' in *. rewrite Nat.eqb_refl in *.
    rewrite Nat.ltb_irrefl in *. simpl in *.
    rewrite H1. now break_match_goal.
  * simpl. clear Hcl1 Hcl2. generalize dependent l0.
    induction l; intros; destruct l0; auto. contradiction.
    destruct a; auto.
    destruct p. inv IHv. inv H2.
    rewrite H0, H1. 2-3: rewrite Vrel_Fix_eq; apply H. simpl.
    destruct H as [_ [_ H]].
    assert (length l = length l0). {
      clear -H. generalize dependent l0. induction l; destruct l0; intros; auto.
      contradiction. destruct a. contradiction.
      simpl. destruct a, p, H as [_[_ H]]. erewrite IHl. reflexivity.
      auto. 
    }
    apply IHl in H; auto. clear IHl.
    rewrite H2 in *. rewrite Nat.eqb_refl in *.
    rewrite Nat.ltb_irrefl in *. simpl in *.
    apply Bool.orb_false_elim in H as [H_1 H_2]. rewrite H_1.
    apply Bool.andb_false_elim in H_2 as [H_2 | H_2]; rewrite H_2;
    break_match_goal; simpl; auto.
    break_match_goal; now rewrite Bool.andb_false_r.
  * simpl. 
Qed.

Lemma Vrel_ltb :
  forall v1 v2,
  Val_ltb v1 v2 = true -> Val_eqb v1 v2 = false.
Proof.
  
Qed.

(* Maps.v? *)
Lemma Vrel_map_insert m l l' k1 v1 k2 v2 :
  list_biforall (fun '(v1, v2) '(v1', v2') => Vrel m v1 v1' /\ Vrel m v2 v2') l l' ->
  Vrel m k1 k2 ->
  Vrel m v1 v2 ->
  list_biforall (fun '(v1, v2) '(v1', v2') => Vrel m v1 v1' /\ Vrel m v2 v2') (map_insert k1 v1 l) (map_insert k2 v2 l').
Proof.
  revert l l'. induction l using list_length_ind; intros.
  destruct l, l'; simpl in *; try inv H0.
  * constructor; auto.
  * destruct p, p0, H6.
    do 2 break_match_goal.
    - do 2 constructor; auto.
    - break_match_goal.
      + admit. (* helper thm needed, it's contradiction *)
      + admit. (* helper thm needed, it's contradiction *)
    - break_match_goal.
      + admit. (* helper thm needed, it's contradiction *)
      + break_match_goal.
        ** constructor; auto.
        ** admit. (* helper thm needed, it's contradiction *)
    - break_match_goal.
      + admit. (* helper thm needed, it's contradiction *)
      + break_match_goal.
      ** admit. (* helper thm needed, it's contradiction *)
      ** constructor; auto.
Qed.

(* Maps.v? *)
Lemma Vrel_make_map m l l' :
  list_biforall (Vrel m) l l' ->
  list_biforall (fun '(v1, v2) '(v1', v2') => Vrel m v1 v1' /\ Vrel m v2 v2')
  (make_val_map (deflatten_list l)) (make_val_map (deflatten_list l')).
Proof.
  revert l'. induction l using list_length_ind; intros.
  inv H0; simpl; auto.
  inv H2; simpl; auto.
  apply H in H3. 2: simpl; lia.
Qed.

Lemma Rel_create_result m l l' ident ident' :
  list_biforall (Vrel m) l l' ->
  IRel m ident ident' ->
  (exists e e', forall k, k < m -> Erel k e e' /\ create_result ident l = e /\ create_result ident' l' = e') \/
  (exists vl vl', list_biforall (Vrel m) vl vl' /\ create_result ident l = RValSeq vl /\ create_result ident' l' = RValSeq vl') \/
  (exists ex ex', Excrel m ex ex' /\ create_result ident l = ex /\ create_result ident' l' = ex').
Proof.
  intros. destruct ident, ident'; simpl; destruct H0 as [Hcl1 [Hcl2 H0]]; try contradiction.
  * right. left. exists l, l'; auto.
  * right. left. exists [VTuple l], [VTuple l']. auto.
  * right. left. do 2 eexists. split.
    2: split; reflexivity.
    constructor; auto. apply Vrel_Map_compat_closed.
    generalize dependent l'. induction l using list_length_ind; intros.
    destruct l, l'; inv H1.
    - simpl. auto.
    - destruct l, l'; inv H7; simpl; auto.
      apply H in H8. 2: slia.
      
  * admit.
  * admit.
  * destruct v.
    1-7: right; right; rewrite Vrel_Fix_eq in H0; destruct H0 as [Hcl3 [Hcl4 H0]], v0; try contradiction.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - do 2 eexists; split; [|split;reflexivity].
      break_match_hyp. 2: contradiction.
      apply Lit_eqb_eq in Heqb. subst.
      split; [|split]; auto.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed, Vrel_Cons_compat_closed.
      1-2: rewrite Vrel_Fix_eq; apply H0.
      Unshelve. lia.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed.
      apply Vrel_Tuple_compat_closed.
      apply go_is_biforall in H0.
      eapply biforall_impl. 2: exact H0.
      intros. rewrite Vrel_Fix_eq. exact H1.
      Unshelve. lia.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed.
      apply Vrel_Map_compat_closed.
      clear Hcl1 Hcl2 Hcl3 Hcl4 H l l'.
      generalize dependent l1.
      induction l0; destruct l1; try contradiction; auto.
      destruct a; contradiction.
      constructor.
      + destruct a, p. do 2 rewrite Vrel_Fix_eq; split; apply H0.
      + apply IHl0. destruct a, p. apply H0.
        Unshelve. lia.
    - break_match_goal.
      + rewrite Vrel_Fix_eq in H0.
        destruct v0, H0 as [Hcl3 [Hcl4 H0]]; try contradiction.
        destruct H0. subst.
        apply biforall_length in H as Hlen. rewrite Hlen in Heqb.
        rewrite Heqb.
        left. do 2 eexists; split; [|split;reflexivity].
        apply H1. lia. apply Nat.eqb_eq in Heqb. rewrite Heqb.
        now apply biforall_length in H.
        eapply biforall_impl. 2: eassumption. intros.
        eapply Vrel_downclosed; eassumption. Unshelve. lia.
      + right. right. rewrite Vrel_Fix_eq in H0.
        destruct v0, H0 as [Hcl3 [Hcl4 H0]]; try contradiction.
        destruct H0. subst.
        apply biforall_length in H as Hlen. rewrite Hlen in Heqb.
        rewrite Heqb. do 2 eexists; split; [|split;reflexivity].
        split; [|split]; auto.
        eapply Vrel_downclosed. rewrite Vrel_Fix_eq. split. 2: split.
        3: {
          split; auto. apply H1.
        }
        now inv Hcl1.
        now inv Hcl2.
        Unshelve.
          lia.
Admitted.

Lemma Erel_Params_compat_closed :
  forall m l l',
  list_biforall (Erel m) l l' ->
  forall ident ident' vl vl' e e',
  (* technical side conditions: *)
  IRel m ident ident' ->
  (ident = IMap -> exists n, length l + length vl = 1 + 2*n) ->
  (ident' = IMap -> exists n, length l' + length vl' = 1 + 2*n) ->
  (****)
  Erel m e e' ->
  forall k, k <= m -> forall F1 F2,
  Frel k F1 F2 ->
  list_biforall (Vrel k) vl vl' ->
  | FParams ident vl l :: F1, e | k ↓ ->
  | FParams ident' vl' l' :: F2, e' | ↓.
Proof.
  induction l; intros.
  * inv H.
    eapply H3 in H7 as [i D]. eexists. exact D.
    lia.
    destruct H. proof_irr.
    split. 2: split.
    1-2: repeat constructor; auto.
    1,4: apply H0.
    2,4: apply H5.
    1,2: now apply biforall_vrel_closed in H6.
    split; intros.
    - inv H10. destruct vl2. 2: destruct vl2. all: inv H9.
      2: { inv H15. }
      assert (list_biforall (Vrel (S k0)) (vl ++ [v]) (vl' ++ [v0])). {
        apply biforall_app; auto.
        eapply biforall_impl. 2: exact H6.
        intros. eapply Vrel_downclosed; eassumption. Unshelve. lia.
      }
      assert (IRel (S k0) ident ident'). {
        destruct ident, ident'; auto.
        split. 2: split. 1-2: apply H0.
        eapply Vrel_downclosed. apply H0.
        Unshelve. lia.
      }
      eapply Rel_create_result in H9.
      2: eassumption.
      intuition.
      + destruct H11 as [e0 [e0' [Hee' [Eq1 Eq2]]]].
        rewrite Eq1 in H17.
        eapply Hee' in H17 as [i D]. eexists.
        econstructor. symmetry. exact Eq2. exact D.
        lia. fold (Frel k0 F1 F2). eapply Frel_downclosed. eassumption.
        Unshelve. lia.
      + destruct H9 as [vl0 [vl0' [Hvlvl' [Eq1 Eq2]]]].
        rewrite Eq1 in H17.
        eapply H5 in H17 as [i D]. eexists.
        econstructor. symmetry. exact Eq2. exact D.
        lia.
        eapply biforall_impl. 2: eassumption.
        intros. eapply Vrel_downclosed. eassumption.
        Unshelve. lia.
      + destruct H9 as [ex0 [ex0' [Hexex' [Eq1 Eq2]]]].
        rewrite Eq1 in H17.
        eapply H5 in H17 as [i D]. eexists.
        econstructor. symmetry. exact Eq2. exact D.
        lia.
        fold (Excrel k0 ex0 ex0'). eapply Excrel_downclosed. eassumption.
        Unshelve. lia.
    - inv H10. eapply H5 in H16 as [i D]. eexists. constructor.
      congruence.
      exact D.
      lia.
      eapply Excrel_downclosed; eassumption.
  * inv H.
    eapply H3 in H7 as [i D]. eexists. exact D. lia.
    destruct H. proof_irr.
    split. 2: split.
    1-2: constructor; auto.
    2,4: apply H5.
    1-2: constructor; auto.
    1,4: apply H0.
    1,3: now apply biforall_vrel_closed in H6.
    1-2: apply Erel_closed in H10.
    1-2: apply biforall_erel_closed in H12.
    1-2: constructor; auto; try apply H12; apply H10.
    split.
    - intros. inv H11. destruct vl2. 2: destruct vl2. all: inv H9.
      2: inv H17.
      eapply IHl in H20 as [i D].
      eexists. econstructor. exact D.
      all: auto.
      + intros. apply H1 in H9 as [n L]. simpl in L.
        exists n. rewrite app_length. slia.
      + intros. apply H2 in H9 as [n L]. simpl in L.
        exists n. rewrite app_length. slia.
      + lia.
      + eapply Frel_downclosed; eassumption.
      + apply biforall_app. 2: constructor.
        eapply biforall_impl. 2: exact H6.
        intros.
        1-2: eapply Vrel_downclosed; eassumption.
        constructor.
    - intros. inv H11. eapply H5 in H18 as [i D].
      eexists. constructor. congruence. exact D. lia.
      eapply Excrel_downclosed; eassumption.
  Unshelve. all: lia.
Qed.

Corollary Erel_Params_compat_closed_box :
  forall m l l',
  list_biforall (Erel m) l l' ->
  forall ident ident' vl vl',
  (* technical side conditions: *)
  IRel m ident ident' ->
  (ident = IMap -> exists n, length l + length vl = 2*n) ->
  (ident' = IMap -> exists n, length l' + length vl' = 2*n) ->
  (****)
  forall k, k <= m -> forall F1 F2,
  Frel k F1 F2 ->
  list_biforall (Vrel k) vl vl' ->
  | FParams ident vl l :: F1, RBox | k ↓ ->
  | FParams ident' vl' l' :: F2, RBox | ↓.
Proof.
  intros. inv H6.
  * inv H. eapply Erel_Params_compat_closed in H13 as [i D].
    - eexists. econstructor. destruct ident, ident'; inv H0; try congruence.
      1-5: now inv H6.
      exact D.
    - exact H10.
    - assumption.
    - intros. apply H1 in H as [n H]. simpl in H. exists (pred n). lia.
    - intros. apply H2 in H as [n H]. simpl in H. exists (pred n). lia.
    - assumption.
    - lia.
    - eapply Frel_downclosed in H4. eassumption.
    - eapply biforall_impl. 2: exact H5. intros.
      eapply Vrel_downclosed; eassumption.
  * admit. (* same admit as in the previous thm *)  
Admitted.

Lemma Erel_Tuple_compat_closed :
  forall m l l',
  list_biforall (Erel m) l l' ->
  Erel m (ETuple l) (ETuple l').
Proof.
  intros. apply biforall_erel_closed in H as Hcl.
  split. 2: split.
  1-2: do 2 constructor; apply indexed_to_forall, Hcl.
  clear Hcl. intros.
  inv H1. eapply Erel_Params_compat_closed_box in H4 as [i D].
  - eexists. constructor. exact D.
  - eassumption.
  - repeat split; auto.
  - intros. congruence.
  - intros. congruence.
  - lia.
  - eapply Frel_downclosed; eassumption.
  - auto.
  - inv_val.
  Unshelve. lia.
Qed.

Global Hint Resolve Erel_Tuple_compat_closed : core.

Lemma Erel_Tuple_compat :
  forall Γ l l',
  list_biforall (Erel_open Γ) l l' ->
  Erel_open Γ (ETuple l) (ETuple l').
Proof.

Admitted.

Global Hint Resolve Erel_Tuple_compat : core.

Lemma Erel_Map_compat_closed :
  forall m l l',
  list_biforall (fun '(e1, e2) '(e1', e2') =>
    Erel m e1 e1' /\ Erel m e2 e2'
  ) l l' ->
  Erel m (EMap l) (EMap l').
Proof.

Admitted.

Global Hint Resolve Erel_Map_compat_closed : core.

Lemma Erel_Map_compat :
  forall Γ l l',
  list_biforall (fun '(e1, e2) '(e1', e2') =>
    Erel_open Γ e1 e1' /\ Erel_open Γ e2 e2'
  ) l l' ->
  Erel_open Γ (EMap l) (EMap l').
Proof.

Admitted.

Global Hint Resolve Erel_Map_compat : core.

Lemma Erel_Call_compat_closed :
  forall m l l' f f',
  f = f' ->
  list_biforall (Erel m) l l' ->
  Erel m (ECall f l) (ECall f' l').
Proof.

Admitted.

Global Hint Resolve Erel_Call_compat_closed : core.

Lemma Erel_Call_compat :
  forall Γ l l' f f',
  f = f' ->
  list_biforall (Erel_open Γ) l l' ->
  Erel_open Γ (ECall f l) (ECall f' l').
Proof.

Admitted.

Global Hint Resolve Erel_Call_compat : core.


Lemma Erel_PrimOp_compat_closed :
  forall m l l' f f',
  f = f' ->
  list_biforall (Erel m) l l' ->
  Erel m (EPrimOp f l) (EPrimOp f' l').
Proof.

Admitted.

Global Hint Resolve Erel_PrimOp_compat_closed : core.

Lemma Erel_PrimOp_compat :
  forall Γ l l' f f',
  f = f' ->
  list_biforall (Erel_open Γ) l l' ->
  Erel_open Γ (EPrimOp f l) (EPrimOp f' l').
Proof.

Admitted.

Global Hint Resolve Erel_PrimOp_compat : core.

Lemma Vrel_Fun_right : forall m v2 ext id1 vl b,
  Vrel m (VClos ext id1 vl b) v2 ->
  exists ext' id' b' vl',
  vl = vl' /\ v2 = VClos ext' id' vl' b'.
Proof.
  intros. rewrite Vrel_Fix_eq in H. destruct H, H0. destruct v2; try contradiction. destruct H1. subst. do 4 eexists.
  split. 2: split. all: try reflexivity.
Qed.

Lemma Erel_App_compat_ind : forall hds hds' tl tl' F1 F2 k0 v1 v2 (* P1 P1' P2 P2' *),
  list_biforall (Erel k0) hds hds' ->
  list_biforall (Vrel k0) tl tl' ->
  Vrel k0 v1 v2 ->
  FSCLOSED F1 ->
  FSCLOSED F2 ->
  (forall m : nat, m <= k0 -> forall v1 v2 : Exp, Vrel m v1 v2 -> | F1, v1 | m ↓ -> | F2, v2 | ↓)
->
  frame_rel k0 (fun (m' : nat) (_ : m' <= k0) => Vrel m') (FApp2 v1 (* P1 *) hds tl (* P2 *) :: F1)
  (FApp2 v2 (* P1' *) hds' tl' (* P2' *) :: F2).
Proof.
  induction hds; intros.
  * inversion H. subst. apply biforall_length in H0 as LEN.
    assert (list_biforall (Vrel k0) tl tl') as BF by auto.
    apply biforall_vrel_closed in H0 as [H0_1 H0_2]. split. 2: split.
    1-2: constructor; auto; constructor; auto; apply Vrel_closed in H1; apply H1.
    intros.
    inversion H5; subst.
    - inversion H0. inversion H7.
    - apply Vrel_Fun_right in H1 as v; destruct v as [e1 [vl1 [? ?]]]. subst.
      rewrite Vrel_Fix_eq in H1. destruct H1 as [VCL1 [VCL2 H1]].
      rewrite H6, Nat.eqb_refl in H1.
      epose proof (H1 k _ (tl ++ [v0]) (tl' ++ [v3]) _ _ _) as E.
      destruct E as [E1CL [E2CL ?]]. eapply H7 in H14.
      destruct H14. exists (S x). constructor.
      + exact H0_2.
      + lia.
      + apply Vrel_closed in H0; apply H0.
      + exact H8.
      + lia.
      + split. 2: split. all: auto. intros. eapply H4 in H11. exact H11. lia. auto.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
    - inversion H0. inversion H7.
  * inversion H. subst.
    apply biforall_length in H0 as LEN.
    apply biforall_vrel_closed in H0 as v. destruct v.
    apply biforall_erel_closed in H as v. destruct v.
    apply Vrel_closed in H1 as v. destruct v. split. 2: split.
    1-2: constructor; auto; now constructor.
    intros. inversion H14; subst.
    - inversion H13. inversion H16.
    - eapply H7 in H24. destruct H24. exists (S x). econstructor; auto.
      apply Vrel_closed in H13; apply H13.
      exact H15.
      lia.
      apply IHhds; auto.
      + inversion H. eapply biforall_impl in H25. exact H25. intros. eapply Erel_downclosed; eauto.
      + apply biforall_app. eapply biforall_impl in H0. exact H0. intros. eapply Vrel_downclosed; eauto.
        constructor. 2: constructor. eapply Vrel_downclosed; eauto.
      + eapply Vrel_downclosed; eauto.
      + intros. eapply H4 in H19. exact H19. lia. auto.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
Unshelve.
  all: auto; try lia.
  ** rewrite app_length. simpl. lia.
  ** rewrite app_length. simpl. lia.
  ** apply biforall_app.
    -- eapply biforall_impl in BF. exact BF. intros. eapply Vrel_downclosed; eauto.
    -- constructor. eapply Vrel_downclosed. eauto. constructor.
Unshelve. all: lia.
Qed.

Lemma Erel_App_compat_helper : forall es es' k F1 F2 (FCL1 : FSCLOSED F1) (FCL2 : FSCLOSED F2),
  (forall m : nat, m <= S k -> forall v1 v2 : Exp, Vrel m v1 v2 -> | F1, v1 | m ↓ -> | F2, v2 | ↓) ->
  list_biforall (Erel k) es es' ->
  forall m, m <= k -> 
  forall v1 v2 : Exp, Vrel m v1 v2 -> | FApp1 es :: F1, v1 | m ↓ -> | FApp1 es' :: F2, v2 | ↓.
Proof.
  destruct es; intros.
  * apply biforall_length in H0 as L. apply eq_sym, length_zero_iff_nil in L. subst.
    apply Vrel_closed in H2 as H2'. destruct H2' as [H2'1 H2'2].
    inversion H3; subst; try inversion_is_value.
    - apply Vrel_Fun_right in H2 as v; destruct v as [e1 [vl1 [? ?]]].
      apply eq_sym, length_zero_iff_nil in H4. subst.
      rewrite Vrel_Fix_eq in H2. destruct H2 as [VCL1 [VCL2 ?]].
      rewrite Nat.eqb_refl in H2.
      specialize (H2 k0 ltac:(lia) [] [] (eq_refl _) (eq_refl _) ltac:(constructor)). simpl in H2.
      destruct H2 as [ECL1 [ECL2 ?]]. eapply H2 in H5.
      destruct H5. exists (S x). constructor. eauto. lia. split. 2: split. all: auto.
      intros. eapply H. 2: exact H4. lia. auto.
  * inversion H3; subst.
    - inversion H2. inversion H5.
    - inversion H0. subst.
      destruct H6 as [ECL1 [ECL2 ?]]. eapply H4 in H10. destruct H10. exists (S x).
      econstructor. apply Vrel_closed in H2; apply H2. exact H5. lia. apply Vrel_closed in H2 as v. destruct v.
      eapply Erel_App_compat_ind; auto.
      + eapply biforall_impl in H8; eauto. intros. eapply Erel_downclosed; eauto.
      + constructor.
      + eapply Vrel_downclosed; eauto.
      + intros. eapply H in H12; eauto. lia.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion H5.
    - inversion H2. inversion_is_value.
Unshelve.
  auto. all: lia.
Qed.

Lemma Erel_App_compat_closed :
  forall n e es e' es',
  Erel n e e' -> list_biforall (Erel n) es es'
->
  Erel n (EApp e es) (EApp e' es').
Proof.
  intros. destruct H, H1. split. 2: split.
  1-2: constructor; auto; rewrite <- indexed_to_forall; apply biforall_erel_closed in H0; apply H0.

 (* eval e *)
  intros. inversion H4; try inversion_is_value. subst.
  intros. eapply H2 in H9. destruct H9. exists (S x). constructor. exact H5. lia.
  destruct H3, H5. split. 2: split. 1-2: constructor; auto.
  1-2: constructor; apply biforall_erel_closed in H0; apply H0.

 (* eval es *)
  
  intros. eapply Erel_App_compat_helper in H8. exact H8. all: auto.
  intros. eapply H6 in H12; eauto. lia.
  eapply biforall_impl in H0. exact H0. intros. eapply Erel_downclosed; eauto.
Unshelve. lia.
Qed.

Global Hint Resolve Erel_App_compat_closed : core.

Lemma Erel_App_compat :
  forall Γ e es e' es',
  Erel_open Γ e e' -> list_biforall (Erel_open Γ) es es'
->
  Erel_open Γ (EApp e es) (EApp e' es').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_App_compat_closed; auto.
  eapply biforall_map; eauto.
Qed.

Global Hint Resolve Erel_App_compat : core.

Lemma Erel_BIF_compat_ind : forall hds hds' tl tl' F1 F2 k0 v1 v2 (* P1 P1' P2 P2' *),
  list_biforall (Erel k0) hds hds' ->
  list_biforall (Vrel k0) tl tl' ->
  Vrel k0 v1 v2 ->
  FSCLOSED F1 ->
  FSCLOSED F2 ->
  (forall m : nat, m <= k0 -> forall v1 v2 : Exp, Vrel m v1 v2 -> | F1, v1 | m ↓ -> | F2, v2 | ↓)
->
  frame_rel k0 (fun (m' : nat) (_ : m' <= k0) => Vrel m') (FBIF2 v1 (* P1 *) hds tl (* P2 *) :: F1)
  (FBIF2 v2 (* P1' *) hds' tl' (* P2' *) :: F2).
Proof.
  induction hds; intros.
  * inversion H. subst. apply biforall_length in H0 as LEN.
    assert (list_biforall (Vrel k0) tl tl') as BF by auto.
    apply biforall_vrel_closed in H0 as [H0_1 H0_2]. split. 2: split.
    1-2: constructor; auto; constructor; auto; apply Vrel_closed in H1; apply H1.
    intros.
    apply Vrel_closed in H0 as H0'. destruct H0' as [H0'1 H0'2].
    inversion H5; subst; try inversion_is_value.
    rewrite Vrel_Fix_eq in H1. destruct H1 as [VCL1 [VCL2 H1]].
    destruct v2; subst; try contradiction.
    rewrite Vrel_Fix_eq in H0. destruct H0 as [VCL3 [VCL4 H0]].
    destruct v3; subst; try contradiction.
    apply element_exist in LEN as EE. destruct EE as [fs [ls eq]]. subst.
    simpl in LEN. inversion LEN. apply eq_sym, length_zero_iff_nil in H1.
    subst. clear LEN.
    inversion BF; subst.
    rewrite Vrel_Fix_eq in H7. destruct H7 as [VCL5 [VCL6 H7]].
    destruct fs; subst; try contradiction.
    eapply H4 in H11 as [x H0].
    exists (S x). constructor. exact H0. lia.
    apply Vrel_Lit_compat_closed.
  * inversion H. subst.
    apply biforall_length in H0 as LEN.
    apply biforall_vrel_closed in H0 as v. destruct v.
    apply biforall_erel_closed in H as v. destruct v.
    apply Vrel_closed in H1 as v. destruct v. split. 2: split.
    1-2: constructor; auto; now constructor.
    intros. inversion H14; subst.
    - inversion H13. inversion H16.
    - eapply H7 in H24. destruct H24. exists (S x). econstructor; auto.
      apply Vrel_closed in H13; apply H13.
      exact H15.
      lia.
      apply IHhds; auto.
      + inversion H. eapply biforall_impl in H25. exact H25. intros. eapply Erel_downclosed; eauto.
      + apply biforall_app. eapply biforall_impl in H0. exact H0. intros. eapply Vrel_downclosed; eauto.
        constructor. 2: constructor. eapply Vrel_downclosed; eauto.
      + eapply Vrel_downclosed; eauto.
      + intros. eapply H4 in H19. exact H19. lia. auto.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
    - inversion H13. inversion H16.
Unshelve.
  all: auto; try lia.
Qed.

Lemma Erel_BIF_compat_helper : forall es es' k F1 F2 (FCL1 : FSCLOSED F1) (FCL2 : FSCLOSED F2),
  (forall m : nat, m <= S k -> forall v1 v2 : Exp, Vrel m v1 v2 -> | F1, v1 | m ↓ -> | F2, v2 | ↓) ->
  list_biforall (Erel k) es es' ->
  forall m, m <= k -> 
  forall v1 v2 : Exp, Vrel m v1 v2 -> | FBIF1 es :: F1, v1 | m ↓ -> | FBIF1 es' :: F2, v2 | ↓.
Proof.
  destruct es; intros.
  * apply biforall_length in H0 as L. apply eq_sym, length_zero_iff_nil in L. subst.
    apply Vrel_closed in H2 as H2'. destruct H2' as [H2'1 H2'2].
    inversion H3; subst; try inversion_is_value.
  * apply Vrel_closed in H2 as H2'. destruct H2' as [H2'1 H2'2].
    inversion H3; subst; try inversion_is_value.
    - inversion H0. subst.
      destruct H6 as [ECL1 [ECL2 ?]]. eapply H4 in H10. destruct H10. exists (S x).
      econstructor. apply Vrel_closed in H2; apply H2. exact H5. lia. apply Vrel_closed in H2 as v. destruct v.
      eapply Erel_BIF_compat_ind; auto.
      + eapply biforall_impl in H8; eauto. intros. eapply Erel_downclosed; eauto.
      + constructor.
      + eapply Vrel_downclosed; eauto.
      + intros. eapply H in H12; eauto. lia.
Unshelve.
  auto. all: lia.
Qed.

Lemma Erel_BIF_compat_closed :
  forall p1 p2 es es' n,
  list_biforall (Erel n) es es' ->
  Erel n p1 p2 ->
  Erel n (EBIF p1 es) (EBIF p2 es').
Proof.
  intros. destruct H0,H1. split. 2: split.
  1-2: constructor; auto.
  1-2: rewrite <- indexed_to_forall; apply biforall_erel_closed in H; apply H.

 (* eval e *)
  intros. inversion H4; try inversion_is_value. subst.
  intros. eapply H2 in H9. destruct H9. exists (S x). constructor. exact H5. lia.
  destruct H3, H5. split. 2: split. 1-2: constructor; auto.
  1-2: constructor; apply biforall_erel_closed in H; apply H.

 (* eval es *)
  intros. eapply Erel_BIF_compat_helper in H8. exact H8. all: auto.
  intros. eapply H6 in H12; eauto. lia.
  eapply biforall_impl in H. exact H. intros. eapply Erel_downclosed; eauto.
Unshelve. lia.
Qed.

Lemma Erel_BIF_compat :
  forall p1 p2 es es' Γ,
  Erel_open Γ p1 p2 -> list_biforall (Erel_open Γ) es es' ->
  Erel_open Γ (EBIF p1 es) (EBIF p2 es').
Proof.
  intros.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_BIF_compat_closed; auto.
  eapply biforall_map; eauto.
Qed.

Global Hint Resolve Erel_BIF_compat : core.

(** TODO: will be changed in the future: *)
Lemma Erel_Receive_compat_closed :
  forall l1 l2 n,
  (* Erel n e1 e2 -> *)
  EXPCLOSED (EReceive l1) -> EXPCLOSED (EReceive l2) ->
  Erel n (EReceive l1) (EReceive l2).
Proof.
  intros. unfold Erel, exp_rel. split. 2: split.
  1-2: auto.
  intros. inversion H2; subst; try inversion_is_value.
Qed.

(** TODO: will be changed in the future: *)
Lemma Erel_Receive_compat :
  forall l1 l2 Γ,
  (* Erel_open Γ e1 e2 -> *)
  EXP Γ ⊢ EReceive l1 -> EXP Γ ⊢ EReceive l2 ->
  Erel_open Γ (EReceive l1) (EReceive l2).
Proof.
  intros. unfold Erel_open. intros. simpl. apply Erel_Receive_compat_closed; auto.
  replace (EReceive (map (fun '(p, v) => (p, v.[upn (pat_vars p) ξ₁])) l1)) with
          ((EReceive l1).[ξ₁]) by auto.
  apply -> subst_preserves_scope_exp; eauto. apply H1.
  replace (EReceive (map (fun '(p, v) => (p, v.[upn (pat_vars p) ξ₂])) l2)) with
          ((EReceive l2).[ξ₂]) by auto.
  apply -> subst_preserves_scope_exp; eauto. apply H1.
Qed.

Global Hint Resolve Erel_Receive_compat : core.

Theorem Erel_Vrel_Fundamental_helper :
  forall (e : Exp),
    (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
    (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e).
Proof.
  induction e using Exp_ind2 with
   (Q := fun l => Forall (fun e => (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
                                   (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e)) l)
   (W := fun l => Forall (fun '(_,e) => (forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e) /\
                                   (forall Γ, VAL Γ ⊢ e -> Vrel_open Γ e e)) l);
  intuition auto; try inversion_is_value.
  * apply Erel_Val_compat, Vrel_Var_compat. inversion H. now inversion H0.
  * apply Vrel_Var_compat. now inversion H.
  * apply Erel_Val_compat, Vrel_FunId_compat. inversion H. now inversion H0.
  * apply Vrel_FunId_compat. now inversion H.
  * apply Erel_Val_compat, Vrel_Fun_compat; auto. apply H. inversion H1. now inversion H2.
  * apply Vrel_Fun_compat; auto. apply H. now inversion H1.
  * inversion H1. subst. 2: inversion H2. apply Erel_App_compat. apply H. auto.
    apply forall_biforall_refl. apply Forall_and_inv in IHe0. destruct IHe0.
    assert (Forall (fun x : Exp => Erel_open Γ x x) el). {
      rewrite <- indexed_to_forall in H5.
      clear H H0 H1 H4 H3. induction el; constructor.
      * inversion H2. inversion H5. subst. apply H1. auto.
      * inversion H2. inversion H5. subst. apply IHel; auto.
    } auto.
  * inversion H3. subst. 2: inversion H4. apply Erel_Let_compat. now apply H. now apply H1.
  * inversion H3. subst. 2: inversion H4. apply Erel_LetRec_compat. auto. now apply H. now apply H1.
  * inversion H5. subst. 2: inversion H6. apply Erel_Case_compat. now apply H. now apply H1. now apply H3.
  * inversion H3. subst. 2: inversion H4. apply Erel_Cons_compat. now apply H. now apply H1.
  * inversion H3. inversion H4. subst. apply Erel_Val_compat.
    apply Vrel_Cons_compat. now apply H0. now apply H2.
  * inversion H3. subst. apply Vrel_Cons_compat. now apply H0. now apply H2.
  * inversion H1. subst. 2: inversion H2. apply Erel_BIF_compat. now apply H.
    assert (Forall (fun x : Exp => Erel_open Γ x x) l). {
      rewrite <- indexed_to_forall in H5.
      induction l; constructor.
      * inversion H5. inversion IHe0. now apply H10.
      * inversion H5. inversion IHe0. subst. apply IHl; auto.
        constructor; auto. now rewrite <- indexed_to_forall.
    }
    now apply forall_biforall_refl.
Qed.

Theorem Erel_Fundamental :
  forall (e : Exp) (Γ : nat),
    EXP Γ ⊢ e ->
    Erel_open Γ e e.
Proof.
  intros.
  apply Erel_Vrel_Fundamental_helper.
  auto.
Qed.

Global Hint Resolve Erel_Fundamental : core.

Theorem Vrel_Fundamental :
  forall (v : Exp) (Γ : nat),
    VAL Γ ⊢ v ->
    Vrel_open Γ v v.
Proof.
  intros.
  apply Erel_Vrel_Fundamental_helper.
  auto.
Qed.

Global Hint Resolve Vrel_Fundamental : core.

Lemma Grel_ids : forall n, Grel n 0 idsubst idsubst.
Proof.
  intros.
  unfold Grel.
  intuition auto using scope_idsubst.
  exfalso; auto. inversion H.
Qed.

Theorem Vrel_Fundamental_closed :
  forall (v : Exp),
    VALCLOSED v ->
    forall n, Vrel n v v.
Proof.
  intros.
  replace v with (v.[idsubst]).
  eapply Vrel_Fundamental; eauto using Grel_ids. apply idsubst_is_id.
Qed.

Global Hint Resolve Vrel_Fundamental_closed : core.

Theorem Erel_Fundamental_closed :
  forall (e : Exp),
    EXPCLOSED e ->
    forall n, Erel n e e.
Proof.
  intros.
  replace e with (e.[idsubst]).
  eapply Erel_Fundamental; eauto using Grel_ids.
  apply idsubst_is_id.
Qed.

Global Hint Resolve Erel_Fundamental_closed : core.

Theorem Grel_Fundamental :
  forall (ξ : Substitution) (Γ : nat),
    SUBSCOPE Γ ⊢ ξ ∷ 0 ->
    forall n, Grel n Γ ξ ξ.
Proof.
  intros.
  unfold Grel.
  intuition. break_match_goal. apply Vrel_Fundamental_closed.
  specialize (H x H0). rewrite Heqs in H. auto.
  specialize (H x H0). rewrite Heqs in H. inversion H. 
Qed.

Global Hint Resolve Grel_Fundamental : core.

Lemma Frel_Case :
    forall n (e2 e2' e3 e3' : Exp) p (CL1 : EXP pat_vars p ⊢ e2) (CL2 : EXP pat_vars p ⊢ e2'),
    (forall m, m <= n -> forall vl1 vl2, length vl1 = pat_vars p -> list_biforall (Vrel m) vl1 vl2 -> Erel m e2.[list_subst vl1 idsubst] e2'.[list_subst vl2 idsubst]) ->
    (forall m, m <= n -> Erel m e3 e3') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCase p e2 e3::F1) (FCase p e2' e3'::F2).
Proof.
  intros. destruct H2, H3.
  specialize (H0 m H1) as H0'.
  apply Erel_closed in H0' as v. destruct v.
  split. 2: split. 1-2: constructor; auto; now constructor.
  intros.
  apply Vrel_closed in H7 as v. destruct v.
  inversion H8; subst; try inversion_is_value.
  * eapply match_pattern_Vrel in H18 as H18'. 2: apply H7. destruct H18' as [l2 [M2 Bif]].
    apply match_pattern_length in H18.
    eapply biforall_impl in Bif. 2: { intros; eapply Vrel_downclosed; exact H11. }
    specialize (H k ltac:(lia) l l2 (eq_sym H18) Bif) as [? [? ?]].
    eapply H12 in H19. destruct H19. exists (S x). eapply term_case_true; auto. exact M2.
    exact H13.
    lia. split; [ auto | split ]; auto. intros. eapply H4. 3: exact H14. lia. auto.
  * eapply nomatch_pattern_Vrel in H18 as H18'. 2: apply H7.
    destruct H0' as [? [? ?]]. eapply H13 in H19.
    destruct H19. exists (S x). apply term_case_false; auto. exact H14.
    lia. split; [ auto | split ]; auto. intros. eapply H4. 3: exact H15. lia. auto.
  Unshelve. lia.
Qed.

Lemma Frel_Let :
    forall n (e2 e2' : Exp) x x',
    (forall m v1 v2, m <= n -> Vrel m v1 v2 -> Erel m (e2.[v1/]) (e2'.[v2/])) ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FLet x e2::F1) (FLet x' e2'::F2).
Proof.
  intros. destruct H1, H2.
  specialize (H m (ELit 0%Z) (ELit 0%Z) H0 ltac:(auto)) as H'.
  apply Erel_closed in H' as v. destruct v.
  apply subst_implies_scope_exp_1 in H4. apply subst_implies_scope_exp_1 in H5.
  split. 2: split. 1-2: constructor; auto; now constructor.
  intros. apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply (H k) in H16. destruct H16. exists (S x0). constructor. auto.
  exact H10. lia. eapply Vrel_downclosed. eauto. lia.

  split. 2: split. 1-2: easy. intros.
  eapply H3 in H13. exact H13. lia. auto.
Unshelve. lia.
Qed.

Lemma Frel_App1 :
    forall n (es es' : list Exp),
    list_biforall (fun e1 e2 => forall m, m <= n -> Erel m e1 e2) es es' ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp1 es::F1) (FApp1 es'::F2).
Proof.
  intros. destruct H1, H2. split. 2: split.
  * constructor; auto. constructor. eapply biforall_impl in H. apply biforall_erel_closed in H. apply H. intros. apply H4. exact H0.
  * constructor; auto. constructor. eapply biforall_impl in H. apply biforall_erel_closed in H. apply H. intros. apply H4. exact H0.
  * intros. destruct (Vrel_closed H4).
    inversion H5; subst; try inversion_is_value.
    - inversion H. subst. eapply H11 in H13. destruct H13. exists (S x).
      econstructor. auto. exact H8. exact H0. lia.
      apply Erel_App_compat_ind; auto.
      + eapply biforall_impl. 2: exact H14. intros. eapply H12. lia.
      + constructor.
      + eapply Vrel_downclosed. eauto.
      + intros. eapply H3 in H16. exact H16. lia. auto.
    - inversion H. subst. apply Vrel_Fun_right in H4 as v. destruct v, H8, H8.
      apply eq_sym, length_zero_iff_nil in H8. subst.
      rewrite Vrel_Fix_eq in H4. destruct H4, H8.
      rewrite Nat.eqb_refl in H9.
      specialize (H9 k ltac:(lia) [] [] (eq_refl _) (eq_refl _) ltac:(constructor)).
      eapply H9 in H12. destruct H12.
      exists (S x0). constructor. exact H10. lia.

      split. 2: split. 1-2: auto. intros. eapply H3 in H14. exact H14.
      lia. auto.
Unshelve. auto.
Qed.

Lemma Frel_App2 :
    forall n (es es' : list Exp) v1 v1' vs vs',
    (forall m, m <= n -> Vrel m v1 v1') ->
    list_biforall (fun v1 v2 => forall m, m <= n -> Vrel m v1 v2) vs vs' ->
    list_biforall (fun e1 e2 => forall m, m <= n -> Erel m e1 e2) es es' ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp2 v1 es vs::F1) 
                                                     (FApp2 v1' es' vs'::F2).
Proof.
  intros. destruct H3, H4.
  apply Erel_App_compat_ind.
  * eapply biforall_impl. 2: exact H1. intros. now apply H6.
  * eapply biforall_impl. 2: exact H0. intros. now apply H6.
  * now apply H.
  * easy.
  * easy.
  * intros. eapply H5 in H8. exact H8. lia. auto.
Qed.

Lemma Frel_BIF1 :
    forall n (es es' : list Exp),
    list_biforall (fun e1 e2 => forall m, m <= n -> Erel m e1 e2) es es' ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FBIF1 es::F1) (FBIF1 es'::F2).
Proof.
  intros. destruct H1, H2. split. 2: split.
  * constructor; auto. constructor. eapply biforall_impl in H. apply biforall_erel_closed in H. apply H. intros. apply H4. exact H0.
  * constructor; auto. constructor. eapply biforall_impl in H. apply biforall_erel_closed in H. apply H. intros. apply H4. exact H0.
  * intros. destruct (Vrel_closed H4).
    inversion H5; subst; try inversion_is_value.
    - inversion H. subst. eapply H11 in H13. destruct H13. exists (S x).
      econstructor. auto. exact H8. exact H0. lia.
      apply Erel_BIF_compat_ind; auto.
      + eapply biforall_impl. 2: exact H14. intros. eapply H12. lia.
      + constructor.
      + eapply Vrel_downclosed. eauto.
      + intros. eapply H3 in H16. exact H16. lia. auto.
Unshelve. auto.
Qed.

Lemma Frel_BIF2 :
    forall n (es es' : list Exp) v1 v1' vs vs',
    (forall m, m <= n -> Vrel m v1 v1') ->
    list_biforall (fun v1 v2 => forall m, m <= n -> Vrel m v1 v2) vs vs' ->
    list_biforall (fun e1 e2 => forall m, m <= n -> Erel m e1 e2) es es' ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FBIF2 v1 es vs::F1) 
                                                     (FBIF2 v1' es' vs'::F2).
Proof.
  intros. destruct H3, H4.
  apply Erel_BIF_compat_ind.
  * eapply biforall_impl. 2: exact H1. intros. now apply H6.
  * eapply biforall_impl. 2: exact H0. intros. now apply H6.
  * now apply H.
  * easy.
  * easy.
  * intros. eapply H5 in H8. exact H8. lia. auto.
Qed.

Lemma Frel_Cons_tail :
    forall n (e2 e2' : Exp),
    (forall m, m <= n -> Erel m e2 e2') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons1 e2::F1) (FCons1 e2'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Erel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply H' in H15. destruct H15. exists (S x). econstructor. auto. exact H10. lia.

  split. 2: split. 1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H13 as v. destruct v.
  inversion H14; subst; try inversion_is_value.

  eapply H3 in H24. subst. destruct H24. exists (S x).
  constructor; auto. exact H18. lia. subst. eapply Vrel_Cons_compat_closed.
  eapply Vrel_downclosed; eassumption.
  eapply Vrel_downclosed; eassumption.
Unshelve. all: lia.
Qed.

Lemma Frel_Cons_head :
    forall n (v1 v1' : Exp),
    (forall m, m <= n -> Vrel m v1 v1') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons2 v1::F1) (FCons2 v1'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Vrel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor. intros.
  apply Vrel_closed in H6 as v. destruct v.
  inversion H7; subst; try inversion_is_value.
  eapply H3 in H16. 2: lia. destruct H16. exists (S x).
  econstructor; auto. exact H10.

  eapply Vrel_Cons_compat_closed.
  eapply Vrel_downclosed; eassumption.
  eapply Vrel_downclosed; eassumption.
Unshelve. all: lia.
Qed.

Theorem Frel_Fundamental_closed :
  forall (F : FrameStack) (n : nat),
    FSCLOSED F ->
    Frel n F F.
Proof.
  induction F; intros.
  * cbn. split. 2: split. 1-2: constructor. intros.
    exists 0. constructor. apply Vrel_closed in H0; apply H0.
  * split. 2: split. all: auto. intros. destruct a; inversion H; inversion H4.
    - eapply Frel_App1; eauto. subst. eapply forall_biforall_refl, Forall_impl.
      2: exact H7. intros. auto.
    - eapply Frel_App2; eauto; subst.
      + eapply forall_biforall_refl, Forall_impl. 2: exact H11. intros. auto.
      + eapply forall_biforall_refl, Forall_impl. 2: exact H10. intros. auto.
    - eapply Frel_Let; eauto.
      intros. subst. eapply Erel_Fundamental; eauto. unfold Grel.
      destruct (Vrel_closed H10). split. 2: split.
      1-2: apply cons_scope; auto.
      intros. inversion H6; subst. 2: inversion H11. simpl. auto.
    - eapply Frel_Case; eauto.
      intros. subst. eapply Erel_Fundamental; eauto.
      rewrite <- H12. eapply (Grel_list _ _ _ _ _ 0) in H13.
      rewrite Nat.add_0_r in H13. exact H13. apply Grel_Fundamental.
      apply scope_idsubst.
    - eapply Frel_Cons_tail; eauto.
    - eapply Frel_Cons_head; eauto.
    - eapply Frel_BIF1; eauto. subst. eapply forall_biforall_refl, Forall_impl.
      2: exact H7. intros. auto.
    - eapply Frel_BIF2; eauto; subst.
      + eapply forall_biforall_refl, Forall_impl. 2: exact H11. intros. auto.
      + eapply forall_biforall_refl, Forall_impl. 2: exact H10. intros. auto.
Qed.

Global Hint Resolve Frel_Fundamental_closed : core.

