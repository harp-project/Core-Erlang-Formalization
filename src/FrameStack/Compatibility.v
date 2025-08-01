(**
  This file proves the compatibility (congruence) properties of logical relations.
*)

From CoreErlang.FrameStack Require Export LogRel SubstSemanticsLemmas.
Import ListNotations.

Lemma Vrel_Tuple_compat_rev :
  forall m l l',
  Vrel m (VTuple l) (VTuple l') ->
  list_biforall (Vrel m) l l'.
Proof.
  induction l; destruct l'; rewrite Vrel_Fix_eq; simpl; intros;
  destruct H as [Hcl1 [Hcl2 H]]; try contradiction; constructor.
  rewrite Vrel_Fix_eq; apply H. apply IHl. rewrite Vrel_Fix_eq.
  simpl. split. 2: split. 3: apply H.
  all: destruct_scopes; constructor; intros.
  1: apply (H3 (S i)); slia.
  1: apply (H2 (S i)); slia.
Qed.

Lemma Vrel_Map_compat_rev :
  forall m l l',
  Vrel m (VMap l) (VMap l') ->
  list_biforall (fun '(a, b) '(c, d) => Vrel m a c /\ Vrel m b d) l l'.
Proof.
  induction l; destruct l'; try destruct a; try destruct p; rewrite Vrel_Fix_eq; simpl; intros;
  destruct H as [Hcl1 [Hcl2 H]]; try contradiction; constructor.
  split. 1-2: rewrite Vrel_Fix_eq; apply H. apply IHl. rewrite Vrel_Fix_eq.
  simpl. split. 2: split. 3: apply H.
  all: destruct_scopes; constructor; intros.
  1: apply (H2 (S i)); slia.
  1: apply (H5 (S i)); slia.
  1: apply (H1 (S i)); slia.
  1: apply (H3 (S i)); slia.
Qed.

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
Lemma Vrel_FunId_Var_compat :
  forall Γ n a,
  n < Γ ->
  Vrel_open Γ (VFunId (n, a)) (VVar n).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; simpl; intuition.
  now rewrite Heqs, Heqs0.
Qed.

Global Hint Resolve Vrel_FunId_Var_compat : core.

Lemma Vrel_Var_FunId_compat :
  forall Γ n a,
  n < Γ ->
  Vrel_open Γ (VVar n) (VFunId (n, a)).
Proof.
  unfold Vrel_open, Grel. intros. destruct H0, H1. simpl subst. specialize (H2 n H).
  repeat break_match_hyp; simpl; intuition.
  now rewrite Heqs, Heqs0.
Qed.

Global Hint Resolve Vrel_Var_FunId_compat : core.

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
Qed.

Global Hint Resolve Vrel_Lit_compat_closed : core.

Lemma Vrel_Lit_compat :
  forall Γ l,
  Vrel_open Γ (VLit l) (VLit l).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Lit_compat : core.

Lemma Vrel_Pid_compat_closed :
  forall m p1 p2,
  Vrel m (VPid p1) (VPid p2).
Proof.
  intros. rewrite Vrel_Fix_eq. unfold Vrel_rec. repeat constructor.
Qed.

Global Hint Resolve Vrel_Pid_compat_closed : core.

Lemma Vrel_Pid_compat :
  forall Γ p1 p2,
  Vrel_open Γ (VPid p1) (VPid p2).
Proof.
  unfold Vrel_open. intros. simpl. auto.
Qed.

Global Hint Resolve Vrel_Pid_compat : core.

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
    unfold convert_to_closlist; rewrite length_app, length_map; try rewrite length_map
  | [H : context G [Datatypes.length ((convert_to_closlist _) ++ _)] |- _] =>
    unfold convert_to_closlist in H; rewrite length_app, length_map,length_map in H
  | |- context G [Datatypes.length (convert_to_closlist _) ] =>
    unfold convert_to_closlist; rewrite length_map,length_map
  | [H : context G [Datatypes.length (convert_to_closlist _)] |- _] =>
    unfold convert_to_closlist in H; rewrite length_map,length_map in H
  end.

Lemma Vrel_Clos_compat :
  forall Γ ext1 ext2 id1 id2 vl1 vl2 b1 b2,
  vl1 = vl2 -> id1 = id2 ->
  Erel_open (length ext1 + vl1 + Γ) b1 b2 ->
  list_biforall (fun '(i, v, e) '(i2, v2, e2) => 
    v = v2 /\ i = i2 /\ Erel_open (length ext1 + v + Γ) e e2) ext1 ext2 ->
  Vrel_open Γ (VClos ext1 id1 vl1 b1) (VClos ext2 id2 vl2 b2).
Proof.
  unfold Vrel_open. intros. subst.
  revert H2 H1 H3.
  revert ext1 ext2 id2 vl2 b1 b2 ξ₁ ξ₂.
  induction n using Wf_nat.lt_wf_ind. intros.
  subst.
  simpl. rewrite Vrel_Fix_eq. unfold Vrel_rec at 1. intuition idtac.
  - constructor; simpl.
    (* scope of environmental extension of closure 1 *)
    + rewrite length_map, map_map, map_map. intros.
      pose proof (biforall_forall _ _ _ (0, 0, ˝VNil) (0, 0, ˝VNil) H2 i H0).
      extract_map_fun F.
      replace 0 with (F (0, 0, ˝VNil)) at 1 by (now subst).
      rewrite map_nth.
      extract_map_fun G.
      replace (˝VNil) with (G (0, 0, ˝VNil)) at 2 by (now subst).
      rewrite map_nth.
      subst F G.
      destruct (nth i ext1 (0, 0, ˝ VNil)), p.
      destruct (nth i ext2 (0, 0, ˝ VNil)), p.
      inv H4. destruct H6 as [H7 H6]. eapply Erel_open_scope in H6 as [H6 _].
      apply -> subst_preserves_scope_exp. exact H6.
      apply upn_scope. now apply H3.
    (* scope of body of closure 1 *)
    + eapply Erel_open_scope in H1 as [H1 _]. rewrite length_map.
      apply -> subst_preserves_scope_exp. exact H1.
      apply upn_scope. now apply H3.
  - apply biforall_length in H2 as H2'. rewrite <- H2' in *.
    constructor; simpl.
  (* scope of environmental extension of closure 2 *)
    + rewrite length_map, map_map, map_map. intros.
      rewrite <- H2' in *.
      pose proof (biforall_forall _ _ _ (0, 0, ˝VNil) (0, 0, ˝VNil) H2 i H0).
      extract_map_fun F.
      replace 0 with (F (0, 0, ˝VNil)) at 1 by (now subst).
      rewrite map_nth.
      extract_map_fun G.
      replace (˝VNil) with (G (0, 0, ˝VNil)) at 2 by (now subst).
      rewrite map_nth.
      subst F G.
      destruct (nth i ext1 (0, 0, ˝ VNil)), p.
      destruct (nth i ext2 (0, 0, ˝ VNil)), p.
      inv H4. cbn. destruct H6 as [H7 H6]. eapply Erel_open_scope in H6 as [_ H6].
      apply -> subst_preserves_scope_exp. exact H6.
      apply upn_scope. now apply H3.
    (* scope of body of closure 2 *)
    + eapply Erel_open_scope in H1 as [_ H1]. rewrite length_map.
      apply -> subst_preserves_scope_exp. exact H1.
      rewrite <- H2' in *.
      apply upn_scope. now apply H3. 
  - unfold Erel_open, Erel in H0.
    do 2 rewrite subst_comp_exp. epose proof (nH0 := H1 m _ _ _).
    destruct nH0 as [nCl1 [nCl2 nH0]].
    split. 2: split. exact nCl1. exact nCl2. intros. eapply nH0.
    3: exact H6.
    lia. assumption.
  Unshelve.
      subst; apply biforall_length in H4 as Hvl1vl0.
      apply biforall_length in H2 as Hext1ext2.
      split. 2: split.
      (** scopes **)
      1-2: rewrite subst_list_extend; auto;[
        |simpl_convert_length; auto].
      1-2: apply scoped_list_subscoped_eq;[
        simpl_convert_length; auto| |apply H3].
      1-2: rewrite indexed_to_forall; intros.
      1: {
        eapply nth_possibilities in H0 as [[Hs Hlia]|[Hs [Hlia1 Hlia2]]];
        repeat simpl_convert_length; rewrite Hs; clear Hs.
        Unshelve.
        3-4: exact VNil.
        * unfold convert_to_closlist. rewrite map_map.
          extract_map_fun F.
          (* these "strange", big extensions are obtained from the simplification of F! If you rewrite this part, first define some default value for d', and then check what is F d', next
          you can modify the chosen d' to fit the purpose of F. 
          This also applies to the other similar places in this proof ↓ *)
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (˝VNil)).
          2: rewrite length_map; lia.
          replace (VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (˝VNil)) with (F (0, 0, ˝VNil)) by now subst F.
          rewrite map_nth. destruct (nth i ext1 (0, 0, ˝ VNil)) eqn:P.
          destruct p. subst F. simpl.
          eapply biforall_forall with (i := i) in H2 as H2'.
          rewrite P in H2'. 2: lia. Unshelve. 2: exact (0, 0, ˝VNil).
          destruct (nth i ext2 (0, 0, ˝ VNil)) eqn:P2. destruct p.
          inv H2'. constructor.
          - intros. do 2 rewrite map_map. repeat rewrite length_map in *.
            extract_map_fun F. replace 0 with (F (0, 0, ˝VNil)) by now subst F.
            rewrite map_nth.
            extract_map_fun G. replace (˝VNil) with (G (0, 0, ˝VNil)) at 3 by now subst G.
            rewrite map_nth.
            destruct (nth i0 ext1 (0, 0, ˝ VNil)) eqn:P3. destruct p.
            subst F G. cbn.
            eapply biforall_forall with (i := i0) in H2 as H2''. 2: lia.
            rewrite P3 in H2''.
            Unshelve. 2: exact (0, 0, ˝VNil).
            destruct (nth i0 ext2 (0, 0, ˝ VNil)). destruct p. inv H2''.
            destruct H7 as [H8 H7].
            apply Erel_open_scope in H7 as [H7 _].
            apply -> subst_preserves_scope_exp. exact H7.
            apply upn_scope. apply H3.
          - rewrite length_map. apply -> subst_preserves_scope_exp.
            destruct H5 as [H6 H5].
            apply Erel_open_scope in H5 as [H5 _]. exact H5.
            apply upn_scope. apply H3.
        * eapply biforall_forall with (i := i - length ext1) in H4. 2: lia.
          apply Vrel_closed_l in H4. exact H4.
      }
      1: {
        (* this is the symmetric version of the previous proof *)
        eapply nth_possibilities in H0 as [[Hs Hlia]|[Hs [Hlia1 Hlia2]]]; rewrite Hs; clear Hs; repeat simpl_convert_length.
        Unshelve.
        3: exact VNil.
        * unfold convert_to_closlist. rewrite map_map.
          extract_map_fun F.
          (* these "strange", big extensions are obtained from the simplification of F! If you rewrite this part, first define some default value for d', and then check what is F d', next
          you can modify the chosen d' to fit the purpose of F. 
          This also applies to the other similar places in this proof ↓ *)
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (˝VNil)).
          2: rewrite length_map; lia.
          replace (VClos (map
          (fun '(y, x) =>
           let '(i0, ls) := y in (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (˝VNil)) with (F (0, 0, ˝VNil)) by now subst F.
          rewrite map_nth. destruct (nth i ext1 (0, 0, ˝ VNil)) eqn:P.
          destruct p. subst F. simpl.
          eapply biforall_forall with (i := i) in H2 as H2'.
          rewrite P in H2'. 2: lia. Unshelve. 2: exact (0, 0, ˝VNil).
          destruct (nth i ext2 (0, 0, ˝ VNil)) eqn:P2. destruct p.
          inv H2'. constructor.
          - intros. do 2 rewrite map_map. repeat rewrite length_map in *.
            extract_map_fun F. replace 0 with (F (0, 0, ˝VNil)) by now subst F.
            rewrite map_nth.
            extract_map_fun G. replace (˝VNil) with (G (0, 0, ˝VNil)) at 3 by now subst G.
            rewrite map_nth.
            destruct (nth i0 ext1 (0, 0, ˝ VNil)) eqn:P3. destruct p.
            subst F G. cbn.
            eapply biforall_forall with (i := i0) in H2 as H2''. 2: lia.
            rewrite P3 in H2''.
            Unshelve. 2: exact (0, 0, ˝VNil).
            destruct (nth i0 ext2 (0, 0, ˝ VNil)). destruct p. inv H2''.
            destruct H7 as [H8 H7].
            apply Erel_open_scope in H7 as [_ H7].
            apply -> subst_preserves_scope_exp. exact H7.
            cbn. rewrite Hext1ext2. apply upn_scope. apply H3.
          - rewrite length_map. apply -> subst_preserves_scope_exp.
            destruct H5 as [H6 H5].
            apply Erel_open_scope in H5 as [_ H5]. exact H5.
            rewrite Hext1ext2. apply upn_scope. apply H3.
        * eapply biforall_forall with (i := i - length ext1) in H4. 2: lia.
          apply Vrel_closed_r in H4.
          rewrite <- Hext1ext2. exact H4.
      }
      (** scopes up to this point **)
      intros.
      do 2 (rewrite substcomp_list_eq; [|simpl_convert_length; lia]).
      do 2 rewrite substcomp_id_l.
      epose proof (list_subst_get_possibilities _ _ _) as [[Hs Hlia]|[Hs Hlia]];
      epose proof (list_subst_get_possibilities _ _ _) as [[Hs2 Hlia2]|[Hs2 Hlia2]].
      * rewrite Hs, Hs2.
        eapply nth_possibilities in Hlia as [[Hs3 Hlia3]|[Hs3 [Hlia31 Hlia32]]];
        eapply nth_possibilities in Hlia2 as [[Hs4 Hlia4]|[Hs4 [Hlia41 Hlia42]]].
        + repeat simpl_convert_length. rewrite Hs3, Hs4.
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (˝VNil)).
          2: simpl_convert_length; lia.
          unfold convert_to_closlist at 1. rewrite map_map.
          extract_map_fun F.
          replace (VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext1 + ls) ξ₁]))
          ext1) 0 0 (˝VNil)) with (F (0, 0, ˝VNil)) by now subst F.
          rewrite map_nth.
          rewrite nth_indep with (d' := VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (˝VNil)).
          2: simpl_convert_length; lia.
          unfold convert_to_closlist at 1. rewrite map_map.
          extract_map_fun G.
          replace (VClos (map
          (fun '(y, x0) =>
           let '(i, ls) := y in (i, ls, x0.[upn (Datatypes.length ext2 + ls) ξ₂]))
          ext2) 0 0 (˝VNil)) with (G (0, 0, ˝VNil)) by now subst G.
          rewrite map_nth.
          destruct (nth x ext1 (0, 0, ˝ VNil)) eqn:P1.
          destruct (nth x ext2 (0, 0, ˝ VNil)) eqn:P2.
          destruct p, p0. subst F G. simpl.
          assert (n1 = n3 /\ n0 = n2) as [? ?]. {
            eapply biforall_forall with (i := x) in H2.
            rewrite P1, P2 in H2. split; apply H2.
            lia.
          }
          subst.
          apply H; auto.
          2: eapply Grel_downclosed; eauto.
          eapply biforall_forall with (i := x) in H2.
          rewrite P1, P2 in H2. apply H2.
          lia.
        + repeat simpl_convert_length.
          rewrite Hvl1vl0, Hext1ext2 in *. lia.
        + repeat simpl_convert_length.
          rewrite Hvl1vl0, Hext1ext2 in *. lia.
        + rewrite Hs3, Hs4. repeat simpl_convert_length.
          do 2 rewrite length_map.
          eapply biforall_forall in H4. rewrite Hext1ext2. exact H4.
          lia.
      * repeat simpl_convert_length. lia.
      * shelve. (* we prove this after the next goal *)
      * rewrite Hs, Hs2. repeat simpl_convert_length.
        rewrite length_app, length_map, length_map.
        destruct H3 as [Hss1 [Hss2 Hrel]].
        specialize (Hrel (x - (length ext1 + length vl1)) ltac:(lia)).
        rewrite Hext1ext2, Hvl1vl0 in *.
        repeat break_match_goal; trivial.
        eapply Vrel_downclosed; eassumption.
  Unshelve.
  1: exact VNil.
  1,3: lia.
  repeat simpl_convert_length. lia.
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
      apply H4. simpl in H1. lia.
  * constructor. intros. destruct i.
    - now apply Vrel_closed_r in H.
    - simpl. apply Vrel_closed_r in IHlist_biforall. destruct_scopes.
      apply H4. simpl in H1. lia.
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
    - apply H4. lia.
    - apply H8. lia.
  * destruct IHlist_biforall as [? [? _]]. destruct hd, hd', H.
    apply Vrel_closed_r in H. apply Vrel_closed_r in H3.
    destruct_scopes.
    constructor; intros; simpl in *; destruct i; auto.
    - apply H5. lia.
    - apply H7. lia.
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
    Erel n (˝v) (˝v').
Proof.
  intros.
  unfold Erel, exp_rel.
  pose proof (Vrel_possibilities H).
  intuition eauto.
  * destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]].
    inv H3. 2: { inv H1. }
    eapply HD1 in H6 as [k' HDF]; [|lia|].
    eexists. constructor. auto. exact HDF.
    now constructor.
  * do 2 destruct_hyps. subst.
    destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]].
    inv H2. 2: { inv H0. }
    eapply HD1 in H4 as [k' HDF]; [|lia|].
    eexists. constructor. auto. exact HDF.
    now constructor.
  * do 2 destruct_hyps. subst.
    destruct H0 as [Hcl1 [Hcl2 [HD1 HD2]]].
    inv H2. 2: { inv H0. }
    eapply HD1 in H4 as [k' HDF]; [|lia|].
    eexists. constructor. inv H1. auto. exact HDF.
    constructor; auto.
  * do 5 destruct_hyps. subst.
    destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H4 as [k' HDF]; [|lia|].
    eexists. constructor. now apply Vrel_closed_r in H. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
  * do 3 destruct_hyps. subst.
    destruct H0 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H4 as [k' HDF]; [|lia|].
    eexists. constructor. now apply Vrel_closed_r in H. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
  * do 3 destruct_hyps. subst.
    destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H4 as [k' HDF]; [|lia|].
    eexists. constructor. now apply Vrel_closed_r in H. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
  * do 9 destruct_hyps. subst.
    destruct H1 as [Hcl1 [Hcl2 [HD1 HD2]]]. subst.
    inv H2. 2: { inv H0. }
    eapply HD1 in H4 as [k' HDF]; [|lia|].
    eexists. constructor. now apply Vrel_closed_r in H. exact HDF.
    constructor. eapply Vrel_downclosed. eauto. auto.
Unshelve.
  all: lia.
Qed.

Global Hint Resolve Erel_Val_compat_closed : core.

Lemma Erel_Val_compat :
  forall {Γ v v'},
    Vrel_open Γ v v' ->
    Erel_open Γ (˝v) (˝v').
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
  8-10: auto.
  1-6: destruct v1, v2; inv H0; rewrite Vrel_Fix_eq in H; destruct H as [_ [_ ?]]; try contradiction.
  * eexists. split. reflexivity. auto.
  * break_match_hyp; try congruence. invSome.
    apply Lit_eqb_eq in Heqb. subst. simpl. rewrite Lit_eqb_refl.
    eexists. split. simpl. reflexivity. auto.
  * eexists. split. reflexivity. constructor; auto.
  * subst. eexists. split. reflexivity. constructor; auto.
  * subst. eexists. split. reflexivity. constructor; auto.
  * subst. eexists. split. reflexivity. constructor; auto.
    rewrite Vrel_Fix_eq; split; auto.
  * subst. eexists. split. reflexivity. constructor; auto.
    rewrite Vrel_Fix_eq; split; auto.
  * subst. eexists. split. reflexivity. constructor; auto.
    rewrite Vrel_Fix_eq; split; auto.
  * subst. eexists. split. reflexivity. constructor; auto.
    rewrite Vrel_Fix_eq; split; auto.
  * break_match_hyp; try congruence.
    break_match_hyp; try congruence. inv H4.
    inv H. destruct_scopes. rewrite <- Vrel_Fix_eq in H0.
    rewrite <- Vrel_Fix_eq in H3.
    eapply IHp1 in H0. eapply IHp2 in H3. all:eauto.
    do 4 destruct_hyps.
    eexists. split. simpl. rewrite H0, H. reflexivity.
    now apply biforall_app.
  * destruct_scopes. generalize dependent l0.
    generalize dependent l2. revert l1. induction l; intros.
    - destruct l0, l2; try congruence. 2: contradiction.
      inv H4. exists []. split; auto.
    - inv IHp.
      destruct l0, l2; try congruence. 1: contradiction.
      repeat break_match_hyp; try congruence. inv H4.
      destruct_hyps.
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
      do 3 destruct_hyps.
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
  * auto.
Qed.

Corollary match_pattern_list_Vrel : forall pl vl1 vl2 n,
  list_biforall (Vrel n) vl1 vl2 ->
  (forall l1, 
        (match_pattern_list pl vl1 = Some l1 ->
         exists l2, match_pattern_list pl vl2 = Some l2 /\
                    list_biforall (Vrel n) l1 l2)).
Proof.
  induction pl; intros.
  * inv H. eexists. split. reflexivity.
    inv H0. now auto.
  * simpl in H0. inv H.
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
    break_match_hyp; try congruence; break_match_goal.
    subst. congruence. reflexivity.
(*   * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition.
    break_match_hyp; try congruence; break_match_goal.
    subst. congruence. reflexivity. *)
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition. destruct_scopes.
    break_match_hyp; try congruence.
    break_match_hyp; try congruence.
    - eapply IHp2 in Heqo0. rewrite Heqo0. all: auto.
      now break_match_goal.
      rewrite Vrel_Fix_eq. eassumption.
    - eapply IHp1 in Heqo. now rewrite Heqo. all: auto.
      rewrite Vrel_Fix_eq. eassumption.
  * destruct v1, v2; rewrite Vrel_Fix_eq in H; simpl in *;
    try congruence; intuition. destruct_scopes. clear H7 H6.
    generalize dependent l0. generalize dependent l1. induction l; intros.
    - destruct l1; auto. destruct l0; auto. contradiction.
    - destruct_foralls.
      destruct l0.
      + destruct l1; auto. contradiction.
      + destruct l1; auto.
        destruct (match_pattern a v) eqn:D1.
        ** break_match_goal; auto.
           destruct_hyps.
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
    try congruence; intuition. destruct_scopes. clear H3 H10 H2 H11.
    generalize dependent l0. generalize dependent l1. induction l; intros.
    - destruct l1; auto. destruct l0; auto. destruct p; contradiction.
    - destruct_foralls.
      destruct l0.
      + destruct l1; auto. contradiction.
      + destruct l1; destruct a; auto.
        destruct p0, p. do 3 destruct_hyps.
        destruct (match_pattern p1 v1) eqn:D1.
        ** destruct (match_pattern p2 v2) eqn:D2.
           -- break_match_goal; auto.
              break_match_hyp. congruence.
              eapply (IHl H3) in Heqo0. rewrite Heqo0.
              now break_match_goal.
              now (intros; apply (H6 (S i) ltac:(snia))).
              now (intros; apply (H8 (S i) ltac:(snia))).
              eassumption.
              now (intros; apply (H4 (S i) ltac:(snia))).
              now (intros; apply (H9 (S i) ltac:(snia))).
           -- eapply H1 in D2. rewrite D2.
              now break_match_goal.
              now apply (H9 0 ltac:(snia)).
              now (rewrite Vrel_Fix_eq; eassumption).
              now apply (H8 0 ltac:(snia)).
        ** eapply H in D1. now rewrite D1.
           now apply (H4 0 ltac:(snia)).
           now (rewrite Vrel_Fix_eq; eassumption).
           now apply (H6 0 ltac:(snia)).
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
     (d1 := ([]:list Pat, ˝VNil, ˝VNil))
     (d2 := ([]:list Pat, ˝VNil, ˝VNil)) in H0; [|try eassumption].
  4,6: rewrite Hlen; exact H.
  1-4: do 2 rewrite map_nth with (d := ([]:list Pat, ˝VNil, ˝VNil)).
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
  1-2: rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)).
  1-2: intros; eapply biforall_forall with
     (d1 := ([]:list Pat, ˝VNil, ˝VNil))
     (d2 := ([]:list Pat, ˝VNil, ˝VNil)) in H0; [|try eassumption].
  3: try rewrite Hlen; exact H1.
  1-2: destruct nth, nth, p, p0, H0; cbn; subst.
  1-2: pose proof (repeat_length VNil (PatListScope l1)).
  1-2: pose proof (Forall_repeat (fun v => VALCLOSED v) VNil (PatListScope l1) ltac:(constructor)) as Fr.
  1-2: assert (list_biforall (Vrel 0) (repeat VNil (PatListScope l1)) (repeat VNil (PatListScope l1))) as H'H by
    (clear; induction (PatListScope l1); simpl; constructor; auto).
  1-2: apply H2 in H'H as [H'1 H'2]; [|lia|now rewrite repeat_length].
  1-2: apply Erel_closed in H'1 as [H'11 H'12], H'2 as [H'21 H'22].
  1-2: split; fold (PatListScope l1); rewrite <- H0; now apply subst_implies_list_scope.
  (* evaluation *)
  generalize dependent k.
  induction H0; split; intros; try split; intros.
  * inv H1. destruct H as [_ [_ [_ H]]].
    eapply H in H4. destruct H4 as [k2 D]. eexists. constructor. exact D.
    lia. unfold if_clause. split; auto. intros. split; apply Vrel_Lit_compat_closed.
  * inv H1. destruct H as [_ [_ [_ H]]].
    eapply H in H7. destruct H7 as [k2 D]. eexists. constructor. 
    congruence. exact D.
    lia. fold (Excrel k0 e1 e2). eapply Excrel_downclosed. exact H0.
    Unshelve. lia.
  * inv H0.
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
      1-2: rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)).
      1-2: intros; eapply biforall_forall with
        (d1 := ([]:list Pat, ˝VNil, ˝VNil))
        (d2 := ([]:list Pat, ˝VNil, ˝VNil)) in H0; [|try eassumption].
      3: assert (length tl = length tl') as Hlen' by lia;
           rewrite Hlen'; exact H.
      1-2: destruct nth, nth, p, p0, H0; cbn; subst.
      1-2: pose proof (repeat_length VNil (PatListScope l0)).
      1-2: pose proof (Forall_repeat (fun v => VALCLOSED v) VNil (PatListScope l0) ltac:(constructor)) as Fr.
      1-2: assert (list_biforall (Vrel 0) (repeat VNil (PatListScope l0)) (repeat VNil (PatListScope l0))) as H'H by
        (clear; induction (PatListScope l0); simpl; constructor; auto).
      1-2: apply H3 in H'H as [H'1 H'2]; [|lia|now rewrite repeat_length].
      1-2: apply Erel_closed in H'1 as [H'11 H'12], H'2 as [H'21 H'22].
      1-2: split; fold (PatListScope l0); rewrite <- H0; now apply subst_implies_list_scope.
      (* evaluation *)
      split. 2: split.
      + (* valid *)
        intros. inv H3.
        ** (* true guard *)
           inv H. inv H7.
           destruct hd'; simpl in H5; destruct H5 as [_ [_ H5]];
           try contradiction.
           subst.
           eapply He in H10 as [k4 D]. eexists. econstructor.
           eassumption.
           lia.
           fold (Frel k1 F1 F2). eapply Frel_downclosed. exact H1.
           Unshelve. lia.
        ** (* false guard *)
           inv H. inv H7.
           destruct hd'; simpl in H5; destruct H5 as [_ [_ H5]];
           try contradiction.
           subst.
           eapply IHlist_biforall in H10 as [k4 D].
           eexists. constructor. exact D.
           lia.
           2: exact H1.
           1-2: lia.
           eapply biforall_impl. 2: exact H2.
           intros. eapply Vrel_downclosed. exact H3. Unshelve. lia.
      + (* exception *)
        intros. inv H3. eapply H1 in H9 as [k4 D]. eexists. constructor.
        reflexivity.
        exact D.
        lia.
        fold (Excrel k1 e0 e3). eapply Excrel_downclosed. exact H.
        Unshelve. lia.
      + intros. inv H.
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
    reflexivity.
    exact D.
    lia.
    fold (Excrel k0 e1 e2). eapply Excrel_downclosed. exact H2.
    Unshelve. lia.
  * inv H2.
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
  apply forall_biforall with (d1 := ([], ˝VNil, ˝VNil)) (d2 := ([], ˝VNil, ˝VNil)).
  now do 2 rewrite length_map.
  rewrite length_map. intros.
  apply biforall_forall with
    (i := i) (d1 := ([], ˝VNil, ˝VNil)) (d2 := ([], ˝VNil, ˝VNil)) in H0; auto.
  extract_map_fun F.
  replace ([], ˝VNil, ˝VNil) with (F ([], ˝VNil, ˝VNil)) by now subst F.
  rewrite map_nth. (* replace does not work at position 1, its buggy *)
  extract_map_fun G.
  replace (F ([], ˝VNil, ˝VNil)) with (G ([], ˝VNil, ˝VNil)) by now subst F G.
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
    Erel_open Γ (˝VVar n) (˝VVar n).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_Var_compat : core.

(* TODO NOTE: currently, function arities are not yet checked when doing the substitution, however, this is going to change! *)
Lemma Erel_FunId_compat :
  forall Γ n a,
    n < Γ ->
    Erel_open Γ (˝VFunId (n, a)) (˝VFunId (n, a)).
Proof.
  auto.
Qed.

Global Hint Resolve Erel_FunId_compat : core.

Lemma Erel_Lit_compat :
  forall Γ l,
    Erel_open Γ (˝VLit l) (˝VLit l).
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
  lia.
  constructor; auto.
  rewrite Vrel_Fix_eq. simpl.
  split. 2: split.
  1-2: constructor; simpl; try (intro; lia).
  1-2: apply Erel_open_scope in H0; apply -> subst_preserves_scope_exp.
  1,3: apply H0.
  1,2: apply upn_scope; apply H.
  intuition. unfold Erel_open, Erel in H0.
  do 2 rewrite subst_comp_exp. apply H0.
  apply Grel_list_subst; auto. eapply Grel_downclosed in H. eassumption.
  Unshelve. lia.
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
    split. 2: split.
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
      1: { eexists. constructor. reflexivity. exact D. }
      1: lia.
      fold (Excrel k e0 e3). eapply Excrel_downclosed. apply H1.
    - intros. inv H1.
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

Lemma Erel_Seq_compat_closed :
  forall m (e1 e1' e2 e2': Exp),
    Erel m e1 e1' ->
    Erel m e2 e2' ->
    Erel m (ESeq e1 e2) (ESeq e1' e2').
Proof.
  intros. split. 2: split.
  1-2: do 2 constructor; apply Erel_closed in H, H0; try apply H; apply H0.
  intros. inv H2. 2: inv_val.
  eapply H in H7 as [k1 D1]. eexists. constructor. exact D1.
  lia.
  split. 2: split.
  1-2: constructor; try apply H1; constructor; apply Erel_closed in H0; apply H0.
  split. 2: split.
  {
    (* normal evaluation *)
    intros. inv H5. inv H4. inv H10. eapply H0 in H11 as [k2 D2].
    eexists. constructor. exact D2.
    lia.
    eapply Frel_downclosed. eassumption.
  }
  {
    (* exception *)
    intros. inv H5. eapply H1 in H12 as [k2 D2].
    eexists. constructor. reflexivity. exact D2.
    lia.
    eapply Excrel_downclosed. eassumption.
  }
  {
    intros. inv H4.
  }
Unshelve.
  all:lia.
Qed.

Global Hint Resolve Erel_Seq_compat_closed : core.

Lemma Erel_Seq_compat :
  forall Γ (e1 e1' e2 e2': Exp),
  Erel_open Γ e1 e1' ->
  Erel_open Γ e2 e2' ->
  Erel_open Γ (ESeq e1 e2) (ESeq e1' e2').
Proof.
  unfold Erel_open. intros. simpl.
  apply Erel_Seq_compat_closed; auto.
Qed.

Global Hint Resolve Erel_Seq_compat : core.

Lemma Erel_Try_compat_closed :
  forall n x x' (e2 e2' : Exp), x = x' ->
    (forall m (Hmn : m <= n) vl vl',
        length vl = x ->
        list_biforall (Vrel m) vl vl' ->
        Erel m e2.[list_subst vl idsubst]
               e2'.[list_subst vl' idsubst]) ->
  forall y y' e3 e3', y = y' ->
    (forall m (Hmn : m <= n) vl vl',
        length vl = y ->
        list_biforall (Vrel m) vl vl' ->
        Erel m e3.[list_subst vl idsubst]
               e3'.[list_subst vl' idsubst]) ->
  forall m (Hmn : m <= n) e1 e1',
    Erel m e1 e1' ->
      Erel m (ETry e1 x e2 y e3) (ETry e1' x' e2' y' e3').
Proof.
  intros n x x' e2 e2' Eq1 He2 y y' e3 e3' Eq2 He3 m Hmn e1 e1' He1.
  subst. intros.
  destruct (Erel_closed He1) as [IsClosed_e1 IsClosed_e2].
  unfold Erel, exp_rel.
  assert (list_biforall (Vrel 0) (repeat VNil x') (repeat VNil x')) as H'xs. {
    clear. induction x'; simpl; constructor; auto.
  }
  assert (list_biforall (Vrel 0) (repeat VNil y') (repeat VNil y')) as H'ys. {
    clear. induction y'; simpl; constructor; auto.
  }
  epose proof (He2 0 ltac:(lia) (repeat VNil x') (repeat VNil x') _ H'xs) as H'.
  epose proof (He3 0 ltac:(lia) (repeat VNil y') (repeat VNil y') _ H'ys) as H''.
  Unshelve.
  2-3: now rewrite repeat_length.
  split. 2: split.
  * apply Erel_closed_l in H' , H''.
    pose proof (repeat_length VNil x'). pose proof (repeat_length VNil y').
    pose proof (Forall_repeat (fun v => VALCLOSED v) VNil x' ltac:(constructor)) as Fr1.
    pose proof (Forall_repeat (fun v => VALCLOSED v) VNil y' ltac:(constructor)) as Fr2.
    do 2 constructor; auto; try rewrite <- H; try rewrite <- H0; rewrite Nat.add_0_r;
    now apply subst_implies_list_scope.
  * apply Erel_closed_r in H' , H''.
    pose proof (repeat_length VNil x'). pose proof (repeat_length VNil y').
    pose proof (Forall_repeat (fun v => VALCLOSED v) VNil x' ltac:(constructor)) as Fr1.
    pose proof (Forall_repeat (fun v => VALCLOSED v) VNil y' ltac:(constructor)) as Fr2.
    do 2 constructor; auto; try rewrite <- H; try rewrite <- H0; rewrite Nat.add_0_r;
    now apply subst_implies_list_scope.
  * intros. inv H0. 2: inv_val. subst.
    eapply He1 in H8 as [x0 D]. exists (S x0). constructor. exact D.
    lia.

    apply Erel_closed_l in H' as e1H.
    apply subst_implies_list_scope in e1H. 2: apply Forall_repeat; auto.
    apply Erel_closed_r in H' as e2H.
    apply subst_implies_list_scope in e2H. 2: apply Forall_repeat; auto.
    apply Erel_closed_l in H'' as e1H2.
    apply subst_implies_list_scope in e1H2. 2: apply Forall_repeat; auto.
    apply Erel_closed_r in H'' as e2H2.
    apply subst_implies_list_scope in e2H2. 2: apply Forall_repeat; auto.
    destruct H as [Hcl3 [Hcl4 [H1_1 H1_2]]].
    rewrite repeat_length in e1H, e2H, e1H2, e2H2.
    split. 2: split. 1-2: constructor; auto; now constructor.
    split. 2: split.
    - (* normal evaluation of e1 *)
      intros. inv H2.
      eapply biforall_impl in H. 2: {
        intros. eapply Vrel_downclosed. exact H2.
      }
      eapply (He2 k0 ltac:(lia) _ _ _ H) in H12. 2: lia.
      destruct H12 as [x1 D]. eexists. constructor.
      1: now apply biforall_length in H.
      1: exact D.
      fold (Frel k F1 F2). eapply Frel_downclosed.
      split. 2: split. 1-2: assumption. split; eassumption.
    - (* exception e1 *)
      intros. inv H2.
      destruct e4,p. destruct H. subst.
      eapply He3 in H11 as [x0 D]. 
      1: { eexists. eapply cool_try_err. exact D. }
      2: reflexivity.
      2: {
        constructor. destruct e; simpl; apply Vrel_Lit_compat_closed.
        constructor. apply H2. shelve.
        constructor. apply H2. shelve.
        constructor.
      }
      1-2: shelve.
      split. 2: split. 3: split. 4: split. all: auto.
      all: intros.
      1: eapply H1_1; try eassumption. lia.
      1: eapply H1_2; try eassumption. lia.
      1: eapply H1_2; try eassumption. lia.
    - intros. inv H.
Unshelve.
  all: try lia.
  exact k0.
  all: lia.
Qed.

Global Hint Resolve Erel_Try_compat_closed : core.

Lemma Erel_Try_compat :
  forall Γ x x' y y' (e1 e1' e2 e2' e3 e3' : Exp),
    x = x' -> y = y' ->
    Erel_open Γ e1 e1' ->
    Erel_open (x + Γ) e2 e2' ->
    Erel_open (y + Γ) e3 e3' ->
    Erel_open Γ (ETry e1 x e2 y e3) (ETry e1' x' e2' y' e3').
Proof.
  intros. subst.
  unfold Erel_open.
  intros.
  cbn.
  eapply Erel_Try_compat_closed; auto.
  * intros.
    apply biforall_length in H4 as Hl.
    do 2 rewrite subst_comp_exp.
    rewrite subst_list_extend; auto.
    rewrite subst_list_extend. 2: now rewrite <- Hl.
    apply H2.
    apply biforall_vrel_closed in H4 as H4'. destruct H4' as [Hvl Hvl'].
    split. 2: split.
    1-2: apply scoped_list_subscoped_eq; auto; try lia; apply H.
    intros.
    assert (x < x' \/ x >= x') as [Hlia1 | Hlia2] by lia.
    - rewrite list_subst_lt, list_subst_lt. 2-3: lia.
      eapply biforall_forall in H4. exact H4. lia.
    - rewrite list_subst_ge, list_subst_ge. 2-3: lia.
      destruct H as [_ [_ H]]. rewrite Hl.
      specialize (H (x - length vl') ltac:(lia)).
      repeat break_match_goal; try contradiction.
      eapply Vrel_downclosed. eassumption.
  * intros.
    apply biforall_length in H4 as Hl.
    do 2 rewrite subst_comp_exp.
    rewrite subst_list_extend; auto.
    rewrite subst_list_extend. 2: now rewrite <- Hl.
    apply H3.
    apply biforall_vrel_closed in H4 as H4'. destruct H4' as [Hvl Hvl'].
    split. 2: split.
    1-2: apply scoped_list_subscoped_eq; auto; try lia; apply H.
    intros.
    assert (x < y' \/ x >= y') as [Hlia1 | Hlia2] by lia.
    - rewrite list_subst_lt, list_subst_lt. 2-3: lia.
      eapply biforall_forall in H4. exact H4. lia.
    - rewrite list_subst_ge, list_subst_ge. 2-3: lia.
      destruct H as [_ [_ H]]. rewrite Hl.
      specialize (H (x - length vl') ltac:(lia)).
      repeat break_match_goal; try contradiction.
      eapply Vrel_downclosed. eassumption.
Unshelve.
  all: lia.
Qed.

Global Hint Resolve Erel_Try_compat : core.

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
    unfold convert_to_closlist in *. repeat rewrite length_map in *.
    apply H0 in H2 as H2'.
    instantiate (1 := VClos (map (fun '(x, y) => (0, x, y)) l') 0 0 (˝VNil)).
    Unshelve. 2: exact (0, ˝VNil).
    rewrite map_map.
    rewrite map_nth with (d := (0, ˝VNil)).
    destruct nth. constructor.
    * intros. rewrite length_map in *.
      do 2 rewrite map_map. apply H0 in H3.
      do 2 rewrite map_nth with (d := (0, ˝VNil)). destruct nth.
      now rewrite Nat.add_0_r.
    * now rewrite length_map, Nat.add_0_r.
  }
  2: {
    rewrite indexed_to_forall.
    rewrite indexed_to_forall in H. intros.
    unfold convert_to_closlist in *. repeat rewrite length_map in *.
    apply H in H2 as H2'.
    instantiate (1 := VClos (map (fun '(x, y) => (0, x, y)) l) 0 0 (˝VNil)).
    Unshelve. 2: exact (0, ˝VNil).
    rewrite map_map.
    rewrite map_nth with (d := (0, ˝VNil)).
    destruct nth. constructor.
    * intros. rewrite length_map in *.
      do 2 rewrite map_map. apply H in H3.
      do 2 rewrite map_nth with (d := (0, ˝VNil)). destruct nth.
      now rewrite Nat.add_0_r.
    * now rewrite length_map, Nat.add_0_r.
  }
  unfold convert_to_closlist in H_1, H_2. do 2 rewrite length_map in *.
  split. 2: split.
  1-2: do 2 constructor; [|now rewrite Nat.add_0_r].
  1-2: rewrite indexed_to_forall in H, H0; intros.
  1-2: do 2 rewrite map_nth with (d := (0, ˝VNil)).
  1-2: rewrite Nat.add_0_r.
  Unshelve. 4-7: exact (0, ˝VNil).
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
  vl1 = vl2 -> id1 = id2 ->
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
    * intros. do 2 rewrite map_nth with (d := (0, 0, ˝VNil)).
      rewrite indexed_to_forall with (def := (0, 0, ˝VNil)) in H1.
      apply H1 in H4. destruct nth, p. cbn. now rewrite Nat.add_0_r.
    * specialize (H3 n ltac:(lia) (repeat VNil vl1) (repeat VNil vl1)).
      replace (length ext1 + vl1 + 0) with
              (length (convert_to_closlist ext1 ++ repeat VNil vl1)).
      2: { unfold convert_to_closlist.
           rewrite length_app, length_map, repeat_length. lia. }
      apply subst_implies_list_scope.
      apply Forall_app. split.
      - apply closlist_scope. intros.
        do 2 rewrite map_nth with (d := (0, 0, ˝VNil)).
        rewrite indexed_to_forall with (def := (0, 0, ˝VNil)) in H1.
        apply H1 in H4. destruct nth, p. now rewrite Nat.add_0_r.
      - now apply Forall_repeat.
      - apply Erel_closed_l in H3; auto.
        now rewrite repeat_length.
        clear. induction vl1; simpl; auto.
  }
  1: {
    constructor.
    * intros. do 2 rewrite map_nth with (d := (0, 0, ˝VNil)).
      rewrite indexed_to_forall with (def := (0, 0, ˝VNil)) in H2.
      apply H2 in H4. destruct nth, p. cbn. now rewrite Nat.add_0_r.
    * specialize (H3 n ltac:(lia) (repeat VNil vl2) (repeat VNil vl2)).
      replace (length ext2 + vl2 + 0) with
              (length (convert_to_closlist ext2 ++ repeat VNil vl2)).
      2: { unfold convert_to_closlist.
           rewrite length_app, length_map, repeat_length. lia. }
      apply subst_implies_list_scope.
      apply Forall_app. split.
      - apply closlist_scope. intros.
        do 2 rewrite map_nth with (d := (0, 0, ˝VNil)).
        rewrite indexed_to_forall with (def := (0, 0, ˝VNil)) in H2.
        apply H2 in H4. destruct nth, p. now rewrite Nat.add_0_r.
      - now apply Forall_repeat.
      - apply Erel_closed_r in H3; auto.
        now rewrite repeat_length.
        clear. induction vl2; simpl; auto.
  }
  split; auto. split; auto. subst.
  intros. apply H3. lia. lia. auto.
Qed.

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
  1-2: rewrite indexed_to_forall; intros; rewrite length_map in *.
  1-2: eapply biforall_forall with (i := i) (d1 := (0, ˝VNil)) (d2 := (0, ˝VNil)) in H0; try lia.
  Unshelve.
  4-5: exact (0, ˝VNil).
  1-2: rewrite map_nth with (d := (0, ˝VNil)).
  1-2: do 2 destruct nth; destruct H0; subst.
  1-2: apply Erel_open_scope in H4 as [H4_1 H4_2]; try rewrite <- H.
  1-2: apply -> subst_preserves_scope_exp; [eassumption|].
  1-2: rewrite <- (Nat.add_0_r (length l + n1)) at 2; apply upn_scope, H2.
  (* evaluation *)
  unfold Erel_open in H0.
  do 2 rewrite subst_comp_exp.
  apply H1.
  rewrite H. apply Grel_list_subst; auto.
  2: unfold convert_to_closlist; now repeat rewrite length_map.
  
  (* Doing some function magic (extensionality mostly) to be able to
     use Vrel_Clos_compat *)
  unfold convert_to_closlist. repeat rewrite map_map.
  eapply forall_biforall with
    (d1 := VClos (map (fun x : nat * Exp =>
    let
    '(x0, y) :=
     let '(n, x0) := x in (n, x0.[upn (Datatypes.length l' + n) ξ₁]) in
     (0, x0, y)) l) 0 0 (˝VNil))
    (d2 := VClos (map (fun x : nat * Exp =>
    let
    '(x0, y) :=
     let '(n, x0) := x in (n, x0.[upn (Datatypes.length l' + n) ξ₂]) in
     (0, x0, y)) l') 0 0 (˝VNil)).
  now do 2 rewrite length_map.
  rewrite length_map. intros.
  eapply biforall_forall with (d1 := (0, ˝VNil)) (d2 := (0, ˝VNil))
    (i := i) in H0 as H0'. 2: lia.
  do 2 rewrite map_nth with (d := (0, ˝VNil)). do 2 destruct nth; simpl.
  destruct H0'. subst.
  extract_map_fun F.
  remember (fun x : nat * Exp =>
  let
  '(x0, y) :=
   let '(n0, x0) := x in (n0, x0.[upn (Datatypes.length l' + n0) ξ₂]) in
   (0, x0, y)) as G.
  epose proof (Vrel_Clos_compat Γ (map (fun '(a, b) => (0, a, b)) l) (map (fun '(a, b) => (0, a, b)) l') 0 0 n1 n1 e0 e1 eq_refl _ _ _ _ ξ₁ ξ₂ H2). simpl in H4.
  repeat rewrite length_map in *. do 2 rewrite map_map in H4.
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
  * reflexivity.
  * clear F G HeqF HeqG.
    intro. intros. apply H5.
    now rewrite length_map in H4.
  * clear F G HeqF HeqG H5 H3 i.
    eapply forall_biforall with (d1 := (0, 0, ˝VNil)) (d2 := (0, 0, ˝VNil)).
    now do 2 rewrite length_map.
    rewrite length_map. intros.
    do 2 rewrite map_nth with (d := (0, ˝VNil)).
    eapply biforall_forall with (d1 := (0, ˝VNil)) (d2 := (0, ˝VNil))in H0.
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
  split. 2: split.
  { (* normal evaluation *)
    intros. inv H0. destruct vl2. 2: destruct vl2. all: inv H. 2: inv H7.
    clear H7.
    eapply HD1 in H6 as [i D]. eexists. constructor. exact D.
    lia.
    split. 2: split.
    1-2: repeat constructor; auto.
    1-2: apply Vrel_closed in H3; apply H3.
    split. 2: split.
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
      eapply HDF2 in H9 as [i D]. eexists. constructor. reflexivity. exact D.
      lia.
      eapply Excrel_downclosed. exact H. Unshelve. lia.
    }
    {
      intros. inv H.
    }
  }
  { (* exception *)
    intros. inv H0.
    eapply HDF2 in H7 as [i D]. eexists. constructor. reflexivity. exact D.
    lia.
    eapply Excrel_downclosed. exact H. Unshelve. lia.
  }
  {
    intros. inv H.
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
Abort. *)

Definition IRel (n : nat) (i1 i2 : FrameIdent) : Prop :=
ICLOSED i1 /\ ICLOSED i2 /\
match i1, i2 with
| IApp v, IApp v' => Vrel n v v'
| ITuple, ITuple => True
| IMap, IMap => True
| ICall m f, ICall m' f' => Vrel n m m' /\ Vrel n f f'
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

Lemma Vrel_Val_eqb m v v' :
  Vrel m v v' ->
  v =ᵥ v' = true.
Proof.
  revert v v'. valinduction; intros;
  try rewrite Vrel_Fix_eq in H; try destruct v', H as [Hcl1 [Hcl2 H]];
  try contradiction; auto.
  * subst. now rewrite Val_eqb_refl.
  (* * subst. now rewrite Val_eqb_refl. *)
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
  * simpl. intuition. subst. now rewrite Nat.eqb_refl.
Qed.

Lemma Vrel_Val_ltb m v v' :
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
  * subst. simpl. apply Lit_ltb_irrefl.
  (* * subst. simpl. apply Nat.ltb_irrefl. *)
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
  * simpl. intuition. subst. now rewrite Nat.ltb_irrefl.
Qed.

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
      + apply Vrel_Val_eqb in H1, H2, H0, H3.
        eapply Val_eqb_trans in Heqb1. 2: eassumption.
        rewrite Val_eqb_sym in H0.
        eapply Val_eqb_trans in H0. 2: eassumption.
        apply Val_eqb_ltb in H0. congruence.
      + apply Vrel_Val_eqb in H1, H2, H0, H3.
        eapply Val_eqb_ltb_trans in Heqb. 2: rewrite Val_eqb_sym; eassumption.
        eapply Val_ltb_eqb_trans in Heqb. 2: eassumption. congruence.
    - break_match_goal.
      + apply Vrel_Val_eqb in H1, H2, H0, H3.
        eapply Val_ltb_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; eassumption.
        eapply Val_eqb_ltb_trans in Heqb1. 2: eassumption.
        congruence.
      + break_match_goal.
        ** constructor; auto.
        ** apply Vrel_Val_eqb in H1, H2, H0, H3.
           eapply Val_eqb_trans in Heqb0. 2: rewrite Val_eqb_sym; exact H1.
           eapply Val_eqb_trans in H0. 2: eassumption. congruence.
    - break_match_goal.
      + apply Vrel_Val_eqb in H1, H2, H0, H3.
        eapply Val_ltb_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; eassumption.
        eapply Val_eqb_ltb_trans in Heqb1. 2: eassumption.
        congruence.
      + break_match_goal.
        ** apply Vrel_Val_eqb in H1, H2, H0, H3.
           eapply Val_eqb_trans in Heqb2. 2: exact H1.
           rewrite Val_eqb_sym in H0.
           eapply Val_eqb_trans in H0. 2: eassumption. congruence.
        ** constructor; auto.
Qed.

Lemma Vrel_make_map m l l' :
  list_biforall (Vrel m) l l' ->
  list_biforall (fun '(v1, v2) '(v1', v2') => Vrel m v1 v1' /\ Vrel m v2 v2')
  (make_val_map (deflatten_list l)) (make_val_map (deflatten_list l')).
Proof.
  revert l'. induction l using list_length_ind; intros.
  inv H0; simpl; auto.
  inv H2; simpl; auto.
  apply H in H3. 2: simpl; lia.
  now apply Vrel_map_insert.
Qed.

(* eval functions *)
Ltac solve_refl_Vrel_exc :=
  try now (right; do 2 eexists; split;[|split;reflexivity];split;[auto|split;auto]).

Ltac solve_refl_Vrel_val :=
  (left; do 2 eexists; split;[|split;reflexivity]; constructor; auto; rewrite Vrel_Fix_eq; auto).

Lemma Rel_eval_io m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   fst (eval_io mname f l) = RValSeq vl /\ fst (eval_io mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   fst (eval_io mname f l) = ex /\ fst (eval_io mname f l') = ex').
Proof.
  intros. unfold eval_io. break_match_goal.
  all: solve_refl_Vrel_exc.
  all: inv H; solve_refl_Vrel_exc; simpl.
  all: inv H1; solve_refl_Vrel_exc; simpl.
  2: inv H2; solve_refl_Vrel_exc; simpl.
  * solve_refl_Vrel_val.
  * solve_refl_Vrel_val. 
Qed.

Ltac choose_compat_lemma :=
  match goal with
  | |- Vrel _ (VTuple _) (VTuple _) => apply Vrel_Tuple_compat_closed
  | |- Vrel _ (VMap _) (VMap _) => apply Vrel_Map_compat_closed
  | |- Vrel _ (VCons _ _) (VCons _ _) => apply Vrel_Cons_compat_closed
  | |- Vrel _ (VClos _ _ _ _) (VClos _ _ _ _) => idtac "closure"
  | |- Vrel _ _ _ => auto
  end.

Ltac solve_complex_excrel_base :=
  do 2 eexists; split; [|split;reflexivity]; auto; try (split;[reflexivity|split;auto]; choose_compat_lemma; repeat (constructor; try downclose_Vrel; auto)).

Ltac solve_complex_Excrel :=
  right; solve_complex_excrel_base.

Ltac solve_complex_Vrel :=
  left; do 2 eexists; split; [|split;reflexivity]; repeat (constructor; try downclose_Vrel; auto).

Lemma Rel_eval_arith m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_arith mname f l) = RValSeq vl /\ (eval_arith mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_arith mname f l) = ex /\ (eval_arith mname f l') = ex').
Proof.
  intros. unfold eval_arith. break_match_goal.
  all: solve_refl_Vrel_exc.
  all: inv H; solve_refl_Vrel_exc; simpl.
  all: inv H1; solve_refl_Vrel_exc; simpl.
  all: try inv H2; solve_refl_Vrel_exc; simpl.
  all: try Vrel_possibilities H0; solve_refl_Vrel_exc.
  all: try solve_complex_Excrel.
  all: try destruct x; try solve_complex_Excrel.
  all: try solve_complex_Vrel.
  all: try Vrel_possibilities H; solve_refl_Vrel_exc; try solve_complex_Excrel.
  all: try destruct x0; try solve_complex_Excrel.
  all: try solve_complex_Vrel.
  all: try destruct x0; try solve_complex_Excrel; solve_complex_Vrel.
Unshelve.
  all: try assumption; lia.
Qed.

Lemma Rel_eval_logical m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_logical mname f l) = RValSeq vl /\ (eval_logical mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_logical mname f l) = ex /\ (eval_logical mname f l') = ex').
Proof.
  intros. unfold eval_logical. break_match_goal.
  all: solve_refl_Vrel_exc.
  all: inv H; solve_refl_Vrel_exc; simpl.
  all: inv H1; solve_refl_Vrel_exc; simpl.
  all: try inv H2; solve_refl_Vrel_exc; simpl.
  * apply Vrel_Val_eqb in H as H0V.
    apply Vrel_Val_eqb in H0 as HV. break_match_goal.
    - eapply Val_eqb_trans in Heqb0. 2: rewrite Val_eqb_sym; exact HV.
      rewrite Heqb0.
      break_match_goal.
      + eapply Val_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; exact H0V.
        rewrite Heqb1. solve_complex_Vrel.
      + eapply Val_eqb_neqb in H0V as H0V'.
        2: rewrite Val_eqb_sym; exact Heqb1.
        rewrite (Val_eqb_sym hd'0), H0V'. break_match_goal.
        ** eapply Val_eqb_trans in Heqb2. 2: rewrite Val_eqb_sym; exact H0V.
           rewrite Heqb2. solve_complex_Vrel.
        ** eapply Val_eqb_neqb in H0V as H0V''.
           2: rewrite Val_eqb_sym; exact Heqb2.
           rewrite (Val_eqb_sym hd'0), H0V''. solve_complex_Excrel.
    - eapply Val_eqb_neqb in HV as HV'.
      2: rewrite Val_eqb_sym; exact Heqb0.
      rewrite (Val_eqb_sym hd'), HV'. break_match_goal.
      + eapply Val_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; exact HV.
        rewrite Heqb1. break_match_goal.
        ** eapply Val_eqb_trans in Heqb2. 2: rewrite Val_eqb_sym; exact H0V.
           rewrite Heqb2. solve_complex_Vrel.
        ** eapply Val_eqb_neqb in H0V as H0V''.
           2: rewrite Val_eqb_sym; exact Heqb2.
           rewrite (Val_eqb_sym hd'0), H0V''. break_match_goal.
           -- eapply Val_eqb_trans in Heqb3. 2: rewrite Val_eqb_sym; exact H0V.
              rewrite Heqb3. solve_complex_Vrel.
           -- eapply Val_eqb_neqb in H0V as H0V'''.
              2: rewrite Val_eqb_sym; exact Heqb3.
              rewrite (Val_eqb_sym hd'0), H0V'''. solve_complex_Excrel.
      + eapply Val_eqb_neqb in HV as HV''.
        2: rewrite Val_eqb_sym; exact Heqb1.
        rewrite (Val_eqb_sym hd'), HV''. solve_complex_Excrel. 
  (* NOTE: boiler plate subproof, it's the copy of the previous one *)
  * apply Vrel_Val_eqb in H as H0V.
    apply Vrel_Val_eqb in H0 as HV. break_match_goal.
    - eapply Val_eqb_trans in Heqb0. 2: rewrite Val_eqb_sym; exact HV.
      rewrite Heqb0.
      break_match_goal.
      + eapply Val_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; exact H0V.
        rewrite Heqb1. solve_complex_Vrel.
      + eapply Val_eqb_neqb in H0V as H0V'.
        2: rewrite Val_eqb_sym; exact Heqb1.
        rewrite (Val_eqb_sym hd'0), H0V'. break_match_goal.
        ** eapply Val_eqb_trans in Heqb2. 2: rewrite Val_eqb_sym; exact H0V.
          rewrite Heqb2. solve_complex_Vrel.
        ** eapply Val_eqb_neqb in H0V as H0V''.
          2: rewrite Val_eqb_sym; exact Heqb2.
          rewrite (Val_eqb_sym hd'0), H0V''. solve_complex_Excrel.
    - eapply Val_eqb_neqb in HV as HV'.
      2: rewrite Val_eqb_sym; exact Heqb0.
      rewrite (Val_eqb_sym hd'), HV'. break_match_goal.
      + eapply Val_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; exact HV.
        rewrite Heqb1. break_match_goal.
        ** eapply Val_eqb_trans in Heqb2. 2: rewrite Val_eqb_sym; exact H0V.
          rewrite Heqb2. solve_complex_Vrel.
        ** eapply Val_eqb_neqb in H0V as H0V''.
          2: rewrite Val_eqb_sym; exact Heqb2.
          rewrite (Val_eqb_sym hd'0), H0V''. break_match_goal.
          -- eapply Val_eqb_trans in Heqb3. 2: rewrite Val_eqb_sym; exact H0V.
              rewrite Heqb3. solve_complex_Vrel.
          -- eapply Val_eqb_neqb in H0V as H0V'''.
              2: rewrite Val_eqb_sym; exact Heqb3.
              rewrite (Val_eqb_sym hd'0), H0V'''. solve_complex_Excrel.
      + eapply Val_eqb_neqb in HV as HV''.
        2: rewrite Val_eqb_sym; exact Heqb1.
        rewrite (Val_eqb_sym hd'), HV''. solve_complex_Excrel. 
  * apply Vrel_Val_eqb in H0 as HV. break_match_goal.
    - eapply Val_eqb_trans in Heqb0. 2: rewrite Val_eqb_sym; exact HV.
      rewrite Heqb0. solve_complex_Vrel.
    - eapply Val_eqb_neqb in HV as HV'.
      2: rewrite Val_eqb_sym; exact Heqb0.
      rewrite (Val_eqb_sym hd'), HV'. break_match_goal.
      + eapply Val_eqb_trans in Heqb1. 2: rewrite Val_eqb_sym; exact HV.
        rewrite Heqb1. solve_complex_Vrel.
      + eapply Val_eqb_neqb in HV as HV''.
        2: rewrite Val_eqb_sym; exact Heqb1.
        rewrite (Val_eqb_sym hd'), HV''. solve_complex_Excrel.
Unshelve.
  all: assumption.
Qed.

Lemma Rel_eval_equality m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_equality mname f l) = RValSeq vl /\ (eval_equality mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_equality mname f l) = ex /\ (eval_equality mname f l') = ex').
Proof.
  intros. unfold eval_equality. break_match_goal.
  all: solve_refl_Vrel_exc.
  all: inv H; solve_refl_Vrel_exc; simpl.
  all: inv H1; solve_refl_Vrel_exc; simpl.
  all: inv H2; solve_refl_Vrel_exc; simpl.
  all: apply Vrel_Val_eqb in H as H0V;
    apply Vrel_Val_eqb in H0 as HV; break_match_goal;
    [eapply Val_eqb_trans in Heqb0;[|rewrite Val_eqb_sym;exact HV];
     eapply Val_eqb_trans in H0V;[|exact Heqb0];
     rewrite H0V; solve_complex_Vrel
    |
     eapply Val_eqb_neqb in Heqb0;[|exact H0V];
     rewrite Val_eqb_sym in Heqb0;
     eapply Val_eqb_neqb in Heqb0;[|exact HV];
     rewrite Val_eqb_sym, Heqb0; solve_complex_Vrel
    ].
Qed.

Lemma Rel_eval_cmp m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_cmp mname f l) = RValSeq vl /\ (eval_cmp mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_cmp mname f l) = ex /\ (eval_cmp mname f l') = ex').
Proof.
  intros. unfold eval_cmp. break_match_goal.
  all: solve_refl_Vrel_exc.
  all: inv H; solve_refl_Vrel_exc; simpl.
  all: inv H1; solve_refl_Vrel_exc; simpl.
  all: inv H2; solve_refl_Vrel_exc; simpl.
  all: apply Vrel_Val_eqb in H0 as H0'.
  all: apply Vrel_Val_eqb in H as H'.
  all: destruct Val_ltb eqn:EQ.
  * eapply Val_eqb_ltb_trans in EQ; [| rewrite Val_eqb_sym; eassumption].
    eapply Val_ltb_eqb_trans in EQ; [| eassumption].
    rewrite EQ. solve_complex_Vrel.
  * eapply Val_geb_eqb_trans in EQ. 2: rewrite Val_eqb_sym; eassumption.
    eapply Val_eqb_geb_trans in EQ. 2: eassumption. rewrite EQ.
    solve_complex_Vrel.
  * simpl. eapply Val_eqb_ltb_trans in EQ. 2: rewrite Val_eqb_sym; eassumption.
    eapply Val_ltb_eqb_trans in EQ. 2: eassumption. rewrite EQ. simpl.
    solve_complex_Vrel.
  * simpl. eapply Val_geb_eqb_trans in EQ. 2: rewrite Val_eqb_sym; eassumption.
    eapply Val_eqb_geb_trans in EQ. 2: eassumption. rewrite EQ. simpl.
    break_match_goal.
    - eapply Val_eqb_trans in H'. 2: eassumption.
      eapply Val_eqb_trans in H0'. 2: rewrite Val_eqb_sym; eassumption.
      rewrite Val_eqb_sym, H0'. solve_complex_Vrel.
    - eapply Val_eqb_neqb in Heqb0. 2: eassumption.
      eapply Val_eqb_neqb in H0'. 2: rewrite Val_eqb_sym; eassumption.
      rewrite Val_eqb_sym, H0'. solve_complex_Vrel.
  * eapply Val_eqb_ltb_trans in EQ. 2: rewrite Val_eqb_sym; eassumption.
    eapply Val_ltb_eqb_trans in EQ. 2: eassumption.
    rewrite EQ. solve_complex_Vrel.
  * eapply Val_eqb_geb_trans in EQ. 2: eassumption.
    eapply Val_geb_eqb_trans in EQ. 2: rewrite Val_eqb_sym;eassumption.
    rewrite EQ. solve_complex_Vrel.
  * simpl. eapply Val_eqb_ltb_trans in EQ. 2: rewrite Val_eqb_sym; eassumption.
    eapply Val_ltb_eqb_trans in EQ. 2: eassumption. rewrite EQ. simpl.
    solve_complex_Vrel.
  * simpl. eapply Val_geb_eqb_trans in EQ. 2: rewrite Val_eqb_sym; eassumption.
    eapply Val_eqb_geb_trans in EQ. 2: eassumption. rewrite EQ. simpl.
    break_match_goal.
    - eapply Val_eqb_trans in H'. 2: eassumption.
      eapply Val_eqb_trans in H0'. 2: rewrite Val_eqb_sym; eassumption.
      rewrite Val_eqb_sym, H0'. solve_complex_Vrel.
    - eapply Val_eqb_neqb in Heqb0. 2: eassumption.
      eapply Val_eqb_neqb in H0'. 2: rewrite Val_eqb_sym; eassumption.
      rewrite Val_eqb_sym, H0'. solve_complex_Vrel.
Qed.

Lemma Vrel_is_shallow_proper_list :
  forall v1 v2 m, Vrel m v1 v2 -> is_shallow_proper_list v1 = is_shallow_proper_list v2.
Proof.
  induction v1; destruct v2; intros.
  (* the only special case is having two lists: *)
  31: {
    rewrite Vrel_Fix_eq in H; destruct H as [_ [_ [H_1 H_2]]].
    simpl. eapply IHv1_2.
    rewrite Vrel_Fix_eq. eassumption.
  }
  all: destruct H as [_ [_ H]]; try inv H; simpl; auto.
Qed.

Ltac start_solve_complex_Excrel :=
  right; do 2 eexists; split; [|split;reflexivity]; split;[reflexivity|split;auto]; try choose_compat_lemma.

Ltac start_solve_complex_Vrel :=
  left; do 2 eexists; split; [|split;reflexivity]; try choose_compat_lemma.

Lemma Rel_subtract_elem m hd hd' tl tl':
  Vrel m hd hd' -> Vrel m tl tl' ->
  Vrel m (subtract_elem tl hd) (subtract_elem tl' hd').
Proof.
  intros H H0. revert tl' H0 hd hd' H.
  induction tl; intros; destruct tl';
    try now (rewrite Vrel_Fix_eq in H0; simpl in H0; destruct_hyps;
      contradiction).
  all: try now (simpl; unfold ErrorVal; choose_compat_lemma).
  clear IHtl1. simpl. 
  assert (Vrel m tl1 tl'1). {
    rewrite Vrel_Fix_eq in H0. rewrite Vrel_Fix_eq. apply H0.
  }
  assert (Vrel m tl2 tl'2). {
    rewrite Vrel_Fix_eq in H0. rewrite Vrel_Fix_eq. apply H0.
  }
  apply Vrel_Val_eqb in H1 as H1', H2 as H2', H as H'.
  break_match_goal.
  * rewrite Val_eqb_sym in H1'.
    pose proof (Val_eqb_trans _ _ _ H1' (Val_eqb_trans _ _ _ Heqb H')).
    now rewrite H3.
  * pose proof (Val_eqb_neqb _ _ _ Heqb H').
    rewrite Val_eqb_sym in H3.
    pose proof (Val_eqb_neqb _ _ _ H3 H1'). rewrite Val_eqb_sym, H4.
    choose_compat_lemma; auto.
Qed.



Ltac destruct_vrel :=
  match goal with
  | [H : Vrel _ (VCons _ _) (VCons _ _) |- _] =>
    let newH1 := fresh "H" in
    let newH2 := fresh "H" in
    rewrite Vrel_Fix_eq in H; destruct H as [_ [_ [newH1 newH2]]];
    rewrite <- Vrel_Fix_eq in newH1; rewrite <- Vrel_Fix_eq in newH2 
  | [H : Vrel _ (VTuple _) (VTuple _) |- _] =>
    apply Vrel_Tuple_compat_rev in H
  | [H : Vrel _ (VMap _) (VMap _) |- _] =>
    apply Vrel_Map_compat_rev in H
  end.

Lemma Rel_eval_transform_list m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_transform_list mname f l) = RValSeq vl /\ (eval_transform_list mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_transform_list mname f l) = ex /\ (eval_transform_list mname f l') = ex').
Proof.
  intros. unfold eval_transform_list in *; break_match_goal.
  all: try solve_complex_Excrel.
  all: inv H; [solve_complex_Excrel|].
  all: inv H1; [solve_complex_Excrel|].
  all: inv H2; [|solve_complex_Excrel].
  {
    generalize dependent hd'.
    induction hd; intros; destruct hd'; try now cbn in H0; destruct H0 as [_ [_ H0]]; inv H0.
    all: simpl.
    solve_complex_Vrel.
    all: try solve_complex_Excrel.
    assert (Vrel m (VCons hd1 hd2) (VCons hd'1 hd'2)) as H0d by exact H0.
    rewrite Vrel_Fix_eq in H0. destruct H0 as [Hcl1 [Hcl2 [Hvrel1 Hvrel2]]].
    rewrite <- Vrel_Fix_eq in Hvrel1. rewrite <- Vrel_Fix_eq in Hvrel2.
    apply IHhd1 in Hvrel1.
    apply IHhd2 in Hvrel2 as [[vl [vl' [Hrel [Heq1 Heq2]]]]|[ex [ex' [Hrel [Heq1 Heq2]]]]].
    - rewrite Heq1, Heq2. inv Hrel. simpl in *. solve_complex_Excrel.
      inv H1. 2: solve_complex_Excrel.
      rewrite Vrel_Fix_eq in H0d. destruct H0d as [Hcl3 [Hcl4 [Hvrel3 Hvrel4]]].
      rewrite <- Vrel_Fix_eq in Hvrel3. rewrite <- Vrel_Fix_eq in Hvrel4.
      solve_complex_Vrel.
    - rewrite Heq1, Heq2.
      rewrite Vrel_Fix_eq in H0d. destruct H0d as [Hcl3 [Hcl4 [Hvrel3 Hvrel4]]].
      rewrite <- Vrel_Fix_eq in Hvrel3. rewrite <- Vrel_Fix_eq in Hvrel4.
      eapply Vrel_Cons_compat_closed in Hvrel4. 2: exact Hvrel3.
      solve_complex_Excrel.
  }
  {
    generalize dependent hd. revert hd' hd'0 H. clear Heqb.
    induction hd0; intros; destruct hd'0; try now cbn in H; destruct H as [_ [_ H]];
      contradiction.
    2-7: simpl; do 2 break_match_goal; try solve_complex_Excrel.
    3-4: apply Vrel_is_shallow_proper_list in H, H0; simpl in H, H0;
         rewrite <- H, <- H0 in Heqb0; congruence.
    * simpl. do 2 break_match_goal.
      - solve_complex_Vrel.
      - apply Vrel_is_shallow_proper_list in H0. simpl in H0. congruence.
      - apply Vrel_is_shallow_proper_list in H0. simpl in H0. congruence.
      - solve_complex_Excrel.
    * apply IHhd0_2.
      - rewrite Vrel_Fix_eq in H. simpl in H. rewrite Vrel_Fix_eq. apply H.
      - apply Rel_subtract_elem; auto.
        rewrite Vrel_Fix_eq in H. rewrite Vrel_Fix_eq. apply H.
  }
  {
    clear Heqb.
    pose proof H0 as HX.
    rewrite Vrel_Fix_eq in H0. destruct hd, hd'; cbn in H0; destruct_hyps; try contradiction.
    1,3-7: simpl; try now solve_complex_Excrel.
    subst.
    destruct l0; simpl.
    1: now solve_complex_Excrel.
    break_match_goal. 1: now solve_complex_Excrel.
    clear -H. remember (Z.to_nat _) as n. clear Heqn.
    revert hd0 hd'0 H. induction n; simpl; intros.
    * solve_complex_Vrel.
    * pose proof H as HX. rewrite Vrel_Fix_eq in H. destruct hd0, hd'0; cbn in H; destruct_hyps; try contradiction.
      1-3,5-7: simpl; try now solve_complex_Excrel.
      clear H1 H2. destruct_vrel.
      apply IHn in H2. clear IHn.
      destruct (split_cons n hd0_2) eqn:P1. destruct p.
      destruct (split_cons n hd'0_2) eqn:P2. destruct p.
      - destruct H2; destruct_hyps.
        + inv H3. inv H2.
          destruct_vrel. inv H6. inv H9. clear H8 H10.
          solve_complex_Vrel.
        + inv H3.
      - destruct H2; destruct_hyps; inv H3; inv H4.
      - destruct (split_cons n hd'0_2) eqn:P2. destruct p.
        + destruct H2; destruct_hyps; inv H3; inv H4.
        + destruct H2; destruct_hyps; inv H3.
          destruct H2.
          right. do 2 eexists. split. 2: split. 2-3: reflexivity.
          constructor; auto. intros.
          apply H3 in Hmn as Hmn'. split.
          now apply Vrel_Lit_compat_closed.
          apply Vrel_Tuple_compat_closed.
          constructor. 2: constructor. 3: constructor; auto.
          1-2: now apply Vrel_Lit_compat_closed.
          destruct Hmn'. destruct_vrel.
          inv H5. inv H11. inv H10.
          apply Vrel_Cons_compat_closed; downclose_Vrel.
  }
  Unshelve. all: lia.
Qed.


Lemma Rel_eval_list_tuple m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_list_tuple mname f l) = RValSeq vl /\ (eval_list_tuple mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_list_tuple mname f l) = ex /\ (eval_list_tuple mname f l') = ex').
Proof.
  intros. unfold eval_list_tuple.
  break_match_goal; clear Heqb; try solve_complex_Excrel.
  {
    inv H. solve_complex_Excrel.
    inv H1. 2: solve_complex_Excrel.
    generalize dependent hd'.
    induction hd; intros; destruct hd'; try now cbn in H0; destruct H0 as [_ [_ H0]]; inv H0.
    all: simpl; try solve_complex_Excrel.
    assert (list_biforall (Vrel m) l l0). {
      rewrite Vrel_Fix_eq in H0. destruct H0 as [_ [_ H0]].
      generalize dependent l0. induction l; destruct l0; intros; auto; try contradiction.
      destruct H0.
      constructor.
      * now rewrite Vrel_Fix_eq.
      * now apply IHl. 
    }
    clear f.
    induction H.
    * solve_complex_Vrel.
    * apply Vrel_Tuple_compat_closed in H1. apply IHlist_biforall in H1.
      destruct H1 as [[vl [vl' [Hrel [Eq1 Eq2]]]]|[ex [ex' [Hrel [Eq1 Eq2]]]]].
      - subst. left. do 2 eexists.
        split. 2: split; reflexivity.
        constructor; auto. apply Vrel_Cons_compat_closed; auto.
        now inv Hrel.
      - inv Eq1.
  }
  {
    inv H. solve_complex_Excrel.
    inv H1. 2: solve_complex_Excrel.
    generalize dependent hd'.
    induction hd; intros; destruct hd'; try now cbn in H0; destruct H0 as [_ [_ H0]]; inv H0.
    all: simpl; try solve_complex_Excrel.
    solve_complex_Vrel.
    clear f IHhd1.
    rewrite Vrel_Fix_eq in H0; destruct H0 as [_ [_ [H0_1 H0_2]]].
    rewrite <- Vrel_Fix_eq in H0_1. rewrite <- Vrel_Fix_eq in H0_2.
    apply IHhd2 in H0_2 as IH. clear IHhd2.
    destruct IH as [[vl [vl' [Hrel [Eq1 Eq2]]]]|[ex [ex' [Hrel [Eq1 Eq2]]]]].
    * do 2 break_match_hyp; try congruence.
      subst.
      inv Hrel.
      apply Vrel_Tuple_compat_rev in H.
      solve_complex_Vrel.
    * do 2 break_match_hyp; try congruence.
      inv Eq1.
      inv Hrel. specialize (H0 m ltac:(lia)) as [H0_1' H0_2'].
      apply Vrel_Tuple_compat_rev in H0_2'. inv H0_2'.
      start_solve_complex_Excrel. constructor. 1: now auto.
      constructor; auto.
      choose_compat_lemma; downclose_Vrel.
  }
Unshelve.
  all: assumption.
Qed.

Lemma Rel_mk_ascii_list m v v':
(Vrel m) v v' ->
  (mk_ascii_list v = mk_ascii_list v').
Proof.
  intro. pose proof H. induction H using Vrel_ind.
  all: simpl; try reflexivity.
  rewrite Vrel_Fix_eq in H0. simpl in H0.
  rewrite Vrel_Fix_eq in IHVrel0.
  destruct_hyps. destruct_scopes.
  rewrite IHVrel0. 2: assumption.
  destruct v1, v1'.
  all: try reflexivity.
  all: simpl in H1; try destruct_hyps; try contradiction.
  subst. reflexivity.
Qed.

Lemma Rel_eval_convert m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists eff eff' : option SideEffect, exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_convert mname f l) = (RValSeq vl, eff) /\ (eval_convert mname f l') = (RValSeq vl', eff')) \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_convert mname f l) = (RExc ex, None) /\ (eval_convert mname f l') = (RExc ex', None)).
Proof.
  intros. unfold eval_convert.
  break_match_goal; clear Heqb; try solve_complex_Excrel.
  {
    inv H. solve_complex_Excrel.
    inv H1. 2: solve_complex_Excrel.

    apply Rel_mk_ascii_list in H0 as H0'.
    rewrite H0'.
    break_match_goal.
    - left. repeat eexists. auto.
    - start_solve_complex_Excrel.
      do 3 (try constructor; auto).
      downclose_Vrel.
  }
  {
    inv H. solve_complex_Excrel.
    inv H1. 2: solve_complex_Excrel.
    pose proof H0 as H00.
    induction H0 using Vrel_ind.
    1: solve_complex_Excrel.
    2-6: solve_complex_Excrel.
    destruct l. solve_complex_Excrel.
    left. repeat eexists.
    constructor; auto.
    remember (NilZero.string_of_int _) as s.
    clear.
    induction s; simpl; auto.
  }
Unshelve.
  all: assumption.
Qed.

Lemma Rel_eval_length m l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_length l) = RValSeq vl /\ (eval_length l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_length l) = ex /\ (eval_length l') = ex').
Proof.
  intros.
  inv H. solve_complex_Excrel.
  inv H1. 2: solve_complex_Excrel.
  assert (Vrel m hd hd') by assumption. revert H.
  induction H0 using Vrel_ind.
  * solve_complex_Vrel.
  * intros. solve_complex_Excrel.
  * intros. solve_complex_Excrel.
  * intros. solve_complex_Excrel.
  * intros. rewrite Vrel_Fix_eq in H. destruct H as [Hcl1 [Hcl2 [H_1 H_2]]].
    rewrite <- Vrel_Fix_eq in H_1. rewrite <- Vrel_Fix_eq in H_2.
    apply IHVrel in H_1 as H_1'. apply IHVrel0 in H_2 as H_2'. clear IHVrel IHVrel0.
    clear H_1'.
    destruct H_2' as [[vl [vl' [Hrel [Eq1 Eq2]]]]|[ex [ex' [Hrel [Eq1 Eq2]]]]].
    - simpl in *. left. do 2 break_match_hyp; try congruence.
      do 2 eexists. split. 2: split; reflexivity. constructor; auto.
      assert (n0 = n). {
        inv Eq1. inv Hrel. destruct H2 as [_ [_ ?]]. inv H.
        lia.
      }
      subst. apply Vrel_Lit_compat_closed.
    - right. simpl in *. do 2 break_match_hyp; try congruence.
      do 2 eexists. split. 2: split; reflexivity.
      constructor; auto. intros. split.
      apply Vrel_Lit_compat_closed.
      apply Vrel_Tuple_compat_closed. constructor.
      apply Vrel_Lit_compat_closed. constructor; auto.
      apply Vrel_Cons_compat_closed; eapply Vrel_downclosed; eassumption.
  * solve_complex_Excrel.
  * solve_complex_Excrel.
Unshelve.
  all: lia.
Qed.

Lemma Rel_eval_tuple_size m l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_tuple_size l) = RValSeq vl /\ (eval_tuple_size l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_tuple_size l) = ex /\ (eval_tuple_size l') = ex').
Proof.
  intros. inv H. solve_complex_Excrel.
  inv H1; simpl. 2: destruct hd, hd'; solve_complex_Excrel.
  assert (Vrel m hd hd') by assumption. revert H.
  induction H0 using Vrel_ind; try solve_complex_Excrel.
  intros. assert (length l = length l'). {
    rewrite Vrel_Fix_eq in H0. destruct H0 as [_ [_ H0]]. clear -H0.
    generalize dependent l'. induction l; destruct l'; simpl; intros; auto; try contradiction.
    erewrite IHl. reflexivity. apply H0.
  }
  rewrite H1. solve_complex_Vrel.
Unshelve.
  all: lia.
Qed.

Lemma Rel_eval_hd_tl m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_hd_tl mname f l) = RValSeq vl /\ (eval_hd_tl mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_hd_tl mname f l) = ex /\ (eval_hd_tl mname f l') = ex').
Proof.
  intros. unfold eval_hd_tl. break_match_goal; try solve_complex_Excrel.
  all: clear Heqb.
  all: inv H; try solve_complex_Excrel.
  all: inv H1; try solve_complex_Excrel.
  all: Vrel_possibilities H0; try solve_complex_Excrel.
  all: destruct_vrel; solve_complex_Vrel.
Unshelve.
  all: lia.
Qed.

Lemma Rel_eval_elem_tuple m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_elem_tuple mname f l) = RValSeq vl /\ (eval_elem_tuple mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_elem_tuple mname f l) = ex /\ (eval_elem_tuple mname f l') = ex').
Proof.
  intros. unfold eval_elem_tuple.
  break_match_goal; try solve_complex_Excrel; clear Heqb; inv H; try solve_complex_Excrel.
  all: inv H1; try solve_complex_Excrel.
  1,3: Vrel_possibilities H0; try solve_complex_Excrel; destruct x; solve_complex_Excrel.
  all: Vrel_possibilities H0.
  all: try inv H2; try solve_complex_Excrel.
  all: try inv H3; try solve_complex_Excrel.
  2-4, 6: destruct x; try solve_complex_Excrel.
  all: try destruct x; Vrel_possibilities H; try solve_complex_Excrel.
  all: destruct x; try solve_complex_Excrel.
  all: destruct_vrel.
  {
    clear -H. remember (Init.Nat.pred (Pos.to_nat p)) as n.
    clear Heqn. revert n.
    induction H; intros.
    all: destruct n; simpl.
    1-2: solve_complex_Excrel.
    solve_complex_Vrel.
    specialize (IHlist_biforall n). intuition; destruct_hyps; subst.
    * do 2 break_match_goal; subst; inv H2.
      inv H1. solve_complex_Vrel.
    * do 2 break_match_goal; subst; inv H2.
      start_solve_complex_Excrel.
      do 3 (constructor; auto). choose_compat_lemma.
      constructor. downclose_Vrel.
      eapply biforall_impl. 2: eassumption.
      intros. downclose_Vrel.
  }
  {
    clear -H H1. remember (Init.Nat.pred (Pos.to_nat p)) as n.
    clear Heqn. revert n.
    induction H; intros.
    all: destruct n; simpl.
    1-2: solve_complex_Excrel.
    solve_complex_Vrel.
    specialize (IHlist_biforall n). intuition; destruct_hyps; subst.
    * do 2 destruct replace_nth_error; subst; inv H4.
      inv H2. start_solve_complex_Vrel. constructor; auto.
      choose_compat_lemma. constructor; try downclose_Vrel.
      now apply Vrel_Tuple_compat_rev in H6.
    * do 2 destruct replace_nth_error; subst; inv H4.
      start_solve_complex_Excrel.
      do 3 (constructor; auto). choose_compat_lemma.
      constructor. downclose_Vrel.
      eapply biforall_impl. 2: eassumption.
      intros. downclose_Vrel.
      constructor; auto.
      inv H2. apply H4. lia.
  }
  Unshelve.
    all: auto.
Qed.

Lemma Rel_eval_check m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_check mname f l) = RValSeq vl /\ (eval_check mname f l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_check mname f l) = ex /\ (eval_check mname f l') = ex').
Proof.
  intros. unfold eval_check. break_match_goal; try solve_complex_Excrel.
  all: clear Heqb; inv H; try solve_complex_Excrel.
  all: inv H1; try solve_complex_Excrel.
  all: apply Vrel_possibilities in H0 as H0'; intuition; destruct_hyps; subst; try solve_complex_Excrel; try solve_complex_Vrel.
  all: destruct x; try solve_complex_Excrel; try solve_complex_Vrel.
  break_match_goal; solve_complex_Vrel.
Qed.

Lemma Rel_eval_error m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_error mname f l) = Some ex /\ (eval_error mname f l') = Some ex')
  \/
   eval_error mname f l = None /\ eval_error mname f l' = None.
Proof.
  intros. unfold eval_error.
  break_match_goal.
  all: try now left; solve_complex_excrel_base.
  all: inv H; try now left; solve_complex_excrel_base.
  all: inv H1; try now left; solve_complex_excrel_base.
  1,3,5: left; solve_complex_excrel_base; downclose_Vrel.
  1-2: inv H2.
  3: now right.
  1-3: left; try solve_complex_excrel_base; try downclose_Vrel.
  inv H3; try solve_complex_excrel_base; downclose_Vrel.
Unshelve.
  all: auto.
Qed.

Lemma Rel_eval_concurrent m mname f l l':
  list_biforall (Vrel m) l l' ->
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_concurrent mname f l) = Some ex /\ (eval_concurrent mname f l') = Some ex')
  \/
   eval_concurrent mname f l = None /\ eval_concurrent mname f l' = None.
Proof.
  intros. unfold eval_concurrent.
  break_match_goal.
  all: try now left; solve_complex_excrel_base.
  all: inv H; try now left; solve_complex_excrel_base.
  all: try now right.
  all: inv H1; try now left; solve_complex_excrel_base.
  all: try now right.
Unshelve.
  all: auto.
Qed.

Lemma Rel_eval_funinfo m l l':
  list_biforall (Vrel m) l l' ->
  (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (eval_funinfo l) = RValSeq vl /\ (eval_funinfo l') = RValSeq vl') \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (eval_funinfo l) = ex /\ (eval_funinfo l') = ex').
Proof.
  intros. unfold eval_funinfo. break_match_goal; try solve_complex_Excrel.
  all: inv H; try solve_complex_Excrel.
  apply Vrel_possibilities in H2 as H2'; intuition; destruct_hyps; subst.
  all: inv H4; try solve_complex_Excrel.
  all: inv H0; try now solve_complex_Excrel.
  do 2 break_match_goal.
  all: apply Vrel_possibilities in H as H'; intuition; destruct_hyps; subst; simpl in *; try congruence.
  2-8: solve_complex_Excrel.
  rewrite Vrel_Fix_eq in H2. destruct H2 as [_ [_ [E _]]]. subst.
  solve_complex_Vrel.
Unshelve.
  all: lia.
Qed.

(* Ltac Rel_solver :=
  try apply Rel_eval_io;
  try apply Rel_eval_arith;
  try apply Rel_eval_logical;
  try apply Rel_eval_equality;
  try apply Rel_eval_cmp;
  try apply Rel_eval_transform_list;
  try apply Rel_eval_list_tuple;
  try apply Rel_eval_length;
  try apply Rel_eval_tuple_size;
  try apply Rel_eval_hd_tl;
  try apply Rel_eval_elem_tuple;
  try apply Rel_eval_check;
  try apply Rel_eval_funinfo. *)

Ltac Rel_eval_macro H0 H2 := (* FRAGILE! H0, H2 are generated from destruct_hyps! *)
intuition; destruct_hyps;
  [ rewrite H0, H2; left; do 2 eexists; solve_complex_Vrel; auto |
    rewrite H0, H2; left; do 2 eexists; solve_complex_Excrel; auto ].

Lemma Rel_eval m mname mname0 f f0 l l':
  f = f0 -> mname = mname0 ->
  list_biforall (Vrel m) l l' ->
  (exists eff eff', (exists (vl vl' : list Val),
   list_biforall (Vrel m) vl vl' /\
   (eval mname f l   ) = Some (RValSeq vl, eff) /\ 
   (eval mname0 f0 l') = Some (RValSeq vl', eff')) \/
  (exists (ex ex' : Exception),
   Excrel m ex ex' /\
   (eval mname f l   ) = Some (RExc ex, eff) /\ 
   (eval mname0 f0 l') = Some (RExc ex', eff'))) \/
  (eval mname f l) = None /\ (eval mname0 f0 l') = None.
Proof.
  intros. subst.
  unfold eval.
  break_match_goal.
  1-9: pose proof (Rel_eval_arith m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-2: shelve.
  1-3: pose proof (Rel_eval_logical m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-4: pose proof (Rel_eval_equality m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-3: pose proof (Rel_eval_transform_list m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-2: pose proof (Rel_eval_list_tuple m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-2: pose proof (Rel_eval_convert m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-4: pose proof (Rel_eval_cmp m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1: pose proof (Rel_eval_length _ _ _ H1); Rel_eval_macro H0 H2.
  1: pose proof (Rel_eval_tuple_size _ _ _ H1); Rel_eval_macro H0 H2.
  1-2: pose proof (Rel_eval_hd_tl m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-2: pose proof (Rel_eval_elem_tuple m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  1-4: pose proof (Rel_eval_check m mname0 f0 _ _ H1); Rel_eval_macro H0 H2.
  12: pose proof (Rel_eval_funinfo m _ _ H1); Rel_eval_macro H0 H2.
  all: try now right.
  11: left; do 2 eexists; solve_complex_Excrel.
  Unshelve.
  * pose proof (Rel_eval_error m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_error m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_error m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * pose proof (Rel_eval_concurrent m mname0 f0 _ _ H1).
    intuition; destruct_hyps; try rewrite H; try rewrite H0; try rewrite H2.
    - left. do 2 eexists. solve_complex_Excrel.
    - now right.
  * left. pose proof (Rel_eval_io m mname0 f0 _ _ H1).
    destruct eval_io, eval_io. simpl in *; subst.
    intuition; destruct_hyps; try rewrite H0; try rewrite H2; subst.
    - do 2 eexists. now solve_complex_Vrel.
    - do 2 eexists. solve_complex_Excrel.
  * left. pose proof (Rel_eval_io m mname0 f0 _ _ H1).
    destruct eval_io, eval_io. simpl in *; subst.
    intuition; destruct_hyps; try rewrite H0; try rewrite H2; subst.
    - do 2 eexists. now solve_complex_Vrel.
    - do 2 eexists. solve_complex_Excrel.
Qed.


Lemma Rel_primop_eval m f f0 l l':
  f = f0 ->
  list_biforall (Vrel m) l l' ->
  (exists eff eff', (exists vl vl' : list Val,
   list_biforall (Vrel m) vl vl' /\
   (primop_eval f l) = Some (RValSeq vl, eff) /\ 
   (primop_eval f0 l') = Some (RValSeq vl', eff')) \/
  (exists ex ex' : Exception,
   Excrel m ex ex' /\
   (primop_eval f l) = Some (RExc ex, eff) /\ 
   (primop_eval f0 l') = Some (RExc ex', eff'))) \/
   (primop_eval f l) = None /\ (primop_eval f0 l') = None.
Proof.
  intros. subst.
  unfold primop_eval.
  break_match_goal.
  3: left; do 2 eexists; solve_complex_Excrel.
  all: unfold eval_primop_error; try rewrite Heqp; inv H0; [|inv H1].
  all: try now right.
  left. do 2 eexists. solve_complex_Excrel. downclose_Vrel.
  inv H2. 2: now right.
  left. do 2 eexists. solve_complex_Excrel; downclose_Vrel.
Unshelve.
  all: assumption.
Qed.

Lemma Rel_create_result_relaxed m l l' ident ident' :
  list_biforall (Vrel m) l l' ->
  IRel (S m) ident ident' ->
  (exists eff eff', (exists e e', forall k, k <= m -> Erel k e e' /\ 
    create_result ident l   = Some (RExp e, eff) /\
    create_result ident' l' = Some (RExp e', eff')) \/
  (exists vl vl', list_biforall (Vrel m) vl vl' /\
    create_result ident l = Some (RValSeq vl, eff) /\
    create_result ident' l' = Some (RValSeq vl', eff')) \/
  (exists ex ex', Excrel m ex ex' /\
    create_result ident l = Some (RExc ex, eff) /\
    create_result ident' l' = Some (RExc ex', eff'))) \/
  create_result ident' l' = None /\ create_result ident l = None.
Proof.
  intros. destruct ident, ident'; simpl; destruct H0 as [Hcl1 [Hcl2 H0]]; try contradiction.
  * left. do 2 eexists. right. left. exists l, l'; auto.
  * left. do 2 eexists. right. left. exists [VTuple l], [VTuple l']. auto.
  * left. do 2 eexists. right. left. do 2 eexists. split.
    2: split; reflexivity.
    constructor; auto. apply Vrel_Map_compat_closed.
    now apply Vrel_make_map.
  * destruct H0.
    apply Vrel_possibilities in H0 as Hvrel; intuition; destruct_hyps; subst.
    1,3-7: left; do 2 eexists;right; solve_complex_Excrel.
    destruct x.
    2: left; do 2 eexists; right; solve_complex_Excrel.
    apply Vrel_possibilities in H1 as Hvrel; intuition; destruct_hyps; subst.
    1,3-7: left; do 2 eexists; right; solve_complex_Excrel.
    destruct x.
    2: left; do 2 eexists; right; solve_complex_Excrel.
    pose proof (Rel_eval m s s s0 s0 _ _ eq_refl eq_refl H).
    intuition; destruct_hyps; subst.
    destruct H2; destruct_hyps; subst; rewrite H3, H4; left; do 2 eexists; right.
    now solve_complex_Vrel.
    solve_complex_Excrel.
    Unshelve. all: lia.
  * pose proof (Rel_primop_eval _ f f0 _ _ H0 H).
    intuition; destruct_hyps; subst.
    destruct H1; destruct_hyps; subst; rewrite H1, H2; left; do 2 eexists; right.
    now solve_complex_Vrel.
    solve_complex_Excrel.
  * destruct v.
    1-8: left; do 2 eexists; right; right; rewrite Vrel_Fix_eq in H0; destruct H0 as [Hcl3 [Hcl4 H0]], v0; try contradiction.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - subst. do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - subst. do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed, Vrel_Cons_compat_closed.
      1-2: rewrite Vrel_Fix_eq; apply H0.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed.
      apply Vrel_Tuple_compat_closed.
      apply go_is_biforall in H0.
      eapply biforall_impl. 2: exact H0.
      intros. rewrite Vrel_Fix_eq. exact H1.
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
    - break_match_goal.
      + rewrite Vrel_Fix_eq in H0.
        destruct v0, H0 as [Hcl3 [Hcl4 H0]]; try contradiction.
        destruct H0. subst.
        apply biforall_length in H as Hlen. rewrite Hlen in Heqb.
        rewrite Heqb. left; do 2 eexists.
        left. do 2 eexists; split; [|split;reflexivity].
        apply H1. lia. apply Nat.eqb_eq in Heqb. rewrite Heqb.
        now apply biforall_length in H.
        eapply biforall_impl. 2: eassumption. intros.
        eapply Vrel_downclosed; eassumption.
      + left; do 2 eexists. right. right. rewrite Vrel_Fix_eq in H0.
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
          all: try lia.
          1-4: exact None. (* was []*)
Qed.

Lemma Rel_create_result m l l' ident ident' :
  list_biforall (Vrel m) l l' ->
  IRel m ident ident' ->
  (exists eff eff', (exists e e', forall k, k < m -> Erel k e e' /\ 
    create_result ident l   = Some (RExp e, eff) /\
    create_result ident' l' = Some (RExp e', eff')) \/
  (exists vl vl', list_biforall (Vrel m) vl vl' /\
    create_result ident l  = Some (RValSeq vl, eff) /\
    create_result ident' l' = Some (RValSeq vl', eff')) \/
  (exists ex ex', Excrel m ex ex' /\
    create_result ident l = Some (RExc ex, eff) /\
    create_result ident' l' = Some (RExc ex', eff'))) \/
  create_result ident' l' = None /\ create_result ident l = None.
Proof.
  (* TODO: boiler plate proof, investigate whether it can be expressed with 
     Rel_create_result_relaxed! *)
  intros. destruct ident, ident'; simpl; destruct H0 as [Hcl1 [Hcl2 H0]]; try contradiction.
  * left. do 2 eexists. right. left. exists l, l'; auto.
  * left. do 2 eexists. right. left. exists [VTuple l], [VTuple l']. auto.
  * left. do 2 eexists. right. left. do 2 eexists. split.
    2: split; reflexivity.
    constructor; auto. apply Vrel_Map_compat_closed.
    now apply Vrel_make_map.
  * destruct H0.
    apply Vrel_possibilities in H0 as Hvrel; intuition; destruct_hyps; subst.
    1,3-7: left; do 2 eexists;right; solve_complex_Excrel.
    destruct x.
    2: left; do 2 eexists; right; solve_complex_Excrel.
    apply Vrel_possibilities in H1 as Hvrel; intuition; destruct_hyps; subst.
    1,3-7: left; do 2 eexists; right; solve_complex_Excrel.
    destruct x.
    2: left; do 2 eexists; right; solve_complex_Excrel.
    pose proof (Rel_eval m s s s0 s0 _ _ eq_refl eq_refl H).
    intuition; destruct_hyps; subst.
    destruct H2; destruct_hyps; subst; rewrite H3, H4; left; do 2 eexists; right.
    now solve_complex_Vrel.
    solve_complex_Excrel.
    Unshelve. all: lia.
  * pose proof (Rel_primop_eval _ f f0 _ _ H0 H).
    intuition; destruct_hyps; subst.
    destruct H1; destruct_hyps; subst; rewrite H1, H2; left; do 2 eexists; right.
    now solve_complex_Vrel.
    solve_complex_Excrel.
  * destruct v.
    1-8: left; do 2 eexists; right; right; rewrite Vrel_Fix_eq in H0; destruct H0 as [Hcl3 [Hcl4 H0]], v0; try contradiction.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - subst. do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - subst. do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed, Vrel_Cons_compat_closed.
      1-2: rewrite Vrel_Fix_eq; apply H0.
    - do 2 eexists; split; [|split;reflexivity].
      split; [|split]; auto.
      eapply Vrel_downclosed.
      apply Vrel_Tuple_compat_closed.
      apply go_is_biforall in H0.
      eapply biforall_impl. 2: exact H0.
      intros. rewrite Vrel_Fix_eq. exact H1.
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
    - break_match_goal.
      + rewrite Vrel_Fix_eq in H0.
        destruct v0, H0 as [Hcl3 [Hcl4 H0]]; try contradiction.
        destruct H0. subst.
        apply biforall_length in H as Hlen. rewrite Hlen in Heqb.
        rewrite Heqb. left; do 2 eexists.
        left. do 2 eexists; split; [|split;reflexivity].
        apply H1. lia. apply Nat.eqb_eq in Heqb. rewrite Heqb.
        now apply biforall_length in H.
        eapply biforall_impl. 2: eassumption. intros.
        eapply Vrel_downclosed; eassumption.
      + left; do 2 eexists. right. right. rewrite Vrel_Fix_eq in H0.
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
          all: try lia.
          1-4: exact None (* was [] *).
Qed.

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
    destruct H. clear H9.
    split. 2: split.
    1-2: repeat constructor; auto.
    1,4: apply H0.
    2,4: apply H5.
    1,2: now apply biforall_vrel_closed in H6.
    split; [|split]; intros.
    - inv H10. destruct vl2. 2: destruct vl2. all: inv H9.
      2: { inv H15. }
      assert (list_biforall (Vrel (S k0)) (vl ++ [v]) (vl' ++ [v0])). {
        apply biforall_app; auto.
        eapply biforall_impl. 2: exact H6.
        intros. eapply Vrel_downclosed; eassumption. Unshelve. lia.
      }
      assert (IRel (S k0) ident ident'). {
        destruct ident, ident'; auto.
        * split. 2: split. 1-2: apply H0.
          destruct H0 as [_ [_ [Hrel1 Hrel2]]].
          split; downclose_Vrel. Unshelve. all: lia.
        * split. 2: split. 1-2: apply H0.
          eapply Vrel_downclosed. apply H0.
          Unshelve. lia.
      }
      eapply Rel_create_result in H9.
      2: eassumption.
      intuition. destruct H11 as [eff0 [eff0' H11]]. intuition.
      + edestruct H9 as [e0 [e0' [Hee' [Eq1 Eq2]]]]. instantiate (1 := k0). lia.
        rewrite Eq1 in H16. invSome.
        eapply Hee' in H17 as [i D]. eexists.
        econstructor. symmetry. exact Eq2. exact D.
        lia. fold (Frel k0 F1 F2). eapply Frel_downclosed. eassumption.
        Unshelve. lia.
      + destruct H11 as [vl0 [vl0' [Hvlvl' [Eq1 Eq2]]]].
        rewrite Eq1 in H16. invSome.
        eapply H5 in H17 as [i D]. eexists.
        econstructor. symmetry. exact Eq2. exact D.
        lia.
        eapply biforall_impl. 2: eassumption.
        intros. eapply Vrel_downclosed. eassumption.
        Unshelve. lia.
      + destruct H11 as [ex0 [ex0' [Hexex' [Eq1 Eq2]]]].
        rewrite Eq1 in H16. invSome.
        eapply H5 in H17 as [i D]. eexists.
        econstructor. symmetry. exact Eq2. exact D.
        lia.
        fold (Excrel k0 ex0 ex0'). eapply Excrel_downclosed. eassumption.
        Unshelve. lia.
      + congruence.
    - inv H10. eapply H5 in H16 as [i D]. eexists. constructor.
      reflexivity.
      exact D.
      lia.
      eapply Excrel_downclosed; eassumption.
    - inv H9.
      assert (list_biforall (Vrel (S k0)) vl vl'). {
        eapply biforall_impl. 2: exact H6.
        intros. eapply Vrel_downclosed; eassumption. Unshelve. all: lia.
      }
      assert (IRel (S k0) ident ident'). {
        destruct ident, ident'; auto.
        * split. 2: split. 1-2: apply H0.
          destruct H0 as [_ [_ [Hrel1 Hrel2]]].
          split; downclose_Vrel. Unshelve. all: lia.
        * split. 2: split. 1-2: apply H0.
          eapply Vrel_downclosed. apply H0.
          Unshelve. lia.
      }
      eapply Rel_create_result in H9. 2: eassumption.
      intuition. destruct H11 as [eff0 [eff0' H11]].
      intuition; destruct_hyps; subst.
      (* same as before *)
      + destruct (H9 k0 ltac:(lia)) as [Hee' [Eq1 Eq2]].
        rewrite Eq1 in H14. invSome.
        eapply Hee' in H16 as [i D]. eexists.
        econstructor. 2: symmetry; exact Eq2. 2: exact D.
        1: destruct ident, ident', H0 as [_ [_ H0]]; congruence.
        lia. eapply Frel_downclosed. eassumption.
        Unshelve. lia.
      + rewrite H11 in H14. invSome.
        eapply H5 in H16 as [i D]. eexists.
        econstructor.
        1: destruct ident, ident', H0 as [_ [_ H0]]; congruence.
        symmetry. exact H12. exact D.
        lia.
        eapply biforall_impl. 2: eassumption.
        intros. eapply Vrel_downclosed. eassumption.
        Unshelve. lia.
      + rewrite H11 in H14. invSome.
        eapply H5 in H16 as [i D]. eexists.
        econstructor.
        1: destruct ident, ident', H0 as [_ [_ H0]]; congruence.
        symmetry. exact H12. exact D.
        lia.
        eapply Excrel_downclosed. eassumption.
        Unshelve. lia.
      + congruence.
  * inv H.
    eapply H3 in H7 as [i D]. eexists. exact D. lia.
    destruct H. clear H9.
    split. 2: split.
    1-2: constructor; auto.
    2,4: apply H5.
    1-2: constructor; auto.
    1,4: apply H0.
    1,3: now apply biforall_vrel_closed in H6.
    1-2: apply Erel_closed in H10.
    1-2: apply biforall_erel_closed in H12.
    1-2: constructor; auto; try apply H12; apply H10.
    split. 2: split.
    - intros. inv H11. destruct vl2. 2: destruct vl2. all: inv H9.
      2: inv H17.
      eapply IHl in H20 as [i D].
      eexists. econstructor. exact D.
      all: auto.
      + intros. apply H1 in H9 as [n L]. simpl in L.
        exists n. rewrite length_app. slia.
      + intros. apply H2 in H9 as [n L]. simpl in L.
        exists n. rewrite length_app. slia.
      + lia.
      + eapply Frel_downclosed; eassumption.
      + apply biforall_app. 2: constructor.
        eapply biforall_impl. 2: exact H6.
        intros.
        1-2: eapply Vrel_downclosed; eassumption.
        constructor.
    - intros. inv H11. eapply H5 in H18 as [i D].
      eexists. constructor. reflexivity. exact D. lia.
      eapply Excrel_downclosed; eassumption.
    - intros. inv H9.
      assert (ident' <> IMap). {
        destruct ident, ident', H0 as [_ [_ H0]]; congruence.
      }
      eapply IHl in H19 as [i D]. eexists. econstructor. 2: exact D.
      all: auto.
      1-2: intros; congruence.
      lia.
      eapply Frel_downclosed; eassumption.
      eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
  Unshelve. all: lia.
Qed.


Lemma Vrel_Params_compat_closed :
  forall m l l',
  list_biforall (Erel m) l l' ->
  forall ident ident' vl vl' vl0 vl0',
  (* technical side conditions: *)
  IRel m ident ident' ->
  (ident = IMap -> exists n, length l + length vl = 1 + 2*n) ->
  (ident' = IMap -> exists n, length l' + length vl' = 1 + 2*n) ->
  (****)
  list_biforall (Vrel m) vl0 vl0' ->
  forall k, k <= m -> forall F1 F2,
  Frel k F1 F2 ->
  list_biforall (Vrel k) vl vl' ->
  | FParams ident vl l :: F1, RValSeq vl0 | k ↓ ->
  | FParams ident' vl' l' :: F2, RValSeq vl0' | ↓.
Proof.
  intros. inv H7.
  * simpl in *. inv H3. inv H11. inv H.
    eapply Erel_Params_compat_closed in H14 as [k D].
    - exists (S k). constructor. exact D.
    - eassumption.
    - assumption.
    - intros. apply H1 in H as [n Eq]. simpl. exists n.
      rewrite length_app; slia.
    - intros. apply H2 in H as [n Eq]. simpl in *. exists n.
      rewrite length_app; slia.
    - assumption.
    - lia.
    - eapply Frel_downclosed; eassumption.
    - apply biforall_app.
      eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
      constructor; auto. downclose_Vrel.
  * inv H3. inv H11. inv H.
    epose proof (Rel_create_result (S k0) (vl ++ [v]) (vl' ++ [hd']) ident ident' _ _).
    intuition. destruct H3 as [eff0 [eff0' H3]].
    intuition; destruct_hyps; subst.
    - specialize (H k0 ltac:(lia)) as [Hrel [Eq1 Eq2]]. rewrite Eq1 in H14. invSome.
      eapply Hrel in H15 as [k1 D]. eexists. econstructor.
      symmetry; eassumption. exact D. lia. eapply Frel_downclosed; eassumption.
    - rewrite H3 in H14. invSome.
      eapply H5 in H15 as [k1 D]. eexists. econstructor.
      symmetry; eassumption. exact D. lia.
      eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
    - rewrite H3 in H14. invSome.
      eapply H5 in H15 as [k1 D]. eexists. econstructor.
      symmetry; eassumption. exact D. lia.
      eapply Excrel_downclosed; eassumption.
    - congruence.
  Unshelve.
    all: try lia.
    eapply biforall_app; auto.
    constructor; auto. downclose_Vrel.
    destruct ident, ident'; auto.
    1-2: constructor. 2, 4: constructor. 1-2,4,6: apply H0.
    + destruct H0 as [_ [_ [Hrel1 Hrel2]]].
      split; downclose_Vrel. Unshelve. all: lia.
    + eapply Vrel_downclosed. apply H0.
      Unshelve. lia.
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
  * destruct l'. 2: inv H.
    assert (IRel (S k0) ident ident'). {
      destruct ident, ident', H0 as [? [? ?]]; split; auto.
      * split. 2: split. all: auto. all: destruct H7; downclose_Vrel.
        Unshelve. all: lia.
      * split. auto. downclose_Vrel.
        Unshelve. lia.
    }
    assert (ident' <> IMap) as ID. {
      destruct ident, ident'; try congruence; destruct H0 as [_ [_ H0]]; congruence.
    }
    epose proof (Rel_create_result _ _ _ _ _ H5 H6).
    intuition. destruct H8 as [eff0 [eff0' H8]].
    intuition; destruct_hyps.
    + specialize (H7 k0 ltac:(lia)). destruct_hyps.
      rewrite H8 in *. invSome.
      eapply H7 in H14; auto. 2: eapply Frel_downclosed; eassumption.
      destruct H14 as [k1 D].
      eexists. econstructor; try eassumption; eauto.
    + rewrite H8 in *. invSome. eapply H4 in H14. 2: lia.
      2: eapply biforall_impl; try eassumption; intros; downclose_Vrel.
      destruct H14 as [k1 D].
      eexists. econstructor; try eassumption; eauto.
    + rewrite H8 in *. invSome. eapply H4 in H14. 2: lia.
      2: eapply Excrel_downclosed; eassumption.
      destruct H14 as [k1 D].
      eexists. econstructor; try eassumption; eauto.
    + congruence.
  Unshelve.
    all: lia.
Qed.

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
  intros. unfold Erel_open. intros. simpl.
  apply Erel_Tuple_compat_closed.
  induction H; constructor; auto.
Qed.

Global Hint Resolve Erel_Tuple_compat : core.

Lemma Erel_Values_compat_closed :
  forall m l l',
  list_biforall (Erel m) l l' ->
  Erel m (EValues l) (EValues l').
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

Global Hint Resolve Erel_Values_compat_closed : core.

Lemma Erel_Values_compat :
  forall Γ l l',
  list_biforall (Erel_open Γ) l l' ->
  Erel_open Γ (EValues l) (EValues l').
Proof.
  intros. unfold Erel_open. intros. simpl.
  apply Erel_Values_compat_closed.
  induction H; constructor; auto.
Qed.

Global Hint Resolve Erel_Values_compat : core.

Lemma Erel_Map_compat_closed :
  forall m l l',
  list_biforall (fun '(e1, e2) '(e1', e2') =>
    Erel m e1 e1' /\ Erel m e2 e2'
  ) l l' ->
  Erel m (EMap l) (EMap l').
Proof.
  intros.
  split. 2: split.
  1: {
    do 2 constructor; intros.
    all: eapply biforall_forall in H; [|eassumption].
    all: rewrite map_nth with (d := (˝VNil, ˝VNil)).
    Unshelve. 3-6: exact (˝VNil, ˝VNil).
    all: do 2 break_match_hyp; simpl; destruct H;
    eapply Erel_closed_l; eassumption.
  }
  1: {
    apply biforall_length in H as H'.
    do 2 constructor; intros.
    all: eapply biforall_forall in H; [|rewrite H';eassumption].
    all: rewrite map_nth with (d := (˝VNil, ˝VNil)).
    Unshelve. 3-6: exact (˝VNil, ˝VNil).
    all: do 2 break_match_hyp; simpl; destruct H;
    eapply Erel_closed_r; eassumption.
  }
  intros.
  inv H1. 3: inv_val.
  * inv H. eapply H0 in H4. 2: lia.
    destruct H4. eexists. econstructor. exact H.
    constructor; auto.
  * inv H. destruct hd', H3.
    eapply H in H4 as D1. destruct D1 as [k1 D1]. 2: lia.
    eexists. constructor. exact D1.
    clear H2 H3.
    split. 2: split.
    1: {
      constructor. 2: apply H0.
      constructor; auto.
      * constructor. now apply Erel_closed_l in H1.
        apply flatten_keeps_prop. clear -H6. induction H6; constructor; auto.
        destruct hd, hd'. split; eapply Erel_closed_l; apply H.
      * intros. clear. simpl. rewrite length_flatten_list.
        exists (length el). lia.
    }
    1: {
      constructor. 2: apply H0.
      constructor; auto.
      * constructor. now apply Erel_closed_r in H1.
        apply flatten_keeps_prop. clear -H6. induction H6; constructor; auto.
        destruct hd, hd'. split; eapply Erel_closed_r; apply H.
      * intros. clear. simpl. rewrite length_flatten_list.
        exists (length tl'). lia.
    }
    split. 2: split.
    { (* normal *)
      intros. inv H3. simpl in H13.
      inv H2. inv H9.
      eapply Erel_Params_compat_closed in H13 as [i D].
      eexists. constructor. exact D.
      {
        instantiate (1 := m).
        clear H7 H13 Hmn0 H H1 Hmn H0 H4.
        induction H6; simpl. constructor.
        destruct hd, hd'0. constructor. 2: constructor.
        1-2: apply H. assumption.
      }
      split; auto; split; auto.
      1-2: intros; simpl; rewrite length_flatten_list.
      1: exists (length el). 2: exists (length tl'). 1-2: lia.
      exact H1. lia.
      eapply Frel_downclosed; eassumption.
      simpl. constructor; auto. downclose_Vrel.
    }
    { (* exceptions *)
      intros. inv H3. eapply H0 in H11. 2: lia.
      destruct H11 as [k2 D2]. eexists. constructor. 2: exact D2.
      2: eapply Excrel_downclosed; eassumption.
      reflexivity.
    }
    {
      intros.
      inv H2.
    }
  Unshelve.
    all: lia.
Qed.

Global Hint Resolve Erel_Map_compat_closed : core.

Lemma Erel_Map_compat :
  forall Γ l l',
  list_biforall (fun '(e1, e2) '(e1', e2') =>
    Erel_open Γ e1 e1' /\ Erel_open Γ e2 e2'
  ) l l' ->
  Erel_open Γ (EMap l) (EMap l').
Proof.
  intros. unfold Erel_open. intros. simpl.
  apply Erel_Map_compat_closed.
  induction H; constructor; auto.
  destruct hd, hd', H; split; auto.
Qed.

Global Hint Resolve Erel_Map_compat : core.

Lemma Erel_Call_compat_closed :
  forall m mname mname' l l' f f',
  Erel m mname mname' ->
  Erel m f f' ->
  list_biforall (Erel m) l l' ->
  Erel m (ECall mname f l) (ECall mname' f' l').
Proof.
  intros. apply biforall_erel_closed in H1 as Hcl.
  apply Erel_closed in H as Hclm.
  apply Erel_closed in H0 as Hclf.
  destruct Hclm, Hcl, Hclf.
  split. 2: split.
  1-2: do 2 constructor; try apply indexed_to_forall; auto.
  intros.
  inv H9. 2: { inv H10. }
  eapply H in H15 as [k1 D1]. 2: lia.
  eexists. constructor. exact D1.
  clear H9 H10 H15. split. 2: split.
  1-2: constructor; try apply H8; constructor; auto.
  split. 2: split.
  * intros. inv H10. inv H9. inv H14.
    eapply H0 in H16 as [k2 D2]. 2: lia.
    eexists. constructor. exact D2.
    clear H9 H10. apply Vrel_closed in H12 as H12'. destruct H12'.
    split. 2: split.
    1-2: constructor; try apply H8; constructor; auto.
    split. 2: split.
    - intros. inv H13. inv H11. inv H18.
      apply Vrel_closed in H15 as H15'. destruct H15'.
      eapply Erel_Params_compat_closed_box in H20 as [i D].
      + eexists. constructor. exact D.
      + eapply biforall_impl. 2: eassumption.
        intros. eapply Erel_downclosed. eassumption.
      + repeat split; auto; downclose_Vrel.
      + intros. congruence.
      + intros. congruence.
      + reflexivity.
      + eapply Frel_downclosed; eassumption.
      + auto.
    - intros. inv H13. eapply H8 in H20 as [k2 D2]. 2: lia.
      eexists. constructor. reflexivity. exact D2.
      eapply Excrel_downclosed in H11. exact H11.
    - intros. inv H11.
  * intros. inv H10. eapply H8 in H16 as [k1 D1]. 2: lia.
    eexists. constructor. reflexivity. exact D1.
    eapply Excrel_downclosed in H9. exact H9.
  * intros. inv H9.
  Unshelve. all: try lia.
Qed.

Global Hint Resolve Erel_Call_compat_closed : core.

Lemma Erel_Call_compat :
  forall Γ l l' m m' f f',
  Erel_open Γ m m' ->
  Erel_open Γ f f' ->
  list_biforall (Erel_open Γ) l l' ->
  Erel_open Γ (ECall m f l) (ECall m' f' l').
Proof.
  intros. unfold Erel_open. intros. simpl.
  apply Erel_Call_compat_closed; auto.
  induction H1; constructor; auto.
Qed.

Global Hint Resolve Erel_Call_compat : core.

Lemma Erel_PrimOp_compat_closed :
  forall m l l' f f',
  f = f' ->
  list_biforall (Erel m) l l' ->
  Erel m (EPrimOp f l) (EPrimOp f' l').
Proof.
  intros. apply biforall_erel_closed in H0 as Hcl.
  split. 2: split.
  1-2: do 2 constructor; apply indexed_to_forall, Hcl.
  clear Hcl. intros.
  inv H2. 2: inv H3. eapply Erel_Params_compat_closed_box in H7 as [i D].
  - eexists. constructor. exact D.
  - eassumption.
  - repeat split; auto.
  - intros. congruence.
  - intros. congruence.
  - lia.
  - eapply Frel_downclosed; eassumption.
  - auto.
  Unshelve. lia.
Qed.

Global Hint Resolve Erel_PrimOp_compat_closed : core.

Lemma Erel_PrimOp_compat :
  forall Γ l l' f f',
  f = f' ->
  list_biforall (Erel_open Γ) l l' ->
  Erel_open Γ (EPrimOp f l) (EPrimOp f' l').
Proof.
  intros. unfold Erel_open. intros. simpl.
  apply Erel_PrimOp_compat_closed; auto.
  induction H0; constructor; auto.
Qed.

Global Hint Resolve Erel_PrimOp_compat : core.

Lemma Vrel_Fun_right : forall m v2 ext id1 vl b,
  Vrel m (VClos ext id1 vl b) v2 ->
  exists ext' id' b' vl',
  vl = vl' /\ v2 = VClos ext' id' vl' b'.
Proof.
  intros. rewrite Vrel_Fix_eq in H. destruct H, H0. destruct v2; try contradiction. destruct H1. subst. do 4 eexists.
  split. 2: split. all: try reflexivity.
Qed.

Lemma Erel_App_compat_closed :
  forall n e es e' es',
  Erel n e e' -> list_biforall (Erel n) es es'
->
  Erel n (EApp e es) (EApp e' es').
Proof.
  intros. apply biforall_erel_closed in H0 as Hcl.
  split. 2: split.
  1-2: do 2 constructor; try apply indexed_to_forall, Hcl;
  apply Erel_closed in H; apply H.
  intros.
  inv H2. 2: inv H3.
  eapply H in H7. 2: lia. destruct H7 as [k1 D1].
  eexists. constructor. exact D1.
  split. 2: split.
  1-2: constructor; try apply H1; constructor; apply Hcl.
  split. 2: split.
  { (* normal *)
    intros. inv H5. inv H4. inv H10. 
    eapply Erel_Params_compat_closed_box in H11 as [k2 D2].
    eexists. econstructor. exact D2.
    - shelve.
    - split. 2: split. 1-2: constructor; apply Vrel_closed in H8; apply H8. downclose_Vrel.
    - congruence.
    - congruence.
    - shelve.
    - eapply Frel_downclosed; eassumption.
    - auto.
  }
  { (* exception *)
    intros. inv H5. eapply H1 in H12 as [k2 D2].
    eexists. constructor. 2: exact D2. reflexivity.
    lia.
    eapply Excrel_downclosed; eassumption.
  }
  {
    intros. inv H4.
  }
Unshelve.
  all: try lia.
  exact k0.
  2-3: lia.
  eapply biforall_impl. 2: eassumption.
  intros. eapply Erel_downclosed; eassumption.
Unshelve.
  lia.
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

Theorem Rel_Fundamental_helper :
  (forall (e : Exp) (Γ : nat),
    EXP Γ ⊢ e ->
    Erel_open Γ e e) /\
  (forall (e : NonVal) (Γ : nat),
    NVAL Γ ⊢ e ->
    Erel_open Γ e e) /\
  (forall (v : Val) (Γ : nat),
    VAL Γ ⊢ v ->
    Vrel_open Γ v v).
Proof.
  eapply Exp_ind with
    (QV := Forall (fun v => forall Γ, VAL Γ ⊢ v -> Vrel_open Γ v v))
    (RV := Forall (PBoth (fun v => forall Γ, VAL Γ ⊢ v -> Vrel_open Γ v v)))
    (VV := Forall (fun '(id, vars, b) => forall Γ, EXP Γ ⊢ b -> Erel_open Γ b b))
    (Q := Forall (fun e => forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e))
    (R := Forall (PBoth (fun e => forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e)))
    (Z := Forall (fun '(x, e) => forall Γ, EXP Γ ⊢ e -> Erel_open Γ e e))
    (W := Forall (fun '(p, g, e) => forall Γ, (EXP Γ ⊢ g -> Erel_open Γ g g) /\ (EXP Γ ⊢ e -> Erel_open Γ e e))); intros; auto; try destruct_scopes.
  - apply Erel_Val_compat. now apply H.
  - now apply H.
  - apply Vrel_Cons_compat; auto.
  - apply Vrel_Tuple_compat, forall_biforall_refl.
    induction H; constructor; auto.
    apply H. apply (H3 0). simpl. lia.
    apply IHForall. intros. apply (H3 (S i)). slia.
  - apply Vrel_Map_compat, forall_biforall_refl.
    induction H; constructor; auto.
    destruct x. inv H. split.
    apply H1. apply (H2 0). slia.
    apply H3. apply (H4 0). slia.
    apply IHForall.
    intros. apply (H2 (S i)). slia.
    intros. apply (H4 (S i)). slia.
  - now apply Vrel_Var_compat.
  - destruct n. now apply Vrel_FunId_compat.
  - apply Vrel_Clos_compat; auto.
    apply forall_biforall_refl.
    rewrite indexed_to_forall. rewrite indexed_to_forall in H. intros.
    apply H in H1 as H1'. clear H. apply H5 in H1. clear H5.
    Unshelve. 2-3: exact (0, 0, ˝VNil).
    rewrite map_nth with (d := (0, 0, ˝VNil)) in H1.
    rewrite map_nth with (d := (0, 0, ˝VNil)) in H1.
    destruct nth, p.
    intuition.
  - apply Erel_Fun_compat; auto.
  - apply Erel_Values_compat, forall_biforall_refl.
    induction H; constructor; auto.
    apply H. apply (H3 0). simpl. lia.
    apply IHForall. intros. apply (H3 (S i)). slia.
  - apply Erel_Cons_compat; auto.
  - apply Erel_Tuple_compat, forall_biforall_refl.
    induction H; constructor; auto.
    apply H. apply (H3 0). simpl. lia.
    apply IHForall. intros. apply (H3 (S i)). slia.
  - apply Erel_Map_compat, forall_biforall_refl.
    induction H; constructor; auto.
    destruct x. inv H. split.
    apply H1. apply (H2 0). slia.
    apply H3. apply (H4 0). slia.
    apply IHForall.
    intros. apply (H2 (S i)). slia.
    intros. apply (H4 (S i)). slia.
  - apply Erel_Call_compat, forall_biforall_refl; auto.
    induction H1; constructor; auto.
    apply H1. apply (H7 0). simpl. lia.
    apply IHForall. intros. apply (H7 (S i)). slia.
  - apply Erel_PrimOp_compat, forall_biforall_refl; auto.
    induction H; constructor; auto.
    apply H. apply (H3 0). simpl. lia.
    apply IHForall. intros. apply (H3 (S i)). slia.
  - apply Erel_App_compat, forall_biforall_refl; auto.
    induction H0; constructor; auto.
    apply H0. apply (H6 0). simpl. lia.
    apply IHForall. intros. apply (H6 (S i)). slia.
  - apply Erel_Case_compat; auto.
    apply forall_biforall_refl. rewrite indexed_to_forall. intros.
    apply H6 in H1 as H1'. apply H7 in H1 as H1''.
    clear H6 H7. Unshelve. 2: exact ([], ˝VNil, ˝VNil).
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H1'.
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H1''.
    rewrite indexed_to_forall in H0. apply H0 in H1. clear H0.
    replace (nth i (map (fst ∘ fst) l) []) with
      ((fst ∘ fst) (nth i l ([], ˝VNil, ˝VNil))) in H1'.
    replace (nth i (map (fst ∘ fst) l) []) with
      ((fst ∘ fst) (nth i l ([], ˝VNil, ˝VNil))) in H1''.
    2-3: rewrite <- map_nth with (f := (fst ∘ fst)); cbn; auto.
    Unshelve. 2: exact ([], ˝VNil, ˝VNil).
    destruct nth, p; intuition; cbn in *; apply H1; auto.
  - apply Erel_Let_compat; auto.
  - apply Erel_Seq_compat; auto.
  - eapply Erel_LetRec_compat; auto.
    apply forall_biforall_refl. rewrite indexed_to_forall.
    rewrite indexed_to_forall in H0. intros.
    apply H5 in H1 as H1'. apply H0 in H1 as H1''. clear H5 H1.
    Unshelve. 2-3: exact (0, ˝VNil).
    do 2 rewrite map_nth with (d := (0, ˝VNil)) in H1'.
    destruct nth. split; auto.
  - apply Erel_Try_compat; auto.
Qed.

Corollary Vrel_Fundamental :
  forall (v : Val) (Γ : nat),
    VAL Γ ⊢ v ->
    Vrel_open Γ v v.
Proof.
  apply Rel_Fundamental_helper.
Qed.

Global Hint Resolve Vrel_Fundamental : core.

Corollary Erel_Fundamental :
  forall (e : Exp) (Γ : nat),
    EXP Γ ⊢ e ->
    Erel_open Γ e e.
Proof.
  apply Rel_Fundamental_helper.
Qed.

Global Hint Resolve Erel_Fundamental : core.

Lemma Grel_ids : forall n, Grel n 0 idsubst idsubst.
Proof.
  intros.
  unfold Grel.
  intuition auto using scope_idsubst.
  exfalso; auto. inversion H.
Qed.

Theorem Vrel_Fundamental_closed :
  forall (v : Val),
    VALCLOSED v ->
    forall n, Vrel n v v.
Proof.
  intros.
  replace v with (v.[idsubst]ᵥ).
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

Corollary default_subst_Grel :
  forall m Γ v, VALCLOSED v -> Grel m Γ (default_subst v) (default_subst v).
Proof.
  intros. unfold Grel. split. 2: split. 1-2: auto.
  intros. unfold default_subst.
  now apply Vrel_Fundamental_closed.
Qed.

Theorem Excrel_Fundamental_closed :
  forall m c r v, VALCLOSED r -> VALCLOSED v ->
  Excrel m (c, r, v) (c, r, v).
Proof.
  intros. split; auto.
Qed.

Lemma Frel_CallMod :
  forall n (f1 f2 : Exp) (l1 l2 : list Exp),
  Erel n f1 f2 ->
  list_biforall (Erel n) l1 l2 ->
  forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCallMod f1 l1 :: F1) (FCallMod f2 l2 :: F2).
Proof.
  intros. eapply biforall_erel_closed in H0 as H0'.
  apply Erel_closed in H as H'.
  split. 2: split.
  1-2: constructor; try apply H2; constructor; try apply H'; try apply H0'.
  split. 2: split.
  {
    intros. inv H4. inv H3. inv H8.
    eapply H in H10 as [k1 D1]. 2: lia.
    eexists. constructor. eassumption.
    clear H3 H4.
    apply Vrel_closed in H6 as H6'.
    split. 2: split. 1-2: constructor; try apply H2; constructor; try apply H0'; try apply H6'.
    split. 2: split.
      * intros. inv H4. inv H3. inv H9.
        apply Vrel_closed in H7 as H7'. destruct_hyps.
        eapply Erel_Params_compat_closed_box in H12 as [k1 D1].
        eexists. econstructor. eassumption.
        eapply biforall_impl. 2: eassumption.
        intros. eapply Erel_downclosed;  eassumption.
        do 2 constructor; auto.
        split; downclose_Vrel.
        1-2: congruence.
        2: eapply Frel_downclosed; eassumption.
        reflexivity.
        auto.
    * intros. inv H4. eapply H2 in H12 as [k1 D1]. 2: lia.
      eexists. constructor. reflexivity. eassumption.
      eapply Excrel_downclosed. eassumption.
    * intros. inv H3.
  }
  {
    intros. inv H4. eapply H2 in H10 as [k1 D1].
    eexists. constructor. reflexivity. exact D1.
    lia.
    eapply Excrel_downclosed; eassumption.
  }
  {
    intros. inv H3.
  }
Unshelve.
  all: lia.
Qed.

Lemma Frel_CallFun :
  forall n (m1 m2 : Val) (l1 l2 : list Exp),
  Vrel n m1 m2 ->
  list_biforall (Erel n) l1 l2 ->
  forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCallFun m1 l1 :: F1) (FCallFun m2 l2 :: F2).
Proof.
  intros. eapply biforall_erel_closed in H0 as H0'.
  apply Vrel_closed in H as H'.
  split. 2: split.
  1-2: constructor; try apply H2; constructor; try apply H'; try apply H0'.
  split. 2: split.
  * intros. inv H4. inv H3. inv H8.
    apply Vrel_closed in H6 as H6'. destruct_hyps.
    eapply Erel_Params_compat_closed_box in H10 as [k1 D1].
    eexists. econstructor. eassumption.
    eapply biforall_impl. 2: eassumption.
    intros. eapply Erel_downclosed;  eassumption.
    do 2 constructor; auto.
    split; downclose_Vrel.
    1-2: congruence.
    2: eapply Frel_downclosed; eassumption.
    reflexivity.
    auto.
  * intros. inv H4. eapply H2 in H10 as [k1 D1]. 2: lia.
    eexists. constructor. reflexivity. eassumption.
    eapply Excrel_downclosed. eassumption.
  * intros. inv H3.
Unshelve. all: lia.
Qed.


Lemma Frel_Cons_tail :
    forall n (e2 e2' : Exp),
    (forall m, m <= n -> Erel m e2 e2') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons1 e2::F1) (FCons1 e2'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Erel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor.
  split. 2: split.
  {
    intros.
    inv H7.
    inv H6. inv H11.
    eapply H' in H12 as [k1 D1]. 
    eexists. econstructor. eassumption. lia.
  
    split. 2: split. 1-2: constructor; auto; eapply Vrel_closed in H9; constructor; apply H9.
    split. 2: split.
    {
      intros. inv H10. inv H8. inv H15.
      eapply H3 in H16 as [k2 D2]. eexists. constructor. eassumption.
      lia.
      constructor; auto.
      eapply Vrel_Cons_compat_closed; downclose_Vrel. 
    }
    {
      intros. inv H10.
      eapply H3 in H17 as [k2 D2]. eexists. constructor.
      reflexivity. eassumption.
      lia.
      eapply Excrel_downclosed. eassumption.
    }
    {
      intros. inv H8.
    }
  } 
  {
    intros. inv H7. eapply H3 in H13 as [k1 D1].
    eexists. constructor.
    reflexivity. eassumption.
    lia.
    eapply Excrel_downclosed. eassumption.
  }
  {
    intros. inv H6.
  }
Unshelve.
  all: lia.
Qed.

Lemma Frel_Cons_head :
    forall n (v1 v1' : Val),
    (forall m, m <= n -> Vrel m v1 v1') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FCons2 v1::F1) (FCons2 v1'::F2).
Proof.
  intros. destruct H1, H2. specialize (H m H0) as H'.
  apply Vrel_closed in H' as v. destruct v. split. 2: split.
  1-2: constructor; auto; now constructor.
  split. 2: split.
  {
    intros. inv H7. inv H6. inv H11.
    eapply H3 in H12 as [k1 D1].
    eexists. econstructor. eassumption.
    lia.
    constructor; auto. choose_compat_lemma; downclose_Vrel. 
  }
  {
    intros. inv H7.
    eapply H3 in H13 as [k1 D1].
    eexists. econstructor. reflexivity. eassumption.
    lia.
    eapply Excrel_downclosed. eassumption.
  }
  {
    intros. inv H6.
  }
Unshelve.
  all: lia.
Qed.

Lemma Vrel_VNil_many :
  forall m x, list_biforall (Vrel m) (repeat VNil x) (repeat VNil x).
Proof.
  intros. induction x; constructor; auto.
Qed.

Lemma VCLOSED_VNil_many :
  forall x, Forall (fun v => VALCLOSED v) (repeat VNil x).
Proof.
  intros. induction x; constructor; auto.
Qed.

#[global]
Hint Resolve VCLOSED_VNil_many : core.

Lemma Frel_Let :
    forall n (e2 e2' : Exp) x x', x = x' ->
    (forall m vl1 vl2, m <= n -> length vl1 = x -> list_biforall (Vrel m) vl1 vl2 -> Erel m (e2.[list_subst vl1 idsubst]) (e2'.[list_subst vl2 idsubst])) ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FLet x e2::F1) (FLet x' e2'::F2).
Proof.
  intros. subst.
  specialize (H0 m (repeat VNil x') (repeat VNil x') H1 (repeat_length _ x') (Vrel_VNil_many _ x')) as H'.
  apply Erel_closed in H' as v. destruct v.
  eapply subst_implies_list_scope in H, H3; auto; rewrite repeat_length in H, H3.
  split. 2: split. 1-2: constructor; auto; try apply H2; constructor; auto.
  split. 2: split.
  {
    intros. inv H5. destruct_foralls.
    apply biforall_length in H4 as H4'.
    eapply H0 in H12 as [k1 D1].
    eexists. constructor; auto. eassumption.
    3: eassumption. 1-3: lia.
    eapply Frel_downclosed; eauto.
  }
  {
    intros. inv H5. destruct_foralls.
    eapply H2 in H11 as [k1 D1].
    eexists. constructor; auto. eassumption.
    lia.
    eapply Excrel_downclosed; eauto.
  }
  {
    intros. inv H4.
  }
Unshelve.
  all: lia.
Qed.

Lemma Frel_Seq :
    forall n (e2 e2' : Exp),
    (forall m, m <= n -> Erel m e2 e2') ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FSeq e2::F1) (FSeq e2'::F2).
Proof.
  intros. specialize (H m H0) as H'.
  split. 2: split.
  1-2: constructor; try apply H1; constructor; eapply Erel_closed in H'; apply H'.
  split. 2: split.
  {
    intros. inv H3. inv H2. inv H7.
    eapply H' in H8 as [k1 D1].
    eexists. econstructor. eassumption.
    lia.
    eapply Frel_downclosed. eassumption.
  }
  {
    intros. inv H3.
    eapply H1 in H9 as [k1 D1].
    eexists. econstructor. reflexivity. eassumption.
    lia.
    eapply Excrel_downclosed. eassumption.
  }
  {
    intros. inv H2.
  }
Unshelve.
  all: lia.
Qed.


Lemma Frel_Try :
    forall n (e2 e2' : Exp) (e3 e3' : Exp) x x' y y', x = x' -> y = y' ->
    (forall m vl1 vl2, m <= n -> length vl1 = x -> list_biforall (Vrel m) vl1 vl2 -> Erel m (e2.[list_subst vl1 idsubst]) (e2'.[list_subst vl2 idsubst])) ->
    (forall m vl1 vl2, m <= n -> length vl1 = y -> list_biforall (Vrel m) vl1 vl2 -> Erel m (e3.[list_subst vl1 idsubst]) (e3'.[list_subst vl2 idsubst])) ->
    forall m F1 F2, m <= n -> Frel m F1 F2 ->
    Frel m (FTry x e2 y e3::F1) (FTry x' e2' y' e3'::F2).
Proof.
  intros. subst.
  specialize (H1 m (repeat VNil x') (repeat VNil x') H3 (repeat_length _ x') (Vrel_VNil_many _ x')) as H'.
  specialize (H2 m (repeat VNil y') (repeat VNil y') H3 (repeat_length _ y') (Vrel_VNil_many _ y')) as H''.
  apply Erel_closed in H' as [H'cl1 H'cl2].
  apply Erel_closed in H'' as [H''cl1 H''cl2].
  eapply subst_implies_list_scope in H'cl1, H'cl2, H''cl1, H''cl2. 
  2-5: auto.
  rewrite repeat_length in *.
  split. 2: split. 1-2: constructor; auto; try apply H4; constructor; auto.
  split. 2: split.
  {
    intros. inv H0.
    apply biforall_length in H as H'.
    eapply H1 in H13 as [k1 D1].
    eexists. constructor; auto. eassumption.
    3: eassumption. 1-3: lia.
    eapply Frel_downclosed; eauto.
  }
  {
    intros. inv H0. destruct e0, p.
    destruct H. subst.
    eapply H2 in H12 as [k1 D1].
    eexists. eapply cool_try_err; auto. eassumption.
    3: {
      constructor. apply Vrel_Fundamental_closed; destruct e; constructor.
      constructor. apply H0.
      2: constructor; auto; apply H0.
      Unshelve. 4: exact k. all: lia.
    }
    1-3: slia.
    eapply Frel_downclosed; eauto.
  }
  {
    intros. inv H.
  }
Unshelve.
  all: lia.
Qed.

Lemma Frel_Params :
  forall n (el el' : list Exp) (vl vl' : list Val),
  list_biforall (Erel n) el el' ->
  list_biforall (Vrel n) vl vl' ->
  forall m F1 F2 id1 id2, m <= n -> Frel m F1 F2 -> IRel m id1 id2 ->
  (* technical side conditions of map *)
  (id1 = IMap -> exists n, length el + length vl = 1 + 2 * n) ->
  (id2 = IMap -> exists n, length el' + length vl' = 1 + 2 * n) ->
    Frel m (FParams id1 vl el::F1) (FParams id2 vl' el'::F2).
Proof.
  intros.
  eapply biforall_erel_closed in H as H'.
  eapply biforall_vrel_closed in H0 as H0'.
  split. 2: split.
  (* scopes *)
  1-2: constructor; try apply H2; constructor; try apply H3.
  1,2,4,5: try apply H'; try apply H0'.
  1,2: auto.
  (* evaluation *)
  split. 2: split.
  {
    intros.
    eapply Vrel_Params_compat_closed in H5.
    1: eassumption.
    4: eapply biforall_impl; [|eassumption]; intros; downclose_Vrel.
    7: eassumption.
    1,6: eapply biforall_impl; [|eassumption].
    1,2: intros.
    1: eapply Erel_downclosed; eassumption.
    1: downclose_Vrel.
    destruct id1, id2; destruct H3 as [Hi1 [Hi2 H3]]; constructor; auto; constructor; auto. destruct H3; split; downclose_Vrel. downclose_Vrel.
    assumption.
    2: eapply Frel_downclosed; eassumption.
    1: reflexivity.
  }
  {
    intros. inv H7. eapply H2 in H13 as [k1 D1].
    eexists. constructor. reflexivity. exact D1.
    lia.
    eapply Excrel_downclosed; eassumption. 
  }
  {
    intros.
    eapply Erel_Params_compat_closed_box in H6. exact H6.
    eapply biforall_impl. 2: eassumption. intros. eapply Erel_downclosed. eassumption.
    exact H3.
    3: lia.
    3: eapply Frel_downclosed; eassumption.
    3: eapply biforall_impl; [|eassumption]; intros;downclose_Vrel.
    1: {
      intros. inv H6; congruence.
    }
    1: {
      intros.
      assert (id1 = IMap). {
        destruct id1, id2, H3 as [_ [_ H3]]; try contradiction; subst; auto.
        congruence. congruence.
      }
      subst. inv H6; congruence.
    }
  }
  Unshelve.
    all: lia.
Qed.

Lemma Frel_App1 :
  forall n (es es' : list Exp),
  list_biforall (Erel n) es es' ->
  forall m F1 F2, m <= n -> Frel m F1 F2 -> Frel m (FApp1 es::F1) (FApp1 es'::F2).
Proof.
  intros. eapply biforall_erel_closed in H as H'.
  split. 2: split.
  1-2: constructor; try apply H1; constructor; apply H'.
  split. 2: split.
  {
    intros. inv H3. inv H2. inv H7.
    eapply Erel_Params_compat_closed_box in H8 as [k1 D1].
    eexists. constructor. eassumption.
    eapply biforall_impl. 2: eassumption.
    intros. eapply Erel_downclosed;  eassumption.
    do 2 constructor. now eapply Vrel_closed_l in H5.
    constructor. now eapply Vrel_closed_r in H5.
    downclose_Vrel.
    1-2: congruence.
    2: eapply Frel_downclosed; eassumption.
    reflexivity.
    auto.
  }
  {
    intros. inv H3. eapply H1 in H9 as [k1 D1].
    eexists. constructor. reflexivity. exact D1.
    lia.
    eapply Excrel_downclosed; eassumption.
  }
  {
    intros. inv H2.
  }
Unshelve.
  all: lia.
Qed.

Corollary Erel_biforall_fundamental :
  forall l,
    Forall (fun e => EXPCLOSED e) l ->
    forall m, list_biforall (Erel m) l l.
Proof.
  induction l; intros; auto.
  inv H. constructor; auto.
Qed.

#[global]
Hint Resolve Erel_biforall_fundamental : core.

Corollary Vrel_biforall_fundamental :
  forall l,
    Forall (fun e => VALCLOSED e) l ->
    forall m, list_biforall (Vrel m) l l.
Proof.
  induction l; intros; auto.
  inv H. constructor; auto.
Qed.

#[global]
Hint Resolve Vrel_biforall_fundamental : core.

Lemma Frel_Case1 :
  forall n l l',
  list_biforall (
      fun '(pl, g, e) '(pl', g', e') => pl = pl' /\
        (forall m vl1 vl2, m <= n -> length vl1 = PatListScope pl ->
        list_biforall (Vrel m) vl1 vl2 ->
        Erel m (g.[list_subst vl1 idsubst]) (g'.[list_subst vl2 idsubst]) /\
        Erel m (e.[list_subst vl1 idsubst]) (e'.[list_subst vl2 idsubst]))
    ) l l' ->
  forall m F1 F2, m <= n -> Frel m F1 F2 ->
    Frel m (FCase1 l:: F1) (FCase1 l' :: F2) .
Proof.
  intros n l l' IH. induction IH; intros.
  * split. 2: split.
    1-2: constructor; try apply H0; constructor; auto.
    split. 2: split.
    {
      intros. inv H2. eapply H0 in H5 as [k1 D1].
      eexists. constructor. exact D1. lia.
      eapply Excrel_Fundamental_closed; constructor.
    }
    {
      intros. inv H2. eapply H0 in H8 as [k1 D1].
      eexists. constructor. congruence. exact D1. lia.
      eapply Excrel_downclosed; eauto.
    }
    {
      intros. inv H1.
    }
  * destruct hd, p, hd', p. destruct H as [Eqq H]. subst.
    split. 2: split.
    (* scopes - boiler plate... *)
    1-2: constructor; try apply H1; constructor.
    1: {
      specialize (H n (repeat VNil (PatListScope l0)) (repeat VNil (PatListScope l0)) ltac:(lia) (repeat_length _ _) ltac:(auto)) as [H_1 H_2].
      simpl. constructor.
      * rewrite <- (repeat_length VNil (PatListScope l0)).
        apply Erel_closed_l in H_1, H_2. apply subst_implies_list_scope in H_1, H_2; auto.
      * apply IHIH in H1. 2: lia.
        apply Frel_closed in H1. inv H1. now destruct_scopes.
    }
    1: {
      specialize (H n (repeat VNil (PatListScope l0)) (repeat VNil (PatListScope l0)) ltac:(lia) (repeat_length _ _) ltac:(auto)) as [H_1 H_2].
      simpl. constructor.
      * rewrite <- (repeat_length VNil (PatListScope l0)).
        apply Erel_closed_r in H_1, H_2. apply subst_implies_list_scope in H_1, H_2; auto.
      * apply IHIH in H1. 2: lia.
        apply Frel_closed in H1. inv H1. now destruct_scopes.
    }
    (* evaluation *)
    split. 2: split.
    {
      intros. inv H3.
      * eapply match_pattern_list_Vrel in H11 as H11'. 2: eassumption.
        eapply match_pattern_list_length in H11 as H11''.
        destruct H11' as [vs'' [Eq1 Eq2]].
        eapply H in H12 as [k1 D1].
        eexists. econstructor. 2: exact D1. eassumption.
        2: auto.
        2: eapply biforall_impl;[|eassumption]; intros; downclose_Vrel. 2: reflexivity. lia.
        apply biforall_vrel_closed in H2 as H2'.
        split. 2: split.
        (* scopes *)
        1-2: constructor; try apply H1; constructor; try apply H2'; clear H3 H4 H5.
        1: {
          eapply Erel_closed_l.
          apply H. 3: exact Eq2.
          all: eauto. lia. 
        }
        1: {
          specialize (IHIH m _ _ ltac:(lia) H1) as [Cl _].
          inv Cl. inv H5. auto.
        }
        1: {
          eapply Erel_closed_r.
          apply H. 3: exact Eq2.
          all: eauto. lia. 
        }
        1: {
          specialize (IHIH m _ _ ltac:(lia) H1) as [_ [Cl _]].
          inv Cl. inv H5. auto.
        }
        split. 2: split.
        {
          clear H3 H4 H5. intros. inv H4.
          - inv H3. inv H8. apply Vrel_possibilities in H6.
            intuition; destruct_hyps; subst; try congruence.
            inv H5.
            eapply H in H13 as [k1 D1].
            eexists. econstructor. exact D1.
            3: eassumption. 3: lia. lia. lia.
            eapply Frel_downclosed; eassumption.
          - inv H3. inv H8. apply Vrel_possibilities in H6.
          intuition; destruct_hyps; subst; try congruence.
            inv H5.
            eapply IHIH in H13 as [k1 D1].
            eexists. constructor. exact D1.
            3: reflexivity. lia.
            eapply Frel_downclosed; eassumption.
            eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
        }
        {
          intros. inv H7. eapply H1 in H15 as [k1 D1].
          eexists. constructor. reflexivity. exact D1.
          lia.
          eapply Excrel_downclosed; eassumption.
        }
        {
          intros. inv H6.
        }
      * eapply nomatch_pattern_list_Vrel in H11.
        2: eassumption.
        eapply IHIH in H12 as [k1 D1].
        eexists. constructor. assumption. exact D1.
        3: reflexivity. lia.
        eapply Frel_downclosed; eassumption.
        eapply biforall_impl. 2: eassumption.
        intros. downclose_Vrel.
    }
    {
      intros. inv H3. eapply H1 in H9 as [k1 D1].
      eexists. constructor. reflexivity. exact D1.
      lia.
      eapply Excrel_downclosed; eassumption.
    }
    {
      intros. inv H2.
    }
  Unshelve.
    all: lia.
Qed.

Lemma Frel_Case2 :
  forall n l l',
  list_biforall (
      fun '(pl, g, e) '(pl', g', e') => pl = pl' /\
        (forall m vl1 vl2, m <= n -> length vl1 = PatListScope pl ->
        list_biforall (Vrel m) vl1 vl2 ->
        Erel m (g.[list_subst vl1 idsubst]) (g'.[list_subst vl2 idsubst]) /\
        Erel m (e.[list_subst vl1 idsubst]) (e'.[list_subst vl2 idsubst]))
    ) l l' ->
  forall vl vl' e e',
    (forall m, m <= n -> list_biforall (Vrel m) vl vl') ->
    (forall m, m <= n -> Erel m e e')
  ->
    forall m F1 F2, m <= n -> Frel m F1 F2 -> 
      Frel m (FCase2 vl e l :: F1) (FCase2 vl' e' l' :: F2) 
.
Proof.
  intros. subst.
  specialize (H0 _ H2) as Hcl1. apply biforall_vrel_closed in Hcl1.
  specialize (H1 _ H2) as Hcl2. apply Erel_closed in Hcl2.
  split. 2: split.
  1-2: constructor; try apply H3; constructor; try apply Hcl1; try apply Hcl2.
  1: {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)).
    intros.
    rewrite indexed_to_biforall with (d1 := ([], ˝VNil, ˝VNil)) (d2 := ([], ˝VNil, ˝VNil)) in H. destruct H.
    apply H in H4.
    destruct nth, p, nth, p. unfold "∘". simpl.
    rewrite <- (repeat_length VNil (PatListScope l0)).
    split; eapply subst_implies_list_scope, Erel_closed_l. 2,4: apply H4.
    all: auto. all: now rewrite repeat_length.
  }
  1: {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)).
    intros.
    rewrite indexed_to_biforall with (d1 := ([], ˝VNil, ˝VNil)) (d2 := ([], ˝VNil, ˝VNil)) in H. destruct H.
    rewrite <- H5 in H4. apply H in H4.
    destruct nth, p, nth, p. unfold "∘". simpl. destruct H4. subst.
    rewrite <- (repeat_length VNil (PatListScope l1)).
    split; eapply subst_implies_list_scope, Erel_closed_r. 2,4: apply H6.
    all: auto. all: now rewrite repeat_length.
  }
  split. 2: split.
  {
    intros. inv H5.
    * inv H4. inv H9. apply Vrel_possibilities in H7.
      intuition; destruct_hyps; subst; try congruence.
      inv H7.
      eapply H1 in H12 as [k1 D1].
      eexists. econstructor. exact D1. exact H2. lia.
      eapply Frel_downclosed; eassumption.
    * inv H4. inv H9. apply Vrel_possibilities in H7.
      intuition; destruct_hyps; subst; try congruence.
      inv H7.
      eapply Frel_Case1 in H12 as [k1 D1].
      eexists. econstructor. exact D1. 4: reflexivity.
      exact H.
      lia.
      eapply Frel_downclosed; eassumption.
      eapply biforall_impl. 2: apply H0. intros. downclose_Vrel.
      eassumption.
  }
  {
    intros. inv H5. eapply H3 in H11 as [k1 D1].
    eexists. econstructor. reflexivity. exact D1. lia.
    eapply Excrel_downclosed. eassumption.
  }
  {
    intros. inv H4.
  }
Unshelve.
  all: lia.
Qed.

Theorem Frel_Fundamental_closed :
  forall (F : FrameStack) (n : nat),
    FSCLOSED F ->
    Frel n F F.
Proof.
  induction F; intros.
  * cbn. split. 2: split. 1-2: constructor. split. 2: split.
    - intros. exists 0. constructor.
      constructor. now apply biforall_vrel_closed in H0.
    - intros. exists 0. econstructor. destruct e2, p, e1, p.
      constructor; unfold exc_rel in H0; eapply Vrel_closed; apply H0; reflexivity.
    - intros. now exists m. (* this is also a contradiction *)
  * split. 2: split. all: auto. inv H. split. 2: split.
    (* Normal evaluation *)
    - intros. destruct a.
      + eapply Frel_Cons_tail; try eassumption; auto.
        intros. apply Erel_Fundamental_closed. now inv H2.
      + eapply Frel_Cons_head; try eassumption; auto.
        intros. apply Vrel_Fundamental_closed. now inv H2.
      + inv H2. eapply Frel_Params.
        6-7,9-10: eassumption. 4: now apply IHF.
        4: destruct ident; constructor; auto; constructor; auto; try split; apply Vrel_Fundamental_closed; now inv H6.
        1-2: auto.
        reflexivity. reflexivity.
      + inv H2. eapply Frel_App1 in H0. eassumption.
        auto.
        2: apply IHF; auto.
        3: auto.
        reflexivity. reflexivity.
      + destruct_scopes. eapply Frel_CallMod; eauto.
      + destruct_scopes. eapply Frel_CallFun; eauto.
      + eapply Frel_Case1. 3: now apply IHF.
        4: eassumption.
        4: eassumption.
        3: reflexivity.
        2: shelve.
        clear H0 H H3. induction l; constructor.
        2: apply IHl; auto. 2: {
          constructor. destruct_scopes. now inv H0.
        }
        destruct a, p. split; auto.
        intros.
        inv H2. inv H4. inv H5.
        split; eapply Erel_Fundamental; try apply H2; try apply H3.
        all: rewrite <- H0; replace (length vl0) with (length vl0 + 0) by lia; eapply Grel_list; auto.
      + eapply Frel_Case2. 8: eassumption.
        all: auto.
        ** clear H0 H H3 IHF. induction le; constructor.
          2: apply IHle; auto. 2: {
            destruct_scopes. constructor; auto. now inv H5.
          }
          destruct a, p. split; auto.
          intros.
          inv H2. inv H8. inv H4.
          split; eapply Erel_Fundamental; try apply H2; try apply H3.
          all: rewrite <- H0; replace (length vl0) with (length vl0 + 0) by lia; eapply Grel_list; auto.
        ** inv H2. auto.
        ** inv H2. auto.
      + eapply Frel_Let; try eassumption; auto.
        intros. eapply Erel_Fundamental. 
        2: eapply Grel_list; auto.
        rewrite Nat.add_0_r. now inv H2.
      + eapply Frel_Seq; try eassumption; auto.
        intros. apply Erel_Fundamental_closed. now inv H2.
      + eapply Frel_Try; try eassumption; auto.
        ** intros. apply biforall_length in H5 as H5'.
           eapply Grel_list in H5. 2: apply Grel_ids.
           rewrite Nat.add_0_r in H5.
           eapply Erel_Fundamental. 2: exact H5. now inv H2.
        ** intros. apply biforall_length in H5 as H5'.
           eapply Grel_list in H5. 2: apply Grel_ids.
           rewrite Nat.add_0_r in H5.
           eapply Erel_Fundamental. 2: exact H5. now inv H2.
    (* Exceptions: *)
    - intros. destruct a.
      (* TODO: boiler plate: *)
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + inv H0. eapply IHF in H8 as [k1 D1]; auto.
        eexists. constructor. congruence. exact D1.
        eapply Excrel_downclosed; eassumption.
      + eapply Frel_Try in H0. exact H0.
        all: auto.
        ** intros. apply biforall_length in H9 as H9'.
           eapply Grel_list in H9. 2: apply Grel_ids.
           rewrite Nat.add_0_r in H9.
           eapply Erel_Fundamental. 2: exact H9. now inv H2.
        ** intros. apply biforall_length in H9 as H9'.
           eapply Grel_list in H9. 2: apply Grel_ids.
           rewrite Nat.add_0_r in H9.
           eapply Erel_Fundamental. 2: exact H9. now inv H2.
    - intros. inv H.
      + inv H2. inv H8.
        eapply Erel_Params_compat_closed in H5 as [i D].
        eexists. constructor. auto. exact D.
        all: auto.
        inv H6; split; try split; auto.
        1-2: intros; congruence.
      + eexists. econstructor. 3: eassumption. all: eauto.
  Unshelve. 2: exact n.
    all: lia.
Qed.

Global Hint Resolve Frel_Fundamental_closed : core.


Theorem Rrel_Fundamental_closed :
  forall n r, REDCLOSED r -> Rrel n r r.
Proof.
  intros. split. 2: split. 1-2: auto. intros. inv H.
  * eapply H0 in H1; eauto.
  * eapply Erel_Fundamental_closed; eauto.
  * eapply H0 in H1 as [k1 D1]. eexists. exact D1. lia.
    now apply Excrel_Fundamental_closed.
  * eapply H0 in H1 as [k1 D1]. eexists. exact D1. lia.
    auto.
Qed.

Lemma Rrel_closed : forall n r1 r2,
  Rrel n r1 r2 -> REDCLOSED r1 /\ REDCLOSED r2.
Proof.
  intros. split; apply H.
Qed.

Lemma Rrel_open_scope : forall Γ r1 r2,
  Rrel_open Γ r1 r2 -> RED Γ ⊢ r1 /\ RED Γ ⊢ r2.
Proof.
  intros. unfold Rrel_open in H.
  split; eapply subst_implies_scope_red with (Γ' := 0); intros; apply (H 0 ξ ξ); auto.
Qed.

Corollary Rrel_open_scope_l : forall Γ r1 r2,
  Rrel_open Γ r1 r2 -> RED Γ ⊢ r1.
Proof.
  now apply Rrel_open_scope.
Qed.

Global Hint Resolve Rrel_open_scope_l : core.

Corollary Rrel_open_scope_r : forall Γ r1 r2,
  Rrel_open Γ r1 r2 -> RED Γ ⊢ r2.
Proof.
  now apply Rrel_open_scope.
Qed.

Global Hint Resolve Rrel_open_scope_r : core.


Lemma Rrel_exp_compat_closed :
  forall n e1 e2, Erel n e1 e2 -> Rrel n e1 e2.
Proof.
  intros. split. 2: split.
  1-2: constructor; apply H.
  intros. eapply H in H1. eassumption. lia.
  eassumption.
Qed.

#[global]
Hint Resolve Rrel_exp_compat_closed : core.

Lemma Rrel_valseq_compat_closed :
  forall n vl1 vl2, list_biforall (Vrel n) vl1 vl2 -> Rrel n (RValSeq vl1) (RValSeq vl2).
Proof.
  intros. apply biforall_vrel_closed in H as Hcl.
  split. 2: split. 1-2: constructor; apply Hcl.
  intros.
  eapply H0. 3: eassumption. lia. eapply biforall_impl.
  2: eassumption. intros. downclose_Vrel.
Unshelve.
  lia.
Qed.

#[global]
Hint Resolve Rrel_valseq_compat_closed : core.

Lemma Rrel_exc_compat_closed :
  forall n ex1 ex2, Excrel n ex1 ex2 ->
  Rrel n (RExc ex1) (RExc ex2).
Proof.
  intros. subst.
  split. 2: split.
  1: {
    destruct ex1, ex2, p, p0. inv H.
    specialize (H1 n ltac:(lia)) as [H1_1 H1_2].
    apply Vrel_closed in H1_1, H1_2.
    now constructor.
  }
  1: {
    destruct ex1, ex2, p, p0. inv H.
    specialize (H1 n ltac:(lia)) as [H1_1 H1_2].
    apply Vrel_closed in H1_1, H1_2.
    now constructor.
  }
  intros. eapply H0 in H1. eassumption. lia.
  eapply Excrel_downclosed. eassumption.
Unshelve.
  lia.
Qed.

#[global]
Hint Resolve Rrel_exc_compat_closed : core.

Corollary Rrel_exp_compat :
  forall Γ e1 e2, Erel_open Γ e1 e2 -> Rrel_open Γ e1 e2.
Proof.
  intros. intro. intros.
  apply Rrel_exp_compat_closed. auto.
Qed.

#[global]
Hint Resolve Rrel_exp_compat : core.

Lemma Rrel_valseq_compat :
  forall Γ vl1 vl2, list_biforall (Vrel_open Γ) vl1 vl2 ->
  Rrel_open Γ (RValSeq vl1) (RValSeq vl2).
Proof.
  intros. intro. intros.
  eapply Rrel_valseq_compat_closed.
  induction H; simpl; constructor; auto.
Qed.

#[global]
Hint Resolve Rrel_valseq_compat : core.

Lemma Rrel_exc_compat :
  forall Γ ex1 ex2, Excrel_open Γ ex1 ex2 ->
  Rrel_open Γ (RExc ex1) (RExc ex2).
Proof.
  intros. intro. intros.
  apply Rrel_exc_compat_closed.
  unfold Excrel_open in *. apply H. auto.
Qed.

#[global]
Hint Resolve Rrel_exc_compat_closed : core.

Theorem Rrel_Fundamental :
  forall Γ r, RED Γ ⊢ r -> Rrel_open Γ r r.
Proof.
  intros.
  destruct r; intros; inv H; auto.
  * apply Rrel_valseq_compat.
    induction H1; auto.
  * apply Rrel_exc_compat.
    unfold Excrel_open, Excrel, exc_rel. simpl. intros.
    split. auto.
    intros. split.
    - apply Vrel_Fundamental in H1. unfold Vrel_open in H1.
      apply H1. eapply Grel_downclosed; eassumption.
    - apply Vrel_Fundamental in H2. unfold Vrel_open in H2.
      apply H2. eapply Grel_downclosed; eassumption.
  * unfold Rrel_open. intros. simpl. apply Rrel_Fundamental_closed.
    auto.
Unshelve.
  all: lia.
Qed.

Corollary Rrel_exp_compat_closed_reverse :
  forall n (e1 e2 : Exp), Rrel n e1 e2 -> Erel n e1 e2.
Proof.
  intros. unfold Erel, exp_rel, Rrel in *.
  destruct H as [? [? ?]]. destruct_scopes.
  split. 2: split. all: auto.
Qed.

Corollary Rrel_exp_compat_reverse :
  forall Γ (e1 e2 : Exp), Rrel_open Γ e1 e2 -> Erel_open Γ e1 e2.
Proof.
  intros. unfold Erel_open, Rrel_open in *.
  intros. apply H in H0. now apply Rrel_exp_compat_closed_reverse.
Qed.


