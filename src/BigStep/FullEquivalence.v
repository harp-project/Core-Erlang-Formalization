(**
  This file contains ad-hoc definitions of strict equivalence for Core Erlang.
*)

From CoreErlang.BigStep Require Export SemanticsEquivalence.

From CoreErlang.BigStep Require Import Tactics.
Import ListNotations.




Definition fully_equivalent_expr (P : list ErlModule -> Prop ) e1 e2 :=
forall env modules own_module eff res eff' id1 id2, P modules ->
  (exists clock, fbs_expr clock env modules own_module id1 e1 eff = Result id2 res eff')
<->
  (exists clock, fbs_expr clock env modules own_module id1 e2 eff = Result id2 res eff').

Definition fully_equivalent_exprlist (P : list ErlModule -> Prop ) l1 l2 :=
forall env modules own_module eff res eff' id1 id2, P modules ->
  (exists clock, fbs_values (fbs_expr clock) env modules own_module id1 l1 eff = Result id2 res eff')
<->
  (exists clock, fbs_values (fbs_expr clock) env modules own_module id1 l2 eff = Result id2 res eff').

Definition fully_equivalent_case (P : list ErlModule -> Prop ) l1 l2 :=
forall env modules own_module eff res eff' id1 id2 vals, P modules ->
  (exists clock, fbs_case l1 env modules own_module id1 eff vals (fbs_expr clock) = Result id2 res eff')
<->
  (exists clock, fbs_case l2 env modules own_module id1 eff vals (fbs_expr clock) = Result id2 res eff').

Section equivalence_relation.

Theorem fully_equivalent_expr_refl (P : list ErlModule -> Prop ) {e} :
  fully_equivalent_expr P e e.
Proof.
  intros. unfold fully_equivalent_expr. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_expr_sym (P : list ErlModule -> Prop ) {e1 e2} :
  fully_equivalent_expr P e1 e2 -> fully_equivalent_expr P  e2 e1.
Proof.
  unfold fully_equivalent_expr; intros.
  split; apply H.
  auto. auto.
Qed.

Theorem fully_equivalent_expr_trans (P : list ErlModule -> Prop ) {e1 e2 e3} :
  fully_equivalent_expr P  e1 e2 -> fully_equivalent_expr P e2 e3
->
  fully_equivalent_expr P e1 e3.
Proof.
  unfold fully_equivalent_expr; intros.
  split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

Theorem fully_equivalent_exprlist_refl (P : list ErlModule -> Prop ) {l} :
  fully_equivalent_exprlist P  l l.
Proof.
  intros. unfold fully_equivalent_exprlist. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_exprlist_sym (P : list ErlModule -> Prop ) {l1 l2} :
  fully_equivalent_exprlist P  l1 l2 -> fully_equivalent_exprlist P l2 l1.
Proof.
  unfold fully_equivalent_exprlist; intros.
  split; apply H. auto. auto.
Qed.

Theorem fully_equivalent_exprlist_trans (P : list ErlModule -> Prop ) {l1 l2 l3} :
  fully_equivalent_exprlist P l1 l2 -> fully_equivalent_exprlist P l2 l3
->
  fully_equivalent_exprlist P l1 l3.
Proof.
  unfold fully_equivalent_exprlist; intros.
  split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.

Theorem fully_equivalent_case_refl (P : list ErlModule -> Prop ) {l} :
  fully_equivalent_case P l l.
Proof.
  intros. unfold fully_equivalent_case. split; intros.
  * auto.
  * auto.
Qed.

Theorem fully_equivalent_case_sym (P : list ErlModule -> Prop ) {l1 l2} :
  fully_equivalent_case P l1 l2 -> fully_equivalent_case P l2 l1.
Proof.
  unfold fully_equivalent_case; intros.
  split; apply H. all : auto.
Qed.

Theorem fully_equivalent_case_trans (P : list ErlModule -> Prop ) {l1 l2 l3} :
  fully_equivalent_case P l1 l2 -> fully_equivalent_case P l2 l3
->
  fully_equivalent_case P l1 l3.
Proof.
  unfold fully_equivalent_case; intros.
  split; intros.
  * apply H in H2. apply H0 in H2. all: auto.
  * apply H0 in H2. apply H in H2. all: auto.
Qed.



(** If all elements are equivalent in a list, then the lists are equivalent too
  * ATTENTION: does not work in the opposite direction 
  * *)
Theorem fully_equivalent_elements_exprlist (P1 : list ErlModule -> Prop ) (l l' : list Expression) :
  length l = length l' ->
  (forall i : nat, i < length l -> fully_equivalent_expr P1 (nth i l ErrorExp) (nth i l' ErrorExp))
->
  fully_equivalent_exprlist P1 l l'
.
Proof.
  generalize dependent l'. induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. split; intros; exact H1.
  * pose (EE := element_exist _ _ H). destruct EE, H1. subst. inversion H.
    pose (F := H0 0 (Nat.lt_0_succ _)). simpl in F.
    epose (IH := IHl _ H2 _).
    split; intros; destruct H3; simpl in H3.
    - destruct (fbs_expr x1 env modules own_module id1 a eff) eqn:D1. destruct res0. destruct v. congruence.
      destruct v0. 2: congruence. 3-4: congruence.
      + edestruct F. eauto. pose (P := H4 (ex_intro _ x1 D1)). destruct P.
        destruct (fbs_values (fbs_expr x1) env modules own_module id l eff0) eqn:D2.
        destruct res0. 3-4: congruence.
        ** edestruct IH. eauto. pose (P := H7 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H9.
           erewrite (bigger_clock_expr _ _ H6), H9. assumption.
           lia. intros. apply clock_increase_expr. assumption.
        ** edestruct IH. eauto. pose (P := H7 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H9.
           erewrite (bigger_clock_expr _ _ H6), H9. assumption.
           lia. intros. apply clock_increase_expr. assumption.
      + edestruct F. eauto. pose (P := H4 (ex_intro _ x1 D1)). destruct P.
        exists x2. simpl. rewrite H6. assumption.
    - destruct (fbs_expr x1 env modules own_module id1 x eff) eqn:D1. destruct res0. destruct v. congruence.
      destruct v0. 2: congruence. 3-4: congruence.
      + edestruct F. eauto. pose (P := H5 (ex_intro _ x1 D1)). destruct P.
        destruct (fbs_values (fbs_expr x1) env modules own_module id x0 eff0) eqn:D2.
        destruct res0. 3-4: congruence.
        ** edestruct IH. eauto. pose (P := H8 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H9.
           erewrite (bigger_clock_expr _ _ H6), H9. assumption.
           lia. intros. apply clock_increase_expr. assumption.
        ** edestruct IH. eauto. pose (P := H8 (ex_intro _ x1 D2)). destruct P.
           exists (x2 + x3). simpl. eapply bigger_clock_list in H9.
           erewrite (bigger_clock_expr _ _ H6), H9. assumption.
           lia. intros. apply clock_increase_expr. assumption.
      + edestruct F. eauto. pose (P := H5 (ex_intro _ x1 D1)). destruct P.
        exists x2. simpl. rewrite H6. assumption.
Unshelve.
all: try lia.
intros. apply (H0 (S i)). simpl. lia.
Qed.

Theorem fully_equivalent_elements_case (PM : list ErlModule -> Prop ) (l l' : list (list Pattern * Expression * Expression )) :
  length l = length l' ->
  ((forall i, i < length l -> fully_equivalent_expr PM
                                                   (nth i (map snd l) ErrorExp)
                                                   (nth i (map snd l') ErrorExp) /\
                             fully_equivalent_expr PM
                                                   (nth i (map snd (map fst l)) ErrorExp)
                                                   (nth i (map snd (map fst l')) ErrorExp)
                   /\ nth i (map fst (map fst l)) [] = nth i (map fst (map fst l')) []))
->
  fully_equivalent_case PM l l'
.
Proof.
  generalize dependent l'. induction l; intros.
  * apply eq_sym, length_zero_iff_nil in H. subst. split; intros; assumption.
  * pose proof (EE := element_exist _ _ H). destruct EE, H1. subst. inversion H.
    pose proof (F := H0 0 (Nat.lt_0_succ _)). simpl in F.
    epose proof (IH := IHl _ H2 _). Unshelve. 2: { intros. apply (H0 (S i)). simpl. lia. }
    split; intros; destruct H3; simpl in H3.
    - destruct a, p. destruct (match_valuelist_to_patternlist vals l0) eqn:D1.
      + destruct (fbs_expr x1 (add_bindings (match_valuelist_bind_patternlist vals l0) env) modules own_module id1 e0
         eff) eqn:D2.
         destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
         ** destruct (((id =? id1) && list_eqb effect_eqb eff eff0)%bool) eqn:D3. 2: congruence.
            apply andb_prop in D3. destruct D3. apply Nat.eqb_eq in H4.
            apply effect_list_eqb_eq in H5. subst.
            destruct v; try congruence. destruct l1; try congruence.
            destruct (s =? "true")%string eqn:D4.
            -- apply eqb_eq in D4. subst.
               destruct F, H5. destruct x, p. simpl in H4, H5, H6.
               epose proof (P := H5 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H7 (ex_intro _ _ D2)).
               epose proof (P := H4 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H9 (ex_intro _ _ H3)).
               destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H11). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_expr _ _ H12). Unshelve. all: lia.
            -- destruct (s =? "false")%string eqn:D5. 2: congruence.
               apply eqb_eq in D5. subst.
               destruct F, H5. destruct x, p. simpl in H4, H5, H6.
               epose proof (P := H5 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H7 (ex_intro _ _ D2)).
               epose proof (P := IH _ _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H9 (ex_intro _ _ H3)).
               clear IH. destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H11). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_case _ H12 _). Unshelve. all: lia.
         ** break_match_hyp. 2: congruence. inversion H3. subst. clear H3.
            destruct x as [[p g] b]. simpl fst in *. simpl snd in *.
            destruct F as [? [? ?]]. subst.
            epose proof (H4 _ _ _ _ _ _ _ _ H1) as [? _].
            apply ex_intro with (x := x1) in D2.
            eapply H5 in D2. destruct D2. exists (x). simpl.
            now rewrite D1, H6, Heqb.
       + epose (P := IH _ _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H4 (ex_intro _ _ H3)).
         clear IH. destruct P2. exists x2. simpl. destruct F, H8. destruct x, p.
         simpl in H, H7, H8, H9. subst. rewrite D1. assumption.
    - destruct x, p. destruct (match_valuelist_to_patternlist vals l0) eqn:D1.
      + destruct (fbs_expr x1 (add_bindings (match_valuelist_bind_patternlist vals l0) env) modules own_module id1 e0
         eff) eqn:D2.
         destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
         ** destruct (((id =? id1) && list_eqb effect_eqb eff eff0)%bool) eqn:D3. 2: congruence.
            apply andb_prop in D3. destruct D3. apply Nat.eqb_eq in H4.
            apply effect_list_eqb_eq in H5. subst.
            destruct v; try congruence. destruct l1; try congruence.
            destruct (s =? "true")%string eqn:D4.
            -- apply eqb_eq in D4. subst.
               destruct F, H5. destruct a, p. simpl in H4, H5, H6.
               epose (P := H5 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H8 (ex_intro _ _ D2)).
               epose (P := H4 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H10 (ex_intro _ _ H3)).
               destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H11). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_expr _ _ H12). Unshelve. all: lia.
            -- destruct (s =? "false")%string eqn:D5. 2: congruence.
               apply eqb_eq in D5. subst.
               destruct F, H5. destruct a, p. simpl in H4, H5, H6.
               epose (P := H5 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H8 (ex_intro _ _ D2)).
               epose (P := IH _ _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H10 (ex_intro _ _ H3)).
               clear IH. destruct P1, P2. exists (x + x2). simpl. subst. rewrite D1.
               erewrite (bigger_clock_expr _ _ H11). rewrite Nat.eqb_refl, effect_list_eqb_refl.
               simpl. eapply (bigger_clock_case _ H12 _). Unshelve. all: lia.
         ** break_match_hyp. 2: congruence. inversion H3. subst. clear H3.
            destruct a as [[p g] b]. simpl fst in *. simpl snd in *.
            destruct F as [? [? ?]]. subst.
            epose proof (H4 _ _ _ _ _ _ _ _ H1) as [_ ?].
            apply ex_intro with (x := x1) in D2.
            eapply H5 in D2. destruct D2. exists (x). simpl.
            now rewrite D1, H6, Heqb.
       + epose (P := IH _ _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H5 (ex_intro _ _ H3)).
         clear IH. destruct P2. exists x. simpl. destruct F, H8. destruct a, p.
         simpl in H7, H8, H9. subst. rewrite D1. assumption.
Qed.

End equivalence_relation.

Section congruence.

Theorem ECons_full_cong (P : list ErlModule -> Prop ) hd tl : forall hd' tl',
  fully_equivalent_expr P hd hd' -> fully_equivalent_expr P tl tl'
->
  fully_equivalent_expr P (ECons hd tl) (ECons hd' tl').
Proof.
  assert (A : forall env modules own_module id hd tl hd' tl' eff id' res eff', P modules ->
    fully_equivalent_expr P hd hd' -> fully_equivalent_expr P tl tl'
   ->
    (exists clock, fbs_expr clock env modules own_module id (ECons hd tl) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env modules own_module id (ECons hd' tl') eff = Result id' res eff')
  ).
  {
    intros env modules own_module id hd0 tl0 hd' tl' eff id' res eff' F H H0 H1.
  * destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id tl0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    - destruct (fbs_expr x env modules own_module id0 hd0 eff0) eqn:D2.
      destruct res0. destruct v0. congruence. destruct v1. 2: congruence. 3-4: congruence.
      + inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _ _ _). destruct D1'. eauto.  epose (H2 (ex_intro _ x D1)).
        epose (D2' := H _ _ _ _ _ _ _ _). destruct D2'. eauto. epose (H4 (ex_intro _ x D2)). destruct e, e0.
        exists (S (x0 + x1)). simpl. erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). reflexivity.
      + inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _ _ _). destruct D1'. eauto. epose (H2 (ex_intro _ x D1)).
        epose (D2' := H _ _ _ _ _ _ _ _). destruct D2'. eauto. epose (H4 (ex_intro _ x D2)). destruct e0, e1.
        exists (S (x0 + x1)). simpl. erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). reflexivity.
    - inversion H1. subst. epose (D1' := H0 _ _ _ _ _ _ _ _). destruct D1'. eauto. epose (H2 (ex_intro _ x D1)).
      destruct e0. exists (S x0). simpl. rewrite H4. auto.
  }
  split; intros.
  * eapply A. auto. exact H. exact H0. exact H2.
  * eapply A. auto. exact (fully_equivalent_expr_sym P H). exact (fully_equivalent_expr_sym P H0).
    exact H2.
Unshelve.
all: lia.
Qed.

Theorem ETuple_full_cong (P : list ErlModule -> Prop ) (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist P l l'
->
  fully_equivalent_expr P (ETuple l) (ETuple l').
Proof.
  assert (A : forall (l l' : list Expression) env modules own_module id eff id' res eff', P modules ->
    fully_equivalent_exprlist P l l'
    ->
    (exists clock, fbs_expr clock env modules own_module id (ETuple l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env modules own_module id (ETuple l') eff = Result id' res eff')).
  {
    intros l0 l' env modules own_module id eff id' res eff' F H H0.
    unfold fully_equivalent_exprlist, fully_equivalent_expr in *. 
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env modules own_module id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _ _ _). destruct E. eauto.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _ _ _). destruct E. eauto.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. auto. exact H. auto.
  * eapply A. auto. exact (fully_equivalent_exprlist_sym P H). exact H1.
Qed.

Theorem ECall_full_cong (PM : list ErlModule -> Prop ) (m : Expression) (f : Expression) (l : list Expression) : forall (m' : Expression) (f' : Expression) (l' : list Expression),
  fully_equivalent_expr PM m m'
->
  fully_equivalent_expr PM f f'
->
  fully_equivalent_exprlist PM l l'
->
  fully_equivalent_expr PM (ECall m f l) (ECall m' f' l').
Proof.
  assert (A : forall m m' f f' (l l' : list Expression) env modules own_module id eff id' res eff', PM modules ->
  fully_equivalent_expr PM m m'
  ->
    fully_equivalent_expr PM f f'
  ->
  fully_equivalent_exprlist PM l l'
  ->
  (exists clock, fbs_expr clock env modules own_module id (ECall m f l) eff = Result id' res eff')
  ->
  (exists clock, fbs_expr clock env modules own_module id (ECall m' f' l') eff = Result id' res eff')). 
  { 
    intros m0 m' f0 f' l0 l' env modules own_module id eff id' res eff' F H H0 H1 H2.
    
   
    destruct H2, x. inversion H2. simpl in H2.
    destruct (fbs_expr x env modules own_module id m0 eff) eqn:D1; try congruence.
    - destruct res0. destruct v; try congruence.
      + destruct v0; try congruence.
        destruct (fbs_expr x env modules own_module id0 f0 eff0) eqn:D2; try congruence.
        destruct res0. destruct v0; try congruence. destruct v1; try congruence.
        ++  destruct (fbs_values (fbs_expr x) env modules own_module id1 l0 eff1) eqn:D; try congruence.
            destruct res0. destruct v ; try congruence.
            * epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H3 (ex_intro _ x D)). destruct P. 
              epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H6 (ex_intro _ x D1)). destruct P.
              epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
               pose (P := H9 (ex_intro _ x D2)). destruct P. 
              apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
              exists (S ( x1 + x0 + x2  )). simpl. 
              rewrite H8. rewrite H11. rewrite H5. 
              exact H2. 1-3: lia. intros; apply clock_increase_expr; auto.
            * destruct l1. destruct v0.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                pose (P := H3 (ex_intro _ x D)). destruct P. 
                epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                pose (P := H6 (ex_intro _ x D1)). destruct P.
                epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                pose (P := H9 (ex_intro _ x D2)). destruct P. 
                apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
                apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
                apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
                exists (S ( x1 + x0 + x2  )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. auto.
                   lia. lia. lia. intros; apply clock_increase_expr; auto.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H3 (ex_intro _ x D)). destruct P. 
                  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H6 (ex_intro _ x D1)). destruct P.
                  epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H9 (ex_intro _ x D2)). destruct P. 
                  apply bigger_clock_list with (clock' := x + x1 + x0 + x2) in H5.
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2) in H8.
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2) in H11.
                  exists (S ( x + x1 + x0 + x2 )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. 
                  destruct l1; try congruence. destruct get_modfunc; try congruence.  
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2 ) in H2.
                   exact H2. 1-4: lia. intros; apply clock_increase_expr; auto.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H3 (ex_intro _ x D)). destruct P. 
                  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H6 (ex_intro _ x D1)). destruct P.
                  epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H9 (ex_intro _ x D2)). destruct P. 
                  apply bigger_clock_list with (clock' := x + x1 + x0 + x2) in H5.
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2) in H8.
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2) in H11.
                  exists (S ( x + x1 + x0 + x2 )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. 
                  exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H3 (ex_intro _ x D)). destruct P. 
                  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H6 (ex_intro _ x D1)). destruct P.
                  epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H9 (ex_intro _ x D2)). destruct P. 
                  apply bigger_clock_list with (clock' := x + x1 + x0 + x2) in H5.
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2) in H8.
                  apply bigger_clock_expr with (clock' := x + x1 + x0 + x2) in H11.
                  exists (S ( x + x1 + x0 + x2 )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. 
                  exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H3 (ex_intro _ x D)). destruct P. 
                  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H6 (ex_intro _ x D1)). destruct P.
                  epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H9 (ex_intro _ x D2)). destruct P. 
                  apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
                  apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
                  apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
                  exists (S (x1 + x0 + x2 )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. 
                  exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H3 (ex_intro _ x D)). destruct P. 
                  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H6 (ex_intro _ x D1)). destruct P.
                  epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H9 (ex_intro _ x D2)). destruct P. 
                  apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
                  apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
                  apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
                  exists (S (x1 + x0 + x2 )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. 
                  exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.
              ** epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H3 (ex_intro _ x D)). destruct P. 
                  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H6 (ex_intro _ x D1)). destruct P.
                  epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
                  pose (P := H9 (ex_intro _ x D2)). destruct P. 
                  apply bigger_clock_list with (clock' := x1 + x2 + x3) in H5.
                  apply bigger_clock_expr with (clock' := x1 + x2 + x3) in H8.
                  apply bigger_clock_expr with (clock' := x1 + x2 + x3) in H11.
                  exists (S (x1 + x2 + x3 )). simpl. 
                  rewrite H8. rewrite H11. rewrite H5. 
                  exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.


            * epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H3 (ex_intro _ x D)). destruct P. 
              epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H6 (ex_intro _ x D1)). destruct P.
              epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H9 (ex_intro _ x D2)). destruct P. 
              apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
              exists (S (x1 + x0 + x2 )). simpl. 
              rewrite H8. rewrite H11. rewrite H5. 
              exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.

            * epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H3 (ex_intro _ x D)). destruct P. 
              epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H6 (ex_intro _ x D1)). destruct P.
              epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H9 (ex_intro _ x D2)). destruct P. 
              apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
              exists (S (x1 + x0 + x2 )). simpl. 
              rewrite H8. rewrite H11. rewrite H5. 
              exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.

            * epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H3 (ex_intro _ x D)). destruct P. 
              epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H6 (ex_intro _ x D1)). destruct P.
              epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H9 (ex_intro _ x D2)). destruct P. 
              apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
              exists (S (x1 + x0 + x2 )). simpl. 
              rewrite H8. rewrite H11. rewrite H5. 
              exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.

            * epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H3 (ex_intro _ x D)). destruct P. 
              epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H6 (ex_intro _ x D1)). destruct P.
              epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H9 (ex_intro _ x D2)). destruct P. 
              apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
              exists (S (x1 + x0 + x2 )). simpl. 
              rewrite H8. rewrite H11. rewrite H5. 
              exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.

            * epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H3 (ex_intro _ x D)). destruct P. 
              epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H6 (ex_intro _ x D1)). destruct P.
              epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
              pose (P := H9 (ex_intro _ x D2)). destruct P. 
              apply bigger_clock_list with (clock' := x1 + x0 + x2) in H5.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H8.
              apply bigger_clock_expr with (clock' := x1 + x0 + x2) in H11.
              exists (S (x1 + x0 + x2 )). simpl. 
              rewrite H8. rewrite H11. rewrite H5. 
              exact H2. lia. lia. lia. intros; apply clock_increase_expr; auto.

        ++  epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
            pose (P := H3 (ex_intro _ x D1)). destruct P. 
            epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto.
            pose (P := H6 (ex_intro _ x D2)). destruct P. 
            apply bigger_clock_expr with (clock' := x0 + x1) in H5.
            apply bigger_clock_expr with (clock' := x0 + x1) in H8.
            
         exists (S ( x0 + x1   )). simpl. rewrite H5. rewrite H8. auto. all:lia.
      + epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto.
        pose (P := H3 (ex_intro _ x D1)). destruct P.
        exists (S ( x0   )). simpl. rewrite H5. auto.

      
                
          
  }
  split; intros.
  * eapply A. auto. auto. exact H. exact H0. exact H1. auto. 
  * eapply A. auto. 
        exact (fully_equivalent_expr_sym PM H).
        exact (fully_equivalent_expr_sym PM H0).
        exact (fully_equivalent_exprlist_sym PM H1).
        exact H3.
  
Qed.

Theorem EPrimOp_full_cong (PM : list ErlModule -> Prop ) (f : string) (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist PM l l'
->
  fully_equivalent_expr PM (EPrimOp f l) (EPrimOp f l').
Proof.
  assert (A : forall f (l l' : list Expression) env modules own_module id eff id' res eff', PM modules ->
  fully_equivalent_exprlist PM l l'
  ->
  (exists clock, fbs_expr clock env modules own_module id  (EPrimOp f l) eff = Result id' res eff')
  ->
  (exists clock, fbs_expr clock env modules own_module id (EPrimOp f l') eff = Result id' res eff')). 
  {
  intros f0 l0 l' env modules own_module id eff id' res eff' F H H0 .
   destruct H0, x. inversion H0. simpl in H0.
  destruct (fbs_values (fbs_expr x) env modules own_module id l0 eff) eqn:D.
  destruct res0. 3-4: congruence.
  all: epose (P := H _ _ _ _ _ _ _ _); destruct P; eauto; pose (P := H1 (ex_intro _ x D));
    destruct P; exists (S x0); simpl; rewrite H3; assumption.
  }
  split; intros.
  * eapply A. auto. exact H. auto.
  * eapply A. auto. exact (fully_equivalent_exprlist_sym PM H). exact H1.
Qed.

Theorem EApp_full_cong (PM : list ErlModule -> Prop ) (exp : Expression) (l : list Expression) : forall (exp' : Expression) (l' : list Expression),
  fully_equivalent_expr PM exp exp' ->
  fully_equivalent_exprlist PM l l'
->
  fully_equivalent_expr PM (EApp exp l) (EApp exp' l').
Proof.
  assert (A : forall exp exp' (l l' : list Expression) env modules own_module id eff id' res eff', PM modules ->
    fully_equivalent_expr PM exp exp' ->
    fully_equivalent_exprlist PM l l'
    ->
    (exists clock, fbs_expr clock env modules own_module id (EApp exp l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env modules own_module id (EApp exp' l') eff = Result id' res eff')).
  {
    intros exp0 exp' l0 l' env modules own_module id eff id' res eff' F H H0 H1 . 
    destruct H1, x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id exp0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2: congruence. 3-4: congruence.
    * destruct (fbs_values (fbs_expr x) env modules own_module id0 l0 eff0) eqn:D2.
      destruct res0. 3-4: congruence.
      - epose (P := H _ _ _ _ _ _ _ _); destruct P; eauto; pose (P := H2 (ex_intro _ x D1)); destruct P;
        epose (P := H0 _ _ _ _ _ _ _ _); destruct P; eauto; pose (P := H5 (ex_intro _ x D2)); destruct P.
        destruct v.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7.
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + destruct (length vl =? length v0) eqn:D3.
          ** exists (S (x0 + x1 + x)). simpl; eapply bigger_clock_list in H7.
             erewrite (bigger_clock_expr _ _ H4), H7, D3, (bigger_clock_expr _ _ H1). auto.
             lia.
             intros; apply clock_increase_expr; auto.
          ** exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7.
             erewrite (bigger_clock_expr _ _ H4), H7, D3. assumption.
             lia.
             intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
        + exists (S (x0 + x1)); simpl; eapply bigger_clock_list in H7;
          try (erewrite (bigger_clock_expr _ _ H4), H7; assumption).
          lia.
          intros; apply clock_increase_expr; auto.
      - epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H2 (ex_intro _ x D1)). destruct P.
        epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H5 (ex_intro _ x D2)). destruct P.
        exists (S (x0 + x1)). simpl. eapply bigger_clock_list in H7.
        erewrite (bigger_clock_expr _ _ H4), H7. assumption.
        lia. intros. apply clock_increase_expr. auto.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H2 (ex_intro _ x D1)).
      destruct P. exists (S x0). simpl. rewrite H4. assumption.
  }
  split; intros.
  * eapply A. auto. exact H. exact H0. auto.
  * eapply A. auto. exact (fully_equivalent_expr_sym PM H). exact (fully_equivalent_exprlist_sym PM H0). exact H2.
Unshelve.
all: lia.
Qed.

Theorem ECase_full_cong (PM : list ErlModule -> Prop ) (exp : Expression) (l : list (list Pattern * Expression * Expression)) : forall (exp' : Expression) (l' : list (list Pattern * Expression * Expression)),
  fully_equivalent_expr PM exp exp' ->
  fully_equivalent_case PM l l'
->
  fully_equivalent_expr PM (ECase exp l) (ECase exp' l').
Proof.
  assert (A : forall exp exp' l l' env modules own_module id eff id' res eff', PM modules ->
    fully_equivalent_expr PM exp exp' ->
    fully_equivalent_case PM l l' ->
    (exists clock, fbs_expr clock env modules own_module id (ECase exp l) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env modules own_module id (ECase exp' l') eff = Result id' res eff')
  ).
  {
    intros exp0 exp' l0 l' env modules own_module id eff id' res eff' F H H0 H1.
    destruct H1, x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id exp0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H2 (ex_intro _ x D)). destruct P.
      epose (P := H0 _ _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H5 (ex_intro _ x H1)). destruct P.
      exists (S (x0 + x1)). simpl. eapply bigger_clock_case in H7.
      erewrite (bigger_clock_expr _ _ H4). exact H7. lia.
      Unshelve. lia.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H2 (ex_intro _ x D)). destruct P.
      exists (S x0). simpl. rewrite H4. auto.
  }
  split; intros.
  * eapply A. auto. exact H. exact H0. auto.
  * eapply A. auto. exact (fully_equivalent_expr_sym PM H). exact (fully_equivalent_case_sym PM H0). auto.
Qed.

Theorem ELet_full_cong (PM : list ErlModule -> Prop ) (e1 e2 : Expression) vl : forall (e1' e2' : Expression),
  fully_equivalent_expr PM e1 e1' ->
  fully_equivalent_expr PM e2 e2'
->
  fully_equivalent_expr PM (ELet vl e1 e2) (ELet vl e1' e2').
Proof.
  assert (A : forall env modules own_module id id' res eff eff' e1 e1' e2 e2', PM modules ->
    fully_equivalent_expr PM e1 e1' ->
    fully_equivalent_expr PM e2 e2' ->
    (exists clock, fbs_expr clock env modules own_module id (ELet vl e1 e2) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env modules own_module id (ELet vl e1' e2') eff = Result id' res eff')
  ).
  {
    intros env modules own_module id id' res eff eff' e0 e1' e3 e2' F H H0 H1.
    destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id e0 eff) eqn:D1.
    destruct res0.
    destruct (Datatypes.length v =? Datatypes.length vl) eqn:D2. 2, 4-5: congruence.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H2 (ex_intro _ _ D1)).
      epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H4 (ex_intro _ _ H1)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7), D2. auto.
      Unshelve. all: lia.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H2 (ex_intro _ _ D1)). destruct P1.
      exists (S x0). simpl. erewrite (bigger_clock_expr _ _ H4). auto. Unshelve. lia.
  }
  split; intros.
  * eapply A. auto. exact H. exact H0. auto.
  * eapply A. auto. exact (fully_equivalent_expr_sym PM H). exact (fully_equivalent_expr_sym PM H0). auto.
Qed.

Theorem ESeq_full_cong (PM : list ErlModule -> Prop ) (e1 e2 : Expression) (l : list Expression) : forall (e1' e2' : Expression),
  fully_equivalent_expr PM e1 e1' ->
  fully_equivalent_expr PM e2 e2'
->
  fully_equivalent_expr PM (ESeq e1 e2) (ESeq e1' e2').
Proof.
  assert (A : forall env modules own_module id id' res eff eff' e1 e1' e2 e2', PM modules ->
    fully_equivalent_expr PM e1 e1' ->
    fully_equivalent_expr PM e2 e2' ->
    (exists clock, fbs_expr clock env modules own_module id (ESeq e1 e2) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env modules own_module id (ESeq e1' e2') eff = Result id' res eff')
  ).
  {
    intros env modules own_module id id' res eff eff' e0 e1' e3 e2' F H H0 H1.
    destruct H1. destruct x. inversion H1. simpl in H1.
    destruct (fbs_expr x env modules own_module id e0 eff) eqn:D1.
    destruct res0. destruct v. congruence. destruct v0. 2, 4-5: congruence.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H2 (ex_intro _ _ D1)).
      epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H4 (ex_intro _ _ H1)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H6), (bigger_clock_expr _ _ H7). auto.
      Unshelve. all: lia.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H2 (ex_intro _ _ D1)). destruct P1.
      exists (S x0). simpl. erewrite (bigger_clock_expr _ _ H4). auto. Unshelve. lia.
  }
  split; intros.
  * eapply A. auto. exact H. exact H0. auto.
  * eapply A. auto. exact (fully_equivalent_expr_sym PM H). exact (fully_equivalent_expr_sym PM H0). auto.
Qed.

Theorem ELetRec_full_cong (PM : list ErlModule -> Prop ) (exp : Expression) l : forall (exp' : Expression),
  fully_equivalent_expr PM exp exp'
->
  fully_equivalent_expr PM (ELetRec l exp) (ELetRec l exp').
Proof.
  intros.
  split ; intros.
  * destruct H1, x. inversion H1. simpl in H1.
    epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H2 (ex_intro _ _ H1)). destruct P.
    exists (S x0). simpl. auto.
  * destruct H1, x. inversion H1. simpl in H1.
    epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P := H3 (ex_intro _ _ H1)). destruct P.
    exists (S x0). simpl. auto.
Qed.

Theorem EMap_full_cong (PM : list ErlModule -> Prop ) (l : list (Expression * Expression)) : 
  forall (l' : list (Expression * Expression)),
  fully_equivalent_exprlist PM (make_map_exps l) (make_map_exps l')
->
  fully_equivalent_expr PM (EMap l) (EMap l').
Proof.
  assert (A :
    forall (l l' : list (Expression * Expression)) env modules own_module id eff eff' id' res, PM modules ->
    fully_equivalent_exprlist PM (make_map_exps l) (make_map_exps l') ->
    (exists clock, fbs_expr clock env modules own_module id (EMap l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env modules own_module id (EMap l') eff = Result id' res eff')
  ).
  {
    intros l0 l' env modules own_module id eff eff' id' res F H H0.
    unfold fully_equivalent_exprlist, fully_equivalent_expr in *.
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env modules own_module id (make_map_exps l0) eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _ _ _). destruct E. eauto.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H4. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _ _ _). destruct E. eauto.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. auto. exact H. auto.
  * eapply A. auto. exact (fully_equivalent_exprlist_sym PM H). auto.
Qed.

Theorem ETry_full_cong (PM : list ErlModule -> Prop ) (e1 e2 e3 : Expression) vl1 vl2 : forall (e1' e2' e3' : Expression),
  fully_equivalent_expr PM e1 e1' ->
  fully_equivalent_expr PM e2 e2' ->
  fully_equivalent_expr PM e3 e3'
->
  fully_equivalent_expr PM (ETry e1 vl1 e2 vl2 e3) (ETry e1' vl1 e2' vl2 e3').
Proof.
  assert (A : forall env modules own_module id id' res eff eff' e1 e1' e2 e2' e3 e3', PM modules ->
    fully_equivalent_expr PM e1 e1' ->
    fully_equivalent_expr PM e2 e2' ->
    fully_equivalent_expr PM e3 e3' ->
    (exists clock, fbs_expr clock env modules own_module id (ETry e1 vl1 e2 vl2 e3) eff = Result id' res eff')
   ->
    (exists clock, fbs_expr clock env modules own_module id (ETry e1' vl1 e2' vl2 e3') eff = Result id' res eff')
  ).
  {
    intros env modules own_module id id' res  eff eff' e0 e1' e4 e2' e5 e3' F H H0 H1 H2.
    destruct H2. destruct x. inversion H2. simpl in H2.
    destruct (fbs_expr x env modules own_module id e0 eff) eqn:D1.
    destruct res0. destruct (Datatypes.length v =? Datatypes.length vl1) eqn:D2.
    2, 4-5: congruence.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H3 (ex_intro _ _ D1)).
      epose (P := H0 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H5 (ex_intro _ _ H2)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H7), (bigger_clock_expr _ _ H8), D2. auto.
      Unshelve. all: lia.
    * epose (P := H _ _ _ _ _ _ _ _). destruct P. eauto. pose (P1 := H3 (ex_intro _ _ D1)).
      epose (P := H1 _ _ _ _ _ _ _ _). destruct P. eauto. pose (P2 := H5 (ex_intro _ _ H2)).
      destruct P1, P2. exists (S (x0 + x1)). simpl.
      erewrite (bigger_clock_expr _ _ H7), (bigger_clock_expr _ _ H8). auto.
      Unshelve. all: lia.
  }
  split; intros.
  * eapply A. auto. exact H. exact H0. exact H1. auto.
  * eapply A. auto. exact (fully_equivalent_expr_sym PM H). exact (fully_equivalent_expr_sym PM H0).
    exact (fully_equivalent_expr_sym PM H1). auto.
Qed.

Theorem EValues_full_cong (PM : list ErlModule -> Prop ) (l : list Expression) : forall (l' : list Expression),
  fully_equivalent_exprlist PM l l'
->
  fully_equivalent_expr PM (EValues l) (EValues l').
Proof.
  assert (A : forall (l l' : list Expression) modules env own_module id eff id' res eff', PM modules ->
    fully_equivalent_exprlist PM l l'
    ->
    (exists clock, fbs_expr clock env modules own_module id (EValues l) eff = Result id' res eff')
    ->
    (exists clock, fbs_expr clock env modules own_module id (EValues l') eff = Result id' res eff')).
  {
   intros l0 l' modules env own_module id eff id' res eff' F H H0.
    unfold fully_equivalent_exprlist, fully_equivalent_expr in *.
    destruct H0. destruct x. inversion H0. simpl in H0.
    destruct (fbs_values (fbs_expr x) env modules own_module id l0 eff) eqn:D.
    destruct res0. 3-4: congruence.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _ _ _). destruct E. eauto.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
    * inversion H0. subst. epose (E := H _ _ _ _ _ _ _ _). destruct E. eauto.
      pose (E := H1 (ex_intro _ x D)). destruct E. exists (S x0). simpl. rewrite H3. auto.
  }
  split; intros.
  * eapply A. auto. exact H. auto.
  * eapply A. auto. exact (fully_equivalent_exprlist_sym PM H). exact H1.
Qed.

End congruence.

Ltac cleanup_unfold_list :=
match goal with
| [H : exists _, _ |- _] => destruct H; cleanup_unfold_list
| _ => idtac
end; idtac.

Ltac unfold_list_once :=
match goal with
| [H : 0 = length ?l |- _ ] => apply eq_sym, length_zero_iff_nil in H; subst
| [H : length ?l = 0 |- _ ] => apply length_zero_iff_nil in H; subst
| [H : S ?n = length ?l |- _ ] => inversion H; apply element_exist in H; cleanup_unfold_list; subst
| [H : length ?l = S ?n |- _] => inversion H; apply eq_sym in H; apply element_exist in H; cleanup_unfold_list; subst
| _ => idtac "nomatch"
end.

Ltac unfold_list :=
match goal with
| [H : S _ = S (length _) |- _] => apply Nat.succ_inj in H; unfold_list
| [H : S (length _) = S _ |- _] => apply Nat.succ_inj in H; unfold_list
| [H : _ = length _ |- _] => simpl in H; unfold_list_once; unfold_list
| [H : length _ = _ |- _] => simpl in H; unfold_list_once; unfold_list
| _ => idtac "nomatch list"
end.

Section examples.

(** 
  * Examples why list congruence and list element congruence works only in one direction
  * *)
Goal
  fully_equivalent_expr (fun _ => True) (ETuple [EApp ErrorExp []]) (ETuple [ErrorExp;EApp ErrorExp []]).
Proof.
  split; intros; destruct H0; destruct x; inversion H0.
  * clear H2. exists (S x).
    simpl in H0; destruct x; inversion H0.
    simpl in H0; destruct x; inversion H0.
    simpl in H0. inversion H0. clear H2.
    simpl. auto.
  * clear H2. exists (S x).
    simpl in H0; destruct x; inversion H0.
    simpl in H0; destruct x; inversion H0.
    simpl in H0. inversion H0. clear H2.
    simpl. auto.
Qed.

(** 
  * The pair of the prevoius example
  *)

Goal
  fully_equivalent_expr (fun _ => True) (ETuple [ErrorExp; EApp ErrorExp []]) (ETuple [ErrorExp;EApp ErrorExp []]).
Proof.
  apply ETuple_full_cong. apply fully_equivalent_elements_exprlist; auto.
  intros. inversion H. 2: inversion H1. 3: inversion H3.
  all: apply fully_equivalent_expr_refl.
Qed.


(**
  * Quite inconvenient to use this
  *)

Example complete1 e :
  fully_equivalent_expr valid_modules (e) (ESeq (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 2); ELit (Integer 2)]) e).
 
 (* 
Example complete1 e :
forall env modules eff res eff' id1 id2, 
    get_modfunc "erlang" "+" 2 modules = None -> 
  (exists clock, fbs_expr clock env modules id1 e eff = Result id2 res eff')
<->
  (exists clock, fbs_expr clock env modules id1 (ESeq (ECall "erlang" "+" [ELit (Integer 2); ELit (Integer 2)]) e) eff = Result id2 res eff').
*)
Proof.
  split; intros.
  
  * destruct H0. exists (S (S (S x))).
    remember (S (S x)) as x'. simpl. rewrite Heqx' at 1.
    simpl. eapply bigger_clock_expr in H0.
    destruct H as [e0 e1]. inversion e0. unfold get_modfunc. 
    eapply module_lhs in H1.
    rewrite H1. simpl. exact H0. lia.

  * destruct H0.
    destruct x. inversion H0. simpl in H0.
    destruct x. inversion H0. simpl fbs_expr in H0 at 1.
    destruct x. inversion H0. simpl fbs_expr in H0 at 1. simpl fbs_expr in H0 at 1.
    remember (S (S x)) as x'. simpl in H0.  exists x'.
    destruct H as [e0 e1]. inversion e0. unfold get_modfunc in H0.
    eapply module_lhs in H1.
    rewrite H1 in H0. auto.
Qed.



End examples.