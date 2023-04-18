From CoreErlang.FrameStack Require Export Compatibility.

Import ListNotations.


Definition CIU (r1 r2 : Redex) : Prop :=
  REDCLOSED r1 /\ REDCLOSED r2 /\
  forall F, FSCLOSED F -> | F, r1 | ↓ -> | F, r2 | ↓.

Definition CIU_open (Γ : nat) (r1 r2 : Redex) :=
  forall ξ, SUBSCOPE Γ ⊢ ξ ∷ 0 ->
  CIU (r1.[ξ]ᵣ) (r2.[ξ]ᵣ).

Lemma CIU_closed :
  forall r1 r2,
  CIU r1 r2 -> REDCLOSED r1 /\ REDCLOSED r2.
Proof.
  intros. unfold CIU in H. intuition.
Qed.


Lemma CIU_closed_l : forall {r1 r2},
    CIU r1 r2 ->
    REDCLOSED r1.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_l : core.



Lemma CIU_closed_r : forall {r1 r2},
    CIU r1 r2 ->
    REDCLOSED r2.
Proof.
  intros.
  apply CIU_closed in H.
  intuition.
Qed.

Global Hint Resolve CIU_closed_r : core.

Lemma CIU_open_scope : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    RED Γ ⊢ r1 /\ RED Γ ⊢ r2.
Proof.
  intros.
  unfold CIU_open in H.
  split; eapply subst_implies_scope_red; intros; apply H in H0; auto;
    now apply CIU_closed in H0.
Qed.


Lemma CIU_open_scope_l : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    RED Γ ⊢ r1.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.


Global Hint Resolve CIU_open_scope_l : core.

Lemma CIU_open_scope_r : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    RED Γ ⊢ r2.
Proof.
  intros.
  apply CIU_open_scope in H.
  intuition.
Qed.

Global Hint Resolve CIU_open_scope_r : core.

Lemma Rrel_implies_CIU : forall Γ r1 r2,
  Rrel_open Γ r1 r2 ->
  CIU_open Γ r1 r2.
Proof.
  intros.
  unfold CIU_open; intros.
  unfold CIU.
  split. 2: split.
  - apply -> (subst_preserves_scope_red); eauto.
  - apply -> (subst_preserves_scope_red); eauto.
  - intros. inv H2. eapply H. 3: apply Frel_Fundamental_closed; auto. 3: eassumption.
    apply Grel_Fundamental; auto.
    reflexivity.
Qed.

Lemma Rrel_comp_CIU_implies_Rrel : forall {Γ r1 r2 r3},
    Rrel_open Γ r1 r2 ->
    CIU_open Γ r2 r3 ->
    Rrel_open Γ r1 r3.
Proof.
  intros Γ r1 r2 r3 HRrel HCIU.
  intros.
  split. 2: split. 1-2: apply -> subst_preserves_scope_red; eauto; apply H.
  intros. eapply HRrel in H1; eauto. eapply HCIU in H1; eauto.
  apply H.
Qed.

Lemma CIU_implies_Rrel : forall {Γ r1 r2},
    CIU_open Γ r1 r2 ->
    Rrel_open Γ r1 r2.
Proof.
  intros.
  eapply Rrel_comp_CIU_implies_Rrel; eauto.
  apply Rrel_Fundamental.
  now apply CIU_open_scope_l in H.
Qed.

Theorem CIU_iff_Rrel : forall {Γ r1 r2},
    CIU_open Γ r1 r2 <->
    Rrel_open Γ r1 r2.
Proof.
  intuition (auto using CIU_implies_Rrel, Rrel_implies_CIU).
Qed.

Theorem CIU_eval : forall r1 v,
  REDCLOSED r1 ->
  ⟨ [], r1 ⟩ -->* v -> CIU r1 v /\ CIU v r1.
Proof.
  intros. split. split. 2: split. auto.
  inv H0. eapply step_any_closedness; eauto. apply H1. now constructor.

  destruct H0 as [k [Hr Hd]].
  intros. inv H1. eapply frame_indep_nil in Hd.
  eapply term_step_term in H2. 2: eassumption. eexists. eassumption.

  split. 2: split. 2: auto.
  inv H0. eapply step_any_closedness; eauto. apply H1. now constructor.

  intros. destruct H0 as [k [Hr Hd]]. inv H2. eapply frame_indep_nil in Hd.
  eapply step_term_term_plus in Hd. 2: eassumption.
  eexists. eassumption.
Qed.

Theorem CIU_transitive_closed :
  forall x y z, CIU x y -> CIU y z -> CIU x z.
Proof.
  unfold CIU; intros. intuition.
Qed.

Theorem CIU_transitive :
  forall Γ x y z, CIU_open Γ x y -> CIU_open Γ y z -> CIU_open Γ x z.
Proof.
  unfold CIU_open; intros. intuition.
  eapply CIU_transitive_closed. apply H; auto. apply H0; auto.
Qed.

Corollary CIU_compat_reverse :
  forall v v' : Val, CIU (`v) (`v') -> CIU (RValSeq [v]) (RValSeq [v']).
Proof.
  intros. assert (⟨[], `v⟩ -->* RValSeq [v]). {
    apply CIU_closed_l in H. destruct_scopes.
    eexists. split; auto. econstructor. constructor; auto.
    econstructor.
  }
  assert (⟨[], `v'⟩ -->* RValSeq [v']). {
    apply CIU_closed_r in H. destruct_scopes.
    eexists. split; auto. econstructor. constructor; auto. constructor.
  }
  apply CIU_eval in H0, H1. 2-3: apply H. intuition.
  epose proof (CIU_transitive_closed _ _ _ H H0).
  now epose proof (CIU_transitive_closed _ _ _ H3 H1).
Qed.

Lemma match_pattern_list_vars :
  forall l, match_pattern_list (repeat PVar (length l)) l = Some l.
Proof.
  induction l; simpl; auto.
  break_match_goal; congruence.
Qed.

Lemma match_pattern_list_tuple_vars :
  forall l, match_pattern_list [PTuple (repeat PVar (length l))] [VTuple l] = Some l.
Proof.
  induction l; simpl; auto.
  break_match_goal; break_match_hyp; try congruence.
  - inversion Heqo. simpl in IHl.
    rewrite Heqo0 in IHl. inv IHl. reflexivity.
  - simpl in IHl. rewrite Heqo0 in IHl. congruence.
Qed.

Lemma match_pattern_list_tuple_vars_length :
  forall m l0 vs, match_pattern_list [PTuple (repeat PVar m)] [VTuple l0] = Some vs ->
  m = length l0 /\ vs = l0.
Proof.
  induction m; destruct l0; intros; simpl in *; inv H; auto.
  break_match_hyp. 2: congruence.
  inv H1. rewrite app_nil_r in *.
  break_match_hyp. 2: congruence. inv Heqo.
  specialize (IHm l0 l1). break_match_hyp. 2: congruence.
  inv Heqo0. clear -IHm.
  rewrite app_nil_r in IHm. specialize (IHm eq_refl) as [IHm1 IHm2].
  split; subst; auto.
Qed.

Lemma match_pattern_list_map_vars_length :
  forall m l0 vs, match_pattern_list [PMap (repeat (PVar, PVar) m)] [VMap l0] = Some vs ->
  m = length l0 /\ vs = flatten_list l0.
Proof.
  induction m; destruct l0; intros; simpl in *; inv H; auto.
  break_match_hyp. 2: congruence.
  inv H1. rewrite app_nil_r in *.
  do 2 break_match_hyp. 2: congruence. inv Heqo.
  specialize (IHm l0 l1). break_match_hyp. 2: congruence.
  inv Heqo0. clear -IHm.
  rewrite app_nil_r in IHm. specialize (IHm eq_refl) as [IHm1 IHm2].
  split; subst; auto.
Qed.

Lemma match_pattern_list_map_vars :
  forall l, match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap l] = Some (flatten_list l).
Proof.
  induction l; simpl; auto.
  break_match_goal; break_match_hyp; try congruence.
  - destruct a. inv Heqp. simpl in IHl. break_match_hyp. 2: congruence.
    inv Heqo. inv IHl. reflexivity.
  - destruct a. inv Heqp. simpl in IHl. break_match_hyp; congruence.
Qed.


(* Substitution.v *)
Fixpoint varsFrom n m : list Val :=
  match m with
  | O => []
  | S m' => VVar n :: varsFrom (S n) m'
  end.

(* Basics.v *)
Lemma skipn_S :
  forall {T : Type} n (l : list T) d,
  length l > n ->
  skipn n l = nth n l d :: skipn (S n) l.
Proof.
  induction n; intros; destruct l; simpl in *; try lia.
  reflexivity.
  erewrite IHn. reflexivity. lia.
Qed.

(* Substitution.v *)
Lemma map_varsFrom : forall m n l,
  length l >= n + m ->
  map (fun x => x.[list_subst l idsubst]ᵥ) (varsFrom n m) =
  firstn m (skipn n l).
Proof.
  induction m; intros; simpl; auto.
  rewrite list_subst_lt. 2: lia. simpl.
  rewrite (IHm (S n) l ltac:(lia)).
  destruct l. simpl in H. lia.
  rewrite (skipn_S n _ VNil); auto. simpl in *; lia.
Qed.

(* Basic.v *)
Theorem deflatten_map :
  forall T1 T2 (f : T1 -> T2) l,
    map (fun '(x, y) => (f x, f y)) (deflatten_list l) =
    deflatten_list (map f l).
Proof.
  induction l using list_length_ind; simpl; auto.
  destruct l; simpl; auto.
  destruct l; simpl; auto.
  rewrite H. reflexivity. slia.
Qed.

(* Substitution.v *)
Lemma varsFrom_length :
  forall m n, length (varsFrom n m) = m.
Proof.
  induction m; intros; simpl; auto.
Qed.

(* ScopingLemmas.v *)
Lemma varsFrom_scope :
  forall m n i,
  VAL S (i + n) ⊢ nth i (varsFrom n m) VNil.
Proof.
  induction m; intros; simpl; destruct i.
  - auto.
  - auto.
  - simpl. constructor. lia.
  - rewrite Nat.add_succ_comm. apply IHm.
Qed.

(* ScopingLemmas.v *)
Lemma scope_repeat_var n:
  fold_right (fun (x : Pat) (y : nat) => PatScope x + y) 0
(repeat PVar n) = n.
Proof.
  induction n; simpl; auto.
Qed.

Lemma Erel_Val_compat_closed_reverse :
  forall (v v' : Val), CIU (`v) (`v') -> forall m, Vrel m v v'.
Proof.
  valinduction; try destruct v'; intros; auto; destruct H as [Hcl1 [Hcl2 H]].
  1-7: epose proof (H [FCase1 [([PNil], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0;
       repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H10; apply inf_diverges in H10; contradiction.
  1,3-8: epose proof (H [FCase1 [([PLit l], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H10; apply inf_diverges in H10; contradiction.
  2-3,5-9: epose proof (H [FCase1 [([PCons PVar PVar], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H10; apply inf_diverges in H10; contradiction.
  3-5,7-10: epose proof (H [FCase1 [([PTuple (repeat PVar (length l))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H10; apply inf_diverges in H10; contradiction.
  4-7,9-11: epose proof (H [FCase1 [([PMap (repeat (PVar, PVar) (length l))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv; inv H9; inv H8; simpl in H11; do 2 deriv; simpl in H10; apply inf_diverges in H10; contradiction.
  5-12: destruct_scopes; lia.
  5-12: destruct_scopes; lia.
  Unshelve. (* evaluation in the omitted proofs *)
  13-19: now do 10 econstructor.
  13-19:
    econstructor; econstructor; auto; econstructor;
    [simpl; rewrite Lit_eqb_refl; reflexivity|];
    simpl; econstructor; auto; econstructor;
    [simpl; rewrite Lit_eqb_refl; reflexivity|]; constructor; auto;
    constructor; auto.
  13-19: 
    destruct_scopes; econstructor; econstructor; auto; econstructor;
    [reflexivity|]; simpl; econstructor; auto; econstructor;
    [reflexivity|]; constructor; auto;
    constructor; auto.
  13-19:
    destruct_scopes; econstructor; econstructor; auto; econstructor;
    [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto; econstructor;
    [apply match_pattern_list_tuple_vars|]; constructor; auto;
    constructor; auto.
  13-19:
    destruct_scopes; econstructor; econstructor; auto; econstructor;
    [apply match_pattern_list_map_vars|];
    simpl; econstructor; auto; econstructor;
    [apply match_pattern_list_map_vars|]; constructor; auto;
    constructor; auto.
  * epose proof (H [FCase1 [([PLit l], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
    - simpl in H9. destruct Lit_beq eqn:EQ.
      + apply Lit_eqb_eq in EQ. subst. choose_compat_lemma.
      + congruence.
    - inv H8. cbn in H11. repeat deriv. now apply inf_diverges in H11.
    - inv H8.
  Unshelve.
    econstructor; econstructor; auto; econstructor;
    [simpl; rewrite Lit_eqb_refl; reflexivity|];
    simpl; econstructor; auto; econstructor;
    [simpl; rewrite Lit_eqb_refl; reflexivity|]; constructor; auto;
    constructor; auto.
  * choose_compat_lemma.
    - apply IHv1. destruct_scopes. split. 2: split. 1-2: auto.
      intros. epose proof (H (FCase1 [([PCons PVar PVar], `ttrue, `VVar 0);([PVar], `ttrue , °inf)] :: F) ltac:(scope_solver) _) as H2; repeat deriv.
      + inv H16. cbn in H17. repeat deriv. inv H16. cbn in H17. now exists k1.
      + inv H16.
      + inv H15.
    - apply IHv2. destruct_scopes. split. 2: split. 1-2: auto.
      intros. epose proof (H (FCase1 [([PCons PVar PVar], `ttrue, `VVar 1);([PVar], `ttrue , °inf)] :: F) ltac:(scope_solver) _) as H2; repeat deriv.
      + inv H16. cbn in H17. repeat deriv. inv H16. cbn in H17. now exists k1.
      + inv H16.
      + inv H15.
  Unshelve.
    all: auto.
    all: destruct H1; destruct_scopes; econstructor; econstructor; auto;
       econstructor; [reflexivity|]; simpl; econstructor; auto;
       econstructor; [reflexivity|]; eauto.
  (* Tuple *)
  * choose_compat_lemma.
    revert l0 Hcl2 H. induction l; destruct l0; intros.
    - now auto.
    - epose proof (H [FCase1 [([PTuple []], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. repeat deriv. now apply inf_diverges in H12.
      + now inv H8.
    - epose proof (H [FCase1 [([PTuple (repeat PVar (length (a :: l)))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. repeat deriv. now apply inf_diverges in H12.
      + now inv H8.
    - inv IHv.
      assert (REDCLOSED (`VTuple l) /\ REDCLOSED (`VTuple l0)) as [IS1 IS2]. {
        destruct_scopes. split; do 3 constructor; intros;
        try apply (H4 (S i)); try apply (H5 (S i)); slia.
      }
      assert (forall F : FrameStack, FSCLOSED F -> | F, ` VTuple l | ↓ -> | F, ` VTuple l0 | ↓) as IS3. {
        intros.
        epose proof (H (FCase1 [([PTuple (repeat PVar (length (a :: l)))], `ttrue, `VTuple (varsFrom 1 (length l)));([PVar], `ttrue , °inf)] :: F) _ _) as H4.
        repeat deriv.
        * pose proof (match_pattern_list_tuple_vars_length (1 + length l) (v::l0) vs') as H1. simpl repeat in H1.
          apply H1 in H14 as H14'. destruct H14' as [Hlen EQ].
          simpl length in *. clear H1. inv EQ.
          simpl in H15. repeat deriv.
          rewrite H14 in H16. inv H16. simpl in H17.
          pose proof (map_varsFrom (length l) 1 (v :: l0) ltac:(slia)) as H17'.
          simpl in H17'. rewrite H17' in H17.
          replace (length l) with (length l0) in H17 by lia.
          rewrite firstn_all in H17. now exists k1.
        * cbn in H16. repeat deriv. now apply inf_diverges in H17.
        * inv H13.
      }
      specialize (IHl H3 IS1 _ IS2 IS3).
      constructor; auto.
      + apply H2. apply biforall_length in IHl as Hlen.
        split. 2: split.
        1-2: do 2 constructor; destruct_scopes; try apply (H6 0); try apply (H7 0); slia.
        intros. epose proof (H (FCase1 [([PTuple (repeat PVar (length (a :: l)))], `ttrue, `VVar 0);([PVar], `ttrue , °inf)] :: F) ltac:(scope_solver) _) as H4; repeat deriv.
        ** pose proof (match_pattern_list_tuple_vars (v :: l0)) as H1.
           simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
           inv H14. simpl in H15. repeat deriv.
           rewrite H1 in H15. inv H15. simpl in H16. now exists k1.
        ** pose proof (match_pattern_list_tuple_vars (v :: l0)) as H1.
           simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
           congruence.
        ** inv H13.
    Unshelve.
      all: auto.
      3: {
        constructor; auto. constructor; intros; destruct i.
        - do 2 constructor.
        - cbn. destruct i. do 2 constructor. destruct i; auto.
        - do 2 constructor; intros.
          rewrite varsFrom_length in H5. simpl.
          rewrite scope_repeat_var.
          pose proof (varsFrom_scope (length l) 1 i).
          eapply loosen_scope_val. 2: eassumption. lia.
        - simpl in *. destruct i. 2: lia.
          simpl. scope_solver.
      }
      {
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [reflexivity|]; simpl; econstructor; auto; econstructor;
        [reflexivity|]; constructor; auto;
        constructor; auto.
      }
      {
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto. econstructor;
        [apply (match_pattern_list_tuple_vars (a :: l))|]; constructor; auto;
        constructor; auto.
      }
      {
        inv H1. inv H4. 2: { inv H1. }
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto. econstructor; simpl;
        [apply (match_pattern_list_tuple_vars (a :: l))|]; constructor; auto; rewrite map_varsFrom; try slia; simpl; rewrite firstn_all; eauto.
      }
      {
        inv H1. inv H4. 2: { inv H1. }
        destruct_scopes; econstructor; econstructor; auto; econstructor;
        [apply match_pattern_list_tuple_vars|]; simpl; econstructor; auto. econstructor; simpl;
        [apply (match_pattern_list_tuple_vars (a :: l))|]; constructor; auto. simpl. eassumption.
      }
  (* Map *)
  * choose_compat_lemma.
    revert l0 Hcl2 H. induction l; destruct l0; intros.
    - now auto.
    - epose proof (H [FCase1 [([PMap []], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. repeat deriv. now apply inf_diverges in H12.
      + now inv H8.
    - epose proof (H [FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      + inv H9.
      + cbn in H11. repeat deriv. now apply inf_diverges in H12.
      + now inv H8.
    - inv IHv.
      assert (REDCLOSED (`VMap l) /\ REDCLOSED (`VMap l0)) as [IS1 IS2]. {
        destruct_scopes. split; do 3 constructor; intros;
        try apply (H1 (S i)); try apply (H4 (S i));
        try apply (H7 (S i)); try apply (H8 (S i)); try slia.
      }
      assert (forall F : FrameStack, FSCLOSED F -> | F, ` VMap l | ↓ -> | F, ` VMap l0 | ↓) as IS3. {
        intros.
        epose proof (H (FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], `ttrue, `VMap (deflatten_list (varsFrom 2 (length (flatten_list l)))));([PVar], `ttrue , °inf)] :: F) _ _) as H4.
        repeat deriv.
        * pose proof (match_pattern_list_map_vars_length (1 + length l) (p::l0) vs') as H1. simpl repeat in H1.
          apply H1 in H14 as H14'. destruct H14' as [Hlen EQ].
          simpl length in *. clear H1. inv EQ.
          simpl in H15. repeat deriv.
          rewrite H14 in H16. inv H16. simpl in H17.
          destruct p.
          pose proof (length_flatten_list l) as Hlen1.
          pose proof (length_flatten_list l0) as Hlen2.
          pose proof (map_varsFrom (length (flatten_list l)) 2 (v :: v0 :: flatten_list l0) ltac:(slia)) as H17'.
          replace (map
          (fun '(x, y) =>
           (x.[list_subst (v :: v0 :: flatten_list l0) idsubst]ᵥ,
            y.[list_subst (v :: v0 :: flatten_list l0) idsubst]ᵥ))
          (deflatten_list (varsFrom 2 (Datatypes.length (flatten_list l))))) with
                  (deflatten_list (map (fun x : Val => x.[list_subst (v :: v0 :: flatten_list l0) idsubst]ᵥ)
                  (varsFrom 2 (Datatypes.length (flatten_list l))))) in H17.
          2: {
            replace (length (flatten_list l)) with (length (flatten_list l0)) by lia.
            clear. rewrite deflatten_map. reflexivity.
          }
          simpl in H17', H17.
          rewrite H17' in H17.
          replace (length (flatten_list l)) with (length (flatten_list l0)) in H17 by lia.
          rewrite firstn_all in H17.
          rewrite flatten_deflatten in H17. now exists k1.
        * cbn in H16. repeat deriv. now apply inf_diverges in H17.
        * inv H13.
      }
      specialize (IHl H3 IS1 _ IS2 IS3). destruct a, p.
      constructor; auto. split.
      + apply H2. simpl. apply biforall_length in IHl as Hlen.
        split. 2: split.
        1-2: do 2 constructor; destruct_scopes; try apply (H5 0); try apply (H6 0); slia.
        intros. epose proof (H (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], `ttrue, `VVar 0);([PVar], `ttrue , °inf)] :: F) ltac:(scope_solver) _) as H4; repeat deriv.
        ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
          simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
          inv H14. simpl in H15. repeat deriv.
          rewrite H1 in H15. inv H15. simpl in H16. now exists k1.
        ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
          simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
          congruence.
        ** inv H13.
    + apply H2. simpl. apply biforall_length in IHl as Hlen.
      split. 2: split.
      1-2: do 2 constructor; destruct_scopes; try apply (H11 0); try apply (H12 0); slia.
      intros. epose proof (H (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], `ttrue, `VVar 1);([PVar], `ttrue , °inf)] :: F) ltac:(scope_solver) _) as H4; repeat deriv.
      ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
        simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
        inv H14. simpl in H15. repeat deriv.
        rewrite H1 in H15. inv H15. simpl in H16. now exists k1.
      ** pose proof (match_pattern_list_map_vars ((v1, v2) :: l0)) as H1.
        simpl repeat in H1. rewrite <-Hlen in H1. rewrite H1 in H14.
        congruence.
      ** inv H13.
  * 
Qed.

Lemma Erel_Val_compat_reverse :
  forall Γ (v v' : Val), Erel_open Γ (`v) (`v') -> Vrel_open Γ v v'.
Proof.
  intros. unfold Erel_open, Vrel_open in *. intros.
  apply H in H0. simpl in H0. destruct H0 as [HCl1 [HCl2 H0]].
  rewrite Vrel_Fix_eq. inv HCl1. inv HCl2.
  
Qed.