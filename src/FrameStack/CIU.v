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

Corollary CIU_iff_Rrel_closed : forall {r1 r2},
  CIU r1 r2 <->
  (forall m, Rrel m r1 r2).
Proof.
  intros.
  split.
  {
    split. 2: split. 1-2: apply H.
    intros. eapply H. apply H0.
    pose proof (Rrel_Fundamental_closed m0 r1 ltac:(apply H)).
    eapply H2; eauto.
  }
  {
    intros.
    split. 2: split. 1-2: apply (H 0).
    intros.
    inv H1. eapply H in H2. eassumption. reflexivity. auto.
  }
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

Corollary match_pattern_list_tuple_vars_map :
  forall l (f : Val -> Val), match_pattern_list [PTuple (repeat PVar (length l))] [VTuple (map f l)] = Some (map f l).
Proof.
  intros.
  pose proof (match_pattern_list_tuple_vars (map f l)). rewrite map_length in H.
  assumption.
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

Lemma match_pattern_list_map_vars_map :
  forall l (f : Val*Val -> Val*Val), match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap (map f l)] = Some (flatten_list (map f l)).
Proof.
  intros.
  pose proof (match_pattern_list_map_vars (map f l)). rewrite map_length in H.
  assumption.
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

(* ScopingLemmas.v *)
Lemma scope_repeat_var_prod n:
  fold_right (fun '(v1, v2) (y : nat) => PatScope v1 + PatScope v2 + y) 0
(repeat (PVar, PVar) n) = 2 * n.
Proof.
  induction n; simpl; auto.
  rewrite IHn. lia.
Qed.

(* Basics.v *)
Lemma deflatten_length :
  forall {T : Type} (l : list T),
    length (deflatten_list l) = Nat.div2 (length l).
Proof.
  induction l using list_length_ind; simpl; auto; destruct l; auto.
  destruct l; auto. simpl in *. rewrite H. 2: lia. lia.
Qed.


(* ScopingLemmas.v *)
Lemma VMap_scope_Forall :
  forall l Γ, Forall (fun '(v1,v2) => VAL Γ ⊢ v1 /\ VAL Γ ⊢ v2) l -> VAL Γ ⊢ VMap l.
Proof.
  induction l; intros; constructor; intros.
  1-2: inv H0.
  1-2: simpl in *; destruct a, i; simpl in *; inv H; try apply H3.
  1-2: apply IHl in H4; inv H4; try apply H1; try apply H5; lia.
Qed.

(* Basics.v *)
Theorem map_repeat {T Q : Type} :
  forall n (f : T -> Q) (x : T), map f (repeat x n) = repeat (f x) n.
Proof.
  induction n; intros; cbn; auto; now rewrite IHn.
Qed.

Lemma CIU_Val_compat_closed_reverse :
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
    Unshelve.
    all: auto.
    3: {
      constructor; auto. constructor; intros; destruct i.
      - do 2 constructor.
      - cbn. destruct i. do 2 constructor. destruct i; auto.
      - simpl. constructor. apply VMap_scope_Forall, deflatten_keeps_prop.
        rewrite indexed_to_forall with (def := VNil). intros.
        rewrite length_flatten_list.
        rewrite scope_repeat_var_prod.
        pose proof (varsFrom_scope (length l * 2) 2 i).
        eapply loosen_scope_val. 2: exact H6.
        rewrite varsFrom_length, length_flatten_list in H5. lia.
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
      [apply match_pattern_list_map_vars|]; simpl; econstructor; auto. econstructor;
      [apply (match_pattern_list_map_vars (a :: l))|]; constructor; auto;
      constructor; auto.
    }
    {
      inv H1. inv H4. 2: { inv H1. }
      destruct_scopes; econstructor; econstructor; auto; econstructor;
      [apply match_pattern_list_map_vars|]; simpl; econstructor; auto. econstructor; simpl;
      [apply (match_pattern_list_map_vars (a :: l))|].
      rewrite deflatten_map.
      constructor; auto.
      * rewrite map_varsFrom.
        2: destruct a; slia.
        destruct a. simpl. rewrite firstn_all, flatten_deflatten.
        constructor; intros; try apply H10; try apply H16; assumption.
      * rewrite map_varsFrom.
        2: destruct a; slia.
        destruct a. simpl. rewrite firstn_all, flatten_deflatten. eassumption.
    }
    {
      inv H1. inv H4. 2: { inv H1. }
      destruct_scopes; econstructor; econstructor; auto. econstructor;      
      [apply (match_pattern_list_map_vars ((v, v0)::l))|]; simpl; econstructor; auto. simpl. econstructor;
      [apply (match_pattern_list_map_vars ((v, v0) :: l))|]; constructor; auto. simpl. eassumption.
    }
    {
      inv H1. inv H4. 2: { inv H1. }
      destruct_scopes; econstructor; econstructor; auto. econstructor;      
      [apply (match_pattern_list_map_vars ((v, v0)::l))|]; simpl; econstructor; auto. simpl. econstructor;
      [apply (match_pattern_list_map_vars ((v, v0) :: l))|]; constructor; auto. simpl. eassumption.
    }
  (* closures - anything : create different exceptions in a try expr.
     e.g., apply the closure with a non-matching argument number, 
     then match on the exception:
      - if it's badarity -> result is VNil
      - if it's badfun -> result is divergence
    TODO: The following proof is identical for the next 7 cases
  *)
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
  * destruct params.
  (* we have to make sure, that the number of parameters differ *)
    - epose proof (H [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H10. repeat deriv. cbn in H12.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: inv H11. inv H11. cbn in H14.
      repeat deriv. now apply inf_diverges in H14.
    - epose proof (H [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H8. repeat deriv. cbn in H11.
      2: { now specialize (H5 _ _ _ _ eq_refl). }
      repeat deriv. inv H11. 2: inv H10. inv H10. cbn in H13.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    {
      eexists. destruct_scopes. repeat econstructor; eauto. congruence.
    }
    (* closure - closure -> induction on m *)
  * inv Hcl1. inv Hcl2.

    (* First, we show that the closures have the same arity with erlang:fun_info *)
    assert (params = params0). {
      epose proof (H [FParams (ICall "erlang" "fun_info") [] [`VLit "arity"%string];FCase1 [([PLit (Z.of_nat params)], `ttrue, `VNil);([PVar], `ttrue, °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      simpl in H11. repeat deriv. all: inv H12.
      3: inv H11.
      1-2: destruct (Z.of_nat params0 =? Z.of_nat params)%Z eqn:P; inv H5.
      - apply Z.eqb_eq in P. now apply Znat.Nat2Z.inj in P.
      - simpl in H14. repeat deriv. now apply inf_diverges in H14. 
      Unshelve.
        congruence.
        auto.
        destruct_scopes. repeat econstructor; auto.
        simpl. rewrite Z.eqb_refl. reflexivity.
        simpl. rewrite Z.eqb_refl. reflexivity.
    }

    (* Next we show that the identifiers are also equal using erlang:== *)
    assert (id = id0). {
      inv H1. inv H2.
      epose proof (H [FParams (ICall "erlang" "==") [] [` VClos ext id params0 e];FCase1 [([PLit "true"%string], `ttrue, `VNil);([PVar], `ttrue, °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H11.
      break_match_hyp. now apply Nat.eqb_eq in Heqb.
      repeat deriv; inv H12; inv H11.  simpl in *.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
      congruence.
      auto.
      destruct_scopes.
      repeat econstructor; auto. cbn.
      rewrite Nat.eqb_refl. repeat econstructor.
    }

      (* Starting the proof of Vrel clos1 clos2: *)
      subst. inv H1. inv H2.

      rewrite Vrel_Fix_eq. simpl. intuition; auto.
      (* scopes *)
      split. 2: split.
      1-2: destruct_scopes; apply -> subst_preserves_scope_exp; eauto.
      1-2: apply scoped_list_subscoped_eq; try simpl_convert_length; auto.
      2: apply biforall_length in H1; auto.
      1-2: apply Forall_app; split.
      1,3: apply closlist_scope; auto.
      1-2: apply biforall_vrel_closed in H1; apply H1.

      (* We fold back the CIU equivalence, with value lists: *)
      assert (H2 : CIU (RValSeq [VClos ext id0 params0 e]) (RValSeq [VClos ext0 id0 params0 e0])). {
        split. 2: split. all: auto.
        intros.
        assert (| F, ` VClos ext id0 params0 e | ↓). {
          inv H5. eexists. econstructor. auto. eassumption.
        }
        eapply H in H2; auto. inv H2. inv H7. eexists. eassumption.
        inv H0.
      }
      intros.

      (* We turn CIU into Rrel so that we can use equivalent frame stacks
         instead of equal ones. *)
      eapply CIU_iff_Rrel_closed in H2 as [_ [_ H2]].
      Unshelve. 2: exact (5 + 2 * Datatypes.length vl1 + 1 + m).
      (* IDEA: we use `try` to even out the evaluation counter for exceptions
          and correct application *)
      assert (Heval_e : | FTry 1 (° EApp (` VVar 0) (map VVal vl1)) 0 (° ETuple (map VVal vl1)) :: F1,
     ` VClos ext id0 params0 e | 5 + 2 * length vl1 + 1 + m1 ↓). {
        simpl. econstructor; auto. constructor; auto. simpl.
        replace (map (fun x : Exp => x.[VClos ext id0 params0 e/]) (map VVal vl1))
           with (map VVal vl1).
        2: {
          clear -H1. rewrite map_map. simpl.
          apply biforall_vrel_closed in H1 as [H1 _].
          apply map_ext_Forall. induction vl1; inv H1; constructor; auto.
          now rewrite vclosed_ignores_sub.
        }
        do 2 constructor. auto.
        constructor. destruct vl1.
        * simpl. econstructor. congruence. reflexivity. simpl.
          break_match_goal. 2: apply Nat.eqb_neq in Heqb; simpl in H0; lia.
          assumption.
        * simpl. constructor. congruence.
          simpl. change clock to (S (1 + 2 * length vl1) + m1).
          inv H1. constructor. now apply Vrel_closed_l in H9.
          eapply step_term_term_plus. apply params_eval_create.
          now apply biforall_vrel_closed in H11. simpl. rewrite Nat.eqb_refl.
          assumption.
      }

      (* We assert that the frame stack with the `try` expressions are equivalent
        in as many steps that are needed to evaluate the closures. *)
      assert (Hrel : Frel (4 + 2 * length vl1 + 1 + m1) (* dirty trick here with 0 *)
          (FTry 1 (EApp (`VVar 0) (map VVal vl1)) 0 (ETuple (map VVal vl1))::F1)
          (FTry 1 (EApp (`VVar 0) (map VVal vl2)) 0 (ETuple (map VVal vl2))::F2)
            ). {
        clear Heval_e.
        split. 2: split. 1-2: constructor; [constructor|apply H5].
        1-4: do 2 constructor; auto; apply indexed_to_forall; apply biforall_vrel_closed in H1; clear -H1.

        (* boiler plate codes: *)
        1-2: destruct H1 as [H1 _]; induction vl1; simpl; auto; inv H1; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        1-2: destruct H1 as [_ H1]; induction vl2; simpl; auto; inv H1; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        (****)

        split. 2: split.
        all: intros.
        * deriv. inv H7. inv H16. inv H8. 2: inv H16.
          simpl in H17.
          deriv. deriv. deriv. inv H1.
          - deriv.
            simpl in Hmn1.
            pose proof (Rel_create_result _ [] [] (IApp hd) (IApp hd') ltac:(auto) ltac:(constructor; eauto)).
            intuition.
            + repeat destruct_hyps.
              specialize (H1 k ltac:(lia)) as [Hrel [Eq1 Eq2]].
              rewrite Eq1 in H14. eapply Hrel in H14 as [kk D]. 2: reflexivity.
              2: eapply Frel_downclosed in H5; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite Eq2. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H7 in H14.
              eapply H5 in H14 as [kk D]. 2: lia. 2: eapply biforall_impl;[|eassumption]; intros; downclose_Vrel.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite H9. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H7 in H14.
              eapply H5 in H14 as [kk D]. 2: lia. 2: eapply Excrel_downclosed; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite H9. exact D.
              Unshelve. lia.
          - inv H13. inv H18.
            rewrite map_map in H12.
            rewrite vclosed_ignores_sub in H10. 2: now apply Vrel_closed_l in H7.
            replace (map (fun x : Val => (` x).[hd/]) tl) with
                    (map VVal tl) in H12.
            2: {
              clear -H9. simpl.
              apply biforall_vrel_closed in H9 as [H1 _].
              apply map_ext_Forall. induction tl; inv H1; constructor; auto.
              now rewrite vclosed_ignores_sub.
            }
            rewrite vclosed_ignores_sub in H12. 2: now apply Vrel_closed_l in H0.
            eapply term_step_term in H12. 2: apply params_eval_create.
            2: now apply biforall_vrel_closed in H9.
            simpl app in H12.
            simpl in Hmn1.
            assert (list_biforall (Vrel (k0 - (1 + 2 * Datatypes.length tl)))
                                  (hd0 :: tl) (hd'0 :: tl') ) as Hfinally.
            {
              constructor. downclose_Vrel.
              eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
            }
            epose proof (Rel_create_result_relaxed _ (hd0 :: tl) (hd'0 :: tl') (IApp hd) (IApp hd') Hfinally _). Unshelve.
            4: {
              split. 2: split.
              1-2: constructor; now apply Vrel_closed in H0.
              downclose_Vrel.
            }
            intuition.
            + repeat destruct_hyps. simpl in Hmn1.
              specialize (H1 (k0 - (1 + 2 * Datatypes.length tl)) ltac:(lia)).
              destruct H1 as [Hrel [H1_1 H1_2]].
              rewrite H1_1 in H12. eapply Hrel in H12 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H9. simpl.
                apply biforall_vrel_closed in H9 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H9. simpl app. rewrite H1_2.
              exact D. lia. eapply Frel_downclosed. eassumption.
              Unshelve. lia. lia.
            + repeat destruct_hyps.
              rewrite H11 in H12. eapply H5 in H12 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H9. simpl.
                apply biforall_vrel_closed in H9 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H9. simpl app. rewrite H13.
              exact D. simpl in Hmn1. lia.
              eapply biforall_impl. 2: eassumption.
              intros. downclose_Vrel.
              Unshelve. lia.
            + repeat destruct_hyps.
              rewrite H11 in H12. eapply H5 in H12 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H9. simpl.
                apply biforall_vrel_closed in H9 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H9. simpl app. rewrite H13.
              exact D. simpl in Hmn1. lia.
              eapply Excrel_downclosed. eassumption.
              Unshelve. simpl in Hmn1. lia.
            + lia.
            + lia.
        * inv H8. (* Having 0 params in `catch` is exploited here,
                     because we only want to evaluate the `of` subexpression
                     in this `try` expression.
                   *)
          specialize (H12 _ _ _ _ eq_refl). contradiction.
        * inv H7.
      }

      (* Finally, we combine the previous assertions with the closures
         being in Rrel (H2). *)
      inv Heval_e.
      epose proof (H2 := H2 _ _ _ _ Hrel H11).
      Unshelve. 2: lia.
      clear -H2 H1. (* DANGER, nothing else is needed for now, however this
                               is fragile if refactoring is needed *)
      (* We deconstruct the evaluation in the premise: *)
      inv H2. deriv. simpl in H9. deriv. deriv. simpl in H3.
      deriv.
      rewrite map_map in H6.
      replace (map (fun x : Val => (` x).[VClos ext0 id0 (Datatypes.length vl1) e0/]) vl2) with
                      (map VVal vl2) in H6.
      2: {
        clear -H1. simpl.
        apply biforall_vrel_closed in H1 as [_ H1].
        apply map_ext_Forall. induction vl2; inv H1; constructor; auto.
        now rewrite vclosed_ignores_sub.
      }
      destruct vl2.
      - deriv. simpl in H9. apply biforall_length in H1. rewrite H1 in H9.
        simpl in H9. eexists. eassumption.
      - deriv. deriv.
        eapply term_step_term in H4. 2: apply params_eval_create.
        2: {
          apply biforall_vrel_closed in H1 as [_ H1]. now inv H1.
        }
        simpl in H4. apply biforall_length in H1. rewrite H1 in H4.
        simpl in H4. rewrite Nat.eqb_refl in H4. eexists. eassumption.
Qed.

Definition default_subst v : Substitution := fun _ => inl v. (* Γ v := list_subst (repeat v Γ) idsubst. *)

Corollary default_subst_scope Γ v :
  VALCLOSED v ->
  SUBSCOPE Γ ⊢ default_subst v ∷ 0.
Proof.
  intro.
  unfold default_subst, subscoped. now intros.
Qed.

#[global]
Hint Resolve default_subst_scope : core.

Corollary default_subst_Grel :
  forall m Γ v, VALCLOSED v -> Grel m Γ (default_subst v) (default_subst v).
Proof.
  intros. unfold Grel. split. 2: split. 1-2: auto.
  intros. unfold default_subst.
  now apply Vrel_Fundamental_closed.
Qed.

Ltac inf_congr :=
  match goal with
  | [H :  | _ , RExp (EExp inf) | _ ↓ |- _ ] => apply inf_diverges in H; contradiction
  | [H :  | _ , RExp (EExp inf.[_]ₑ) | _ ↓ |- _ ] => apply inf_diverges in H; contradiction
  end.

Lemma inf_scope :
  forall Γ, NVAL Γ ⊢ inf.
Proof.
  intros. unfold inf. scope_solver.
Qed.

#[global]
Hint Resolve inf_scope : core.

Opaque inf.

Lemma redex_val_scope :
  forall Γ (v : Val), RED Γ ⊢ `v -> VAL Γ ⊢ v.
Proof.
  intros. now destruct_scopes.
Qed.

Lemma Erel_Tuple_compat_reverse :
  forall Γ l l', Erel_open Γ (`VTuple l) (`VTuple l') ->
    list_biforall (Erel_open Γ) (map VVal l) (map VVal l').
Proof.
  induction l; destruct l'; intros; auto.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PTuple []], `ttrue, `VNil);([PVar], `ttrue, °inf)]], `VTuple [] |↓). {
        eexists. econstructor. scope_solver.
        econstructor. reflexivity. simpl.
        constructor. auto.
        econstructor. reflexivity. simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H12.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PTuple (repeat PVar (length (a :: l)))], `ttrue, `VNil);([PVar], `ttrue, °inf)]], (`VTuple (a :: l)).[default_subst VNil]ᵣ |↓). {
        assert (VALCLOSED (VTuple (a :: l)).[default_subst VNil]ᵥ). {
          apply CIU_open_scope_l in H. inv H. inv H1.
          apply -> subst_preserves_scope_val; eauto.
        }
        eexists. simpl. econstructor. exact H0.
        econstructor. apply (match_pattern_list_tuple_vars_map (a :: l)). simpl.
        constructor. auto.
        econstructor. apply (match_pattern_list_tuple_vars_map (a :: l)). simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H12.
  * simpl.
    assert (Erel_open Γ (`VTuple l) (`VTuple l')). {
      apply Rrel_exp_compat, CIU_iff_Rrel in H.
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H0. clear H. simpl in *.
      destruct H0 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED (VTuple l).[ξ]ᵥ /\ VALCLOSED (VTuple l').[ξ]ᵥ) as [Hsc3 Hsc4]. {
        simpl in *.
        destruct_scopes. simpl. split; constructor; intros;
          try apply (H1 (S i)); try apply (H2 (S i)); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PTuple (repeat PVar (length (a :: l)))], `ttrue, `VTuple (varsFrom 1 (length l)));([PVar], `ttrue , °inf)] :: F) _ _) as Hrel.
      repeat deriv.
      * pose proof (match_pattern_list_tuple_vars_length (1 + length l) (map (fun x => x.[ξ]ᵥ) (v::l')) vs') as H1. simpl repeat in H1.
        apply H1 in H10 as H10'. destruct H10' as [Hlen EQ].
        simpl length in *. rewrite map_length in Hlen. clear H1. destruct vs'; inv EQ.
        simpl in H11. repeat deriv.
        rewrite H10 in H12. inv H12. simpl in H13.
        pose proof (map_varsFrom (length l) 1 (map (fun x => x.[ξ]ᵥ) (v :: l')) ltac:(rewrite map_length;slia)) as H17'.
        simpl in H17'. rewrite H17' in H13.
        replace (length l) with (length l') in H13 by lia.
        rewrite <- (map_length (fun x => x.[ξ]ᵥ) l') in H13.
        rewrite firstn_all in H13. now exists k0.
      * cbn in H12. repeat deriv. now apply inf_diverges in H14.
      * inv H9.
      Unshelve.
        - constructor; auto. do 5 scope_solver_step. constructor.
          constructor. intros. rewrite scope_repeat_var.
          pose proof (varsFrom_scope (length l) 1 i).
          eapply loosen_scope_val. 2: eassumption.
          rewrite varsFrom_length in H1. lia.
        - inv H0. inv H1. 2: { inv H0. }
          pose proof (match_pattern_list_tuple_vars (map (fun x : Val => x.[ξ]ᵥ) (a :: l))). rewrite map_length in H0.
          destruct_scopes; econstructor; econstructor; auto; econstructor.
          apply H0.
          simpl; econstructor. auto. econstructor; simpl;
          [apply H0|]; constructor.
          rewrite map_varsFrom; try (rewrite map_length; slia).
          simpl. rewrite <- (map_length (fun x : Val => x.[ξ]ᵥ) l). rewrite firstn_all; eauto.
          rewrite map_varsFrom. 2: rewrite map_length; slia.
          simpl. rewrite <- (map_length (fun x : Val => x.[ξ]ᵥ) l). rewrite firstn_all.
          eassumption.
    }
    apply IHl in H0. constructor; auto.
    apply biforall_length in H0. do 2 rewrite map_length in H0.
    apply Rrel_exp_compat, CIU_iff_Rrel in H.
    apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
    intros ??. apply H in H1. clear H. simpl in *.
    destruct H1 as [Hsc1 [Hsc2 Hrel]].
    assert (VALCLOSED a.[ξ]ᵥ /\ VALCLOSED v.[ξ]ᵥ) as [Hsc3 Hsc4]. {
      simpl in *.
      destruct_scopes. simpl. split; try apply (H3 0); try apply (H2 0); slia.
    }
    split. 2: split.
    1-2: do 2 constructor; auto.
    intros.
    epose proof (Hrel (FCase1 [([PTuple (repeat PVar (length (a :: l)))], `ttrue, `VVar 0);([PVar], `ttrue , °inf)] :: F) _ _) as Hrel.
    repeat deriv.
    - pose proof (match_pattern_list_tuple_vars_length (1 + length l) (map (fun x => x.[ξ]ᵥ) (v::l')) vs') as H1. simpl repeat in H1.
      apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
      simpl length in *. rewrite map_length in Hlen. clear H1. destruct vs'; inv EQ.
      simpl in H12. repeat deriv.
      rewrite H11 in H13. inv H13. simpl in H14. eexists. eassumption.
    - cbn in H13. repeat deriv. now apply inf_diverges in H15.
    - inv H10.
  Unshelve.
    + constructor; auto. do 5 scope_solver_step. constructor.
      constructor. intros. rewrite scope_repeat_var. lia.
    + inv H1. inv H2. 2: { inv H1. }
      pose proof (match_pattern_list_tuple_vars (map (fun x : Val => x.[ξ]ᵥ) (a :: l))).
      rewrite map_length in H1.
      destruct_scopes; econstructor; econstructor; auto; econstructor.
      apply H1.
      simpl; econstructor. auto. econstructor; simpl;
      [apply H1|]; constructor.
      cbn. auto.
      simpl. eassumption.
Qed.

Lemma Erel_Map_compat_reverse :
  forall Γ l l', Erel_open Γ (`VMap l) (`VMap l') ->
    list_biforall (fun '(e1, e2) '(e1', e2') => Erel_open Γ e1 e1' /\ Erel_open Γ e2 e2') (map (fun '(e1, e2) => (`e1, `e2)) l) (map (fun '(e1, e2) => (`e1, `e2)) l').
Proof.
  induction l; destruct l'; intros; auto.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PMap []], `ttrue, `VNil);([PVar], `ttrue, °inf)]], `VMap [] |↓). {
        eexists. econstructor. scope_solver.
        econstructor. reflexivity. simpl.
        constructor. auto.
        econstructor. reflexivity. simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H12.
  * exfalso. apply Rrel_exp_compat in H. apply CIU_iff_Rrel in H.
      assert (| [FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], `ttrue, `VNil);([PVar], `ttrue, °inf)]], (`VMap (a :: l)).[default_subst VNil]ᵣ |↓). {
        assert (VALCLOSED (VMap (a :: l)).[default_subst VNil]ᵥ). {
          apply CIU_open_scope_l in H. inv H. inv H1.
          apply -> subst_preserves_scope_val; eauto.
        }
        eexists. simpl. econstructor. exact H0. destruct a. Check match_pattern_list_map_vars_map.
        pose proof (HM := match_pattern_list_map_vars_map ((v, v0) :: l) (fun '(x, y) => (x.[default_subst VNil]ᵥ, y.[default_subst VNil]ᵥ))). (* Coq cannot infer f correctly somewhy *)
        simpl repeat in HM. simpl map in HM.
        econstructor. apply HM.
        simpl.
        constructor. auto.
        econstructor. apply HM. simpl.
        do 2 constructor. auto.
      }
      specialize (H (default_subst VNil) ltac:(auto)). simpl in H.
      apply H in H0. 2: scope_solver.
      inv H0. repeat deriv. inv H9. 2: inv H8. simpl in H11. inv H11.
      inv H4. now apply inf_diverges in H12.
  * simpl.
    assert (Erel_open Γ (`VMap l) (`VMap l')). {
      apply Rrel_exp_compat, CIU_iff_Rrel in H.
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H0. clear H. simpl in *.
      destruct H0 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED (VMap l).[ξ]ᵥ /\ VALCLOSED (VMap l').[ξ]ᵥ) as [Hsc3 Hsc4]. {
        simpl in *.
        destruct_scopes. simpl. split; constructor; intros;
          try apply (H1 (S i)); try apply (H5 (S i));
          try apply (H0 (S i)); try apply (H4 (S i)); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PMap (repeat (PVar, PVar) (length (a :: l)))], `ttrue, `VMap (deflatten_list (varsFrom 2 (length (flatten_list l)))));([PVar], `ttrue , °inf)] :: F) _ _) as H4.
        repeat deriv.
        * pose proof (match_pattern_list_map_vars_length (1 + length l) (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) (p::l')) vs') as H1. simpl repeat in H1. destruct p.
          apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
          simpl length in *. clear H1. destruct vs'; inv EQ.
          simpl in H12. repeat deriv.
          rewrite H11 in H12. inv H12. simpl in H13.
          pose proof (length_flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l)) as Hlen1.
          pose proof (length_flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')) as Hlen2.
          epose proof (map_varsFrom (length (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l))) 2 (v.[ξ]ᵥ :: v0.[ξ]ᵥ :: flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')) ltac:(rewrite map_length in *; slia)) as H13'.
          replace (map
             (fun '(x, y) =>
              (x.[v.[ξ]ᵥ
                  .: v0.[ξ]ᵥ
                     .: list_subst
                          (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l'))
                          idsubst]ᵥ,
               y.[v.[ξ]ᵥ
                  .: v0.[ξ]ᵥ
                     .: list_subst
                          (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l'))
                          idsubst]ᵥ))
             (deflatten_list (varsFrom 2 (Datatypes.length (flatten_list l))))) with
                  (deflatten_list (map (fun x : Val => x.[list_subst (v.[ξ]ᵥ :: v0.[ξ]ᵥ :: flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')) idsubst]ᵥ)
                  (varsFrom 2 (Datatypes.length (flatten_list l))))) in H13.
          2: {
            rewrite map_length in *.
            replace (length (flatten_list l)) with (length (flatten_list l')).
            clear. rewrite deflatten_map. reflexivity.
            do 2 rewrite length_flatten_list. lia.
          }
          simpl in H13', H13. rewrite length_flatten_list in H13', H13.
          rewrite map_length in H13'.
          rewrite H13' in H13.
          replace (Datatypes.length l * 2) with
                  (length (flatten_list (map (fun '(x0, y0) => (x0.[ξ]ᵥ, y0.[ξ]ᵥ)) l')))
            in H13 by (rewrite length_flatten_list; lia).
          rewrite firstn_all in H13.
          rewrite flatten_deflatten in H13. now exists k1.
        * cbn in H13. repeat deriv. now apply inf_diverges in H14.
        * inv H10.
      Unshelve.
        - constructor; auto. do 5 scope_solver_step.
          constructor.
          apply VMap_scope_Forall, deflatten_keeps_prop.
          rewrite indexed_to_forall with (def := VNil). intros.
          rewrite length_flatten_list.
          rewrite scope_repeat_var_prod.
          pose proof (varsFrom_scope (length l * 2) 2 i).
          eapply loosen_scope_val. 2: exact H2.
          rewrite varsFrom_length, length_flatten_list in H1. lia.
        - inv H0. inv H1. 2: { inv H0. }
          destruct a.
          pose proof (match_pattern_list_map_vars (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v, v0) :: l))). rewrite map_length in H0.
          destruct_scopes; econstructor; econstructor; auto; econstructor.
          apply H0.
          simpl; econstructor. auto. econstructor; simpl;
          [apply H0|]; constructor.
          {
            apply VMap_scope_Forall. rewrite deflatten_map.
            apply deflatten_keeps_prop. rewrite map_varsFrom.
            replace (length (flatten_list l)) with
                  (length (skipn 2
            (flatten_list (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v, v0) :: l))))).
            2: {
              rewrite skipn_length, length_flatten_list, length_flatten_list, map_length.
              simpl. lia.
            }
            rewrite firstn_all. simpl.
            apply flatten_keeps_prop. rewrite indexed_to_forall with (def := (VNil, VNil)); intros.
            2: rewrite length_flatten_list, length_flatten_list, map_length; slia.
            specialize (H6 i H1). specialize (H10 i H1).
            rewrite map_nth with (d := (VNil, VNil)) in H6, H10.
            destruct (nth i (map _ l) _); auto.
          }
          rewrite deflatten_map.
          rewrite map_varsFrom.
          replace (length (flatten_list l)) with
                  (length (skipn 2
            (flatten_list (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v, v0) :: l))))).
          2: {
            rewrite skipn_length, length_flatten_list, length_flatten_list, map_length.
            simpl. lia.
          }
          rewrite firstn_all. simpl.
          rewrite flatten_deflatten. eassumption.
          rewrite length_flatten_list, length_flatten_list, map_length. slia.
    }
    apply IHl in H0. constructor; auto.
    apply biforall_length in H0. do 2 rewrite map_length in H0.
    apply Rrel_exp_compat, CIU_iff_Rrel in H.
    destruct a as [v1 v2], p as [v1' v2'].

    (* boiler plate code starts here *)
    split.
    {
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H1. clear H. simpl in *.
      destruct H1 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED v1.[ξ]ᵥ /\ VALCLOSED v1'.[ξ]ᵥ) as [Hsc3 Hsc4]. {
        simpl in *.
        destruct_scopes. simpl. split; try apply (H1 0); try apply (H2 0); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], `ttrue, `VVar 0);([PVar], `ttrue , °inf)] :: F) _ _) as Hrel.
      repeat deriv.
      - pose proof (match_pattern_list_map_vars_length (1 + length l) (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v1', v2')::l')) vs') as H1. simpl repeat in H1.
        apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
        simpl length in *. rewrite map_length in Hlen. clear H1. destruct vs'; inv EQ.
        simpl in H12. repeat deriv.
        rewrite H11 in H13. inv H13. simpl in H14. eexists. eassumption.
      - cbn in H13. repeat deriv. now apply inf_diverges in H15.
      - inv H10.
    Unshelve.
      + constructor; auto. do 5 scope_solver_step. constructor.
        constructor. intros. rewrite scope_repeat_var_prod. lia.
      + inv H1. inv H2. 2: { inv H1. }
        pose proof (match_pattern_list_map_vars (map (fun '(x,y) => (x.[ξ]ᵥ,y.[ξ]ᵥ)) ((v1,v2) :: l))).
        rewrite map_length in H1.
        destruct_scopes; econstructor; econstructor; auto; econstructor.
        apply H1.
        simpl; econstructor. auto. econstructor; simpl;
        [apply H1|]; constructor.
        cbn. auto.
        simpl. eassumption.
    }
    { (* Same as before, except at two places *)
      apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
      intros ??. apply H in H1. clear H. simpl in *.
      destruct H1 as [Hsc1 [Hsc2 Hrel]].
      assert (VALCLOSED v2.[ξ]ᵥ /\ VALCLOSED v2'.[ξ]ᵥ) as [Hsc3 Hsc4]. { (* difference here *)
        simpl in *.
        destruct_scopes. simpl. split; try apply (H5 0); try apply (H6 0); slia.
      }
      split. 2: split.
      1-2: do 2 constructor; auto.
      intros.
      epose proof (Hrel (FCase1 [([PMap (repeat (PVar, PVar) (length ((v1, v2) :: l)))], `ttrue, `VVar 1);([PVar], `ttrue , °inf)] :: F) _ _) as Hrel. (* difference here: VVar 1 !!! *)
      repeat deriv.
      - pose proof (match_pattern_list_map_vars_length (1 + length l) (map (fun '(x, y) => (x.[ξ]ᵥ, y.[ξ]ᵥ)) ((v1', v2')::l')) vs') as H1. simpl repeat in H1.
        apply H1 in H11 as H11'. destruct H11' as [Hlen EQ].
        simpl length in *. rewrite map_length in Hlen. clear H1. destruct vs'; inv EQ.
        simpl in H12. repeat deriv.
        rewrite H11 in H13. inv H13. simpl in H14. eexists. eassumption.
      - cbn in H13. repeat deriv. now apply inf_diverges in H15.
      - inv H10.
    Unshelve.
      + constructor; auto. do 5 scope_solver_step. constructor.
        constructor. intros. rewrite scope_repeat_var_prod. lia.
      + inv H1. inv H2. 2: { inv H1. }
        pose proof (match_pattern_list_map_vars (map (fun '(x,y) => (x.[ξ]ᵥ,y.[ξ]ᵥ)) ((v1,v2) :: l))).
        rewrite map_length in H1.
        destruct_scopes; econstructor; econstructor; auto; econstructor.
        apply H1.
        simpl; econstructor. auto. econstructor; simpl;
        [apply H1|]; constructor.
        cbn. auto.
        simpl. eassumption.
    }
Qed.

Lemma map_map_subst :
  forall l ξ,
    map (fun x => x.[ξ]) (map VVal l) =
    map VVal (map (fun x => x.[ξ]ᵥ) l).
Proof.
  induction l; intros; simpl; auto.
  now rewrite IHl.
Qed.

Lemma vmap_ignores_sub :
  forall l ξ,
    Forall (fun x => VALCLOSED x) l ->
    map (substVal ξ) l = l.
Proof.
  induction l; intros; simpl; auto. inv H.
  rewrite IHl. rewrite vclosed_ignores_sub. all: auto.
Qed.

Lemma convert_map : forall l ξ, map (substVal ξ) (convert_to_closlist l) =
                                convert_to_closlist (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length l + ls) ξ])) l).
Proof.
  clear. intros. unfold convert_to_closlist.
  do 2 rewrite map_map. f_equal.
  extensionality x. destruct x, p. now simpl.
Qed.


Lemma CIU_Clos_compat_reverse :
  forall Γ b1 b2 ext1 ext2 id1 id2 p1 p2, p1 = p2 -> id1 = id2 ->
    CIU_open Γ (`VClos ext1 id1 p1 b1) (`VClos ext2 id2 p2 b2) ->
    (* Erel_open (p1 + Γ) (b1.[list_subst (convert_to_closlist ext1) idsubst])
                       (b2.[list_subst (convert_to_closlist ext1) idsubst]) *)
    forall ξ l, SUBSCOPE Γ ⊢ ξ ∷ 0 -> Forall (fun v => VALCLOSED v) l -> length l = p1 ->
      CIU (b1.[list_subst (convert_to_closlist ext1 ++ l) idsubst].[ξ])
          (b2.[list_subst (convert_to_closlist ext2 ++ l) idsubst].[ξ]).
Proof.
  intros. subst.
  assert (VALCLOSED (VClos ext1 id2 (length l) b1).[ξ]ᵥ /\
          VALCLOSED (VClos ext2 id2 (length l) b2).[ξ]ᵥ) as [Hcl1 Hcl2]. {
    apply CIU_open_scope in H1. destruct H1. inv H. inv H0. inv H4. inv H1.
    split; apply -> subst_preserves_scope_val; eauto.
  }
  split. 2: split.
  (* scopes *)
  1-2: simpl in *; destruct_scopes; rewrite map_length in *.
  1-2: constructor; rewrite subst_comp_exp.
  {
    rewrite subst_comm, <- subst_comp_exp. simpl_convert_length.
    apply -> subst_preserves_scope_exp; eauto.
    apply scoped_list_subscoped_eq; auto.
    now rewrite map_length, app_length, map_length.
    rewrite map_app. apply Forall_app. split. 2: now rewrite vmap_ignores_sub.
    epose proof (closlist_scope _ (map (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ]))
               ext1) _).
    Unshelve.
      3: {
        intros. rewrite map_length in H. apply H6 in H.
        rewrite map_length. exact H.
      }
    unfold convert_to_closlist in H. rewrite map_map in *.
    assert (
    (fun x : nat * nat * Exp =>
          let
          '(id, vc, e) :=
           let '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext1 + ls) ξ]) in
           VClos
             (map (fun '(i0, ls, x0) => (i0, ls, x0.[upn (Datatypes.length ext1 + ls) ξ]))
                ext1) id vc e)
     = (fun x : nat * nat * Exp => (let '(id, vc, e) := x in VClos ext1 id vc e).[ξ]ᵥ)
     ). {
      clear. extensionality x. destruct x, p. now simpl.
    }
    rewrite H0 in H. assumption.
  }
  (* boiler plate code for ext2 *)
  {
    rewrite subst_comm, <- subst_comp_exp. simpl_convert_length.
    apply -> subst_preserves_scope_exp; eauto.
    apply scoped_list_subscoped_eq; auto.
    now rewrite map_length, app_length, map_length.
    rewrite map_app. apply Forall_app. split. 2: now rewrite vmap_ignores_sub.
    epose proof (closlist_scope _ (map (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ]))
               ext2) _).
    Unshelve.
      3: {
        intros. rewrite map_length in H. apply H5 in H.
        rewrite map_length. exact H.
      }
    unfold convert_to_closlist in H. rewrite map_map in *.
    assert (
    (fun x : nat * nat * Exp =>
          let
          '(id, vc, e) :=
           let '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext2 + ls) ξ]) in
           VClos
             (map (fun '(i0, ls, x0) => (i0, ls, x0.[upn (Datatypes.length ext2 + ls) ξ]))
                ext2) id vc e)
     = (fun x : nat * nat * Exp => (let '(id, vc, e) := x in VClos ext2 id vc e).[ξ]ᵥ)
     ). {
      clear. extensionality x. destruct x, p. now simpl.
    }
    rewrite H0 in H. assumption.
  }
  (* evaluation *)
  intros.
  apply H1 in H2 as [_ [_ Hrel]]. clear H1.
  unshelve (epose proof (Hrel (FApp1 (map VVal l) :: F) _ _)).
  {
    constructor; auto. constructor. clear -H3. induction l; simpl; inv H3; constructor; auto.
  }
  {
    destruct H0 as [k D].
    simpl. destruct l.
    * eexists. constructor. auto. constructor. econstructor. congruence.
      reflexivity. simpl.
      rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r.
      rewrite subst_comp_exp in D. rewrite <- convert_map.
      2: simpl_convert_length;slia.
      rewrite scons_substcomp_list in D.
      rewrite app_nil_r in *. eassumption.
    * eexists. simpl. constructor; auto. constructor.
      constructor. congruence. inv H3. constructor; auto.
      eapply step_term_term_plus. apply params_eval_create. assumption.
      simpl. rewrite Nat.eqb_refl.
      rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r.
      rewrite subst_comp_exp in D. rewrite <- convert_map.
      2: simpl_convert_length;slia.
      rewrite scons_substcomp_list, substcomp_id_l in D.
      rewrite map_app in D. rewrite (vmap_ignores_sub (v::l)) in D.
      2: now constructor. exact D.
  }
  destruct H1 as [k D]. simpl in D. inv D. destruct l.
  * inv H5. inv H8. simpl in H10.
    rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r in H10.
    rewrite subst_comp_exp. rewrite <- convert_map in H10.
    2: simpl_convert_length;slia.
    rewrite scons_substcomp_list.
    rewrite app_nil_r in *. eexists. eassumption.
  * inv H5. inv H8. inv H11. eapply term_step_term in H6.
    2: apply params_eval_create. simpl in H6. rewrite Nat.eqb_refl in H6.
    rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r in H6.
    rewrite subst_comp_exp. rewrite <- convert_map in H6.
    2: simpl_convert_length;slia.
    rewrite scons_substcomp_list, substcomp_id_l.
    rewrite map_app. rewrite (vmap_ignores_sub (v::l)).
    2: assumption. eexists. exact H6. now inv H3.
Qed.

(*
Lemma Erel_Clos_compat_reverse :
  forall Γ b1 b2 ext1 ext2 id1 id2 p1 p2, p1 = p2 -> id1 = id2 ->
    Erel_open Γ (`VClos ext1 id1 p1 b1) (`VClos ext2 id2 p2 b2) ->
    (* Erel_open (p1 + Γ) (b1.[list_subst (convert_to_closlist ext1) idsubst])
                       (b2.[list_subst (convert_to_closlist ext1) idsubst]) *)
    forall m ξ₁ ξ₂ l₁ l₂, Grel m Γ ξ₁ ξ₂ -> list_biforall (Vrel m) l₁ l₂ ->
      length l₁ = p1 ->
      Erel m (b1.[list_subst (convert_to_closlist ext1 ++ l₁) idsubst].[ξ₁])
             (b2.[list_subst (convert_to_closlist ext2 ++ l₂) idsubst].[ξ₂]).
Proof.
  intros. subst.
  assert (VALCLOSED (VClos ext1 id2 (length l₁) b1).[ξ₁]ᵥ /\
          VALCLOSED (VClos ext2 id2 (length l₁) b2).[ξ₂]ᵥ) as [Hcl1 Hcl2]. {
    apply Erel_open_scope in H1. destruct H1. inv H. inv H0.
    split; apply -> subst_preserves_scope_val; eauto; apply H2.
  }
  split. 2: split.
  (* scopes *)
  1-2: simpl in *; destruct_scopes; rewrite map_length in *.
  1-2: rewrite subst_comp_exp.
  {
    rewrite subst_comm, <- subst_comp_exp. simpl_convert_length.
    apply -> subst_preserves_scope_exp; eauto.
    apply scoped_list_subscoped_eq; auto.
    now rewrite map_length, app_length, map_length.
    rewrite map_app. apply Forall_app. split. 2: apply biforall_vrel_closed in H3; now rewrite vmap_ignores_sub.
    epose proof (closlist_scope _ (map (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext1 + ls) ξ₁]))
               ext1) _).
    Unshelve.
      3: {
        intros. rewrite map_length in H. apply H6 in H.
        rewrite map_length. exact H.
      }
    unfold convert_to_closlist in H. rewrite map_map in *.
    assert (
    (fun x : nat * nat * Exp =>
          let
          '(id, vc, e) :=
           let '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext1 + ls) ξ₁]) in
           VClos
             (map (fun '(i0, ls, x0) => (i0, ls, x0.[upn (Datatypes.length ext1 + ls) ξ₁]))
                ext1) id vc e)
     = (fun x : nat * nat * Exp => (let '(id, vc, e) := x in VClos ext1 id vc e).[ξ₁]ᵥ)
     ). {
      clear. extensionality x. destruct x, p. now simpl.
    }
    rewrite H0 in H. assumption.
  }
  (* boiler plate code for ext2 *)
  {
    apply biforall_length in H3 as H3'. rewrite H3' in *.
    rewrite subst_comm, <- subst_comp_exp. simpl_convert_length.
    apply -> subst_preserves_scope_exp; eauto.
    apply scoped_list_subscoped_eq; auto.
    now rewrite map_length, app_length, map_length.
    rewrite map_app. apply Forall_app. split. 2: apply biforall_vrel_closed in H3;now rewrite vmap_ignores_sub.
    epose proof (closlist_scope _ (map (fun '(i0, ls, x) => (i0, ls, x.[upn (Datatypes.length ext2 + ls) ξ₂]))
               ext2) _).
    Unshelve.
      3: {
        intros. rewrite map_length in H. apply H5 in H.
        rewrite map_length. exact H.
      }
    unfold convert_to_closlist in H. rewrite map_map in *.
    assert (
    (fun x : nat * nat * Exp =>
          let
          '(id, vc, e) :=
           let '(i0, ls, x0) := x in (i0, ls, x0.[upn (Datatypes.length ext2 + ls) ξ₂]) in
           VClos
             (map (fun '(i0, ls, x0) => (i0, ls, x0.[upn (Datatypes.length ext2 + ls) ξ₂]))
                ext2) id vc e)
     = (fun x : nat * nat * Exp => (let '(id, vc, e) := x in VClos ext2 id vc e).[ξ₂]ᵥ)
     ). {
      clear. extensionality x. destruct x, p. now simpl.
    }
    rewrite H0 in H. assumption.
  }
  (* evaluation *)
  intros. clear Hcl1 Hcl2. apply Erel_open_scope in H1 as Hscopes.
  assert (SUBSCOPE Γ + 0 ⊢ ξ₁ ∷ 0) by (rewrite Nat.add_0_r; apply H2).
  assert (SUBSCOPE Γ + 0 ⊢ ξ₂ ∷ 0) by (rewrite Nat.add_0_r; apply H2).
  apply subscoped_add_list in H4, H5.
  destruct H4 as [l₁' [ξ₁' H4]], H5 as [l₂' [ξ₂' H5]]. repeat destruct_hyps.
  subst.
  pose proof H2 as HGrel.

  replace ξ₁' with (idsubst >> ξ₁') in * by auto.
  replace ξ₂' with (idsubst >> ξ₂') in * by auto.
  replace l₁' with (map (substVal ξ₁') l₁') in H0 by now rewrite vmap_ignores_sub.
  replace l₂' with (map (substVal ξ₂') l₂') by now rewrite vmap_ignores_sub.
  repeat rewrite <- (scons_substcomp_list) in *.
  repeat rewrite <- subst_comp_exp in *.
  assert (list_biforall (Vrel m) l₁' l₂'). {
    rewrite indexed_to_biforall with (d1 := VNil) (d2 := VNil). split. 2: auto.
    intros. destruct HGrel as [_ [_ HGrel]]. specialize (HGrel i ltac:(lia)).
    do 2 rewrite list_subst_lt in HGrel. 2-4: lia. auto.
  }
  clear HGrel H2.

  rewrite (eclosed_ignores_sub _ ξ₁') in *.
  rewrite (eclosed_ignores_sub _ ξ₂') in *.
  all: clear dependent ξ₁'; clear dependent ξ₂'.
  2-3: admit.
  apply Rrel_valseq_compat_closed in H3 as Hrel. destruct Hrel as [_ [_ Hrel]].
  
  epose proof (| FLet  :: FTry 1 (EApp (`VVar 0) (map VVal vl1)) 0 (ETuple (map VVal vl1))::F1| ? ↓).
  
  unshelve (epose proof (Hrel (FApp1 (map VVal l) :: F1) _ _)).
  {
    constructor; auto. constructor. clear -H3. induction l; simpl; inv H3; constructor; auto.
  }
  {
    destruct H0 as [k D].
    simpl. destruct l.
    * eexists. constructor. auto. constructor. econstructor. congruence.
      reflexivity. simpl.
      rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r.
      rewrite subst_comp_exp in D. rewrite <- convert_map.
      2: simpl_convert_length;slia.
      rewrite scons_substcomp_list in D.
      rewrite app_nil_r in *. eassumption.
    * eexists. simpl. constructor; auto. constructor.
      constructor. congruence. inv H3. constructor; auto.
      eapply step_term_term_plus. apply params_eval_create. assumption.
      simpl. rewrite Nat.eqb_refl.
      rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r.
      rewrite subst_comp_exp in D. rewrite <- convert_map.
      2: simpl_convert_length;slia.
      rewrite scons_substcomp_list, substcomp_id_l in D.
      rewrite map_app in D. rewrite (vmap_ignores_sub (v::l)) in D.
      2: now constructor. exact D.
  }
  destruct H1 as [k D]. simpl in D. inv D. destruct l.
  * inv H5. inv H8. simpl in H10.
    rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r in H10.
    rewrite subst_comp_exp. rewrite <- convert_map in H10.
    2: simpl_convert_length;slia.
    rewrite scons_substcomp_list.
    rewrite app_nil_r in *. eexists. eassumption.
  * inv H5. inv H8. inv H11. eapply term_step_term in H6.
    2: apply params_eval_create. simpl in H6. rewrite Nat.eqb_refl in H6.
    rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r in H6.
    rewrite subst_comp_exp. rewrite <- convert_map in H6.
    2: simpl_convert_length;slia.
    rewrite scons_substcomp_list, substcomp_id_l.
    rewrite map_app. rewrite (vmap_ignores_sub (v::l)).
    2: assumption. eexists. exact H6. now inv H3.
Qed.

Lemma ERel_Val_compat_closed_reverse :
  forall (v v' : Val) Γ, Erel_open Γ (`v) (`v') -> Vrel_open Γ v v'.
Proof.
  valinduction; try destruct v'; intros; auto; intro m; intros;
  apply Rrel_exp_compat, CIU_iff_Rrel in H as Hcontra;
  epose proof (Hcontra_for_vars := Hcontra);
  specialize (Hcontra (default_subst VNil) ltac:(auto)) as [_ [_ Hcontra]].

  (* VNil-Var/FunId combination needs special care: *)
  5-6: clear Hcontra; specialize (Hcontra_for_vars (default_subst (VCons VNil VNil)) ltac:(auto)) as [_ [_ Hcontra]].

  1-7: epose proof (Hcontra [FCase1 [([PNil], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr;
       destruct n; congruence.
  1,3-8: epose proof (Hcontra [FCase1 [([PLit l], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr;
       destruct n; congruence.
  2-3,5-9: epose proof (Hcontra [FCase1 [([PCons PVar PVar], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr;
       destruct n; congruence.
  3-5,7-10: epose proof (Hcontra [FCase1 [([PTuple (repeat PVar (length l))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr;
       destruct n; congruence.
  4-7,8-11: epose proof (Hcontra [FCase1 [([PMap (repeat (PVar, PVar) (length l))], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr.
  5: destruct n; congruence.
  Unshelve. (* evaluations: *)
    29-64:
      apply Rrel_open_scope in H as [Hsc1 Hsc2]; apply redex_val_scope in Hsc1, Hsc2; eexists; simpl;
      econstructor; [ auto; shelve |];
      econstructor; [ try apply match_pattern_list_tuple_vars_map;
                      try apply match_pattern_list_map_vars_map;
                      simpl;
                      try rewrite Lit_eqb_refl; try reflexivity |];
      econstructor; [ auto; shelve |];
      econstructor; [ try apply match_pattern_list_tuple_vars_map;
                      try apply match_pattern_list_map_vars_map;
                      simpl;
                      try rewrite Lit_eqb_refl; try reflexivity |]; simpl;
      econstructor; auto; constructor; auto.
    Unshelve. (* scopes: *)
      29-86: cbn; auto.
      29-35: constructor; destruct_scopes; apply -> subst_preserves_scope_val; eauto.
      29-35: clear -Hsc1; replace (VTuple (map (fun x => x.[default_subst VNil]ᵥ) l))
                            with ((VTuple l).[default_subst VNil]ᵥ) by auto;
            apply -> subst_preserves_scope_val; eauto.
      29-36: clear -Hsc1; replace (VMap (map (fun '(x, y) => (x.[default_subst VNil]ᵥ, y.[default_subst VNil]ᵥ)) l))
                            with ((VMap l).[default_subst VNil]ᵥ) by auto;
            apply -> subst_preserves_scope_val; eauto.

    5, 13:
      clear Hcontra; specialize (Hcontra_for_vars (default_subst (VCons VNil VNil)) ltac:(auto)) as [_ [_ Hcontra]];
     epose proof (Hcontra [FCase1 [([PCons PVar PVar], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr.
    5-8,11-15, 18: epose proof (Hcontra [FCase1 [([PNil], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr.
    Unshelve.
     17-28: cbn. 24-28,18: destruct n.
     17-28:
      apply Rrel_open_scope in H as [Hsc1 Hsc2]; apply redex_val_scope in Hsc1, Hsc2; eexists; simpl;
      econstructor; [ auto; shelve |];
      econstructor; [ try apply match_pattern_list_tuple_vars_map;
                      try apply match_pattern_list_map_vars_map;
                      simpl;
                      try rewrite Lit_eqb_refl; try reflexivity |];
      econstructor; [ auto; shelve |];
      econstructor; [ try apply match_pattern_list_tuple_vars_map;
                      try apply match_pattern_list_map_vars_map;
                      simpl;
                      try rewrite Lit_eqb_refl; try reflexivity |]; simpl;
      econstructor; auto; constructor; auto.
    Unshelve.
      17-28: cbn; auto.

  (* Only similary value pairs are left: *)
  * epose proof (Hcontra [FCase1 [([PLit l], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr.
    destruct Lit_beq eqn:EQ. 2: congruence.
    apply Lit_eqb_eq in EQ. subst. auto.
    Unshelve.
      econstructor. auto. simpl.
      econstructor. auto.
      econstructor. cbn. rewrite Lit_eqb_refl. reflexivity.
      simpl. econstructor. auto.
      econstructor. cbn. rewrite Lit_eqb_refl. reflexivity.
      simpl. econstructor. auto.
      constructor. auto.
  (* Lists *)
  * simpl. choose_compat_lemma.
    - eapply IHv1. 2: eassumption.
      apply Rrel_exp_compat_reverse.
      apply CIU_iff_Rrel in H. apply CIU_iff_Rrel.
      clear -H.
      intros ? ?. specialize (H _ H0) as [Hsc1 [Hsc2 Hrel]].
      inv Hsc1. inv Hsc2. destruct_scopes. split. 2: split.
      1-2: scope_solver.
      intros.
      epose proof (Hrel (FCase1 [([PCons PVar PVar], `ttrue, `VVar 0);([PVar], `ttrue , °inf)] :: F) _ _) as [k D].
      simpl in D. do 3 deriv; inv H15. simpl in *.
      do 2 deriv. inv H15. simpl in *. eexists. eassumption.
      Unshelve.
        constructor; auto; scope_solver.
        destruct H1 as [k D]. eexists. simpl. econstructor. auto.
        econstructor. reflexivity. simpl.
        econstructor. auto.
        econstructor. reflexivity.
        simpl. exact D.
    - eapply IHv2. 2: eassumption.
      apply Rrel_exp_compat_reverse.
      apply CIU_iff_Rrel in H. apply CIU_iff_Rrel.
      clear -H.
      intros ? ?. specialize (H _ H0) as [Hsc1 [Hsc2 Hrel]].
      inv Hsc1. inv Hsc2. destruct_scopes. split. 2: split.
      1-2: scope_solver.
      intros.
      epose proof (Hrel (FCase1 [([PCons PVar PVar], `ttrue, `VVar 1);([PVar], `ttrue , °inf)] :: F) _ _) as [k D].
      simpl in D. do 3 deriv; inv H15. simpl in *.
      do 2 deriv. inv H15. simpl in *. eexists. eassumption.
      Unshelve.
        constructor; auto; scope_solver.
        destruct H1 as [k D]. eexists. simpl. econstructor. auto.
        econstructor. reflexivity. simpl.
        econstructor. auto.
        econstructor. reflexivity.
        simpl. exact D.
  (* Tuples *)
  * apply Rrel_exp_compat_reverse, Erel_Tuple_compat_reverse in H.
    simpl. choose_compat_lemma.
    clear -H IHv H0. apply biforall_length in H as Hlen.
    do 2 rewrite map_length in Hlen. apply forall_biforall with (d1 := VNil) (d2 := VNil).
    now do 2 rewrite map_length. intros.
    eapply biforall_forall with (i := i) (d1 := `VNil) (d2 := `VNil) in H.
    2: now rewrite map_length in *.
    rewrite indexed_to_forall in IHv. rewrite map_length in H1.
    do 2 rewrite map_nth in H. do 2 rewrite map_nth with (d := VNil).
    apply (IHv i H1 _ _ H). assumption.
  (* Maps *)
  * apply Rrel_exp_compat_reverse, Erel_Map_compat_reverse in H.
    simpl. choose_compat_lemma.
    clear -H IHv H0. apply biforall_length in H as Hlen.
    do 2 rewrite map_length in Hlen. apply forall_biforall with (d1 := (VNil, VNil)) (d2 := (VNil, VNil)).
    now do 2 rewrite map_length. intros.
    eapply biforall_forall with (i := i) (d1 := (`VNil, `VNil)) (d2 := (`VNil, `VNil)) in H.
    2: now rewrite map_length in *.
    rewrite indexed_to_forall with (def := (VNil, VNil)) in IHv.
    rewrite map_length in H1.
    do 2 rewrite map_nth with (d := (VNil, VNil)) in H.
    do 2 rewrite map_nth with (d := (VNil, VNil)).
    specialize (IHv i H1). destruct IHv.
    destruct nth, nth. simpl in *. destruct H.
    split. eapply H2; eassumption. eapply H3; eassumption.
  (* var + var *)
  (* TODO: the following 4 cases are pretty much the same *)
  * assert (n = n0). {
      clear -Hcontra_for_vars.
      epose proof (Hcontra_for_vars (fun x => if Nat.eq_dec x n
                                              then inl (VLit 1%Z)
                                              else
                                                if Nat.eq_dec x n0
                                                then inl (VLit 2%Z)
                                                else inl (VLit 3%Z)) _) as [_ [_ Hrel]].
    Unshelve.
      2: { (*scope*)
        unfold subscoped. intros. repeat destruct Nat.eq_dec; auto.
      }
      simpl in Hrel.
      destruct Nat.eq_dec. 2: congruence. destruct Nat.eq_dec. auto.
      destruct Nat.eq_dec. 2: congruence.
      epose proof (Hrel [FCase1 [([PLit 1%Z], `ttrue, `VNil);([PVar], `ttrue, °inf)]] _ _) as [k D].
      repeat deriv. inv H8. 2: inv H7. simpl in H10. repeat deriv.
      now apply inf_diverges in H11.
    Unshelve.
      {
        scope_solver.
      }
      {
        eexists. repeat econstructor.
      }
    }
    subst.
    assert (n0 < Γ). {
      apply Rrel_open_scope_l in H.
      now destruct_scopes.
    }
    apply (Vrel_Var_compat Γ n0 H1 _ _ _ H0).
  (* var + funid *)
  * destruct n0 as [n0 a].
    assert (n = n0). {
      clear -Hcontra_for_vars.
      epose proof (Hcontra_for_vars (fun x => if Nat.eq_dec x n
                                              then inl (VLit 1%Z)
                                              else
                                                if Nat.eq_dec x n0
                                                then inl (VLit 2%Z)
                                                else inl (VLit 3%Z)) _) as [_ [_ Hrel]].
    Unshelve.
      2: { (*scope*)
        unfold subscoped. intros. repeat destruct Nat.eq_dec; auto.
      }
      simpl in Hrel.
      destruct Nat.eq_dec. 2: congruence. destruct Nat.eq_dec. auto.
      destruct Nat.eq_dec. 2: congruence.
      epose proof (Hrel [FCase1 [([PLit 1%Z], `ttrue, `VNil);([PVar], `ttrue, °inf)]] _ _) as [k D].
      repeat deriv. inv H8. 2: inv H7. simpl in H10. repeat deriv.
      now apply inf_diverges in H11.
    Unshelve.
      {
        scope_solver.
      }
      {
        eexists. repeat econstructor.
      }
    }
    subst.
    assert (n0 < Γ). {
      apply Rrel_open_scope_l in H.
      now destruct_scopes.
    }
    apply (Vrel_Var_FunId_compat Γ n0 _ H1 _ _ _ H0).
  (* funid + var *)
  * destruct n as [n a].
    assert (n = n0). {
      clear -Hcontra_for_vars.
      epose proof (Hcontra_for_vars (fun x => if Nat.eq_dec x n
                                              then inl (VLit 1%Z)
                                              else
                                                if Nat.eq_dec x n0
                                                then inl (VLit 2%Z)
                                                else inl (VLit 3%Z)) _) as [_ [_ Hrel]].
    Unshelve.
      2: { (*scope*)
        unfold subscoped. intros. repeat destruct Nat.eq_dec; auto.
      }
      simpl in Hrel.
      destruct Nat.eq_dec. 2: congruence. destruct Nat.eq_dec. auto.
      destruct Nat.eq_dec. 2: congruence.
      epose proof (Hrel [FCase1 [([PLit 1%Z], `ttrue, `VNil);([PVar], `ttrue, °inf)]] _ _) as [k D].
      repeat deriv. inv H8. 2: inv H7. simpl in H10. repeat deriv.
      now apply inf_diverges in H11.
    Unshelve.
      {
        scope_solver.
      }
      {
        eexists. repeat econstructor.
      }
    }
    subst.
    assert (n0 < Γ). {
      apply Rrel_open_scope_l in H.
      now destruct_scopes.
    }
    apply (Vrel_FunId_Var_compat Γ n0 _ H1 _ _ _ H0).
  (* funid + funid *)
  * destruct n as [n a1]. destruct n0 as [n0 a2].
    assert (n = n0). {
      clear -Hcontra_for_vars.
      epose proof (Hcontra_for_vars (fun x => if Nat.eq_dec x n
                                              then inl (VLit 1%Z)
                                              else
                                                if Nat.eq_dec x n0
                                                then inl (VLit 2%Z)
                                                else inl (VLit 3%Z)) _) as [_ [_ Hrel]].
    Unshelve.
      2: { (*scope*)
        unfold subscoped. intros. repeat destruct Nat.eq_dec; auto.
      }
      simpl in Hrel.
      destruct Nat.eq_dec. 2: congruence. destruct Nat.eq_dec. auto.
      destruct Nat.eq_dec. 2: congruence.
      epose proof (Hrel [FCase1 [([PLit 1%Z], `ttrue, `VNil);([PVar], `ttrue, °inf)]] _ _) as [k D].
      repeat deriv. inv H8. 2: inv H7. simpl in H10. repeat deriv.
      now apply inf_diverges in H11.
    Unshelve.
      {
        scope_solver.
      }
      {
        eexists. repeat econstructor.
      }
    }
    subst.
    assert (n0 < Γ). {
      apply Rrel_open_scope_l in H.
      now destruct_scopes.
    }
    apply (Vrel_FunId_compat Γ n0 _ _ H1 _ _ _ H0).
  (* Closure + something <- always inequivalent! 
     TODO: boiler plate code: The following 7 cases are pretty much the same *)
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  * destruct params.
    (* we have to make sure, that the number of parameters differ *)
    - epose proof (Hcontra [FApp1 [`VNil];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. destruct n. repeat deriv. cbn in H11. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H13. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H13. simpl in H15. repeat deriv. 2: { inv H12. }
      now apply inf_diverges in H16.
    - epose proof (Hcontra [FApp1 [];FTry 1 (`VNil) 3 (ECase (`VVar 1) [
        ([PLit "badarity"%string], `ttrue, `VNil);
        ([PVar], `ttrue, °inf)
      ])] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      cbn in H1. destruct n. repeat deriv. cbn in H9. repeat deriv.
      2: { now specialize (H6 _ _ _ _ eq_refl). }
      repeat deriv. inv H12. 2: { inv H1. } inv H7. cbn in H6.
      repeat deriv. inv H12. simpl in H14. repeat deriv. 2: { inv H11. }
      now apply inf_diverges in H15.
    Unshelve.
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
    {
      eexists. apply Rrel_open_scope_l in H. 
      inv H. inv H2. eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H3.
      2: auto.
      repeat (econstructor; eauto). congruence.
    }
  (* Closure + closure *)
  * clear Hcontra_for_vars.
    apply Rrel_open_scope in H as HH. destruct HH as [HH1 HH2].
    inv HH1. inv HH2. inv H2. inv H3.
    eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H5 as H5'. 2: {
      eauto.
    }
    eapply subst_preserves_scope_val with (ξ := default_subst VNil) in H4 as H4'. 2: {
      eauto.
    }
    eapply subst_preserves_scope_val with (ξ := ξ₁) in H5. 2: apply H0.
    eapply subst_preserves_scope_val with (ξ := ξ₂) in H4. 2: apply H0.
    rename H5 into Hcl1. rename H4 into Hcl2.

    (* First, we show that the closures have the same arity with erlang:fun_info *)
    assert (params = params0). {
      epose proof (Hcontra [FParams (ICall "erlang" "fun_info") [] [`VLit "arity"%string];FCase1 [([PLit (Z.of_nat params)], `ttrue, `VNil);([PVar], `ttrue, °inf)]] ltac:(scope_solver) _) as Hcontra; repeat deriv.
      simpl in H1. repeat deriv. simpl in H10. deriv.
      - simpl in H11. destruct (Z.of_nat params0 =? Z.of_nat params)%Z eqn:P; inv H11.
        now apply Z.eqb_eq, Znat.Nat2Z.inj in P.
      - simpl in H12. deriv. inv H13. 2: inv H10.
        inv H6. now apply inf_diverges in H14. 
      Unshelve.
        congruence.
        auto.
        repeat (econstructor; eauto).
        simpl. rewrite Z.eqb_refl. reflexivity.
        simpl. rewrite Z.eqb_refl. reflexivity.
    }

    (* Next we show that the identifiers are also equal using erlang:== *)
    assert (id = id0). {
      epose proof (Hcontra [FParams (ICall "erlang" "==") [] [` (VClos ext id params0 e).[default_subst VNil]ᵥ];FCase1 [([PLit "true"%string], `ttrue, `VNil);([PVar], `ttrue, °inf)]] _ _) as Hcontra; deriv.
      cbn in H2. deriv. simpl in H5. do 3 deriv. cbn in H10.
      break_match_hyp. now apply Nat.eqb_eq in Heqb.
      repeat deriv; inv H11; inv H10. simpl in *.
      repeat deriv. now apply inf_diverges in H12.
    Unshelve.
      - do 2 scope_solver_step. 1-2,4-6: auto; scope_solver.
        congruence. constructor; auto. constructor. subst. assumption.
      - simpl. subst. repeat (econstructor; eauto). cbn.
        rewrite Nat.eqb_refl. repeat econstructor.
    }

      (* Starting the proof of Vrel clos1 clos2: *)
    subst. clear Hcontra H5' H4'.
    apply CIU_iff_Rrel in H. eapply CIU_Clos_compat_reverse in H.
      
      
      
      
      
      
      
      
      
      
      
      
      

      rewrite Vrel_Fix_eq. simpl. intuition; auto.

      (* Vrel_clos_compat_reverse *)
      assert (Erel_open (params0 + Γ) (e.[list_subst
                                                 (convert_to_closlist ext) idsubst]) e0.[list_subst
                                                   (convert_to_closlist ext0) idsubst]). {
        clear -H.
        apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
        apply CIU_iff_Rrel in H.
        intros ??. apply subscoped_add_list in H0 as H0'.
        destruct H0' as [vl [ξ' EQ]]. intuition. subst ξ.
        simpl.
        split. 2: split.
        1-2: constructor; apply -> subst_preserves_scope_exp; eauto.
        1-2: apply CIU_open_scope in H as [? ?]; destruct_scopes.
        1: {
          apply -> subst_preserves_scope_exp; eauto.
          rewrite <- Nat.add_assoc.
          apply scoped_list_subscoped_eq; auto. unfold convert_to_closlist.
          now rewrite map_length.
          apply closlist_scope. intros.
          apply H6 in H. eapply loosen_scope_exp. 2: eassumption.
          lia.
        }
        1: {
          apply -> subst_preserves_scope_exp; eauto.
          rewrite <- Nat.add_assoc.
          apply scoped_list_subscoped_eq; auto. unfold convert_to_closlist.
          now rewrite map_length.
          apply closlist_scope. intros.
          apply H7 in H. eapply loosen_scope_exp. 2: eassumption.
          lia.
        }
        intros. apply CIU_open_scope in H as H'.
        Search subst eq.
        specialize (H ξ' H5) as [Hcl1 [Hcl2 Hrel]].
        epose proof (Hrel (FApp1 (map VVal vl)::F) _ _) as [k D].
        Unshelve.
        2: {
          constructor; auto. constructor. clear - H2.
          induction vl; constructor; inv H2; auto.
        }
        2: {
          eexists. simpl. econstructor. admit.
          econstructor. destruct vl.
          - econstructor. congruence. reflexivity. simpl.
            rewrite <- H3. simpl.
            rewrite subst_comp_exp in H4. admit.
          -
        }
        clear -D Hcl1 Hcl2 H2 H3 H'.
        simpl in D. inv D. inv H4. inv H6.
        * destruct vl; inv H4. inv H8.
          eapply term_step_term in H4. 2: apply params_eval_create.
          2: now inv H2.
          simpl in H4. rewrite Nat.eqb_refl in H4.
          rewrite subst_comp_exp in H4.
          rewrite substcomp_list_eq, substcomp_id_r in H4.
          2: simpl_convert_length; simpl; lia.
          rewrite subst_comp_exp. rewrite <- list_subst_app.
          2: {
            apply closlist_scope. intros.
            destruct H' as [? ?]; destruct_scopes.
            apply H10 in H. eapply loosen_scope_exp. 2: eassumption.
            lia.
          }
          replace (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext0 + ls) ξ']))
                 ext0) with (map id ext0) in H4.
          replace (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext0 + ls) idsubst]))
            ext0) with (map id ext0).
          eexists. admit.
          admit. (* scope does not allow this *)
          admit. (* idsubst *)
        * destruct vl. 2: inv H3.
          simpl in H9. rewrite subst_comp_exp in H9.
          rewrite substcomp_list_eq, substcomp_id_r in H9.
          2: simpl_convert_length; simpl; lia.
          rewrite subst_comp_exp. rewrite <- list_subst_app.
          2: apply closlist_scope; admit.
          replace (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext0 + ls) ξ']))
                 ext0) with (map id ext0) in H9.
          replace (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length ext0 + ls) idsubst]))
            ext0) with (map id ext0).
          eexists. eassumption.
          admit. (* scope does not allow this *)
          admit. (* idsubst *)
      }
      do 2 rewrite subst_comp_exp.
      rewrite substcomp_list_eq, substcomp_list_eq.
      2-3: simpl_convert_length; apply biforall_length in H2; lia.
      Search list_subst ">>".
      Check scons_substcomp_list.
      rewrite scons_substcomp_list. *)
      
      
      
      
      
      
      (*
      assert (Erel_open Γ (e.[list_subst
                                                 ((convert_to_closlist ext) ++ vl1) idsubst]) e0.[list_subst
                                                   ((convert_to_closlist
                                                      ext0) ++ vl2) idsubst]).
      {
        Search Erel_open ELet.
      
        apply Rrel_exp_compat_reverse, CIU_iff_Rrel.
        clear H0 Hcl1 Hcl2.
        intros ??.
        epose proof (Grel_Fundamental _ _ H0).
        apply CIU_iff_Rrel_closed. intros.
        
        split. 2: split.
        1-2: admit.
        intros.
        assert (VALCLOSED (VClos ext id0 params0 e).[ξ]ᵥ /\ VALCLOSED (VClos ext0 id0 params0 e0).[ξ]ᵥ) as [Hclos1 Hclos2]. {
          clear -H H0.
          apply Rrel_open_scope in H as [H1 H2].
          inv H1. inv H2. inv H3. inv H1.
          split; apply -> subst_preserves_scope_val; eauto.
        }

        assert (Heval_e : | FTry 1 (° EApp (` VVar 0) (map VVal vl1)) 0 (° ETuple (map VVal vl1)) :: F1,
     ` (VClos ext id0 params0 e).[ξ]ᵥ | 5 + 2 * length vl1 + 1 + m2 ↓). {
          simpl. econstructor; auto. constructor; auto. simpl.
          replace (map
       (fun x : Exp =>
        x.[VClos
             (map (fun '(i, ls, x0) => (i, ls, x0.[upn (Datatypes.length ext + ls) ξ]))
                ext) id0 params0 e.[upn (Datatypes.length ext + params0) ξ]/])
       (map VVal vl1))
             with (map VVal vl1).
          2: {
            clear -H2. rewrite map_map. simpl.
            apply biforall_vrel_closed in H2 as [H1 _].
            apply map_ext_Forall. induction vl1; inv H1; constructor; auto.
            now rewrite vclosed_ignores_sub.
          }
          do 2 constructor. auto.
          constructor. destruct vl1.
          * simpl. econstructor. congruence. reflexivity. simpl.
            break_match_goal. 2: apply Nat.eqb_neq in Heqb; simpl in H1; lia.
            rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r.
            2: simpl_convert_length; lia.
            simpl in H5. rewrite subst_comp_exp in H5.
            rewrite scons_substcomp_list, substcomp_id_l in H5.
            
            (* TODO: separate this:!!! *)
            assert (Hthm : forall l ξ, map (substVal ξ) (convert_to_closlist l) =
                                convert_to_closlist (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length l + ls) ξ])) l)). {
              clear. intros. unfold convert_to_closlist.
              do 2 rewrite map_map. f_equal.
              extensionality x. destruct x, p. now simpl.
            }
            rewrite <- Hthm. rewrite app_nil_r in *. assumption.
          * simpl. constructor. congruence.
            simpl. change clock to (S ((1 + 2 * length vl1) + m2)).
            inv H2. constructor.
            now apply Vrel_closed_l in H8.
            eapply step_term_term_plus. repeat rewrite map_map_subst.
            apply params_eval_create.
            { now apply biforall_vrel_closed in H10 as [H10 _]. }
            simpl. rewrite Nat.eqb_refl.

            rewrite subst_comp_exp, substcomp_list_eq, substcomp_id_r.
            2: simpl_convert_length; slia.
            simpl in H5. rewrite subst_comp_exp in H5.
            rewrite scons_substcomp_list, substcomp_id_l in H5.
            assert (Hthm : forall l ξ, map (substVal ξ) (convert_to_closlist l) =
                                convert_to_closlist (map (fun '(i, ls, x) => (i, ls, x.[upn (Datatypes.length l + ls) ξ])) l)). {
              clear. intros. unfold convert_to_closlist.
              do 2 rewrite map_map. f_equal.
              extensionality x. destruct x, p. now simpl.
            }
            rewrite <- Hthm.
            rewrite map_app in H5.
            replace (map (substVal ξ) (v :: vl1)) with (v :: vl1) in H5.
            2: {
              clear -H10 H8. simpl.
              apply Vrel_closed_l in H8.
              rewrite vclosed_ignores_sub; auto.
              rewrite vmap_ignores_sub; auto.
              now apply biforall_vrel_closed in H10.
            }
            assumption.
        }
        assert (Hrel : Frel (4 + 2 * length vl1 + 1 + m2) (* dirty trick here with 0 *)
          (FTry 1 (EApp (`VVar 0) (map VVal vl1)) 0 (ETuple (map VVal vl1))::F1)
          (FTry 1 (EApp (`VVar 0) (map VVal vl2)) 0 (ETuple (map VVal vl2))::F2)
            ). {
        clear -H2 H4.
        split. 2: split. 1-2: constructor; [constructor|apply H4].
        1-4: do 2 constructor; auto; apply indexed_to_forall; apply biforall_vrel_closed in H2; clear -H2.

        (* boiler plate codes: *)
        1-2: destruct H2 as [H2 _]; induction vl1; simpl; auto; inv H2; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        1-2: destruct H2 as [_ H2]; induction vl2; simpl; auto; inv H2; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        (****)

        split. 2: split.
        all: intros.
        * deriv. inv H. inv H10. inv H1. 2: { inv H10. }
          simpl in H11.
          deriv. deriv. deriv. inv H2.
          - deriv.
            simpl in Hmn.
            pose proof (Rel_create_result _ [] [] (IApp hd) (IApp hd') ltac:(auto) ltac:(constructor; eauto)).
            intuition.
            + repeat destruct_hyps.
              specialize (H k ltac:(lia)) as [Hrel [Eq1 Eq2]].
              rewrite Eq1 in H9. eapply Hrel in H9 as [kk D]. 2: reflexivity.
              2: eapply Frel_downclosed in H4; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite Eq2. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H2 in H9.
              eapply H4 in H9 as [kk D]. 2: lia. 2: eapply biforall_impl;[|eassumption]; intros; downclose_Vrel.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite H3. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H2 in H9.
              eapply H4 in H9 as [kk D]. 2: lia. 2: eapply Excrel_downclosed; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite H3. exact D.
              Unshelve. lia.
          - inv H8. inv H13.
            rewrite map_map, vclosed_ignores_sub in H7.
            2: now apply Vrel_closed_l in H.
            replace (map (fun x : Val => (` x).[hd/]) tl) with
                    (map VVal tl) in H7.
            2: {
              clear -H3. simpl.
              apply biforall_vrel_closed in H3 as [H3 _].
              induction tl; simpl; auto; inv H3.
              now rewrite IHtl, vclosed_ignores_sub.
            }
            eapply term_step_term in H7. 2: apply params_eval_create.
            2: now apply biforall_vrel_closed in H3.
            simpl app in H7.
            simpl in Hmn.
            assert (list_biforall (Vrel (k0 - (1 + 2 * Datatypes.length tl)))
                                  (hd0 :: tl) (hd'0 :: tl') ) as Hfinally.
            {
              constructor. downclose_Vrel.
              eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
            }
            epose proof (Rel_create_result_relaxed _ (hd0 :: tl) (hd'0 :: tl') (IApp hd) (IApp hd') Hfinally _). Unshelve.
            4: {
              split. 2: split.
              1-2: constructor; now apply Vrel_closed in H0.
              downclose_Vrel.
            }
            intuition.
            + repeat destruct_hyps. simpl in Hmn.
              specialize (H2 (k0 - (1 + 2 * Datatypes.length tl)) ltac:(lia)).
              destruct H2 as [Hrel [H1_1 H1_2]].
              rewrite H1_1 in H7. eapply Hrel in H7 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H3. simpl.
                apply biforall_vrel_closed in H3 as [_ H3].
                induction tl'; simpl; auto; inv H3.
                now rewrite IHtl', vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H3. simpl app. rewrite H1_2.
              exact D. lia. eapply Frel_downclosed. eassumption.
              Unshelve. lia. lia.
            + repeat destruct_hyps.
              rewrite H6 in H7. eapply H4 in H7 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H3. simpl.
                apply biforall_vrel_closed in H3 as [_ H3].
                induction tl'; simpl; auto; inv H3.
                now rewrite IHtl', vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H3. simpl app. rewrite H8.
              exact D. simpl in Hmn. lia.
              eapply biforall_impl. 2: eassumption.
              intros. downclose_Vrel.
              Unshelve. lia.
            + repeat destruct_hyps.
              rewrite H6 in H7. eapply H4 in H7 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H3. simpl.
                apply biforall_vrel_closed in H3 as [_ H3].
                induction tl'; simpl; auto; inv H3.
                now rewrite IHtl', vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H3. simpl app. rewrite H8.
              exact D. simpl in Hmn. lia.
              eapply Excrel_downclosed. eassumption.
              Unshelve. simpl in Hmn. lia.
            + lia.
            + lia.
        * inv H5. (* Having 0 params in `catch` is exploited here,
                     because we only want to evaluate the `of` subexpression
                     in this `try` expression.
                   *)
          specialize (H9 _ _ _ _ eq_refl). contradiction.
        * inv H4.
        
        
        
        
        }
        assert (Rrel_open Γ (RValSeq [VClos ext id0 params0 e])
                      (RValSeq [VClos ext0 id0 params0 e0])). { admit. }
        epose proof (H6 _ _ _ (H3 _)) as [Hcl1 [Hcl2 Hrel2]].
        inv Heval_e.
        epose proof (Hrel2 _ _ _ _ Hrel H11). Unshelve.
        3: reflexivity.
        admit.
      }
      specialize (H3 _ _ _ H0).
      do 2 rewrite subst_comp_exp.
      rewrite substcomp_list_eq.
      rewrite substcomp_list_eq.
      2-3: simpl_convert_length; apply biforall_length in H2; lia.
      do 2 rewrite substcomp_id_r.
      do 2 rewrite subst_comp_exp in H3.
      do 2 rewrite scons_substcomp_list in H3.
      do 2 rewrite substcomp_id_l in H3.
      do 2 rewrite map_app in H3.
      rewrite (vmap_ignores_sub vl1), (vmap_ignores_sub vl2) in H3.
      2-3: now apply biforall_vrel_closed in H2.
      unfold convert_to_closlist in *. repeat rewrite map_map in *.
      replace (fun x : nat * nat * Exp =>
                (let '(id, vc, e) := x in VClos ext id vc e).[ξ₁]ᵥ) with (fun x : nat * nat * Exp =>
           let
           '(id, vc, e1) :=
            let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length ext + ls) ξ₁]) in
            VClos
              (map (fun '(i, ls, x0) => (i, ls, x0.[upn (Datatypes.length ext + ls) ξ₁]))
                 ext) id vc e1) in H3.
      2: { clear. extensionality x. destruct x, p. simpl. auto. }
      replace (fun x : nat * nat * Exp =>
                 (let '(id, vc, e) := x in VClos ext0 id vc e).[ξ₂]ᵥ) with (fun x : nat * nat * Exp =>
            let
            '(id, vc, e1) :=
             let '(i, ls, x0) := x in (i, ls, x0.[upn (Datatypes.length ext0 + ls) ξ₂]) in
             VClos
               (map
                  (fun '(i, ls, x0) => (i, ls, x0.[upn (Datatypes.length ext0 + ls) ξ₂]))
                  ext0) id vc e1) in H3.
      2: { clear. extensionality x. destruct x, p. auto. }
      eapply Erel_downclosed in H3. apply H3.
      Unshelve. lia. *)
      
      
      
      
      
      
      
      
      
      (*
      split. 2: split.
      1-2: simpl in *; destruct_scopes; auto; admit.
      intros.
      (* IDEA: we use `try` to even out the evaluation counter for exceptions
          and correct application *)
      assert (Heval_e : | FTry 1 (° EApp (` VVar 0) (map VVal vl1)) 0 (° ETuple (map VVal vl1)) :: F1,
     ` (VClos ext id0 params0 e).[ξ₁]ᵥ | 5 + 2 * length vl1 + 1 + m1 ↓). {
        simpl. econstructor; auto. constructor; auto. simpl.
        replace (map (fun x : Exp => x.[VClos ext id0 params0 e/]) (map VVal vl1))
           with (map VVal vl1).
        2: {
          clear -H2. rewrite map_map. simpl.
          apply biforall_vrel_closed in H2 as [H1 _].
          apply map_ext_Forall. induction vl1; inv H1; constructor; auto.
          now rewrite vclosed_ignores_sub.
        }
        do 2 constructor. auto.
        constructor. destruct vl1.
        * simpl. econstructor. congruence. reflexivity. simpl.
          break_match_goal. 2: apply Nat.eqb_neq in Heqb; simpl in H1; lia.
          assumption.
        * simpl. constructor. congruence.
          simpl. change clock to (S ((1 + 2 * length vl1) + m1)).
          inv H2. constructor.
          apply Vrel_closed_l in H7. now rewrite vclosed_ignores_sub.
          eapply step_term_term_plus. repeat rewrite map_map_subst.
          erewrite <- (map_length _ vl1) at 1.
          apply params_eval_create.
          { apply biforall_vrel_closed in H9 as [H9 _]. clear -H9.
            rewrite indexed_to_forall with (def := VNil) in *. intros.
            specialize (H9 i ltac:(rewrite map_length in H; auto)).
            rewrite map_nth with (d := VNil). now rewrite vclosed_ignores_sub.
          }
          simpl. rewrite map_length, Nat.eqb_refl.
          rewrite vclosed_ignores_sub. 2: now apply Vrel_closed_l in H7.
          rewrite vmap_ignores_sub. 2: apply biforall_vrel_closed in H9; apply H9.
          assumption.
      }

      (* We assert that the frame stack with the `try` expressions are equivalent
        in as many steps that are needed to evaluate the closures. *)
      assert (Hrel : Frel (4 + 2 * length vl1 + 1 + m1) (* dirty trick here with 0 *)
          (FTry 1 (EApp (`VVar 0) (map VVal vl1)) 0 (ETuple (map VVal vl1))::F1)
          (FTry 1 (EApp (`VVar 0) (map VVal vl2)) 0 (ETuple (map VVal vl2))::F2)
            ). {
        clear Heval_e H4.
        split. 2: split. 1-2: constructor; [constructor|apply H3].
        1-4: do 2 constructor; auto; apply indexed_to_forall; apply biforall_vrel_closed in H2; clear -H2.

        (* boiler plate codes: *)
        1-2: destruct H2 as [H2 _]; induction vl1; simpl; auto; inv H2; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        1-2: destruct H2 as [_ H2]; induction vl2; simpl; auto; inv H2; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        (****)

        split. 2: split.
        all: intros.
        * deriv. inv H4. inv H13. inv H5. 2: { inv H13. }
          simpl in H14.
          deriv. deriv. deriv. inv H2.
          - deriv.
            simpl in Hmn1.
            pose proof (Rel_create_result _ [] [] (IApp hd) (IApp hd') ltac:(auto) ltac:(constructor; eauto)).
            intuition.
            + repeat destruct_hyps.
              specialize (H2 k ltac:(lia)) as [Hrel [Eq1 Eq2]].
              rewrite Eq1 in H11. eapply Hrel in H11 as [kk D]. 2: reflexivity.
              2: eapply Frel_downclosed in H3; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H1.
              constructor. econstructor. congruence. reflexivity.
              rewrite Eq2. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H4 in H11.
              eapply H3 in H11 as [kk D]. 2: lia. 2: eapply biforall_impl;[|eassumption]; intros; downclose_Vrel.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H1.
              constructor. econstructor. congruence. reflexivity.
              rewrite H6. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H4 in H11.
              eapply H3 in H11 as [kk D]. 2: lia. 2: eapply Excrel_downclosed; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H1.
              constructor. econstructor. congruence. reflexivity.
              rewrite H6. exact D.
              Unshelve. lia.
          - inv H10. inv H15.
            rewrite map_map in H9.
            rewrite vclosed_ignores_sub in H9. 2: now apply Vrel_closed_l in H4.
            replace (map (fun x : Val => (` x).[hd/]) tl) with
                    (map VVal tl) in H9.
            2: {
              clear -H6. simpl.
              apply biforall_vrel_closed in H6 as [H1 _].
              apply map_ext_Forall. induction tl; inv H1; constructor; auto.
              now rewrite vclosed_ignores_sub.
            }
            rewrite vclosed_ignores_sub in H7. 2: now apply Vrel_closed_l in H4.
            eapply term_step_term in H9. 2: apply params_eval_create.
            2: now apply biforall_vrel_closed in H6.
            simpl app in H9.
            simpl in Hmn1.
            assert (list_biforall (Vrel (k0 - (1 + 2 * Datatypes.length tl)))
                                  (hd0 :: tl) (hd'0 :: tl') ) as Hfinally.
            {
              constructor. downclose_Vrel.
              eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
            }
            epose proof (Rel_create_result_relaxed _ (hd0 :: tl) (hd'0 :: tl') (IApp hd) (IApp hd') Hfinally _). Unshelve.
            4: {
              split. 2: split.
              1-2: constructor; now apply Vrel_closed in H1.
              downclose_Vrel.
            }
            intuition.
            + repeat destruct_hyps. simpl in Hmn1.
              specialize (H2 (k0 - (1 + 2 * Datatypes.length tl)) ltac:(lia)).
              destruct H2 as [Hrel [H1_1 H1_2]].
              rewrite H1_1 in H9. eapply Hrel in H9 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H1.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H4.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H6. simpl.
                apply biforall_vrel_closed in H6 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H4.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H6. simpl app. rewrite H1_2.
              exact D. lia. eapply Frel_downclosed. eassumption.
              Unshelve. lia. lia.
            + repeat destruct_hyps.
              rewrite H8 in H9. eapply H3 in H9 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H1.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H4.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H6. simpl.
                apply biforall_vrel_closed in H6 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H4.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H6. simpl app. rewrite H10.
              exact D. simpl in Hmn1. lia.
              eapply biforall_impl. 2: eassumption.
              intros. downclose_Vrel.
              Unshelve. lia.
            + repeat destruct_hyps.
              rewrite H8 in H9. eapply H3 in H9 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H1.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H4.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H6. simpl.
                apply biforall_vrel_closed in H6 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H4.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H6. simpl app. rewrite H10.
              exact D. simpl in Hmn1. lia.
              eapply Excrel_downclosed. eassumption.
              Unshelve. simpl in Hmn1. lia.
            + lia.
            + lia.
        * inv H5. (* Having 0 params in `catch` is exploited here,
                     because we only want to evaluate the `of` subexpression
                     in this `try` expression.
                   *)
          specialize (H9 _ _ _ _ eq_refl). contradiction.
        * inv H4.
      }

      (* Finally, we combine the previous assertions with the closures
         being in Rrel (H2). *)
      clear H4.
      assert (Rrel_open Γ (RValSeq [VClos ext id0 params0 e])
                          (RValSeq [VClos ext0 id0 params0 e0])). {
        clear -H.
        apply CIU_iff_Rrel in H.
        assert (CIU_open Γ (RValSeq [VClos ext id0 params0 e])
                           (` VClos ext id0 params0 e)). {
          intros ??. assert (VALCLOSED (VClos ext id0 params0 e).[ξ]ᵥ). {
            specialize (H ξ H0) as [H _]. inv H. now inv H2.
          }
          apply CIU_eval.
          now apply H.
          eexists. split. do 2 constructor; auto.
          econstructor. simpl. constructor; auto.
          constructor.
        }
        assert (CIU_open Γ (` VClos ext0 id0 params0 e0)
                           (RValSeq [VClos ext0 id0 params0 e0])). {
          intros ??. assert (VALCLOSED (VClos ext0 id0 params0 e0).[ξ]ᵥ). {
            specialize (H ξ H1) as [_ [H _]]. inv H. now inv H3.
          }
          unshelve (eapply (proj1 (CIU_eval _ _ _ _))).
          now apply H.
          eexists. split. do 2 constructor; auto.
          econstructor. simpl. constructor; auto.
          constructor.
        }
        apply CIU_iff_Rrel.
        pose proof (CIU_transitive _ _ _ _ H0 H) as HH.
        now pose proof (CIU_transitive _ _ _ _ HH H1) as HHH.
      }
      clear H. inv Heval_e.
      epose proof (H4 _ _ ξ₂ _ ) as [_ [_ Hrel2]].
      epose proof (Hrel2 _ _ _ _ Hrel H8) as [k D].
      simpl in D. clear -D H7 H2. repeat deriv. simpl in H9.
      inv H9. inv H4. inv H3.
      
      
      rewrite map_map in H6.
      replace (map (fun x : Val => (` x).[VClos
                       (map
                          (fun '(i, ls, x0) =>
                           (i, ls, x0.[upn (Datatypes.length ext0 + ls) ξ₂])) ext0) id0
                       (Datatypes.length vl1)
                       e0.[upn (Datatypes.length ext0 + Datatypes.length vl1) ξ₂]/]) vl2) with
                      (map VVal vl2) in H6.
      2: {
        clear -H2. simpl.
        apply biforall_vrel_closed in H2 as [_ H2].
        apply map_ext_Forall. induction vl2; inv H2; constructor; auto.
        now rewrite vclosed_ignores_sub.
      }
      destruct vl2.
      - deriv. simpl in H10. apply biforall_length in H2. rewrite H2 in *.
        simpl in H10. eexists. eassumption.
      - deriv. deriv.
        eapply term_step_term in H4. 2: apply params_eval_create.
        2: {
          apply biforall_vrel_closed in H2 as [_ H2]. now inv H2.
        }
        simpl in H4. apply biforall_length in H2. rewrite H2 in *.
        simpl in H4. rewrite Nat.eqb_refl in H4. eexists. eassumption.
      - inv H.
  Unshelve.
    2: eassumption.
    
Abort.

(*
    (* closure - closure -> induction on m *)
  * inv Hcl1. inv Hcl2.

    (* First, we show that the closures have the same arity with erlang:fun_info *)
    assert (params = params0). {
      epose proof (H [FParams (ICall "erlang" "fun_info") [] [`VLit "arity"%string];FCase1 [([PLit (Z.of_nat params)], `ttrue, `VNil);([PVar], `ttrue, °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      simpl in H11. repeat deriv. all: inv H12.
      3: inv H11.
      1-2: destruct (Z.of_nat params0 =? Z.of_nat params)%Z eqn:P; inv H5.
      - apply Z.eqb_eq in P. now apply Znat.Nat2Z.inj in P.
      - simpl in H14. repeat deriv. now apply inf_diverges in H14. 
      Unshelve.
        congruence.
        auto.
        destruct_scopes. repeat econstructor; auto.
        simpl. rewrite Z.eqb_refl. reflexivity.
        simpl. rewrite Z.eqb_refl. reflexivity.
    }

    (* Next we show that the identifiers are also equal using erlang:== *)
    assert (id = id0). {
      inv H1. inv H2.
      epose proof (H [FParams (ICall "erlang" "==") [] [` VClos ext id params0 e];FCase1 [([PLit "true"%string], `ttrue, `VNil);([PVar], `ttrue, °inf)]] ltac:(scope_solver) _) as H0; repeat deriv.
      cbn in H11.
      break_match_hyp. now apply Nat.eqb_eq in Heqb.
      repeat deriv; inv H12; inv H11.  simpl in *.
      repeat deriv. now apply inf_diverges in H13.
    Unshelve.
      congruence.
      auto.
      destruct_scopes.
      repeat econstructor; auto. cbn.
      rewrite Nat.eqb_refl. repeat econstructor.
    }

      (* Starting the proof of Vrel clos1 clos2: *)
      subst. inv H1. inv H2.

      rewrite Vrel_Fix_eq. simpl. intuition; auto.
      (* scopes *)
      split. 2: split.
      1-2: destruct_scopes; apply -> subst_preserves_scope_exp; eauto.
      1-2: apply scoped_list_subscoped_eq; try simpl_convert_length; auto.
      2: apply biforall_length in H1; auto.
      1-2: apply Forall_app; split.
      1,3: apply closlist_scope; auto.
      1-2: apply biforall_vrel_closed in H1; apply H1.

      (* We fold back the CIU equivalence, with value lists: *)
      assert (H2 : CIU (RValSeq [VClos ext id0 params0 e]) (RValSeq [VClos ext0 id0 params0 e0])). {
        split. 2: split. all: auto.
        intros.
        assert (| F, ` VClos ext id0 params0 e | ↓). {
          inv H5. eexists. econstructor. auto. eassumption.
        }
        eapply H in H2; auto. inv H2. inv H7. eexists. eassumption.
        inv H0.
      }
      intros.

      (* We turn CIU into Rrel so that we can use equivalent frame stacks
         instead of equal ones. *)
      eapply CIU_iff_Rrel_closed in H2 as [_ [_ H2]].
      Unshelve. 2: exact (5 + 2 * Datatypes.length vl1 + 1 + m).
      (* IDEA: we use `try` to even out the evaluation counter for exceptions
          and correct application *)
      assert (Heval_e : | FTry 1 (° EApp (` VVar 0) (map VVal vl1)) 0 (° ETuple (map VVal vl1)) :: F1,
     ` VClos ext id0 params0 e | 5 + 2 * length vl1 + 1 + m1 ↓). {
        simpl. econstructor; auto. constructor; auto. simpl.
        replace (map (fun x : Exp => x.[VClos ext id0 params0 e/]) (map VVal vl1))
           with (map VVal vl1).
        2: {
          clear -H1. rewrite map_map. simpl.
          apply biforall_vrel_closed in H1 as [H1 _].
          apply map_ext_Forall. induction vl1; inv H1; constructor; auto.
          now rewrite vclosed_ignores_sub.
        }
        do 2 constructor. auto.
        constructor. destruct vl1.
        * simpl. econstructor. congruence. reflexivity. simpl.
          break_match_goal. 2: apply Nat.eqb_neq in Heqb; simpl in H0; lia.
          assumption.
        * simpl. constructor. congruence.
          simpl. change clock to (S (1 + 2 * length vl1) + m1).
          inv H1. constructor. now apply Vrel_closed_l in H9.
          eapply step_term_term_plus. apply params_eval_create.
          now apply biforall_vrel_closed in H11. simpl. rewrite Nat.eqb_refl.
          assumption.
      }

      (* We assert that the frame stack with the `try` expressions are equivalent
        in as many steps that are needed to evaluate the closures. *)
      assert (Hrel : Frel (4 + 2 * length vl1 + 1 + m1) (* dirty trick here with 0 *)
          (FTry 1 (EApp (`VVar 0) (map VVal vl1)) 0 (ETuple (map VVal vl1))::F1)
          (FTry 1 (EApp (`VVar 0) (map VVal vl2)) 0 (ETuple (map VVal vl2))::F2)
            ). {
        clear Heval_e.
        split. 2: split. 1-2: constructor; [constructor|apply H5].
        1-4: do 2 constructor; auto; apply indexed_to_forall; apply biforall_vrel_closed in H1; clear -H1.

        (* boiler plate codes: *)
        1-2: destruct H1 as [H1 _]; induction vl1; simpl; auto; inv H1; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        1-2: destruct H1 as [_ H1]; induction vl2; simpl; auto; inv H1; constructor;
             [ constructor; eapply loosen_scope_val; [|eassumption]; lia | auto].
        (****)

        split. 2: split.
        all: intros.
        * deriv. inv H7. inv H16. inv H8. 2: inv H16.
          simpl in H17.
          deriv. deriv. deriv. inv H1.
          - deriv.
            simpl in Hmn1.
            pose proof (Rel_create_result _ [] [] (IApp hd) (IApp hd') ltac:(auto) ltac:(constructor; eauto)).
            intuition.
            + repeat destruct_hyps.
              specialize (H1 k ltac:(lia)) as [Hrel [Eq1 Eq2]].
              rewrite Eq1 in H14. eapply Hrel in H14 as [kk D]. 2: reflexivity.
              2: eapply Frel_downclosed in H5; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite Eq2. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H7 in H14.
              eapply H5 in H14 as [kk D]. 2: lia. 2: eapply biforall_impl;[|eassumption]; intros; downclose_Vrel.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite H9. exact D.
              Unshelve. lia.
            + repeat destruct_hyps. rewrite H7 in H14.
              eapply H5 in H14 as [kk D]. 2: lia. 2: eapply Excrel_downclosed; eassumption.
              eexists. constructor; auto. simpl.
              constructor; auto. constructor; auto. now apply Vrel_closed_r in H0.
              constructor. econstructor. congruence. reflexivity.
              rewrite H9. exact D.
              Unshelve. lia.
          - inv H13. inv H18.
            rewrite map_map in H12.
            rewrite vclosed_ignores_sub in H10. 2: now apply Vrel_closed_l in H7.
            replace (map (fun x : Val => (` x).[hd/]) tl) with
                    (map VVal tl) in H12.
            2: {
              clear -H9. simpl.
              apply biforall_vrel_closed in H9 as [H1 _].
              apply map_ext_Forall. induction tl; inv H1; constructor; auto.
              now rewrite vclosed_ignores_sub.
            }
            rewrite vclosed_ignores_sub in H12. 2: now apply Vrel_closed_l in H0.
            eapply term_step_term in H12. 2: apply params_eval_create.
            2: now apply biforall_vrel_closed in H9.
            simpl app in H12.
            simpl in Hmn1.
            assert (list_biforall (Vrel (k0 - (1 + 2 * Datatypes.length tl)))
                                  (hd0 :: tl) (hd'0 :: tl') ) as Hfinally.
            {
              constructor. downclose_Vrel.
              eapply biforall_impl. 2: eassumption. intros. downclose_Vrel.
            }
            epose proof (Rel_create_result_relaxed _ (hd0 :: tl) (hd'0 :: tl') (IApp hd) (IApp hd') Hfinally _). Unshelve.
            4: {
              split. 2: split.
              1-2: constructor; now apply Vrel_closed in H0.
              downclose_Vrel.
            }
            intuition.
            + repeat destruct_hyps. simpl in Hmn1.
              specialize (H1 (k0 - (1 + 2 * Datatypes.length tl)) ltac:(lia)).
              destruct H1 as [Hrel [H1_1 H1_2]].
              rewrite H1_1 in H12. eapply Hrel in H12 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H9. simpl.
                apply biforall_vrel_closed in H9 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H9. simpl app. rewrite H1_2.
              exact D. lia. eapply Frel_downclosed. eassumption.
              Unshelve. lia. lia.
            + repeat destruct_hyps.
              rewrite H11 in H12. eapply H5 in H12 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H9. simpl.
                apply biforall_vrel_closed in H9 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H9. simpl app. rewrite H13.
              exact D. simpl in Hmn1. lia.
              eapply biforall_impl. 2: eassumption.
              intros. downclose_Vrel.
              Unshelve. lia.
            + repeat destruct_hyps.
              rewrite H11 in H12. eapply H5 in H12 as [k D].
              eexists. constructor. reflexivity. simpl.
              do 2 constructor. now apply Vrel_closed_r in H0.
              do 2 constructor. congruence. rewrite vclosed_ignores_sub.
              2: now apply Vrel_closed_r in H7.
              rewrite map_map.
              replace (map (fun x : Val => (` x).[hd'/]) tl') with
                      (map VVal tl').
              2: {
                clear -H9. simpl.
                apply biforall_vrel_closed in H9 as [_ H1].
                apply map_ext_Forall. induction tl'; inv H1; constructor; auto.
                now rewrite vclosed_ignores_sub.
              }
              constructor. now apply Vrel_closed_r in H7.
              eapply step_term_term_plus. apply params_eval_create.
              now apply biforall_vrel_closed in H9. simpl app. rewrite H13.
              exact D. simpl in Hmn1. lia.
              eapply Excrel_downclosed. eassumption.
              Unshelve. simpl in Hmn1. lia.
            + lia.
            + lia.
        * inv H8. (* Having 0 params in `catch` is exploited here,
                     because we only want to evaluate the `of` subexpression
                     in this `try` expression.
                   *)
          specialize (H12 _ _ _ _ eq_refl). contradiction.
        * inv H7.
      }

      (* Finally, we combine the previous assertions with the closures
         being in Rrel (H2). *)
      inv Heval_e.
      epose proof (H2 := H2 _ _ _ _ Hrel H11).
      Unshelve. 2: lia.
      clear -H2 H1. (* DANGER, nothing else is needed for now, however this
                               is fragile if refactoring is needed *)
      (* We deconstruct the evaluation in the premise: *)
      inv H2. deriv. simpl in H9. deriv. deriv. simpl in H3.
      deriv.
      rewrite map_map in H6.
      replace (map (fun x : Val => (` x).[VClos ext0 id0 (Datatypes.length vl1) e0/]) vl2) with
                      (map VVal vl2) in H6.
      2: {
        clear -H1. simpl.
        apply biforall_vrel_closed in H1 as [_ H1].
        apply map_ext_Forall. induction vl2; inv H1; constructor; auto.
        now rewrite vclosed_ignores_sub.
      }
      destruct vl2.
      - deriv. simpl in H9. apply biforall_length in H1. rewrite H1 in H9.
        simpl in H9. eexists. eassumption.
      - deriv. deriv.
        eapply term_step_term in H4. 2: apply params_eval_create.
        2: {
          apply biforall_vrel_closed in H1 as [_ H1]. now inv H1.
        }
        simpl in H4. apply biforall_length in H1. rewrite H1 in H4.
        simpl in H4. rewrite Nat.eqb_refl in H4. eexists. eassumption.
Qed.











(* Lemma Rrel_Val_compat_closed_reverse :
  forall (v v' : Val), forall m, Rrel m (`v) (`v') -> Vrel m v v'.
Proof.
  intros. apply CIU_Val_compat_closed_reverse.
Qed.*)

Corollary CIU_Val_compat_reverse :
  forall Γ (v v' : Val), CIU_open Γ (`v) (`v') -> Vrel_open Γ v v'.
Proof.
  intros. unfold Vrel_open; intros.
  epose proof (CIU_Val_compat_closed_reverse (v.[ξ₁]ᵥ) (v'.[ξ₁]ᵥ) ltac:(apply H) n).
  epose proof (CIU_Val_compat_closed_reverse (v.[ξ₂]ᵥ) (v'.[ξ₂]ᵥ) ltac:(apply H) n).
  Search Vrel subst.

Qed.


Lemma Erel_Val_compat_reverse :
  forall Γ (v v' : Val), Erel_open Γ (`v) (`v') -> Vrel_open Γ v v'.
Proof.
  intros. unfold Erel_open, Vrel_open in *. intros.
  apply H in H0. simpl in H0. destruct H0 as [HCl1 [HCl2 H0]].
  rewrite Vrel_Fix_eq. inv HCl1. inv HCl2.
  
Qed. *)
*)
