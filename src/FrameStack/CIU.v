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
      29-50: admit. (* technical *)
    5, 13:
      clear Hcontra; specialize (Hcontra_for_vars (default_subst (VCons VNil VNil)) ltac:(auto)) as [_ [_ Hcontra]];
     epose proof (Hcontra [FCase1 [([PCons PVar PVar], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr.
    5-8,11-15: epose proof (Hcontra [FCase1 [([PNil], `ttrue, `VNil);([PVar], `ttrue , °inf)]] ltac:(scope_solver) _) as Hcontra;
       do 6 (deriv; simpl in *; try congruence); try inf_congr.
    Unshelve.
     18-28: cbn. 25-28,19: destruct n.
     18-28:
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
      18-28: cbn; auto.

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