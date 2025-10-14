From CoreErlang.FrameStack Require Export SubstSemanticsLemmas
                                          CIU
                                          CTX
                                          Compatibility.
Require Export Basics.

Import ListNotations.

Definition is_exit_bif (modu func : string) (n : nat) : bool :=
match convert_string_to_code (modu, func) with
| BThrow | BExit => Nat.eqb n 1
| BError => Nat.eqb n 1 || Nat.eqb n 2
| _ => false
end.

Definition is_safe (modu func : string) (n : nat) : bool :=
match convert_string_to_code (modu, func) with
| BEq | BTypeEq | BNeq | BTypeNeq
| BLe | BLt | BGe | BGt           => Nat.eqb n 2
(**)
| BIsAtom | BIsNumber | BIsBoolean | BIsInteger => Nat.eqb n 1
(* TODO: rest of the bifs in erl_bifs.erl *)
| _ => false
end.

Fixpoint will_fail (e : Exp) : bool :=
match e with
| ELet _ e1 e2 => will_fail e1 || will_fail e2
| EPrimOp name _  => match convert_primop_to_code name with
                     | PMatchFail => true
                     | _ => false
                     end
| ECall (VVal (VLit (Atom modu))) (VVal (VLit (Atom func))) args =>
   is_exit_bif modu func (length args)
| _ => false
end.

Fixpoint is_safe_simple (e : Exp) : bool :=
match e with
| VVal (VFunId _) => false
| VVal (VVar _)   => true
| VVal _          => true
| EExp (ECons e1 e2) => is_safe_simple e1 && is_safe_simple e2
| EExp (ETuple l) => forallb is_safe_simple l
| EExp (ECall (VVal (VLit (Atom modu))) (VVal (VLit (Atom func))) args) =>
  is_safe modu func (length args) (* TODO: missing parts *)
| _ => false
end.

Fixpoint seq_elim (e : Exp) : Exp :=
(*   match fuel with
  | O => e  (* out of fuel: return original expression unchanged *)
  | S => *)
    match e with
    | VVal v => VVal v
    | EExp nv =>
      match nv with
      | EFun vl body =>
          EExp (EFun vl (seq_elim body))
      | EValues l =>
          EExp (EValues (map (fun x => seq_elim x) l))
      | ECons hd tl =>
          EExp (ECons (seq_elim hd) (seq_elim tl))
      | ETuple l =>
          EExp (ETuple (map (fun x => seq_elim x) l))
      | EMap l =>
          EExp (EMap (map (fun '(a,b) => (seq_elim a, seq_elim b)) l))
      | ECall m f l =>
          EExp (ECall (seq_elim m) (seq_elim f) (map (fun x => seq_elim x) l))
      | EPrimOp fn l =>
          EExp (EPrimOp fn (map (fun x => seq_elim x) l))
      | EApp e0 l =>
          EExp (EApp (seq_elim e0) (map (fun x => seq_elim x) l))
      | ECase e0 branches =>
          let e0' := seq_elim e0 in
          let branches' := map (fun '(p,g,b) => (p, seq_elim g, seq_elim b)) branches in
          EExp (ECase e0' branches')
      | ELet n e1 e2 =>
          EExp (ELet n (seq_elim e1) (seq_elim e2))
      | ESeq e1 e2 =>
          (* First fold the left part *)
          let e1' := seq_elim e1 in
          let e2' := seq_elim e2 in
            if will_fail e1' then e1'
            else
              match is_safe_simple e1' (* , is_safe_simple e2' *) with
              | true (* , _ *)      => e2'
              (* | false, true  => e1' <- this only needs to be done
                                          when using 'effect' *)
              | false (* , false *) => ESeq e1' e2'
              end
      | ELetRec l ebody =>
          let l' := map (fun '(n, e0) => (n, seq_elim e0)) l in
          EExp (ELetRec l' (seq_elim ebody))
      | ETry e1 vl1 e2 vl2 e3 =>
          EExp (ETry (seq_elim e1) vl1 (seq_elim e2) vl2 (seq_elim e3))
      end
    end
(*   end *).

Fixpoint size_val (v : Val) : nat :=
  1 (* match v with
  | VNil => 1
  | VLit _ => 1
  | VPid _ => 1
  | VCons hd tl => 1 + size_val hd + size_val tl
  | VTuple l => 1 + list_sum (map size_val l)
  | VMap pairs => 1 + list_sum (map (fun '(a, b) => size_val a + size_val b) pairs)
  | VVar _ => 1
  | VFunId _ => 1
  | VClos ext _ _ e => 1 + fold_left (fun acc '(_,_,e0) => acc + size_exp e0) ext 0 + size_exp e
  end *)
with size_exp (e : Exp) : nat :=
  match e with
  | VVal v => 1 + size_val v
  | EExp nv => 1 + size_nonval nv
  end
with size_nonval (nv : NonVal) : nat :=
  match nv with
    | EFun _ e => size_exp e
    | EValues l => list_sum (map size_exp l)
    | ECons hd tl => size_exp hd + size_exp tl
    | ETuple l => list_sum (map size_exp l)
    | EMap l => list_sum (map (fun '(a, b) => size_exp a + size_exp b) l)
    | ECall m f l => size_exp m + size_exp f + list_sum (map size_exp l)
    | EPrimOp _ l => list_sum (map size_exp l)
    | EApp e l => size_exp e + list_sum (map size_exp l)
    | ECase e branches => size_exp e + list_sum (map (
         fun '(p, g, e) => size_exp g + size_exp e
       ) branches)
    | ELet _ e1 e2 => size_exp e1 + size_exp e2
    | ESeq e1 e2 => size_exp e1 + size_exp e2
    | ELetRec l e => list_sum (map (fun '(_, a) => size_exp a) l) + size_exp e
    | ETry e1 _ e2 _ e3 => size_exp e1 + size_exp e2 + size_exp e3
  end.

Ltac do_step := econstructor; [constructor;auto| simpl].

Lemma will_fail_subst:
  forall e ξ,
    will_fail e = true ->
    will_fail e.[ξ] = true.
Proof.
  intro. remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H.
  induction n using lt_wf_ind. destruct e; simpl; intros.
  assumption.
  destruct e; simpl in *; try assumption.
  {
    destruct m; simpl in *; try congruence.
    destruct e; simpl in *; try congruence.
    destruct l0; simpl in *; try congruence.
    destruct f; simpl in *; try congruence.
    destruct e; simpl in *; try congruence.
    destruct l0; simpl in *; try congruence.
    by rewrite length_map.
  }
  {
    apply orb_true_iff in H1 as [H1 | H1]; eapply H in H1; try rewrite H1.
    all: auto.
    1,3: lia.
    by rewrite orb_comm.
  }
Qed.

Lemma is_safe_simple_subst:
  forall e Γ ξ,
    SUBSCOPE Γ ⊢ ξ ∷ 0 ->
    EXP Γ ⊢ e ->
    is_safe_simple e = true ->
    is_safe_simple e.[ξ] = true.
Proof.
  intro. remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H.
  induction n using lt_wf_ind. destruct e; simpl; intros.
  * destruct e; simpl in *; try assumption.
    - inv H2. inv H6. specialize (H1 n0 ltac:(lia)).
      destruct ξ.
      + destruct v; try reflexivity. inv H1. lia.
      + reflexivity.
    - inv H3.
  * destruct e; simpl in *; try assumption.
    - apply andb_true_iff in H3 as [H3_1 H3_2].
      destruct_scopes.
      eapply H in H3_1. eapply H in H3_2. by rewrite H3_1, H3_2.
      all: try eassumption.
      all: lia.
    - apply forallb_forall. intros.
      apply in_map_iff in H4 as [newx [Heq H4]]. subst.
      eapply forallb_forall in H3. 2: exact H4.
      eapply H; try eassumption.
      + pose proof elem_of_list_split l newx.
        apply elem_of_list_In in H4.
        apply H5 in H4 as [? [? H4]]. subst l.
        rewrite map_app, list_sum_app. slia.
      + apply elem_of_list_In in H4.
        inv H2. inv H7. apply indexed_to_forall in H6.
        eapply list.Forall_forall in H6; eassumption.
    - destruct m; simpl in *; try congruence.
      destruct e; simpl in *; try congruence.
      destruct l0; simpl in *; try congruence.
      destruct f; simpl in *; try congruence.
      destruct e; simpl in *; try congruence.
      destruct l0; simpl in *; try congruence.
      by rewrite length_map.
Qed.

Lemma closed_seq_elim Γ e :
  EXP Γ ⊢ e -> EXP Γ ⊢ (seq_elim e).
Proof.
Admitted.

Lemma subst_preserves_size :
  forall e ξ,
    size_exp (e.[ξ]) = size_exp e.
Proof.

Admitted.

Lemma will_fail_exception :
  forall e res, will_fail e = true ->
    ⟨[], e⟩ -->* res ->
    exists exc, res = RExc exc.
Proof.
  intro. remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H.
  induction n using lt_wf_ind. rename H into IH.
  destruct e; simpl; try congruence.
  destruct e; simpl; try congruence.
  * destruct m; simpl; try congruence.
    destruct e; simpl; try congruence.
    destruct l0; simpl; try congruence.
    destruct f; simpl; try congruence.
    destruct e; simpl; try congruence.
    destruct l0; simpl; try congruence.
    intros Hsize ???.
    destruct H0 as [k [Hres D]].
    inv D. inv_result.
    inv H0. inv H1.
    inv H0. inv H2.
    inv H0. inv H1.
    inv H0. inv H2.
    inv H0. inv H1.
    unfold is_exit_bif in H. case_match; try congruence.
    - destruct l; simpl in H; try congruence.
      destruct l; simpl in H; try congruence.
      2: destruct l; simpl in H; try congruence.
      (* single param exception *)
      + inv H0.
        pose proof (proj1 (semantic_iff_termination k _ _)
           (ex_intro _ res (conj Hres H2))) as TERM.
        apply term_eval_empty in TERM as [rese [ke [Hrese [D Hlt]]]].
        eapply frame_indep_core in D.
        pose proof (transitive_eval_rev_lt H2 Hlt D). simpl in H, D.
        destruct rese; try by inv_result.
        ** inv H. inv H3.
           simpl in H11. unfold eval in H11. rewrite H1 in H11.
           case_match; try congruence.
           inv H11. inv H6. by eexists. inv H3.
        ** inv H. inv H3. inv H6. by eexists. inv H.
      (* two param exception *)
      + inv H0.
        pose proof (proj1 (semantic_iff_termination k _ _)
           (ex_intro _ res (conj Hres H2))) as TERM.
        apply term_eval_empty in TERM as [rese [ke [Hrese [D Hlt]]]].
        eapply frame_indep_core in D.
        pose proof (transitive_eval_rev_lt H2 Hlt D). simpl in H, D.
        destruct rese; try by inv_result.
        ** inv H. inv H3.
           pose proof (proj1 (semantic_iff_termination k0 _ _)
             (ex_intro _ res (conj Hres H6))) as TERM.
           apply term_eval_empty in TERM as [rese2 [ke2 [Hrese2 [D2 Hlt2]]]].
           eapply frame_indep_core in D2.
           pose proof (transitive_eval_rev_lt H6 Hlt2 D2).
           simpl in H, D2.
           destruct rese2; try by inv_result.
           -- inv H. inv H4.
              simpl in H13. unfold eval in H13. rewrite H1 in H13.
              case_match; try congruence.
              inv H13. inv H8. by eexists. inv H4.
           -- inv H. inv H4. inv H8. by eexists. inv H.
        ** inv H. inv H3. inv H6. by eexists. inv H.
    - destruct l; simpl in H; try congruence.
      destruct l; simpl in H; try congruence.
      (* single param exception - as above *)
      inv H0.
      pose proof (proj1 (semantic_iff_termination k _ _)
         (ex_intro _ res (conj Hres H2))) as TERM.
      apply term_eval_empty in TERM as [rese [ke [Hrese [D Hlt]]]].
      eapply frame_indep_core in D.
      pose proof (transitive_eval_rev_lt H2 Hlt D). simpl in H, D.
      destruct rese; try by inv_result.
      + inv H. inv H3.
        simpl in H11. unfold eval in H11. rewrite H1 in H11.
        case_match; try congruence.
        inv H11. inv H6. by eexists. inv H3.
      + inv H. inv H3. inv H6. by eexists. inv H.
    - destruct l; simpl in H; try congruence.
      destruct l; simpl in H; try congruence.
      (* single param exception - as above *)
      inv H0.
      pose proof (proj1 (semantic_iff_termination k _ _)
         (ex_intro _ res (conj Hres H2))) as TERM.
      apply term_eval_empty in TERM as [rese [ke [Hrese [D Hlt]]]].
      eapply frame_indep_core in D.
      pose proof (transitive_eval_rev_lt H2 Hlt D). simpl in H, D.
      destruct rese; try by inv_result.
      + inv H. inv H3.
        simpl in H11. unfold eval in H11. rewrite H1 in H11.
        case_match; try congruence.
        inv H11. inv H6. by eexists. inv H3.
      + inv H. inv H3. inv H6. by eexists. inv H.
  * intros Hsize ???. case_match; try congruence.
    destruct H0 as [k [Hres D]].
    inv D. inv_result.
    inv H0. inv H2. admit. (* DOABLE, by induction *)
  * intros. destruct H1 as [k [Hres D]].
    inv D. inv_result.
    inv H1.
    pose proof (proj1 (semantic_iff_termination k0 _ _)
         (ex_intro _ res (conj Hres H2))) as TERM.
    apply term_eval_empty in TERM as [rese [ke [Hrese [D Hlt]]]].
    eapply frame_indep_core in D as D'.
    pose proof (transitive_eval_rev_lt H2 Hlt D'). simpl in H, D'.
    apply orb_true_iff in H0 as [|].
    - simpl in *.
      specialize (IH (size_exp e1) ltac:(lia) e1 ltac:(lia)
                     rese H0 (ex_intro _ ke (conj Hrese D))) as [exc Hexc].
      subst. inv H1. inv H4. inv H7.
      by eexists.
      inv H1.
    - simpl in *. inv Hrese.
      + inv H1. inv H4.
        inv H7. by eexists. inv H1.
      + inv H1. inv H4.
        ospecialize* (IH (size_exp e2) ltac:(lia) e2.[list_subst vs idsubst] _
                     res _ (ex_intro _ k (conj Hres H7))).
        ** rewrite subst_preserves_size. lia.
        ** by rewrite will_fail_subst.
        ** assumption.
Admitted.

Require Import SubstSemanticsLabeled.
Lemma is_safe_simple_no_effects: 
  forall e, is_safe_simple e = true ->
    exists vs, ⟨[], e⟩  -[ [] ]->ₗ* ⟨[], RValSeq vs⟩.
Proof.
  
Admitted.

(* Lemma eval_seq_optim_1 :
  forall e1 e2 res,
   ⟨ [], (° ESeq e1 e2)⟩ -->* res ->
   ⟨ [], (if will_fail (seq_elim e1)
   then seq_elim e1
   else
    if is_safe_simple (seq_elim e1)
    then seq_elim e2
    else
     if is_safe_simple (seq_elim e2)
     then seq_elim e1
     else ° ESeq (seq_elim e1) (seq_elim e2)) ⟩ -->* res.
Proof.

Admitted.

Lemma eval_seq_optim_2 :
  forall e1 e2 res,
   ⟨ [], (if will_fail (seq_elim e1)
   then seq_elim e1
   else
    if is_safe_simple (seq_elim e1)
    then seq_elim e2
    else
     if is_safe_simple (seq_elim e2)
     then seq_elim e1
     else ° ESeq (seq_elim e1) (seq_elim e2)) ⟩ -->* res
     ->
      ⟨ [], (° ESeq e1 e2)⟩ -->* res.
Proof.

Admitted. *)

(*
This won't work, because bodies of binders (e.g., EFun) are not closed!

Theorem seq_optim (e : Exp) :
  EXPCLOSED e ->
  CIU e (seq_elim e).
Proof.
  remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H.
  induction n using lt_wf_ind. destruct e; simpl; intros.
  { apply CIU_iff_Rrel_closed. intros. apply Rrel_Fundamental_closed.
    scope_solver.  }
  destruct e; simpl.
  * apply CIU_iff_Rrel_closed.
    intros. apply Rrel_exp_compat_closed.
    apply Erel_Fun_compat_closed.
    - by destruct_scopes.
    - apply closed_seq_elim. by destruct_scopes.
    - eapply H. 2: reflexivity. 2: by destruct_scopes.
      simpl in H0. lia.
Qed. *)

(* Lemma seq_elim_subst e ξ: 
  (seq_elim e).[ξ] = seq_elim (e.[ξ]).
Proof.
  remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H ξ.
  induction n using lt_wf_ind. destruct e; simpl; intros.
  reflexivity.
  destruct e; simpl in *; try assumption.
  * erewrite H. reflexivity. 2: reflexivity. lia.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * case_match. 2: case_match. 3: case_match.
    - eapply will_fail_subst in H1.
      erewrite H in H1. rewrite H1. 3: reflexivity. 2: lia.
      erewrite H. reflexivity. 2: reflexivity. lia.
    - 
  * admit.
  * admit.
Admitted. *)

Lemma CIU_irrefl :
  forall (e : Exception) (vs : ValSeq),
    CIU e vs -> False.
Proof.
  intros. destruct H as [? [? H]].
  Check FTry.
  ospecialize* (H [FTry (length vs) (°inf) 3 (˝VNil)]).
  * split.
    - constructor; constructor. constructor. apply inf_scope. do 2 constructor.
    - constructor; constructor.
  * eexists. destruct e as [[? ?] ?]. constructor.
    do 3 constructor.
  * inv H. inv H2.
    rewrite eclosed_ignores_sub in H10. 2: constructor; apply inf_scope.
    by apply inf_diverges in H10.
Qed.

Theorem seq_optim Γ (e : Exp) :
  EXP Γ ⊢ e ->
  CIU_open Γ e (seq_elim e) /\
  CIU_open Γ (seq_elim e) e. (* both are needed in the ind hyps. *)
Proof.
  remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H Γ.
  induction n using lt_wf_ind. destruct e; simpl; intros.
  { split. all: apply CIU_iff_Rrel; auto. }
  pose proof CIU_IsPreCtxRel as CONG.
  destruct e; simpl.
  * split.
    { apply CONG; auto.
      - by destruct_scopes.
      - apply closed_seq_elim. by destruct_scopes.
      - eapply H. 2: reflexivity. 2: by destruct_scopes.
        simpl in H0. lia.
    }
    {
      apply CONG; auto.
      - apply closed_seq_elim. by destruct_scopes.
      - by destruct_scopes.
      - eapply H. 2: reflexivity. 2: by destruct_scopes.
        simpl in H0. lia.
    }
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * admit.
  * split.
    {
      split. 2: split.
      - apply -> subst_preserves_scope_red. 2: exact H2. scope_solver.
      - apply -> subst_preserves_scope_red. 2: exact H2.
        repeat case_match.
        1-2: constructor; apply closed_seq_elim; by destruct_scopes.
        do 3 constructor;
        destruct_scopes;
        by apply closed_seq_elim.
      - intros. destruct H4.
        simpl in *.
        inv H4. 2: inv_result.
        case_match.
        2: case_match.
        {
          eapply will_fail_subst in H4 as H4'.
          pose proof will_fail_exception (seq_elim e1).[ξ] H4' as [exc D1].
          destruct D1 as [n1 [Hres1 D1]].
          pose proof (H (size_exp e1) ltac:(lia) e1 ltac:(lia) Γ
            ltac:(by destruct_scopes)) as [CIUe1_1 CIUe1_2].
          specialize (CIUe1_1 _ H2) as [_ [_ D3]].
          simpl in D3. destruct H3.
          ospecialize *(D3 (FSeq e2.[ξ]::F)).
          { split. constructor. 2: assumption.
            * constructor.
              clear -H1 H2.
              destruct_scopes.
              apply -> subst_preserves_scope_exp; eassumption.
            * constructor. constructor. assumption. }
          { eexists. exact H9. }
          destruct D3.
          eapply frame_indep_nil in D1 as D1'.
          eapply term_step_term in H6. 2: exact D1'.
          inv H6.
          eexists.
          eapply step_term_term_plus.
          eapply frame_indep_nil in D1. exact D1.
          exact H13.
        }
        {
          eapply is_safe_simple_subst with (ξ := ξ) in H5.
          apply is_safe_simple_no_effects in H5 as D.
          destruct D as [vs [k1 D]].
          apply step_rt_labeled_to_unlabeled in D.
          pose proof (H (size_exp e1) ltac:(lia) e1 ltac:(lia) Γ
            ltac:(by destruct_scopes)) as [CIUe1_1 CIUe1_2].
          eapply term_eval_empty in H9 as D'.
          destruct D' as [res [k1' [Hres [D' Hlt]]]].
          pose proof (CIUe1_1 _ H2).
          pose proof (CIUe1_2 _ H2).
          assert (CIU res vs /\ CIU vs res). {
            clear -D D' H6 H7 H1 H2.
            apply CIU_eval_base in D' as [].
            2: { destruct_scopes. constructor.
                 apply -> subst_preserves_scope_exp; eassumption.
            }
            apply CIU_eval_base in D as [].
            2: { destruct_scopes. constructor.
                 apply -> subst_preserves_scope_exp; try eassumption.
                 by apply closed_seq_elim.
            }
            split.
            * pose proof (CIU_transitive_closed _ _ _ H0 H6).
              pose proof (CIU_transitive_closed _ _ _ H5 H3).
              assumption.
            * pose proof (CIU_transitive_closed _ _ _ H7 H).
              pose proof (CIU_transitive_closed _ _ _ H4 H5).
              assumption.
          }
          eapply frame_indep_core in D'.
          epose proof term_step_term _ _ _ _ H9 _ _ D'.
          2: eassumption.
          2: apply closed_seq_elim; by destruct_scopes.
          simpl in *.
          destruct res; try by inv_result.
          2: {
            destruct H8 as [C1 C2].
            clear -C1. exfalso.
            by apply CIU_irrefl in C1.
          }
          inv H10.
          apply ex_intro with (x := k0) in H12.
          pose proof (H (size_exp e2) ltac:(lia) e2 ltac:(lia) Γ
            ltac:(by destruct_scopes)) as [CIUe2_1 CIUe2_2].
          eapply CIUe2_1; eassumption.
        }
        {
          
        }
      }
      {
        admit.
      }
  * admit.
  * admit.
Admitted.

Theorem seq_optim (e : Exp) :
  EXPCLOSED e ->
  CIU (seq_elim e) e.
Proof.

Qed.

