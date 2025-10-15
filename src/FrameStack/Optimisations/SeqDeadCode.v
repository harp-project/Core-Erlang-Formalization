From CoreErlang.FrameStack Require Export SubstSemanticsLemmas
                                          CIU
                                          CTX
                                          Compatibility.
Require Export Basics.

Import ListNotations.

(* Lemma exp_params_eval (exps : list Exp) vals :
  list_biforall (fun exp val => ⟨[], RExp exp⟩ -->* RValSeq [val]) exps vals ->
  forall vals0 v Fs id,
    exists k, ⟨FParams id vals0 exps :: Fs, RValSeq [v]⟩ -[k]->
              ⟨FParams id (vals0 ++ removelast (v::vals)) [] :: Fs, RValSeq [last vals v]⟩.
Proof.
Admitted. *)

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
  is_safe modu func (length args) (* TODO: missing parts *) &&
  forallb is_safe_simple args (* NOTE: this is missing from the compiler
                                 which uses useless call elimination
                                 instead *)
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

Fixpoint (* size_val (v : Val) : nat :=
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
with *) size_exp (e : Exp) : nat :=
  match e with
  | VVal v => 1
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
      rewrite length_map.
      apply andb_true_iff in H3 as [].
      apply andb_true_iff. split. by idtac.
      apply forallb_forall. intros.
      apply in_map_iff in H5 as [? [? ?]]. subst.
      apply forallb_forall with (x := x0) in H4; try assumption.
      eapply H. 5: exact H4. 2: reflexivity. 2: eassumption.
      + apply in_split in H6 as [? [? ?]]. subst l.
        rewrite map_app, list_sum_app in H0. simpl in H0. lia.
      + destruct_scopes. apply indexed_to_forall in H10.
        by apply Forall_forall with (x := x0) in H10.
Qed.

Lemma closed_seq_elim Γ e :
  EXP Γ ⊢ e -> EXP Γ ⊢ (seq_elim e).
Proof.
  intro. remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert Γ e H0 H.
  induction n using lt_wf_ind. rename H into IH. intros.
  destruct e; simpl; try congruence.
  destruct e; simpl; try congruence.
  all: destruct_scopes; simpl in H0.
  * do 2 constructor. eapply IH. 2: reflexivity. 2: assumption. lia.
  * (* same for tuples, primops, similar to maps, case, app *)
    do 2 constructor. intros.
    rewrite length_map in H. apply H2 in H as H'.
    rewrite map_nth with (d := seq_elim (˝VNil)). simpl.
    eapply IH. 3: exact H'.
    2: reflexivity.
    apply nth_In with (d := ˝VNil) in H.
    apply In_split in H as [? [? H]]. rewrite H in H0.
    rewrite map_app, list_sum_app in H0. simpl in H0. lia.
  * do 2 constructor; eapply IH; try eassumption.
    all: lia.
  * do 2 constructor. intros.
    rewrite length_map in H. apply H2 in H as H'.
    rewrite map_nth with (d := seq_elim (˝VNil)). simpl.
    eapply IH. 3: exact H'.
    2: reflexivity.
    apply nth_In with (d := ˝VNil) in H.
    apply In_split in H as [? [? H]]. rewrite H in H0.
    rewrite map_app, list_sum_app in H0. simpl in H0. lia.
  * do 2 constructor; intros;
    rewrite length_map in H; apply H1 in H as H'1; apply H4 in H as H'2.
    all: rewrite map_map.
    (* only H'1 and H'2 are different in the following 2 subgoals *)
    - rewrite map_nth with (d := prod_map seq_elim seq_elim (˝VNil,˝VNil)). cbn.
      rewrite map_nth with (d := (˝VNil,˝VNil)) in H'1.
      apply nth_In with (d := (˝VNil, ˝VNil)) in H.
      apply In_split in H as [? [? H]]. rewrite H in H0.
      rewrite map_app, list_sum_app in H0. simpl in H0.
      destruct (nth i l); simpl in *.
      eapply IH. 3: exact H'1.
      2: reflexivity. lia.
    - rewrite map_nth with (d := prod_map seq_elim seq_elim (˝VNil,˝VNil)). cbn.
      rewrite map_nth with (d := (˝VNil,˝VNil)) in H'2.
      apply nth_In with (d := (˝VNil, ˝VNil)) in H.
      apply In_split in H as [? [? H]]. rewrite H in H0.
      rewrite map_app, list_sum_app in H0. simpl in H0.
      destruct (nth i l); simpl in *.
      eapply IH. 3: exact H'2.
      2: reflexivity. lia.
  * do 2 constructor.
    2-3: eapply IH; try eassumption; lia.
    intros.
    rewrite length_map in H. apply H5 in H as H'.
    rewrite map_nth with (d := seq_elim (˝VNil)). simpl.
    eapply IH. 3: exact H'.
    2: reflexivity.
    apply nth_In with (d := ˝VNil) in H.
    apply In_split in H as [? [? H]]. rewrite H in H0.
    rewrite map_app, list_sum_app in H0. simpl in H0. lia.
  * do 2 constructor. intros.
    rewrite length_map in H. apply H2 in H as H'.
    rewrite map_nth with (d := seq_elim (˝VNil)). simpl.
    eapply IH. 3: exact H'.
    2: reflexivity.
    apply nth_In with (d := ˝VNil) in H.
    apply In_split in H as [? [? H]]. rewrite H in H0.
    rewrite map_app, list_sum_app in H0. simpl in H0. lia.
  * do 2 constructor.
    1: eapply IH; try eassumption; lia.
    intros.
    rewrite length_map in H. apply H5 in H as H'.
    rewrite map_nth with (d := seq_elim (˝VNil)). simpl.
    eapply IH. 3: exact H'.
    2: reflexivity.
    apply nth_In with (d := ˝VNil) in H.
    apply In_split in H as [? [? H]]. rewrite H in H0.
    rewrite map_app, list_sum_app in H0. simpl in H0. lia.
  * do 2 constructor; intros.
    1: eapply IH; try eassumption; lia.
    all: rewrite length_map in H; apply H5 in H as H'1; apply H6 in H as H'2.
    all: repeat rewrite map_map.
    (* only H'1 and H'2 are different in the following 2 subgoals *)
    - rewrite map_nth with (d := prod_map (prod_map id seq_elim) seq_elim ([],˝VNil,˝VNil)).
      setoid_rewrite map_nth with (d := prod_map (prod_map id seq_elim) seq_elim ([],˝VNil,˝VNil)).
      setoid_rewrite map_nth with (d := prod_map (prod_map id seq_elim) seq_elim ([],˝VNil,˝VNil)) in H'1. cbn.
      apply nth_In with (d := ([],˝VNil, ˝VNil)) in H.
      apply In_split in H as [? [? H]]. rewrite H in H0.
      rewrite map_app, list_sum_app in H0. simpl in H0.
      destruct (nth i l), p; simpl in *.
      eapply IH. 3: exact H'1.
      2: reflexivity. lia.
    - rewrite map_nth with (d := prod_map (prod_map id seq_elim) seq_elim ([],˝VNil,˝VNil)).
      setoid_rewrite map_nth with (d := prod_map (prod_map id seq_elim) seq_elim ([],˝VNil,˝VNil)).
      setoid_rewrite map_nth with (d := prod_map (prod_map id seq_elim) seq_elim ([],˝VNil,˝VNil)) in H'2. cbn.
      apply nth_In with (d := ([],˝VNil, ˝VNil)) in H.
      apply In_split in H as [? [? H]]. rewrite H in H0.
      rewrite map_app, list_sum_app in H0. simpl in H0.
      destruct (nth i l), p; simpl in *.
      eapply IH. 3: exact H'2.
      2: reflexivity. lia.
  * do 2 constructor; eapply IH; try eassumption.
    all: lia.
  * (* Sequences: the only tricky case *)
    case_match.
    - eapply IH; try eassumption; lia.
    - case_match.
      + eapply IH; try eassumption; lia.
      + do 2 constructor.
        all: eapply IH; try eassumption; lia.
  * do 2 constructor.
    2: rewrite length_map; eapply IH; try eassumption; lia.
    intros.
    repeat rewrite map_map.
    rewrite length_map in H. apply H4 in H as H'.
    setoid_rewrite map_nth with (d := prod_map id seq_elim (0,˝VNil)). simpl.
    setoid_rewrite map_nth with (d := prod_map id seq_elim (0,˝VNil)) in H'. simpl in H'.
    apply nth_In with (d := (0, ˝VNil)) in H.
    apply In_split in H as [? [? H]]. rewrite H in H0.
    rewrite map_app, list_sum_app in H0. simpl in H0.
    destruct (nth i l).
    rewrite length_map.
    eapply IH. 3: exact H'.
    2: reflexivity.
    lia.
  * do 2 constructor; eapply IH; try eassumption.
    all: lia.
Qed.

Lemma subst_preserves_size :
  forall e ξ,
    size_exp (e.[ξ]) = size_exp e.
Proof.
  intro. remember (size_exp e) as n. rewrite Heqn.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H.
  induction n using lt_wf_ind. rename H into IH. intros.
  destruct e; simpl in *; try congruence;
  destruct e; simpl in *; try congruence.
  * erewrite IH; try reflexivity. lia.
  * rewrite map_map.
    f_equal. f_equal.
    apply map_ext_in. intros.
    eapply IH; try reflexivity.
    apply in_split in H0 as [? [? ?]]. subst.
    rewrite map_app, list_sum_app in H. simpl in H. lia.
  * erewrite IH, IH; try reflexivity; lia.
  * rewrite map_map.
    f_equal. f_equal.
    apply map_ext_in. intros.
    eapply IH; try reflexivity.
    apply in_split in H0 as [? [? ?]]. subst.
    rewrite map_app, list_sum_app in H. simpl in H. lia.
  * rewrite map_map.
    f_equal. f_equal.
    apply map_ext_in. intros. destruct a.
    erewrite IH, IH; try reflexivity.
    all: apply in_split in H0 as [? [? ?]]; subst;
    rewrite map_app, list_sum_app in H; simpl in H; lia.
  * erewrite IH; try reflexivity. 2: lia.
    erewrite IH; try reflexivity. 2: lia.
    rewrite map_map.
    f_equal. f_equal. f_equal.
    apply map_ext_in. intros.
    eapply IH; try reflexivity.
    apply in_split in H0 as [? [? ?]]. subst.
    rewrite map_app, list_sum_app in H. simpl in H. lia.
  * rewrite map_map.
    f_equal. f_equal.
    apply map_ext_in. intros.
    eapply IH; try reflexivity.
    apply in_split in H0 as [? [? ?]]. subst.
    rewrite map_app, list_sum_app in H. simpl in H. lia.
  * erewrite IH; try reflexivity. 2: lia.
    rewrite map_map.
    f_equal. f_equal. f_equal.
    apply map_ext_in. intros.
    eapply IH; try reflexivity.
    apply in_split in H0 as [? [? ?]]. subst.
    rewrite map_app, list_sum_app in H. simpl in H. lia.
  * erewrite IH; try reflexivity. 2: lia.
    rewrite map_map.
    f_equal. f_equal. f_equal.
    apply map_ext_in. intros. destruct a, p.
    erewrite IH, IH; try reflexivity.
    all: apply in_split in H0 as [? [? ?]]; subst;
    rewrite map_app, list_sum_app in H; simpl in H; lia.
  * erewrite IH, IH; try reflexivity; lia.
  * erewrite IH, IH; try reflexivity; lia.
  * erewrite IH; try reflexivity. 2: lia.
    rewrite map_map.
    f_equal. f_equal. f_equal.
    apply map_ext_in. intros. destruct a.
    erewrite IH; try reflexivity.
    all: apply in_split in H0 as [? [? ?]]; subst;
    rewrite map_app, list_sum_app in H; simpl in H; lia.
  * erewrite IH, IH, IH; try reflexivity; lia.
Qed.

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
    inv H0. clear IH Hsize n.
    revert k0 res Hres H2.
    remember [] as vals. clear Heqvals. revert vals.
    (* induction - TODO separate it *)
    induction l; intros.
    { (* empty par list remainder *)
      inv H2. inv H.
      cbn in H8. unfold primop_eval in H8.
      unfold eval_primop_error in H8.
      rewrite H1 in H8.
      destruct vals; try congruence.
      destruct vals; try congruence.
      inv H8. inv H0. by eexists. inv H.
    }
    inv H2. inv H.
    pose proof (proj1 (semantic_iff_termination k _ _)
         (ex_intro _ res (conj Hres H0))) as TERM.
    apply term_eval_empty in TERM as [resa [ka [Hresa [D Hlt]]]].
    eapply frame_indep_core in D as D'.
    pose proof (transitive_eval_rev_lt H0 Hlt D'). simpl in H, D'.
    inv Hresa. 1: { inv H. inv H3. inv H6. by eexists. inv H. }
    clear D'. inv H. inv H3.
    - (* more than 1 param in the remainder *)
      ospecialize* (IHl _ _ _ Hres).
      { econstructor. constructor. congruence. eassumption. }
      assumption.
    - (* only 1 param in the remainder - same as in empty list *)
      cbn in H12. unfold primop_eval in H12.
      unfold eval_primop_error in H12.
      rewrite H1 in H12.
      destruct vals; simpl in *; try congruence.
      + inv H12. inv H6. by eexists. inv H.
      + destruct (vals ++ [v]) eqn:ERROR; try congruence.
        apply app_eq_nil in ERROR as []. inv H3.
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
Qed.

Lemma is_safe_eval :
  forall m f n, is_safe m f n = true -> forall vals, length vals = n -> 
    exists v eff, eval m f vals = Some (RValSeq [v], eff).
Proof.
  intros. unfold is_safe in H. case_match; try congruence.
  all: apply Nat.eqb_eq in H; subst.
  all: destruct vals; try by simpl in H0; congruence.
  all: destruct vals; try by simpl in H0; congruence.
  all: try destruct vals; try by simpl in H0; congruence.
  all: clear H0.
  all: unfold eval; rewrite H1.
  all: unfold eval_equality, eval_cmp, eval_check; rewrite H1.
  all: case_match; try by do 2 eexists.
  all: case_match; try by do 2 eexists.
Qed.

Require Import SubstSemanticsLabeled.
Lemma is_safe_simple_no_effects: 
  forall e res, is_safe_simple e = true ->
    (* is_result res -> *)
    ⟨[], e⟩  -->* res -> (* TODO: no side effects - labeled termination needed *)
    exists v, res = RValSeq [v].
Proof.
  intro. remember (size_exp e) as n.
  assert (size_exp e <= n) by lia. clear Heqn.
  revert e H.
  induction n using lt_wf_ind. rename H into IH.
  destruct e; simpl; try congruence.
  * intros. destruct H1 as [? [? ?]]. destruct e; try congruence.
    all: inv H2; (try by inv_result);
      inv H3; inv H4.
    all: try by eexists.
    all: inv H0.
  * destruct e; simpl; try congruence.
    - intros Hlt res Hsafe D.
      apply andb_true_iff in Hsafe as [Hsafe1 Hsafe2].
      destruct D as [k [Hres D]].
      inv D. inv_result.
      inv H.
      pose proof (proj1 (semantic_iff_termination k0 _ _)
         (ex_intro _ res (conj Hres H0))) as TERM.
      apply term_eval_empty in TERM as [restl [ktl [Hrestl [D Hlt2]]]].
      eapply frame_indep_core in D as D'.
      pose proof (transitive_eval_rev_lt H0 Hlt2 D'). simpl in H, D'.
      eapply conj, ex_intro with (x := ktl), IH in D; try eassumption.
      2: lia.
      destruct D as [vtl ?]. subst. clear D'.
      inv H. inv H2.
      pose proof (proj1 (semantic_iff_termination k _ _)
         (ex_intro _ res (conj Hres H5))) as TERM.
      apply term_eval_empty in TERM as [reshd [khd [Hreshd [D Hlt3]]]].
      eapply frame_indep_core in D as D'.
      pose proof (transitive_eval_rev_lt H5 Hlt3 D'). simpl in H, D'.
      eapply conj, ex_intro with (x := khd), IH in D; try eassumption.
      2: lia.
      destruct D as [vhd ?]. subst. clear D'.
      inv H. inv H3. inv H7. 2: { inv H. } by eexists.
    - intros. destruct H1 as [k [Hres D]].
      inv D. inv_result. inv H1.
      (* induction - TODO separate it *)
      remember [] as vals in H2. clear Heqvals.
      revert k0 vals res H2 Hres.
      induction l; intros.
      { (* final step *)
        inv H2. inv H1. cbn in H9. inv H9.
        inv H3. 2: { inv H1. } by eexists.
      }
      inv H2. inv H1.
      pose proof (proj1 (semantic_iff_termination _ _ _)
         (ex_intro _ res (conj Hres H3))) as TERM.
      apply term_eval_empty in TERM as [resa [ka [Hresa [D Hlt3]]]].
      eapply frame_indep_core in D as D'.
      pose proof (transitive_eval_rev_lt H3 Hlt3 D'). simpl in H1, D'.
      clear D'.
      eapply conj, ex_intro with (x := ka), IH in D as [va EQ].
      5: assumption.
      3: reflexivity.
      2: { simpl in H. lia. }
      2: { simpl in H0. by apply andb_true_iff in H0 as []. }
      subst. inv H1. inv H4.
      + (* params remain *)
        eapply IHl.
        { simpl in *. lia. }
        { simpl in *. by apply andb_true_iff in H0 as []. }
        { econstructor. constructor. congruence. exact H7. }
        { assumption. }
      + (* final step *)
        cbn in H13. inv H13.
        inv H7. 2: { inv H1. } by eexists.
    - intros.
      destruct m; simpl; try congruence.
      destruct e; simpl; try congruence.
      destruct l0; simpl; try congruence.
      destruct f; simpl; try congruence.
      destruct e; simpl; try congruence.
      destruct l0; simpl; try congruence.
      apply andb_true_iff in H0 as [].
      destruct H1 as [k [Hres D]].
      (* decompose evaluation *)
      inv D. inv_result. inv H1.
      inv H3. inv H1.
      inv H4. inv H1.
      inv H3. inv H1.
      inv H4. inv H1.
      (* induction - TODO separate it *)
      remember [] as vals in H3.
      assert (length l = length l + length vals) by (subst vals; slia).
      clear Heqvals. rewrite H1 in H0. clear H1.
      revert k0 vals res H3 Hres H0.
      induction l; intros.
      { (* final step *)
        inv H3. inv H1. cbn in H10.
        pose proof is_safe_eval _ _ _ H0 vals eq_refl as [v [eff ?]].
        rewrite H1 in H10. inv H10.
        inv H4. by eexists. inv H3.
      }
      inv H3. inv H1.
      pose proof (proj1 (semantic_iff_termination _ _ _)
         (ex_intro _ res (conj Hres H4))) as TERM.
      apply term_eval_empty in TERM as [resa [ka [Hresa [D Hlt3]]]].
      eapply frame_indep_core in D as D'.
      pose proof (transitive_eval_rev_lt H4 Hlt3 D'). simpl in H1, D'.
      clear D'.
      eapply conj, ex_intro with (x := ka), IH in D as [va EQ].
      5: assumption.
      3: reflexivity.
      2: { simpl in H. lia. }
      2: { simpl in H2. by apply andb_true_iff in H2 as []. }
      subst. inv H1. inv H5.
      + (* params remain *)
        eapply IHl.
        { simpl in *. lia. }
        { simpl in *. by apply andb_true_iff in H2 as []. }
        { econstructor. constructor. congruence. exact H8. }
        { assumption. }
        { clear-H0. simpl in *. rewrite length_app. simpl.
          by replace (S (length el + (length vals + 1))) with
            (S (S (length el + length vals))) by lia. }
      + (* final step *)
        cbn in H14.
        pose proof is_safe_eval _ _ _ H0 (vals ++ [va]) ltac:(rewrite length_app; slia) as [v [eff ?]].
        rewrite H1 in H14. inv H14.
        inv H8. by eexists. inv H5.
Qed.

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
    { (* The bracketed subgoals in the following proofs are completely symmetric
         They are proved almost always the same way, with the same script. *)
      apply CONG; auto.
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
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      - by apply indexed_to_forall in H3.
      - apply indexed_to_forall in H3.
        induction H3; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - clear - H0 H H3. induction el; constructor.
        2: apply IHel. 2: by simpl in H0; lia.
        2: intros; apply (H3 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H3 0). slia.
    }
    {
      apply CONG; auto.
      - apply indexed_to_forall in H3.
        induction H3; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - by apply indexed_to_forall in H3.
      - clear - H0 H H3. induction el; constructor.
        2: apply IHel. 2: by simpl in H0; lia.
        2: intros; apply (H3 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H3 0). slia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1-2: by apply closed_seq_elim.
      1-2: eapply H; try reflexivity; try lia; assumption.
    }
    {
      apply CONG; auto.
      1-2: by apply closed_seq_elim.
      1-2: eapply H; try reflexivity; try lia; assumption.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      - by apply indexed_to_forall in H3.
      - apply indexed_to_forall in H3.
        induction H3; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - clear - H0 H H3. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H3 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H3 0). slia.
    }
    {
      apply CONG; auto.
      - apply indexed_to_forall in H3.
        induction H3; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - by apply indexed_to_forall in H3.
      - clear - H0 H H3. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H3 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H3 0). slia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      pose proof (Forall_pair _ _ _ _ _ H2 H5). clear H2 H5.
      apply CONG; auto.
      - eapply Forall_impl. 2: exact H1. intros. by destruct a.
      - induction H1; constructor. 2: apply IHForall. 2: by simpl in H0; lia.
        destruct x; unfold PBoth; destruct_and?; split; by apply closed_seq_elim.
      - clear - H1 H H0. induction H1; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        destruct x. split;
        eapply H; try reflexivity; try (simpl in H0; lia).
        all: apply H1.
    }
    {
      pose proof (Forall_pair _ _ _ _ _ H2 H5). clear H2 H5.
      apply CONG; auto.
      - induction H1; constructor. 2: apply IHForall. 2: by simpl in H0; lia.
        destruct x; unfold PBoth; destruct_and?; split; by apply closed_seq_elim.
      - eapply Forall_impl. 2: exact H1. intros. by destruct a.
      - clear - H1 H H0. induction H1; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        destruct x. split;
        eapply H; try reflexivity; try (simpl in H0; lia).
        all: apply H1.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1-2: by apply closed_seq_elim.
      1-2: eapply H; try reflexivity; try assumption; lia.
      - by apply indexed_to_forall in H6.
      - apply indexed_to_forall in H6.
        induction H6; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - clear - H0 H H6. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H6 0). slia.
    }
    {
      apply CONG; auto.
      1-2: by apply closed_seq_elim.
      1-2: eapply H; try reflexivity; try assumption; lia.
      - apply indexed_to_forall in H6.
        induction H6; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - by apply indexed_to_forall in H6.
      - clear - H0 H H6. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H6 0). slia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      - by apply indexed_to_forall in H3.
      - apply indexed_to_forall in H3.
        induction H3; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - clear - H0 H H3. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H3 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H3 0). slia.
    }
    {
      apply CONG; auto.
      - apply indexed_to_forall in H3.
        induction H3; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - by apply indexed_to_forall in H3.
      - clear - H0 H H3. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H3 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H3 0). slia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1: by apply closed_seq_elim.
      3: eapply H; try reflexivity; try assumption; lia.
      - by apply indexed_to_forall in H6.
      - apply indexed_to_forall in H6.
        induction H6; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - clear - H0 H H6. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H6 0). slia.
    }
    {
      apply CONG; auto.
      1: by apply closed_seq_elim.
      3: eapply H; try reflexivity; try assumption; lia.
      - apply indexed_to_forall in H6.
        induction H6; constructor.
        2: apply IHForall. 2: by simpl in H0; lia.
        by apply closed_seq_elim.
      - by apply indexed_to_forall in H6.
      - clear - H0 H H6. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        eapply H. 2: reflexivity. 1: { simpl in H0. lia. }
        apply (H6 0). slia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1: by apply closed_seq_elim.
      3: eapply H; try reflexivity; try assumption; lia.
      - eapply indexed_to_forall with (def := ([], ˝VNil, ˝VNil)). intros. 
        apply H6 in H1 as H'1.
        apply H7 in H1 as H'2.
        setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H'1.
        setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H'2.
        destruct nth, p. by auto.
      - induction l; constructor. 2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        2: intros; apply (H7 (S i)); slia.
        clear IHl.
        destruct a, p; simpl in *.
        split; apply closed_seq_elim.
        1: apply (H6 0); slia.
        1: apply (H7 0); slia.
      - clear - H6 H7 H H0. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        2: intros; apply (H7 (S i)); slia.
        clear IHl.
        destruct a, p. split; auto. split;
        eapply H; try reflexivity; try (simpl in H0; lia).
        1: apply (H6 0); slia.
        1: apply (H7 0); slia.
    }
    {
      apply CONG; auto.
      1: by apply closed_seq_elim.
      3: eapply H; try reflexivity; try assumption; lia.
      - induction l; constructor. 2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        2: intros; apply (H7 (S i)); slia.
        clear IHl.
        destruct a, p; simpl in *.
        split; apply closed_seq_elim.
        1: apply (H6 0); slia.
        1: apply (H7 0); slia.
      - eapply indexed_to_forall with (def := ([], ˝VNil, ˝VNil)). intros. 
        apply H6 in H1 as H'1.
        apply H7 in H1 as H'2.
        setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H'1.
        setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)) in H'2.
        destruct nth, p. by auto.
      - clear - H6 H7 H H0. induction l; constructor.
        2: apply IHl. 2: by simpl in H0; lia.
        2: intros; apply (H6 (S i)); slia.
        2: intros; apply (H7 (S i)); slia.
        clear IHl.
        destruct a, p. split; auto. split;
        eapply H; try reflexivity; try (simpl in H0; lia).
        1: apply (H6 0); slia.
        1: apply (H7 0); slia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1-2: by apply closed_seq_elim.
      1-2: eapply H; try reflexivity; try lia; assumption.
    }
    {
      apply CONG; auto.
      1-2: by apply closed_seq_elim.
      1-2: eapply H; try reflexivity; try lia; assumption.
    }
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
          
          apply term_eval_empty in H3 as HELPER.
          destruct HELPER as [? [x0 [Helpres [HELPER _]]]].
          pose proof HELPER as EVAL.
          apply (conj Helpres), ex_intro with (x := x0) in HELPER.
          epose proof will_fail_exception (seq_elim e1).[ξ] _ H4' HELPER as [exc EQ].
          subst. clear HELPER. (* now we can use EVAL for showing the exception *)
          
          eapply frame_indep_nil in EVAL as D1'.
          eapply term_step_term in H3. 2: exact D1'.
          inv H3.
          eexists.
          eapply step_term_term_plus.
          eapply frame_indep_nil in EVAL. exact EVAL.
          exact H11.
        }
        {
          eapply is_safe_simple_subst with (ξ := ξ) in H5. 2: eassumption.
          2: apply closed_seq_elim; by destruct_scopes.
          pose proof (H (size_exp e1) ltac:(lia) e1 ltac:(lia) Γ
            ltac:(by destruct_scopes)) as [CIUe1_1 CIUe1_2].
          eapply term_eval_empty in H9 as D'.
          destruct D' as [res [k1' [Hres [D' Hlt]]]].
          pose proof (CIUe1_1 _ H2).
          pose proof (CIUe1_2 _ H2).
          
          (* modifications to use is_safe_simple_no_effects *)
          pose proof (ex_intro _ k H9) as HELPER.
          unshelve (epose proof (proj2 (proj2 H6) _ _ HELPER) as [? HELPER2]).
          { split.
            * econstructor. 2: apply H3.
              constructor. apply -> subst_preserves_scope_exp.
              destruct_scopes. eassumption. assumption.
            * constructor; try apply H3. by simpl.
          }
          apply term_eval_empty in HELPER2 as [? [x1 [Helpres [HELPER2 _]]]].
          pose proof HELPER2 as D.
          apply (conj Helpres), ex_intro with (x := x1) in HELPER2.
          eapply is_safe_simple_no_effects in HELPER2 as [v EQ].
          subst. clear HELPER.
          (***)
          
          assert (CIU res (RValSeq [v]) /\ CIU (RValSeq [v]) res). {
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
          (* Here, we use congruence - reshape the goal for it *)
          enough (CIU_open Γ (° ESeq e1 e2) (° ESeq (seq_elim e1) (seq_elim e2))).
          apply H6; try eassumption.
          eexists. simpl. econstructor. eassumption.
          apply CONG. 1-4: try apply closed_seq_elim; by destruct_scopes.
          all: eapply H; [ | reflexivity | by destruct_scopes]; simpl in H0; lia.
        }
      }
      { (* reverse direction *)
        admit.
      }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1: rewrite length_map; by apply closed_seq_elim.
      4: eapply H; try reflexivity; try assumption; lia.
      - eapply indexed_to_forall with (def := (0, ˝VNil)). intros.
        apply H5 in H1 as H'1.
        setoid_rewrite map_nth with (d := (0, ˝VNil)) in H'1.
        destruct nth. by auto.
      - eapply indexed_to_forall with (def := (0, ˝VNil)). intros.
        rewrite length_map in H1. rewrite length_map. apply H5 in H1.
        rewrite map_nth with (d := (0, ˝VNil)).
        setoid_rewrite map_nth with (d := (0, ˝VNil)) in H1.
        destruct nth.
        by apply closed_seq_elim.
      - clear - H5 H H0.
        eapply indexed_to_biforall with (d1 := (0, ˝VNil)) (d2 := (0, ˝VNil)).
        intros. rewrite length_map. split. 2: reflexivity.
        intros. apply H5 in H1 as H5'.
        rewrite map_nth with (d := (0, ˝VNil)).
        setoid_rewrite map_nth with (d := (0, ˝VNil)) in H5'.
        apply nth_In with (d := (0, ˝VNil)) in H1.
        destruct nth. split. reflexivity.
        eapply H; try reflexivity. 2: assumption.
        apply in_split in H1 as [? [? ?]]. subst.
        rewrite map_app, list_sum_app in H0. simpl in H0. lia.
    }
    {
      apply CONG; auto.
      1: rewrite length_map; by apply closed_seq_elim.
      4: rewrite length_map; eapply H; try reflexivity; try assumption; lia.
      - eapply indexed_to_forall with (def := (0, ˝VNil)). intros.
        rewrite length_map in H1. rewrite length_map. apply H5 in H1.
        rewrite map_nth with (d := (0, ˝VNil)).
        setoid_rewrite map_nth with (d := (0, ˝VNil)) in H1.
        destruct nth.
        by apply closed_seq_elim.
      - eapply indexed_to_forall with (def := (0, ˝VNil)). intros.
        apply H5 in H1 as H'1.
        setoid_rewrite map_nth with (d := (0, ˝VNil)) in H'1.
        destruct nth. by auto.
      - clear - H5 H H0.
        eapply indexed_to_biforall with (d1 := (0, ˝VNil)) (d2 := (0, ˝VNil)).
        intros. rewrite length_map. split. 2: reflexivity.
        intros. apply H5 in H1 as H5'.
        rewrite map_nth with (d := (0, ˝VNil)).
        setoid_rewrite map_nth with (d := (0, ˝VNil)) in H5'.
        apply nth_In with (d := (0, ˝VNil)) in H1.
        destruct nth. split. reflexivity.
        eapply H; try reflexivity. 2: assumption.
        apply in_split in H1 as [? [? ?]]. subst.
        rewrite map_app, list_sum_app in H0. simpl in H0. lia.
    }
  * destruct_scopes. simpl in H0. split.
    {
      apply CONG; auto.
      1-3: by apply closed_seq_elim.
      1-3: eapply H; try reflexivity; try lia; assumption.
    }
    {
      apply CONG; auto.
      1-3: by apply closed_seq_elim.
      1-3: eapply H; try reflexivity; try lia; assumption.
    }
Admitted.

Theorem seq_optim (e : Exp) :
  EXPCLOSED e ->
  CIU (seq_elim e) e.
Proof.

Qed.

