From CoreErlang.TMP Require Export Basics.

From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: INDUCTION ////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Induction_Value
* Induction_Expression
*)



(**
NOTES:  Maybe place this in BigStep/Induction
*)






Section Induction_Value.



  Variables
    (P : Value -> Prop).



  Hypotheses
    (HNil : P VNil)

    (HLit :
      forall l,
        P (VLit l))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (VCons hd tl))

    (HClos :
      forall ref ext id params body funid,
          Forall (fun x => P (snd x)) ref
      ->  P (VClos ref ext id params body funid))

    (HTuple :
      forall l,
          Forall P l
      ->  P (VTuple l))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (VMap l)).



  Theorem value_ind :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd x))); intuition.
  Defined.



End Induction_Value.






Section Induction_Expression.



  Variables
    (P : Expression -> Prop).



  Hypotheses
    (HValues :
      forall el,
          Forall P el
      ->  P (EValues el))

    (HNil : P ENil)

    (HLit :
      forall l,
          P (ELit l))

    (HVar :
      forall v,
          P (EVar v))

    (HFunId :
      forall f,
        P (EFunId f))

    (HFun :
      forall vl e,
          P e
      ->  P (EFun vl e))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (ECons hd tl))

    (HTuple :
      forall l,
          Forall P l
      ->  P (ETuple l))

    (HCall :
      forall m f l,
          P m
      ->  P f
      ->  Forall P l
      ->  P (ECall m f l))

    (HPrimOp :
      forall f l,
          Forall P l
      ->  P (EPrimOp f l))

    (HApp :
      forall exp l,
          P exp
      ->  Forall P l
      ->  P (EApp exp l))

    (HCase :
      forall e l,
          P e
      ->  Forall (fun x => P (snd (fst x)) /\ P (snd x)) l
      ->  P (ECase e l))

    (HLet :
      forall l e1 e2,
          P e1
      ->  P e2
      ->  P (ELet l e1 e2))

    (HSeq :
      forall e1 e2,
          P e1
      ->  P e2
      ->  P (ESeq e1 e2))

    (HLetRec :
      forall l e,
          P e
      ->  Forall (fun x => P (snd (snd x))) l
      ->  P (ELetRec l e))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (EMap l))

    (HTry :
      forall e1 vl1 e2 vl2 e3,
          P e1
      ->  P e2
      ->  P e3
      ->  P (ETry e1 vl1 e2 vl2 e3)).



  Theorem exp_ind :
    forall e, P e.
  Proof.
    induction e using Expression_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd (fst x)) /\ P (snd x)))
      (Z := Forall (fun x => P (snd (snd x)))); intuition.
  Defined.



End Induction_Expression.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: WELLFORMEDMAP ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* WellFormedMap
  - well_formed_map_bs
  - well_formed_map_fs
*)



(**
NOTES:  Later change lists to maps in Syntax
*)






Section WellFormedMap.



  Definition well_formed_map_bs
    (v : Value)
    : Prop
    :=
  match v with
  | VMap vl =>
      vl
      =
      let (f , l) :=
        (make_value_map
          (fst (split vl)) 
          (snd (split vl)))
      in zip f l

  | _ => True
  end.



  Fixpoint well_formed_map_fs
    (v : Val)
    : Prop
    :=
  match v with
  | Syntax.VCons hd tl =>
      well_formed_map_fs hd
      /\
      well_formed_map_fs tl

  | Syntax.VTuple l =>
      foldr
        (fun v acc =>
          well_formed_map_fs v /\ acc)
        True 
        l

  | Syntax.VMap l =>
      l = make_val_map l
      /\
      foldr
        (fun v acc =>
          PBoth well_formed_map_fs v /\ acc)
        True
        l

  | _ => True
  end.



End WellFormedMap.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: WELLFORMEDMAPLEMMASS /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Import SubstSemantics.



(**
* Help
  - map_insert_length1 [NotUsing]
  - map_insert_length2
  - make_val_map_length
  - make_val_map_cons
* Main
  - well_formed_map_fs_tuple
  - well_formed_map_fs_map
*)



(**
NOTES:  Later change lists to maps in Syntax
*)






Section WellFormedMapLemmas_Help.



  Theorem map_insert_length1 :
    forall k v ms,
      length ms <= length (map_insert k v ms).
  Proof.
    intros.
    induction ms as [| (key, var) ms IHms].
    * (* Case: ms is empty *)
      slia.
    * (* Inductive case: ms is (key, var) :: ms *)
      fold map_insert in *.
      simpl.
      destruct (k <ᵥ key).
      - (* Case: k <ᵥ key *)
        clear IHms. 
        slia.
      - destruct (k =ᵥ key).
        + (* Case: k =ᵥ key *)
          clear IHms.
          slia.
        + (* Case: k >ᵥ key *)
          by apply le_n_S.
  Qed.



  Theorem map_insert_length2 :
    forall k k' v v' ms,
      length (map_insert k v ms) <= length ((k', v') :: ms).
  Proof.
    intros.
    induction ms as [| (key, var) ms IHms].
    * (* Case: ms is empty *)
      slia.
    * (* Inductive case: ms is (key, var) :: ms *)
      fold map_insert in *.
      simpl.
      destruct (k <ᵥ key).
      - (* Case: k <ᵥ key *)
        clear IHms. 
        slia.
      - destruct (k =ᵥ key).
        + (* Case: k =ᵥ key *)
          clear IHms.
          slia.
        + (* Case: k >ᵥ key *)
          by apply le_n_S.
  Qed.



  Theorem make_val_map_length :
    forall ms,
      length (make_val_map ms) <= length ms.
  Proof.
    induction ms as [| (k, v) ms IHms].
    * (* Base case: ms is empty *)
      slia.
    * (* Inductive case: ms = (k, v) :: ms'*)
      simpl.
      destruct (make_val_map ms) as [| (k', v') ms'].
      - (* Case: make_val_map ms = [] *)
        by apply le_n_S.
      - (* Case: make_val_map ms = (k', v') :: ms' *)
        simpl.
        destruct (k <ᵥ k').
        + (* Case: k <ᵥ k' *)
          simpl in *.
          apply le_n_S.
          apply IHms.
        + destruct (k =ᵥ k').
          ** (* Case: k =ᵥ k' *)
             simpl in *.
             apply le_S.
             apply IHms.
          ** (* Case: k >ᵥ k' *)
             simpl.
             apply le_n_S.
             pose proof map_insert_length2 k k' v v' ms' as Hinsert.
             eapply Nat.le_trans.
             -- apply Hinsert.
             -- apply IHms.
  Qed.



  Theorem make_val_map_cons :
    forall v1 v2 vl,
        (v1, v2) :: vl = make_val_map ((v1, v2) :: vl)
    ->  vl = make_val_map vl.
  Proof.
    intros v1 v2 vl H.
    invc H: H <- H1.
    unfold Maps.map_insert in H.
    destruct (make_val_map vl) as [| (v1', v2') vl'] eqn:Hmake.
    - (* Case: make_val_map vl = [] *)
      clear Hmake.
      by inv H.
    - (* Case: make_val_map vl = (v1', v2') :: vl' *)
      destruct (v1 <ᵥ v1') eqn:Hlt.
      + (* Case: v1 <ᵥ v1' *)
        clear Hmake Hlt.
        by inv H.
      + destruct (v1 =ᵥ v1') eqn:Heq.
        * (* Case: v1 =ᵥ k' *)
          clear Hlt Heq.
          invc H.
          pose proof make_val_map_length vl' as Hlength.
          rewrite Hmake in Hlength.
          simpl in Hlength.
          lia.
        * (* Case: v1 >ᵥ v1' *)
          clear Hmake Hlt.
          invc H.
          rewrite Val_eqb_refl in Heq.
          congruence.
  Qed.



End WellFormedMapLemmas_Help.






Section WellFormedMapLemmas_Main.



  Theorem well_formed_map_fs_tuple :
    forall v vl,
        Forall well_formed_map_fs [VTuple (v :: vl)]
    ->  Forall well_formed_map_fs [v]
    /\  Forall well_formed_map_fs [VTuple vl].
  Proof.
    intros v vl Hvvl.
    invc Hvvl.
    clear H2.
    destruct H1.
    ren Hv Hvl <- H H0.
    split.
    * apply Forall_cons.
      - exact Hv.
      - apply Forall_nil.
    * apply Forall_cons.
      - unfold well_formed_map_fs.
        exact Hvl.
      - apply Forall_nil.
  Qed.



  Theorem well_formed_map_fs_map :
    forall v1 v2 vl,
        Forall well_formed_map_fs [VMap ((v1, v2) :: vl)]
    ->  Forall well_formed_map_fs [v1]
    /\  Forall well_formed_map_fs [v2]
    /\  Forall well_formed_map_fs [VMap vl].
  Proof.
    intros v1 v2 vl Hv1v2vl.
    invc Hv1v2vl.
    clear H2.
    destruct H1 as [Hmake H].
    invc H: Hvl <- H1.
    invc H0: Hv1 Hv2 <- H H1.
    smp in Hv1 Hv2.
    split.
    - clear Hmake Hvl Hv2.
      apply Forall_cons.
      + exact Hv1.
      + apply Forall_nil.
    - clear Hv1.
      split.
      + clear Hmake Hvl.
        apply Forall_cons. 
        * exact Hv2.
        * apply Forall_nil.
      + clear Hv2.
        apply Forall_cons.
        * unfold well_formed_map_fs.
          split. 2: { exact Hvl. }
          clear Hvl.
          by pose proof make_val_map_cons v1 v2 vl Hmake.
       * apply Forall_nil.
  Qed.



End WellFormedMapLemmas_Main.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ENVIRONMENTDEFINITIONS ///////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Import BigStep.



(**
* Help
  - rem_keys
* Main
  - rem_vars
  - rem_fids
  - rem_both
  - rem_nfifes
*)



(**
NOTES:  Maybe place this in BigStep/Environment
*)






Section EnvironmentDefinitions_Help.



  Definition rem_keys
    (keys : list (Var + FunctionIdentifier))
    (env : Environment)
    : Environment
    :=
  fold_left
    (fun env' key =>
      filter (fun '(k, v) =>
        negb (var_funid_eqb k key))
        env')
    keys
    env.



End EnvironmentDefinitions_Help.






Section EnvironmentDefinitions_Main.



  Definition rem_vars
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inl vars) env.



  Definition rem_fids
    (fids : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr (map fst fids)) env.



  Definition rem_both
    (fids : list (FunctionIdentifier * FunctionExpression))
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_fids fids (rem_vars vars env).



  Definition rem_nfifes
    (nfifes : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr (map snd (map fst nfifes))) env.



End EnvironmentDefinitions_Main.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ENVIRONMENTLEMMAS ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - Get
    + get_value_cons
  - Remove
    + rem_keys_empty
* Main
  - Fold
    + rem_keys_fold
    + rem_vars_unfold
    + rem_fids_unfold
    + rem_both_unfold
    + rem_nfifes_unfold
  - Get
    + can_get_value_than_in
    + get_value_singelton
    + get_value_singelton_length
  - Remove
    + rem_vars_empty
    + rem_fids_empty
    + rem_both_empty
    + rem_nfifes_empty
    + rem_both_empty_map [NotUsing]
*)



(**
NOTES:  Maybe place this in BigStep/Environment
*)






Section EnvironmentLemmas_Help.



  Section EnvironmentLemmas_Help_Get.

    Lemma get_value_cons :
      forall env key k var v,
          get_value ((k, v) :: env) key = Some [var]
      ->  get_value [(k, v)] key = Some [var] 
      \/  get_value env key = Some [var].
    Proof.
      intros env key k var v Hcons.
      unfold get_value in Hcons.
      remember
        (var_funid_eqb key k)
        as _key_eqb.
      symmetry in Heq_key_eqb.
      destruct _key_eqb.
      * left.
        clear env.
        inv Hcons.
        unfold var_funid_eqb in Heq_key_eqb.
        destruct key.
        - destruct k.
          + cbn.
            rewrite Heq_key_eqb.
            reflexivity.
          + congruence.
        - destruct k.
          + congruence.
          + cbn.
            rewrite Heq_key_eqb.
            reflexivity.
      * right.
        exact Hcons.
    Qed.

  End EnvironmentLemmas_Help_Get.



  Section EnvironmentLemmas_Help_Remove.

    Lemma rem_keys_empty :
      forall keys,
        rem_keys keys [] = [].
    Proof.
      intros.
      unfold rem_keys.
      induction keys.
      * by cbn.
      * cbn.
        by rewrite IHkeys.
    Qed.

  End EnvironmentLemmas_Help_Remove.



End EnvironmentLemmas_Help.






Section EnvironmentLemmas_Main.



  Section EnvironmentLemmas_Main_Fold.

    Lemma rem_keys_fold :
      forall keys env,
        fold_left
          (λ (env' : list ((Var + FunctionIdentifier) * Value))
             (key : Var + FunctionIdentifier),
            filter
              (λ '(k, _), negb (var_funid_eqb k key))
              env')
          keys
          env
      = rem_keys keys env.
    Proof.
      by int.
    Qed.

    Lemma rem_vars_fold :
      forall vars env,
        rem_keys (map inl vars) env
      = rem_vars vars env.
    Proof.
      by int.
    Qed.

    Lemma rem_fids_fold :
      forall fids env,
        rem_keys (map inr (map fst fids)) env
      = rem_fids fids env.
    Proof.
      by int.
    Qed.

    Lemma rem_both_fold :
      forall fids vars env,
        rem_fids fids (rem_vars vars env)
      = rem_both fids vars env.
    Proof.
      by int.
    Qed.

    Lemma rem_nfifes_unfold :
      forall nfifes env,
        rem_keys (map inr (map snd (map fst nfifes))) env
      = rem_nfifes nfifes env.
    Proof.
      by int.
    Qed.

  End EnvironmentLemmas_Main_Fold.



  Section EnvironmentLemmas_Main_Get.

    Theorem get_value_in :
      forall env key var,
          get_value env key = Some [var]
      ->  In (key , var) env.
    Proof.
      intros env.
      induction env; intros key var Hget_value.
      * inv Hget_value.
      * destruct a as [k v].
        apply get_value_cons in Hget_value.
        destruct Hget_value.
        - clear IHenv.
          rename H into Hget_value.
          unfold get_value in Hget_value.
          remember
            (var_funid_eqb key k)
            as key_eqb
            eqn:Heq_key_eqb.
          symmetry in Heq_key_eqb.
          destruct key_eqb.
          + inv Hget_value.
            apply var_funid_eqb_eq in Heq_key_eqb.
            rewrite <- Heq_key_eqb.
            clear Heq_key_eqb k.
            constructor.
            clear env.
            reflexivity.
          + clear Heq_key_eqb.
            congruence.
        - rename H into Hget_value.
          specialize (IHenv key var Hget_value).
          pose proof in_cons (k, v) (key, var) env IHenv.
          clear IHenv Hget_value.
          assumption.
    Qed.

    Lemma get_value_singelton :
      forall env key vs,
          get_value env key = Some vs
      ->  exists value, vs = [value].
    Proof.
       intros env key vs.
       induction env as [| [k v] env IHenv]; intros Hget; cbn in Hget.
       * congruence.
       * destruct (var_funid_eqb key k) eqn:Heqb.
         - exists v.
           by inv Hget.
         - by apply IHenv.
    Qed.

    Lemma get_value_singelton_length :
      forall env key l,
          get_value env key = Some l
      ->  length l = 1.
    Proof.
       intros env key vs Hget.
       pose proof get_value_singelton env key vs Hget as Hsingelton.
       by invc Hsingelton.
    Qed.

  End EnvironmentLemmas_Main_Get.



  Section EnvironmentLemmas_Main_Remove.

    Lemma rem_vars_empty :
      forall vars,
        rem_vars vars [] = [].
    Proof.
      intros.
      unfold rem_vars.
      by rewrite rem_keys_empty.
    Qed.

    Lemma rem_fids_empty :
      forall fids,
        rem_fids fids [] = [].
    Proof.
      intros.
      unfold rem_fids.
      by rewrite rem_keys_empty.
    Qed.

    Lemma rem_both_empty :
      forall fids vars,
        rem_both fids vars [] = [].
    Proof.
      intros.
      unfold rem_both.
      rewrite rem_vars_empty.
      rewrite rem_fids_empty.
      reflexivity.
    Qed.

    Lemma rem_nfifes_empty :
      forall ext,
        rem_nfifes ext [] = [].
    Proof.
      intros.
      unfold rem_nfifes.
      by rewrite rem_keys_empty.
    Qed.

    Lemma rem_both_empty_map :
      forall (f : Environment -> Expression -> Expression) el,
        map
          (fun  '(fid, (vl, b)) =>
            (fid, (vl, f (rem_both el vl []) b)))
          el
      = map
          (fun '(fid, (vl, b)) =>
            (fid, (vl, f [] b)))
          el.
    Proof.
      intros.
      apply map_ext.
      intros [fid [vl b]].
      by rewrite rem_both_empty.
    Qed.

  End EnvironmentLemmas_Main_Remove.



End EnvironmentLemmas_Main.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: FRAMESTACKLEMMAS /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* FrameStackLemmas
  - framestack_ident
  - framestack_ident_rev [Admitted]
*)



(**
Note: Maybe place this into CoreErlang.FrameStack/SubstSemanticsLemmas
*)


Section FrameStackLemmas.



  Theorem framestack_ident :
    forall ident el vl vl' r x eff Fs,
        create_result ident (vl ++ x :: vl') [] = Some (r , eff)
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl'
    ->  exists k, 
          ⟨ FParams ident vl el :: Fs, RValSeq [x] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    intros ident el vl vl' r x eff Fs Hcreate Hbiforall.
    generalize dependent r.
    generalize dependent vl'.
    revert vl.
    revert x.
    induction el; intros.
    * invc Hbiforall.
      exists 1.
      econstructor.
      econstructor.
      by symmetry.
      constructor.
    * invc Hbiforall.
      rename H3 into Hbiforall.
      destruct H1 as [khd [Hhd Dhd]].
      replace
        (vl ++ x :: hd' :: tl') with
        ((vl ++ [x]) ++ hd' :: tl') 
        in Hcreate.
      2:
      {
        rewrite <- app_assoc.
        by rewrite <- app_cons_swap.
      }
      specialize (IHel _ _ _ Hbiforall _ Hcreate).
      destruct IHel as [kIH DIH].
      eexists.
      econstructor.
      constructor.
      eapply transitive_eval.
      eapply frame_indep_core in Dhd. 
      exact Dhd.
      simpl.
      exact DIH.
  Qed.



  Theorem framestack_ident_rev :
    forall el ident vl e k r,
        ⟨ [FParams ident vl el], RExp e ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
    ->  exists v vl' eff,
            create_result ident (vl ++ v :: vl') [] = Some (RValSeq r, eff)
        /\  list_biforall 
              (λ (e0 : Exp) (v : Val), ⟨ [], RExp e0 ⟩ -->* RValSeq [v])
              (e :: el)
              (v :: vl').
  Proof.
    induction el; intros.
    * Search step_rt.
      pose proof term_eval.
      pose proof terminates_in_k_eq_terminates_in_k_sem.
      unfold terminates_in_k_sem in H1.
      assert (is_result r).
      {
        constructor.
        admit. (*scope *)
      }
      pose proof conj H2 H.
      apply ex_intro with (x := RValSeq r) in H3.
      apply H1 in H3.
      apply H0 in H3. 2:
      {
        admit. (* scope *)
      }
      destruct H3 as [v [k0 [Hres [Hv Hk]]]].
      invc Hres.
      {
        pose proof transitive_eval_rev. (* H Hv *) (* inv H*)
        admit.
      }
      admit.
    * admit.
  Admitted.



End FrameStackLemmas.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SCOPINGLEMMAS ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Import SubstSemantics.



(**
* ScopingLemmas
  - scope_vl_succ
  - scope_vl_succ_id
*)



(**
NOTES:  Maybe place this in CoreFrameStack/Scoping! or into FrameStack
*)






Section ScopingLemmas.



Theorem scope_vl_succ :
  forall A i vl (f : A -> Val),
      (∀ i : nat, i < length vl → VALCLOSED (nth i (map f vl) VNil))
  ->  (S i < S (length vl) → VALCLOSED (nth i (map f vl) VNil)).
Proof.
  intros A i vl f Hvl.
  specialize (Hvl i).
  intros Hsucc_lt.
  pose proof Nat.succ_lt_mono 
    as Hmono_succ_lt.
  specialize (Hmono_succ_lt i (base.length vl)).
  destruct Hmono_succ_lt
    as [Hto_succ_lt Hfrom_succ_lt].
  clear Hto_succ_lt.
  apply Hfrom_succ_lt
    in Hsucc_lt 
    as Hlt.
  clear Hfrom_succ_lt Hsucc_lt.
  apply Hvl in Hlt.
  clear Hvl.
  rename Hlt into Hvl.
  exact Hvl.
Qed.



Theorem scope_vl_succ_id :
  forall i vl,
      (∀ i : nat, i < length vl → VALCLOSED (nth i vl VNil))
  ->  (S i < S (length vl) → VALCLOSED (nth i vl VNil)).
Proof.
  intros i vl Hvl.
  assert (map id vl = vl).
  {
    apply Basics.map_id.
  }
  remember
    (base.length vl)
    as _n.
  rewrite <- H.
  rewrite <- H in Hvl.
  rewrite Heq_n in *.
  clear Heq_n _n H.
  pose proof scope_vl_succ Val i vl id Hvl.
  assumption.
Qed.



End ScopingLemmas.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MEASURE //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Import BigStep.



(**
* Help
  - Generic
    + measure_list
    + measure_map
  - Expression
    + measure_case
    + measure_letrec
  - Value
    + measure_env
* Main
  - measure_exp
  - measure_val
  - measure_env_exp
*)






Section Measure_Help.



  Section Measure_Help_Generic.

    Definition measure_list
      {A : Type}
      (f : A -> nat)
      (al : list A)
      : nat 
      :=
    list_sum (map f al).

    Definition measure_map
      {A : Type}
      (f : A -> nat)
      (aml : list (A * A))
      : nat
      :=
    list_sum (map (fun '(a1, a2) => (f a1) + (f a2)) aml).

  End Measure_Help_Generic.



  Section Measure_Help_Expression.

    Definition measure_case
      (f : Expression -> nat)
      (cl : list ((list Pattern) * Expression * Expression))
      : nat
      :=
    list_sum (map (fun '(pl, g, b) => (f g) + (f b)) cl).

    Definition measure_letrec
      (f : Expression -> nat)
      (lrl : list (FunctionIdentifier * (list Var * Expression)))
      : nat
      :=
    list_sum (map (fun '(fid, (vl, b)) => (f b)) lrl).

  End Measure_Help_Expression.



  Section Measure_Help_Value.

    Definition measure_env
      (f : Value -> nat)
      (env : Environment)
      : nat
      :=
    list_sum (map (fun '(vf, v) => (f v)) env).

  End Measure_Help_Value.



End Measure_Help.






Section Measure_Main.



  Fixpoint measure_exp
    (e : Expression)
    : nat
    :=
  match e with
  | ENil => 1
  | ELit l => 1
  | EVar v => 1
  | EFunId f => 1

  | EFun vl e => 1
      + measure_exp e

  | ECons hd tl => 1
      + measure_exp hd
      + measure_exp tl

  | ESeq e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ELet l e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ETry e1 vl1 e2 vl2 e3 => 1
      + measure_exp e1
      + measure_exp e2
      + measure_exp e3

  | EValues el => 1
      + measure_list measure_exp el

  | EPrimOp f l => 1
      + measure_list measure_exp l

  | ETuple l => 1
      + measure_list measure_exp l

  | EMap l =>  1
      + measure_map measure_exp l

  | EApp exp l => 1
      + measure_exp exp
      + measure_list measure_exp l

  | ECall m f l => 1
      + measure_exp m
      + measure_exp f
      + measure_list measure_exp l

  | ECase e l => 1
      + measure_exp e
      + measure_case measure_exp l

  | ELetRec l e => 1
      + measure_exp e
      + measure_letrec measure_exp l
  end.



  Fixpoint measure_val
    (v : Value) 
    : nat
    :=
  match v with
  | VNil => 1
  | VLit l => 1

  | VCons hd tl => 1
      + measure_val hd
      + measure_val tl

  | VTuple l => 1
      + measure_list measure_val l

  | VMap l => 1
      + measure_map measure_val l

  | VClos env ext id vl e fid => 1
      + measure_exp e
      + measure_env measure_val env
  end.



  Definition measure_env_exp
    (env : Environment)
    (e : Expression)
    : nat
    :=
  measure_exp e
  + measure_env measure_val env.



End Measure_Main.