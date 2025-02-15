From CoreErlang.Eqvivalence.BsFs Require Export BX1EraseNames.

Import BigStep.

(** CONTENT:
* MEASURE_REDUCTION (TACTICS/LEMMAS/THEOREMS)
  - MeasureReduction_LesserOrEqualTactics (TACTICS)
    + mred_le_solver
    + ass_le
    + ass_le_trn
  - MeasureReduction_MeasureValueLemmas (LEMMAS)
    + measure_val_not_zero
    + measure_env_list_eq
  - MeasureReduction_RemoveFromEnvironmentLemmas (LEMMAS)
    + rem_keys_length
    + rem_ext_vars_length
    + rem_ext_vars_single
    + rem_keys_cons
    + rem_ext_vars_cons
  - MeasureReduction_ListSubstTheorems (THEOREMS)
    + functions_equal_pointwise
    + list_subst_inj
  - MeasureReduction_InductionTheorems (THEOREMS)
    + measure_reduction_vnil
    + measure_reduction_vlit
    + measure_reduction_vcons
    + measure_reduction_vtuple
    + measure_reduction_vmap
    + measure_reduction_vclos
  - MeasureReduction_MainTheorem (THEOREMS)
    + measure_reduction
  - MeasureReduction_ListTheorems (THEOREMS)
    + measure_reduction_list
    + measure_reduction_map
    + measure_reduction_env
  - MeasureReduction_MinimalizeTheorems (THEOREMS)
    + mred_min
    + mred_min_list
    + mred_min_map
    + mred_min_env
  - MeasureReduction_AbsoluteMinimalizeTheorems (THEOREMS)
    + mred_absmin_list
    + mred_absmin_list_any
    + mred_absmin_map
    + mred_absmin_env
  - MeasureReduction_RewriteTactics (TACTICS)
    + mred
* ERASE_VAL_REM_FUEL (THEOREMS/Tactics)
  - EraseValRemFuel_Theorems (THEOREMS)
    + erase_val_rem_fuel
    + erase_val_rem_fuel_any
    + erase_val_rem_fuel_list
    + erase_val_rem_fuel_map
  - EraseValRemFuel_Tactics (TACTICS)
    + mvr
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_REDUCTION ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






(* Section: MeasureReduction_LesserOrEqualTactics. *)



(* Trivial *)

  Ltac mred_le_solver :=
    smp;
    try unfold measure_val_list;
    try unfold measure_val_map;
    try unfold measure_val_env;
    try rewrite map_app, list_sum_app;
    sli.






(* Less or Equal *)

  Tactic Notation "ass_le"
      "as"  ident(Ile)
      ":"   constr(Cle)
      :=
    assert Cle as Ile by mred_le_solver.

  Tactic Notation "ass_le"
      ">"   constr(Cle)
      "as"  ident(Ile)
      ":"   hyp(Hm1) hyp(Hm2)
      :=
    assert Cle as Ile by
      (rewrite Hm1, Hm2;
      mred_le_solver).

  Tactic Notation "ass_le"
      ">"   constr(Cle)
      "as"  ident(Ile)
      ":"   hyp(Hm1) hyp(Hm2) hyp(Hm3)
      :=
    assert Cle as Ile by
      (rewrite Hm1, Hm2, Hm3;
      mred_le_solver).



  Tactic Notation "ass_le_trn"
      ">"   constr(Cle_n1_n3)
      "as"  ident(Ile_n1_n3)
      ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3)
      :=
    assert Cle_n1_n3 as Ile_n1_n3 by
      (eapply Nat.le_trans;
        [exact Hle_n1_n2 | exact Hle_n2_n3]).

  Tactic Notation "ass_le_trn"
      ">"   constr(Cle_n1_n4)
      "as"  ident(Ile_n1_n4)
      ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3) hyp(Hle_n3_n4)
      :=
    assert Cle_n1_n4 as Ile_n1_n4 by
      (eapply Nat.le_trans;
        [eapply Nat.le_trans;
          [exact Hle_n1_n2 | exact Hle_n2_n3]
        | exact Hle_n3_n4]).



(* End: MeasureReduction_LesserOrEqualTactics. *)









Section MeasureReduction_MeasureValueLemmas.



  Lemma measure_val_not_zero :
    forall v,
      0 < measure_val v.
  Proof.
    itr - v.
    des - v; sli.
  Qed.



  Lemma measure_env_list_eq :
    forall Γ,
      measure_val_env measure_val Γ
    = measure_val_list measure_val (map snd Γ).
  Proof.
    itr.
    unfold measure_val_env.
    unfold measure_val_list.
    rwr - map_map.
    trv.
  Qed.



End MeasureReduction_MeasureValueLemmas.









Section MeasureReduction_RemoveFromEnvironmentLemmas.



  Lemma env_rem_key_one_length :
    forall x k,
      length x -ᵏ k <= length [x].
  Proof.
    itr - x k.
    des - x as [k₁ v₁].
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁) :- sli.
  Qed.



  Lemma env_rem_key_length :
    forall Γ k,
      length Γ /ᵏ k <= length Γ.
  Proof.
    itr - Γ k.
    ind - Γ as [| [k₁ v₁] Γ IHΓ]:
          sli.
    rwr - cons_app
          env_rem_key_app
          length_app
          length_app.
    replace ([k₁ ⇰ v₁] /ᵏ k) with ((k₁ ⇰ v₁) -ᵏ k).
          2: ufl - env_rem_key env_rem_key_one; smp; bwr - app_nil_r.
    pse - env_rem_key_one_length as Hx₁:
          (k₁ ⇰ v₁) k.
    app - Nat.add_le_mono;
          asm.
  Qed.



  Lemma env_rem_keys_length :
    forall Γ ks,
      length Γ //ᵏ ks <= length Γ.
  Proof.
    itr - Γ ks.
    ind - ks as [| k₁ ks IHks]:
          sli.
    rwr - cons_app
          env_rem_keys_app_r.
    replace (Γ //ᵏ ks //ᵏ [k₁]) with (Γ //ᵏ ks /ᵏ k₁).
          2: bmp.
    pse - env_rem_key_length as Hk₁:
          (Γ //ᵏ ks) k₁.
    lia.
  Qed.



  Lemma env_rem_ext_vars_length :
    forall Γ xs os,
      length (Γ //ˣ xs //ᵒ os) <= length Γ.
  Proof.
    itr.
    rwl - env_rem_ext_vars_r.
    app - env_rem_keys_length.
  Qed.






  Lemma env_rem_key_single :
    forall k v k',
        [k ⇰ v] /ᵏ k'
      = [k ⇰ v]
    \/  [k ⇰ v] /ᵏ k'
      = [].
  Proof.
    itr.
    smp.
    ufl - env_rem_key_one.
    smp.
    des > (k' =ᵏ k).
    * rgt.
      bmp.
    * lft.
      bmp.
  Qed.



  Lemma env_rem_keys_single :
    forall k v ks,
        [k ⇰ v] //ᵏ ks
      = [k ⇰ v]
    \/  [k ⇰ v] //ᵏ ks
      = [].
  Proof.
    itr.
    ind - ks as [| k₁ ks IHks]:
          smp; lft.
    smp.
    des - IHks as [Hsame | Hempty].
    * cwr - Hsame.
      app - env_rem_key_single.
    * cwr - Hempty.
      smp.
      by rgt.
  Qed.



  Lemma env_rem_ext_vars_single :
    forall k v xs os,
        [k ⇰ v] //ˣ xs //ᵒ os
      = [k ⇰ v]
    \/  [k ⇰ v] //ˣ xs //ᵒ os
      = [].
  Proof.
    itr.
    ufl - env_rem_ext
          env_rem_fids
          env_rem_vars
          get_fids.
    pse - env_rem_keys_single as Hxs:
          k v (↤⟦xs⟧ : list Key).
    des - Hxs as [Hxs_same | Hxs_empty].
    * cwr - Hxs_same.
      pse - env_rem_keys_single as Hos:
            k v (⟦map (snd ∘ fst) os⟧↦ : list Key).
      des - Hos as [Hos_same | Hos_empty].
      - cwr - Hos_same.
        by lft.
      - cwr - Hos_empty.
        by rgt.
    * cwr - Hxs_empty.
      rwr - env_rem_keys_nil_l.
      by rgt.
  Qed.






  Lemma env_rem_keys_cons :
    forall k v Γ ks,
      ((k ⇰ v) :: Γ) //ᵏ ks
    = [k ⇰ v] //ᵏ ks ++ Γ //ᵏ ks.
  Proof.
    itr.
    bwr - cons_app
          env_rem_keys_app_l.
  Qed.



  Lemma env_rem_ext_vars_cons :
    forall k v Γ xs os,
      ((k ⇰ v) :: Γ) //ˣ xs //ᵒ os
    = [k ⇰ v] //ˣ xs //ᵒ os ++ Γ //ˣ xs //ᵒ os.
  Proof.
    itr.
    rwl - env_rem_ext_vars_r.
    ufl - env_rem_ext
          env_rem_fids
          env_rem_vars
          get_fids.
    rwr - env_rem_keys_cons
          env_rem_keys_app_r.
    replace (map (inr ∘ snd ∘ fst) os : list Key)
          with (⟦map (snd ∘ fst) os⟧↦ : list Key).
          2: bwr - map_map.
    bwr - env_rem_keys_app_r.
  Qed.



End MeasureReduction_RemoveFromEnvironmentLemmas.









Section MeasureReduction_ListSubstTheorems.



  Theorem functions_equal_pointwise :
    forall (A B : Type) (f1 f2 : A -> B),
      f1 = f2 ->
      forall x, f1 x = f2 x.
  Proof.
    itr - A B f1 f2 H_eq x.
    bwr - H_eq.
  Qed.



  Theorem list_subst_inj :
    forall vs1 vs2,
        length vs1 = length vs2
    ->  list_subst vs1 idsubst = list_subst vs2 idsubst
    ->  vs1 = vs2.
  Proof.
    itr - vs1 vs2 Hlen Hsubst.
    rem - vs as Hzip:
      (zip vs1 vs2).
    pose proof zip_equal _ _ vs vs1 vs2 Hlen Hzip as Heq.
    des - Heq as [Hvs1 Hvs2].
    cwr - Hvs1 Hvs2 / vs1 vs2.
    clr - Hlen Hzip.
    ind - vs as [| [v1 v2] vs IHvs]: smp.
    smp *.
    pose proof functions_equal_pointwise _ _
      (v1 .: list_subst (map fst vs) idsubst)
      (v2 .: list_subst (map snd vs) idsubst)
      Hsubst.
    spe - H: 0.
    smp - H.
    ivc - H.
    ren - v: v2.
    feq.
    unfold scons in Hsubst.
    ass >
      ((fun x => list_subst (map fst vs) idsubst x) =
      (fun x => list_subst (map snd vs) idsubst x)).
    1: {
      clr - IHvs.
      apply functional_extensionality.
      intros x.
      pose proof functions_equal_pointwise _ _
        (fun x => match x with
                  | 0 => inl v
                  | S y => list_subst (map fst vs) idsubst y
                  end)
        (fun x => match x with
                  | 0 => inl v
                  | S y => list_subst (map snd vs) idsubst y
                  end)
        Hsubst (S x).
      des - x; asm.
    }
    spe - IHvs: H.
    asm.
  Qed.



End MeasureReduction_ListSubstTheorems.









Section MeasureReduction_InductionTheorems.



  Lemma measure_reduction_vnil :
    forall n1 n2,
        measure_val VNil <= n1
    ->  measure_val VNil <= n2
    ->  erase_val n1 VNil
      = erase_val n2 VNil.
  Proof.
    itr - n1 n2 Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    bmp.
  Qed.






  Lemma measure_reduction_vlit :
    forall lit n1 n2,
        measure_val (VLit lit) <= n1
    ->  measure_val (VLit lit) <= n2
    ->  erase_val n1 (VLit lit)
      = erase_val n2 (VLit lit).
  Proof.
    itr - lit n1 n2 Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    bmp.
  Qed.






  Lemma measure_reduction_vcons :
    forall v1 v2 n1 n2,
        (forall n1 n2,
            measure_val v1 <= n1
        ->  measure_val v1 <= n2
        ->  erase_val n1 v1
          = erase_val n2 v1)
    ->  (forall n1 n2,
            measure_val v2 <= n1
        ->  measure_val v2 <= n2
        ->  erase_val n1 v2
          = erase_val n2 v2)
    ->  measure_val (VCons v1 v2) <= n1
    ->  measure_val (VCons v1 v2) <= n2
    ->  erase_val n1 (VCons v1 v2)
      = erase_val n2 (VCons v1 v2).
  Proof.
    itr - v1 v2 n1 n2 IHv1 IHv2 Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    smp.
    ass > (measure_val v1 ≤ n1) as Hv1n1: smp - Hn1; lia.
    ass > (measure_val v1 ≤ n2) as Hv1n2: smp - Hn2; lia.
    ass > (measure_val v2 ≤ n1) as Hv2n1: smp - Hn1; lia.
    ass > (measure_val v2 ≤ n2) as Hv2n2: smp - Hn2; lia.
    spc - IHv1: n1 n2 Hv1n1 Hv1n2.
    spc - IHv2: n1 n2 Hv2n1 Hv2n2.
    bwr - IHv1 IHv2.
  Qed.






  Lemma measure_reduction_vtuple :
    forall vl n1 n2,
        (Forall
          (fun v =>
            (forall n1 n2,
                measure_val v <= n1
            ->  measure_val v <= n2
            ->  erase_val n1 v
              = erase_val n2 v))
          vl)
    ->  measure_val (VTuple vl) <= n1
    ->  measure_val (VTuple vl) <= n2
    ->  erase_val n1 (VTuple vl)
      = erase_val n2 (VTuple vl).
  Proof.
    itr - vl n1 n2 IFH Hn1 Hn2.
    ind - vl as [| v vl].
    * clr - IFH.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      bmp.
    * ivc - IFH as IHv IFH: H1 H2.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      smp.
      ufl - measure_val_list in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val (VTuple vl) ≤ S n1) as Hvln1:
        smp; ufl - measure_val_list; lia.
      ass > (measure_val (VTuple vl) ≤ S n2) as Hvln2:
        smp; ufl - measure_val_list; lia.
      spc - IHv: n1 n2 Hvn1 Hvn2.
      spc - IHvl: IFH Hvln1 Hvln2.
      smp - IHvl.
      ivc - IHvl as IHvl: H0.
      bwr - IHv IHvl.
  Qed.






  Lemma measure_reduction_vmap :
    forall vll n1 n2,
        (Forall
          (fun v =>
            (forall n1 n2,
                measure_val v.1 <= n1
            ->  measure_val v.1 <= n2
            ->  erase_val n1 v.1
              = erase_val n2 v.1)
          /\(forall n1 n2,
                measure_val v.2 <= n1
            ->  measure_val v.2 <= n2
            ->  erase_val n1 v.2
              = erase_val n2 v.2))
          vll)
    ->  measure_val (VMap vll) <= n1
    ->  measure_val (VMap vll) <= n2
    ->  erase_val n1 (VMap vll)
      = erase_val n2 (VMap vll).
  Proof.
    itr - vll n1 n2 IFH Hn1 Hn2.
    ind - vll as [| v vll].
    * clr - IFH.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      bmp.
    * ivc - IFH as IHv IFH: H1 H2.
      des - IHv as [IHv1 IHv2].
      des - v as [v1 v2].
      smp - IHv1 IHv2.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      smp.
      ufl - measure_val_map in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v1 ≤ n1) as Hv1n1: lia.
      ass > (measure_val v1 ≤ n2) as Hv1n2: lia.
      ass > (measure_val v2 ≤ n1) as Hv2n1: lia.
      ass > (measure_val v2 ≤ n2) as Hv2n2: lia.
      ass > (measure_val (VMap vll) ≤ S n1) as Hvln1:
        smp; ufl - measure_val_map; lia.
      ass > (measure_val (VMap vll) ≤ S n2) as Hvln2:
        smp; ufl - measure_val_map; lia.
      spc - IHv1: n1 n2 Hv1n1 Hv1n2.
      spc - IHv2: n1 n2 Hv2n1 Hv2n2.
      spc - IHvll: IFH Hvln1 Hvln2.
      smp - IHvll.
      ivc - IHvll as IHvll: H0.
      bwr - IHv1 IHv2 IHvll.
  Qed.






  Lemma measure_reduction_vclos :
    forall Γ ext id vars e n1 n2,
        (Forall
          (fun x =>
            (forall n1 n2,
                measure_val x.2 <= n1
            ->  measure_val x.2 <= n2
            ->  erase_val n1 x.2
              = erase_val n2 x.2))
          Γ)
    ->  measure_val (VClos Γ ext id vars e) <= n1
    ->  measure_val (VClos Γ ext id vars e) <= n2
    ->  erase_val n1 (VClos Γ ext id vars e)
      = erase_val n2 (VClos Γ ext id vars e).
  Proof.
    itr - Γ ext id vars e n1 n2 IFH Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    smp.
    feq.
    * clr - e vars.
      app - map_ext; itr.
      des - a as [[n fid] [vars' body]].
      feq.
      clr - n id fid.
      do 2 feq.
      clr - body.
      rwl - Nat.succ_le_mono in Hn1 Hn2.
      ind - Γ as [| [k v] Γ IHvl]:
            rwr - env_rem_ext_vars_nil_l; smp.
      ivc - IFH as IHv IFH: H1 H2.
      smp - IHv.
      ufl - measure_val_env in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val_env measure_val Γ ≤ n1) as Hvln1:
        smp; ufl - measure_val_env; lia.
      ass > (measure_val_env measure_val Γ ≤ n2) as Hvln2:
        smp; ufl - measure_val_env; lia.
      clr - Hn1 Hn2.
      spc - IHv: n1 n2 Hvn1 Hvn2.
      spc - IHvl: IFH Hvln1 Hvln2.
      rwr - env_rem_ext_vars_cons.
      pse - env_rem_ext_vars_single as Hsingle: k v vars' ext.
      des - Hsingle.
      - cwr - H.
        rwl - cons_app.
        smp.
        bwr - IHv IHvl.
      - clr - IHv.
        cwr - H.
        rwr - app_nil_l.
        exa - IHvl.
    * do 2 feq.
      clr - id.
      rwl - Nat.succ_le_mono in Hn1 Hn2.
      ind - Γ as [| [k v] Γ IHvl]:
            rwr - env_rem_ext_vars_nil_l; smp.
      ivc - IFH as IHv HForall: H1 H2.
      smp - IHv.
      ufl - measure_val_env in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val_env measure_val Γ ≤ n1) as Hvln1:
        smp; ufl - measure_val_env; lia.
      ass > (measure_val_env measure_val Γ ≤ n2) as Hvln2:
        smp; ufl - measure_val_env; lia.
      clr - Hn1 Hn2.
      spc - IHv: n1 n2 Hvn1 Hvn2.
      spc - IHvl: HForall Hvln1 Hvln2.
      rwr - env_rem_ext_vars_cons.
      pse - env_rem_ext_vars_single as Hsingle: k v vars ext.
      des - Hsingle.
      - cwr - H.
        rwl - cons_app.
        smp.
        bwr - IHv IHvl.
      - clr - IHv.
        cwr - H.
        rwr - app_nil_l.
        exa - IHvl.
  Qed.



End MeasureReduction_InductionTheorems.









Section MeasureReduction_MainTheorem.



  Theorem measure_reduction :
    forall v n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  erase_val n1 v
      = erase_val n2 v.
  Proof.
    itr - v.
    ind ~ ind_bs_val - v; itr - n1 n2 Hn1 Hn2.
    1: bse - measure_reduction_vnil: n1 n2 Hn1 Hn2.
    1: bse - measure_reduction_vlit: l n1 n2 Hn1 Hn2.
    1: bse - measure_reduction_vcons: v1 v2 n1 n2 IHv1 IHv2 Hn1 Hn2.
    2: bse - measure_reduction_vtuple: l n1 n2 H Hn1 Hn2.
    2: bse - measure_reduction_vmap: l n1 n2 H Hn1 Hn2.
    1: bse - measure_reduction_vclos: ref ext id params body n1 n2 H Hn1 Hn2.
  Qed.



End MeasureReduction_MainTheorem.









Section MeasureReduction_ListTheorems.



  Theorem measure_reduction_list :
    forall vl n1 n2,
        measure_val_list measure_val vl <= n1
    ->  measure_val_list measure_val vl <= n2
    ->  map (erase_val n1) vl
      = map (erase_val n2) vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (measure_val_list measure_val vl)
      (measure_val_list measure_val (v :: vl)).
    (* #3 Assert: assert *)
    ass_le > (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_le > (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_le_trn > (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_le_trn > (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_le_trn > (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_le_trn > (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - measure_reduction as Heq_v: v n1 n2 Hle_v_n1 Hle_v_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.






  Theorem measure_reduction_map :
    forall vll n1 n2,
        measure_val_map measure_val vll <= n1
    ->  measure_val_map measure_val vll <= n2
    ->  map (fun '(x, y) => (erase_val n1 x, erase_val n1 y)) vll
      = map (fun '(x, y) => (erase_val n2 x, erase_val n2 y)) vll.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vll n1 n2 Hle_vvll_n1 Hle_vvll_n2.
    ind - vll as [| v vll Heq_vll]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    rem - mv1 mv2 mv mvll mvvll as Hmv1 Hmv2 Hmv Hmvll Hmvvll:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (measure_val_map measure_val vll)
      (measure_val_map measure_val ((v1, v2) :: vll)).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_le > (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_le > (mv <= mvvll) as Hle_v_vvll: Hmv Hmvvll.
    ass_le > (mvll <= mvvll) as Hle_vll_vvll: Hmvll Hmvvll.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mvll <= n1) as Hle_vll_n1: Hle_vll_vvll Hle_vvll_n1.
    ass_le_trn > (mvll <= n2) as Hle_vll_n2: Hle_vll_vvll Hle_vvll_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvll Hmvvll in *.
    clr + Heq_vll Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vll_n1 Hle_vll_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vll: Hle_vll_n1 Hle_vll_n2.
    psc - measure_reduction as Heq_v1: v1 n1 n2 Hle_v1_n1 Hle_v1_n2.
    psc - measure_reduction as Heq_v2: v2 n1 n2 Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.






  Theorem measure_reduction_env :
    forall Γ n1 n2,
        measure_val_env measure_val Γ <= n1
    ->  measure_val_env measure_val Γ <= n2
    ->  map (erase_val n1) (map snd Γ)
      = map (erase_val n2) (map snd Γ).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - Γ n1 n2 Hle_vvll_n1 Hle_vvll_n2.
    rwr - measure_env_list_eq in *.
    rem - vl as Hvl: (map snd Γ).
    clr - Hvl Γ.
    app - measure_reduction_list; asm.
  Qed.



End MeasureReduction_ListTheorems.









Section MeasureReduction_Minimalize.



  Theorem mred_min :
    forall v n,
        measure_val v <= n
    ->  erase_val n v
      = erase_val (measure_val v) v.
  Proof.
    itr - v n Hn.
    pse - measure_reduction as Hmr.
    app - Hmr; lia.
  Qed.



  Theorem mred_min_list :
    forall vl n,
        measure_val_list measure_val vl <= n
    ->  map (erase_val n) vl
      = map (erase_val (measure_val_list measure_val vl)) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vl n Hn.
    pse - measure_reduction_list as Hmr.
    app - Hmr; lia.
  Qed.



  Theorem mred_min_map :
    forall vll n,
        measure_val_map measure_val vll <= n
    ->  map (fun '(x, y) => (erase_val n x, erase_val n y)) vll
      = map
        (fun '(x, y) =>
          (erase_val (measure_val_map measure_val vll) x,
           erase_val (measure_val_map measure_val vll) y))
        vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vll n Hn.
    pse - measure_reduction_map as Hmr.
    app - Hmr; lia.
  Qed.



  Theorem mred_min_env :
    forall Γ n,
        measure_val_env measure_val Γ <= n
    ->  map (erase_val n) (map snd Γ)
      = map (erase_val (measure_val_env measure_val Γ)) (map snd Γ).
  Proof.
    itr - Γ n Hn.
    pse - measure_reduction_env as Hmr.
    app - Hmr; lia.
  Qed.



End MeasureReduction_Minimalize.









Section MeasureReduction_AbsoluteMinimalize.



  Theorem mred_absmin_list :
    forall vl,
      map (erase_val (measure_val_list measure_val vl)) vl
    = map (fun v => erase_val (measure_val v) v) vl.
  Proof.
    itr.
    ind - vl as [| v vl IHvl]: smp.
    smp.
    rwr - mred_min.
    2: mred_le_solver.
    feq.
    rwl - IHvl.
    app - mred_min_list.
    mred_le_solver.
  Qed.



  Theorem mred_absmin_list_any :
    forall vl n,
      measure_val_list measure_val vl <= n
    ->  map (erase_val n) vl
      = map (fun v => erase_val (measure_val v) v) vl.
  Proof.
    itr - vl n Hle.
    pse - mred_min_list as Hvl: vl n Hle.
    cwr - Hvl.
    app - mred_absmin_list.
  Qed.



  Theorem mred_absmin_map :
    forall vll,
      map
        (fun '(x, y) =>
          (erase_val (measure_val_map measure_val vll) x,
           erase_val (measure_val_map measure_val vll) y))
        vll
    = map
        (fun '(x, y) =>
          (erase_val (measure_val x) x,
           erase_val (measure_val y) y))
        vll.
  Proof.
    itr.
    ind - vll as [| [vk vv] vll IHvll]: smp.
    smp.
    rwr - mred_min.
    2: mred_le_solver.
    feq.
    feq.
    rwr - mred_min.
    2: mred_le_solver.
    rfl.
    rwl - IHvll.
    app - mred_min_map.
    mred_le_solver.
  Qed.



  Theorem mred_absmin_env :
    forall Γ,
      map (erase_val (measure_val_env measure_val Γ)) (map snd Γ)
    = map (fun v => erase_val (measure_val v) v) (map snd Γ).
  Proof.
    itr.
    ind - Γ as [| [k v] Γ IH]: smp.
    smp.
    rwr - mred_min.
    2: mred_le_solver.
    feq.
    rwl - IH.
    app - mred_min_env.
    mred_le_solver.
  Qed.




End MeasureReduction_AbsoluteMinimalize.









(* Section: MeasureReduction_RewriteTactics. *)



  Tactic Notation "mred"
      :=
    try (rewrite mred_min; [idtac | mred_le_solver]);
    try (rewrite mred_min_list; [idtac | mred_le_solver]);
    try (rewrite mred_min_map; [idtac | mred_le_solver]).

  Tactic Notation "mred"
      "-"   hyp(H)
      :=
    try (rewrite mred_min in H; [idtac | mred_le_solver]);
    try (rewrite mred_min_list in H; [idtac | mred_le_solver]);
    try (rewrite mred_min_map in H; [idtac | mred_le_solver]).



(* Section: MeasureReduction_RewriteTactics. *)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_VAL_REM_FUEL ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EraseValRemFuel_RemoveFromEnvironmentLemmas.



  Lemma env_rem_keys_le :
    forall Γ keys,
        measure_val_env measure_val (env_rem_keys keys Γ)
    <=  measure_val_env measure_val Γ.
  Proof.
    itr.
    ind - Γ as [| [k1 v1] Γ IHΓ]:
          rwr - env_rem_keys_nil_l; lia.
    rwr - env_rem_keys_cons.
    unfold measure_val_env in *.
    rewrite cons_app with (l := Γ).
    do 2 rwr - map_app.
    do 2 rwr - list_sum_app.
    app - Nat.add_le_mono.
    2: exa - IHΓ.
    clr - IHΓ.
    smp.
    rwr - Nat.add_0_r.
    pse - env_rem_keys_single as Hsingle:
          k1 v1 keys.
    des - Hsingle;
          cwr - H; sli.
  Qed.



  Lemma env_rem_fids_le :
    forall Γ fids,
        measure_val_env measure_val (env_rem_fids fids Γ)
    <=  measure_val_env measure_val Γ.
  Proof.
    itr.
    app - env_rem_keys_le.
  Qed.



  Lemma env_rem_vars_le :
    forall Γ vars,
        measure_val_env measure_val (env_rem_vars vars Γ)
    <=  measure_val_env measure_val Γ.
  Proof.
    itr.
    app - env_rem_keys_le.
  Qed.



  Lemma env_rem_ext_le :
    forall Γ ext,
        measure_val_env measure_val (env_rem_ext ext Γ)
    <=  measure_val_env measure_val Γ.
  Proof.
    itr.
    app - env_rem_keys_le.
  Qed.



  Lemma env_rem_ext_vars_le :
    forall Γ ext vars,
        measure_val_env measure_val (env_rem_ext ext (env_rem_vars vars Γ))
    <=  measure_val_env measure_val Γ.
  Proof.
    itr.
    ufl - env_rem_ext_vars.
    pse - env_rem_vars_le as Hle_vars: Γ vars.
    pse - env_rem_ext_le as Hle_ext: (env_rem_vars vars Γ) ext.
    lia.
  Qed.



End EraseValRemFuel_RemoveFromEnvironmentLemmas.









Section EraseValRemFuel_Theorems.



  Theorem erase_val_rem_fuel :
    forall v,
      erase_val (measure_val v) v
    = erase_val' v.
  Proof.
    itr - v.
    rem - n as Hn:
      (measure_val v).
    pse - measure_val_not_zero as Hnot_zero': v.
    ass > (0 < n) as Hnot_zero: lia.
    clr - Hnot_zero'.
    des - n :- lia.
    clr - Hnot_zero.
    ufl - erase_val'.
    smp.
    des - v
      :- rfl
      |> smp - Hn; app - eq_add_S in Hn; cwr - Hn / n.
    * feq.
      - feq.
        clr - vl e.
        apply functional_extensionality.
        itr - x.
        des - x as [[n fid] [vars e]].
        do 4 feq.
        app - mred_absmin_list_any.
        rwl - measure_env_list_eq.
        pse - env_rem_ext_vars_le: env ext vars.
        lia.
      - do 3 feq.
        app - mred_absmin_list_any.
        rwl - measure_env_list_eq.
        pse - env_rem_ext_vars_le: env ext vl.
        lia.
    * feq.
      - app - measure_reduction; lia.
      - app - measure_reduction; lia.
    * feq.
      app - mred_absmin_list.
    * feq.
      app - mred_absmin_map.
  Qed.






  Theorem erase_val_rem_fuel_any :
    forall v n,
        measure_val v <= n
    ->  erase_val n v
      = erase_val' v.
  Proof.
    itr - v n Hlen.
    rwr - mred_min.
    2: exa - Hlen.
    app - erase_val_rem_fuel.
  Qed.



  Theorem erase_val_rem_fuel_list :
    forall vl,
      map (fun v => erase_val (measure_val v) v) vl
    = map (fun v => erase_val' v) vl.
  Proof.
    itr.
    ind - vl as [| v vl IHvl]: smp.
    smp.
    feq.
    * app - erase_val_rem_fuel.
    * exa - IHvl.
  Qed.



  Lemma erase_val_rem_fuel_map :
    forall vll,
      map
        (fun '(v1, v2) =>
          (erase_val (measure_val v1) v1, erase_val (measure_val v2) v2))
        vll
    = map (fun '(v1, v2) => (erase_val' v1, erase_val' v2)) vll.
  Proof.
    itr.
    ind - vll as [| [v1 v2] vll IHvl]: smp.
    smp.
    feq.
    * feq.
      - app - erase_val_rem_fuel.
      - app - erase_val_rem_fuel.
    * exa - IHvl.
  Qed.



End EraseValRemFuel_Theorems.









(* Section EraseValRemFuel_Tactics. *)



  Ltac mvr :=
    try (rewrite erase_val_rem_fuel in *);
    try (rewrite erase_val_rem_fuel_any in *; [idtac | mred_le_solver]);
    try (rewrite erase_val_rem_fuel_list in *);
    try (rewrite erase_val_rem_fuel_map in *).



(* End EraseValRemFuel_Tactics. *)