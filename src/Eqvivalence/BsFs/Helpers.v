From CoreErlang.Eqvivalence.BsFs Require Export EraseNames.

Import SubstSemantics.

(** CONTENT:
* SCOPE (LEMMAS & TACTICS)
  - Scope_Destructs (TACTICS)
    + des_for
  - Scope_Lists (LEMMAS)
    + scope_list_succ
    + scope_list_succ_id
  - Scope_Values (THEOREMS)
    + scope_vcons
    + scope_vtuple
    + scope_vmap
  - Scope_Tactics (TACTICS)
    + scope
    + start
* STEP (TACTICS)
  - Step
    + do_step
    + do_transitive
    + step
* ENVIRONMENT_LEMMAS (LEMMAS)
  - EnvironmentLemmas_GetValue
    + get_value_singleton
    + get_value_singleton_length
    + get_value_single_det
    + get_value_cons
  - EnvironmentLemmas_Remove
* ERASER_SUBST_APPEND (LEMMAS & THEOREMS)
  - EraserSubstAppend_EraserLemmas (LEMMAS)
    + add_keys_app
    + add_keys_get_env_app
    + add_keys_append_vars_to_env_app
    + add_keys_append_vars_to_env_get_env_app
    + add_keys_append_funs_to_env_app
  - EraserSubstAppend_SubstLemmas (LEMMAS)
    + list_subst_cons
    + list_subst_fold_right
    + list_subst_app
  - EraserSubstAppend_Theorems (THEOREMS)
    + erase_exp_append_vars
* FRAMEIDENT (LEMMAS)
  * BIFORALL ?
  * CREATE_RESULTS
* AXIOMS

*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: SCOPE ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






(* Section Scope_Destructs. *)



  (** DOCUMENTATION:
  * des_for --> destruct_foralls; rename
    - N:[ident]:1-10 : N:[ident]:1-10
  *)

  Tactic Notation "des_for"
      :=
    destruct_foralls.

  Tactic Notation "des_for"
      "-"   ident(In1)
      ":"   ident(Io1)
      :=
    destruct_foralls;
    ren - In1:
          Io1.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2)
      ":"   ident(Io1) ident(Io2)
      :=
    destruct_foralls;
    ren - In1 In2:
          Io1 Io2.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3)
      ":"   ident(Io1) ident(Io2) ident(Io3)
      :=
    destruct_foralls;
    ren - In1 In2 In3:
          Io1 Io2 Io3.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4:
          Io1 Io2 Io3 Io4.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5:
          Io1 Io2 Io3 Io4 Io5.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6:
          Io1 Io2 Io3 Io4 Io5 Io6.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7) ident(In8)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7) ident(Io8)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7) ident(In8) ident(In9)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7) ident(Io8) ident(Io9)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.



(* End Scope_Destructs. *)









Section Scope_Lists.



  Lemma scope_list_succ :
    forall A i vl (f : A -> Val),
        (i < length vl
        ->  VALCLOSED (nth i (map f vl) VNil))
    ->  (S i < S (length vl)
        ->  VALCLOSED (nth i (map f vl) VNil)).
  Proof.
    (* #1 Pose: intro/pose/destruct/ *)
    itr - A i vl f Hvl Hsucc_lt.
    pse - Nat.succ_lt_mono as Hmono_succ_lt: i (base.length vl).
    des - Hmono_succ_lt as [_ Hfrom_succ_lt].
    (* #2 Apply: apply *)
    app - Hfrom_succ_lt in Hsucc_lt as Hlt; clr - Hfrom_succ_lt.
    bpp - Hvl in Hlt.
  Qed.



  Lemma scope_list_succ_id :
    forall i vl,
        (i < length vl
        ->  VALCLOSED (nth i vl VNil))
    ->  (S i < S (length vl)
        ->  VALCLOSED (nth i vl VNil)).
  Proof.
    (* #1 Assert: intro/assert/remember + apply *)
    itr - i vl Hvl.
    ass > (map id vl = vl) as Hid: apply Basics.map_id.
    rem - n as Hn: (base.length vl).
    (* #2 Rewrite: rewrite *)
    cwl + Hid in Hvl.
    cwr - Hn in *.
    (* #3 Pose by Previus: pose *)
    by pose proof scope_list_succ Val i vl id Hvl.
  Qed.



End Scope_Lists.









Section Scope_Value.



  Theorem scope_vcons :
    forall v1 v2,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VCons v1 v2]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 Hv1 Hv2.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    des_for - Hv1 Hv2: H3 H1.
    (* #2 Finish: pose *)
    ato.
  Qed.



  Theorem scope_vtuple :
    forall v vl,
        is_result (RValSeq [v])
    ->  is_result (RValSeq [VTuple vl])
    ->  is_result (RValSeq [VTuple (v :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v vl Hv Hvl.
    ivc - Hv as Hv: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv Hvl: H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    (* #4 Simplify: intro/simpl *)
    itr - i Hl.
    smp *.
    (* #5 Destruct: destruct + exact *)
    des - i: exa - Hv.
    (* #6 Inversion: inversion *)
    ivc - Hvl as Hvl: H1 / v Hv.
    (* #7 Finish: pose *)
    bse - scope_list_succ_id: i vl (Hvl i) Hl.
  Qed.



  Theorem scope_vmap :
    forall v1 v2 vl,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VMap vl])
    ->  is_result (RValSeq [VMap ((v1, v2) :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 vl Hv1 Hv2 Hvl.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv1 Hv2 Hvl: H5 H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    * (* #4.1 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.1 Destruct: clear/destruct + exact *)
      clr - Hv2 v2.
      des - i: exa - Hv1.
      (* #6.1 Inversion: inversion *)
      ivc - Hvl as Hvl: H0 / H2 v1 Hv1.
      (* #7.1 Finish: pose *)
      by pose proof scope_list_succ (Val * Val) i vl fst (Hvl i) Hl.
    * (* #4.2 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.2 Destruct: clear/destruct + exact *)
      clr - Hv1 v1.
      des - i: exa - Hv2.
      (* #6.2 Inversion: inversion *)
      ivc - Hvl as Hvl: H2 / H0 v2 Hv2.
      (* #7.2 Finish: pose *)
      by pose proof scope_list_succ (Val * Val) i vl snd (Hvl i) Hl.
  Qed.



End Scope_Value.









(* Section Scope_Tactics. *)



  Ltac scope :=
    try (apply scope_vcons; [assumption ..]);
    try (apply scope_vtuple; [assumption ..]);
    try (apply scope_vmap; [assumption ..]);
    try (constructor);
    try (destruct_foralls);
    try (assumption + scope_solver).



  (** DOCUMENTATION:
  * start --> eexists; split; [> scope]; clear.
    / [ident]:0-3
    - hyp
  *)

  Tactic Notation "start"
      :=
    eexists; split; [(scope + admit) | idtac].

  Tactic Notation "start"
      "/"   ident(I1)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1.

  Tactic Notation "start"
      "/"   ident(I1) ident(I2)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2.

  Tactic Notation "start"
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2 I3.

  Tactic Notation "start"
      "-"   ident(H)
      :=
    eexists; split; [ivs - H; (scope + admit) | clear H].



(* End Scope_Tactics. *)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: STEP /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






(* Section Step. *)



  Ltac do_step
    :=
    (econstructor;
    [ (constructor; auto + scope_solver + congruence)
    + (econstructor; constructor)
    + (econstructor;
      [ congruence
      | constructor ])
    | simpl ])
    + (cbn; constructor).



  Ltac do_transitive H
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in H;
      exact H
    | clear H;
      simpl ].



  (** DOCUMENTATION:
  * step --> repeat step; (exact H + do_transitive H).
    - hyp / [ident]:0-10
  *)

  Tactic Notation "step"
      :=
    repeat do_step.

  Tactic Notation "step"
      "-"   hyp(H)
      :=
    repeat do_step;
    (exact H + do_transitive H).

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8) ident(I9)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.



(* End Step. *)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ENVIRONMENT_LEMMAS ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.






Section EnvironmentLemmas_GetValue.



  Lemma get_value_singleton :
    forall Γ key vs,
        get_value Γ key = Some vs
    ->  exists value, vs = [value].
  Proof.
    intros Γ key vs.
     induction Γ as [| [k v] Γ IH]; intros Hget; cbn in Hget.
     * congruence.
     * destruct (var_funid_eqb key k) eqn:Heqb.
       - exists v.
         by inv Hget.
       - by apply IH.
  Qed.



  Lemma get_value_singleton_length :
    forall Γ key l,
        get_value Γ key = Some l
    ->  length l = 1.
  Proof.
    (* #1 Pose by Previous: intro/pose/inversion *)
    itr - Γ key vs Hget.
    pse - get_value_singleton as Hsingl: Γ key vs Hget.
    bvs - Hsingl.
  Qed.



  Lemma get_value_single_det :
    forall k1 k2 v1 v2,
        get_value [(k1, v1)] k2 = Some [v2]
    ->  k1 = k2 /\  v1 = v2.
  Proof.
    itr - k1 k2 v1 v2 Hget.
    smp - Hget.
    des > (var_funid_eqb k2 k1) as Hk; ivc - Hget.
    spl.
    2: rfl.
    ufl - var_funid_eqb in Hk.
    des - k1 as [s1 | f1]; des - k2 as [s2 | f2]; smp - Hk.
    * app - String.eqb_eq in Hk.
      bvs - Hk.
    * con.
    * con.
    * ufl - funid_eqb in Hk.
      des - f1 as [i1 n1]; des - f2 as [i2 n2]; smp - Hk.
      app - andb_prop in Hk.
      des - Hk as [Hi Hn].
      app - String.eqb_eq in Hi.
      app - Nat.eqb_eq in Hn.
      sbt.
      rfl.
  Qed.



  Lemma get_value_cons :
    forall Γ key k var v,
        get_value ((k, v) :: Γ) key = Some [var]
    ->  get_value [(k, v)] key = Some [var] 
    \/  get_value Γ key = Some [var].
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - Γ key k var v Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb_key; ato.
  Qed.



  Theorem get_value_in :
    forall Γ key var,
        get_value Γ key = Some [var]
    ->  In (key , var) Γ.
  Proof.
    (* #1 Induction on Environment: intro/induction + intro/inversion *)
    itr - Γ.
    ind - Γ as [| [k v] Γ IH] :> itr - key var Hget :- ivc - Hget.
    (* #2 Destruct Get_Value: apply/destruct *)
    app - get_value_cons in Hget.
    des - Hget as [Hget | Hget].
    * (* #3.1 Destruct Key Equality: clear/simpl/destruct + congruence *)
      clr - IH.
      smp *.
      des > (var_funid_eqb key k) as Hkey :- con.
      (* #4.1 Rewrite Var & FunId: left/inversion/apply/rewrite *)
      lft.
      ivc - Hget.
      app - var_funid_eqb_eq in Hkey.
      bwr - Hkey.
    * (* #3.2 Pose In_Cons: specialize/pose *)
      spc - IH: key var Hget.
      by pose proof in_cons (k, v) (key, var) Γ IH.
  Qed.



End EnvironmentLemmas_GetValue.









Section EnvironmentLemmas_Remove.



  Lemma rem_keys_empty :
    forall Γ,
      rem_keys [] Γ = Γ.
  Proof.
    (* #1 Induction on Environment: induction + simpl*)
    ind - Γ as [| [k v] Γ IH] :> smp.
    (* #2 Rewrite by Induction: rewrite *)
    bwr - IH.
  Qed.



  Lemma rem_ext_empty :
    forall Γ,
      rem_ext [] Γ = Γ.
  Proof.
    app - rem_keys_empty.
  Qed.



End EnvironmentLemmas_Remove.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASER_SUBST_APPEND //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Section EraserSubstAppend_EraserLemmas.



  Lemma add_keys_app :
    forall keys1 keys2 σ,
      add_keys keys1 (add_keys keys2 σ)
    = add_keys (keys1 ++ keys2) σ.
  Proof.
    itr.
    ufl - add_keys.
    unfold add_names.
    bwr - foldr_app.
  Qed.



  Lemma add_keys_get_env_app :
    forall ext Γ σ,
        add_keys (map fst (get_env Γ ext)) σ
      = add_ext ext (add_keys (map fst Γ) σ).
  Proof.
    itr - ext Γ σ.
    ufl - get_env.
    rwr - map_app.
    rwr - ext_to_env_fst.
    rwl - add_keys_app.
    ufl - add_ext add_fids.
    bwr - map_map.
  Qed.



  Lemma add_keys_append_vars_to_env_app :
    forall vars vs Γ σ,
        length vars = length vs
    ->  add_keys (map fst (append_vars_to_env vars vs Γ)) σ
      = add_vars vars (add_keys (map fst Γ) σ).
  Proof.
    itr - vars vs Γ σ Hlength.
    ufl - append_vars_to_env.
    rwr - map_app.
    rwl - add_keys_app.
    epose proof length_map (inl : Var -> (Var + FunctionIdentifier)) vars
      as Hlength_map_inl.
    cwl - Hlength_map_inl in Hlength.
    epose proof zip_fst _ _ _ _ Hlength as Hzip_fst;
      clr - Hlength.
    cwr - Hzip_fst.
    ufl - add_vars.
    trv.
  Qed.



  Lemma add_keys_append_vars_to_env_get_env_app :
    forall vars vs ext Γ σ,
        length vars = length vs
    ->  add_keys (map fst (append_vars_to_env vars vs (get_env Γ ext))) σ
      = add_vars vars (add_ext ext (add_keys (map fst Γ) σ)).
  Proof.
    itr - vars vs ext Γ σ Hlength.
    rwr - add_keys_append_vars_to_env_app.
    2: asm.
    bwr - add_keys_get_env_app.
  Qed.



  Lemma add_keys_append_funs_to_env_app :
    forall ext n Γ σ,
        add_keys (map fst (append_funs_to_env ext Γ n)) σ
      = add_fids (map fst ext) (add_keys (map fst Γ) σ).
  Proof.
    itr - ext n Γ σ.
    ufl - append_funs_to_env.
    rwr - add_keys_get_env_app.
    ufl - add_ext.
    feq.
    gen - n.
    ind - ext as [| [fid [vars e]] ext IH]: smp.
    itr.
    smp.
    feq.
    bpe - IH: (S n).
  Qed.


End EraserSubstAppend_EraserLemmas.









Section EraserSubstAppend_SubstLemmas.



  Lemma list_subst_cons :
    forall v vs ξ,
      list_subst [v] (list_subst vs ξ)
    = list_subst (v::vs) ξ.
  Proof.
    trv.
  Qed.



  Lemma list_subst_fold_right :
    forall vs ξ,
      fold_right (fun v σ => v .: σ) ξ vs
    = list_subst vs ξ.
  Proof.
    trv.
  Qed.



  Lemma list_subst_app :
    forall vs1 vs2 ξ,
      list_subst vs1 (list_subst vs2 ξ)
    = list_subst (vs1 ++ vs2) ξ.
  Proof.
    itr.
    rewrite <- list_subst_fold_right with (vs:= vs1 ++ vs2).
    rewrite <- list_subst_fold_right with (vs:= vs1).
    rewrite <- list_subst_fold_right with (vs:= vs2).
    bwr - foldr_app.
  Qed.



End EraserSubstAppend_SubstLemmas.









Section EraserSubstAppend_Theorems.



  Theorem erase_exp_append_vars :
    forall e fns env vars vs,
        base.length vars = base.length vs
    ->  (erase_exp
          (add_keys
            (map fst (append_vars_to_env vars vs env))
            fns)
          e)
        .[list_subst
          (map
            (fun v => erase_val (measure_val v) fns v)
            (map snd (append_vars_to_env vars vs env)))
          idsubst]
      = (erase_exp
          (add_vars
            vars
            (add_keys (map fst env) fns))
          e)
        .[upn
          (base.length vars)
          (list_subst
            (map
               (fun v =>
                 erase_val 
                 (measure_val v) fns v)
               (map snd env)) idsubst)]
        .[list_subst
          (map
            (fun v => erase_val (measure_val v) fns v) vs)
            idsubst].
  Proof.
    itr - e fns env vars vs Hlength.
    (* add_keys *)
    rwr - add_keys_append_vars_to_env_app.
    (* upn to ++ *)
    rwr - subst_comp_exp.
    ass >
      (length vs
        = length (map (λ v : Value, erase_val (measure_val v) fns v) vs))
      as Hlength_vars:
      rwr - length_map.
    rwl - Hlength in Hlength_vars.
    cwr - Hlength_vars.
    rwr - substcomp_list.
    rwr - substcomp_id_l.
    rwr - list_subst_app.
    (* append to ++ *)
    ufl - append_vars_to_env.
    rwr - map_app.
    epose proof length_map (inl : Var -> (Var + FunctionIdentifier)) vars
      as Hlength_map_inl.
    2: asm.
    cwl - Hlength_map_inl in Hlength.
    epose proof zip_snd _ _ _ _ Hlength as Hzip_snd;
      clr - Hlength.
    rwr - Hzip_snd.
    bwr - map_app.
  Qed.



End EraserSubstAppend_Theorems.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section tmp.
End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section tmp.
End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section tmp.
End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section tmp.
End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Section tmp.
End tmp.