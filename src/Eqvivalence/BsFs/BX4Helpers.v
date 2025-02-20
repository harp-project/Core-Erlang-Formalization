From CoreErlang.Eqvivalence.BsFs Require Export BX3Tactics.

Import SubstSemantics.

(** CONTENT:
* ENVIRONMENT_LEMMAS (LEMMAS)
  - EnvironmentLemmas_GetValue (LEMMAS)
    + get_value_singleton
    + get_value_singleton_length
    + get_value_single_det
    + get_value_cons
* ERASE_SUBST_APPEND (LEMMAS; THEOREMS)
  - EraseSubstAppend_EraserLemmas (LEMMAS)
    + add_keys_get_env_app
    + add_keys_append_vars_to_env_app
    + add_keys_append_vars_to_env_get_env_app
    + add_keys_append_funs_to_env_app
  - EraseSubstAppend_SubstLemmas (LEMMAS)
    + list_subst_cons
    + list_subst_fold_right
    + list_subst_app
  - EraseSubstAppend_Theorems (THEOREMS)
    + erase_subst_append_vars
* FRAMEIDENT_Lemmas (LEMMAS)
  * FrameStackEvaluation_NthLemmas
    - BIFORALL ?
    - CREATE_RESULTS ?
* EQVIVALENCE_HELPERS (LEMMAS)
  - EqvivalenceHelpers
* AXIOMS (AXIOM; LEMMAS)
  - Axioms (AXIOM)
    + all_val_is_wfm
    + no_modfunc
    + result_is_result
    + eval_catch_vars_length
    + erase_subst_rem_vars
  - Axioms_Lemmas (LEMMAS)
    + get_value_is_result
    + evar_is_result
    + efunid_is_result
    + efun_is_result
    + catch_vars_length
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: FRAMESTACK_EVALUATION ////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section FrameStackEvaluation_Nth.

  Import BigStep.



  Theorem fs_eval_nth_map_erase_forall :
    forall σ ξ el ex vl vx,
        (forall i,
            i < length vl
        ->  ⟨ [], (erase_exp σ (nth i el ex)).[ξ] ⟩ -->*
              RValSeq [erase_val (nth i vl vx)])
    ->  (forall i,
            i < length vl
        ->  ⟨ [], nth i (map (fun e => (erase_exp σ e).[ξ]) el)
                        (erase_exp σ ex).[ξ] ⟩ -->*
              RValSeq [nth i (map erase_val vl) (erase_val vx)]).
  Proof.
    itr - σ ξ el ex vl vx Hnth.
    itr - i Hi.
    spe - Hnth: i Hi.
    rewrite <- map_nth
      with (d := ex) (f := fun e => (erase_exp σ e).[ξ]) in Hnth.
    rewrite <- map_nth
      with (d := vx) (f := erase_val) in Hnth.
    exa - Hnth.
  Qed.






  Theorem fs_eval_nth_map_erase_single :
    forall σ ξ el ex i,
       (erase_exp σ (nth i el ex)).[ξ]
    =  nth i (map (fun e => (erase_exp σ e).[ξ]) el) (erase_exp σ ex).[ξ].
  Proof.
    itr - σ ξ el ex i.
    rewrite map_nth with (d := ex) (f := fun e => (erase_exp σ e).[ξ]).
    rfl.
  Qed.






  Theorem fs_eval_nth_cons :
    forall e el ex v vl vx,
        (forall i,
            i < base.length (v :: vl)
        ->  ⟨ [], RExp (nth i (e :: el) ex) ⟩ -->* RValSeq [nth i (v :: vl) vx])
    ->  (⟨ [], RExp e ⟩ -->* RValSeq [v]
      /\
        (forall i,
            i < base.length vl
        ->  ⟨ [], RExp (nth i el ex) ⟩ -->* RValSeq [nth i vl vx])).
  Proof.
    itr - e el ex v vl vx Hnth.
    spl.
    * ass > (0 < base.length (v :: vl)) as Hlt: sli.
      spe + Hnth as IHv: 0 Hlt.
      smp - IHv.
      exa - IHv.
    * itr - i Hi.
      spe - Hnth: (S i).
      smp - Hnth.
      rwr - Nat.succ_lt_mono in Hi.
      spe - Hnth: Hi.
      exa - Hnth.
  Qed.






  Theorem fs_eval_nth_to_scope :
    forall el ex vl vx,
        length vl = length el
    ->  (forall i,
            i < length vl
        ->  ⟨ [], RExp (nth i el ex) ⟩ -->* RValSeq [nth i vl vx])
    ->  is_result (RValSeq vl).
  Proof.
    itr - el.
    (* #1 Induction on Expression List: induction + intro *)
    ind - el as [| e el IHvl];
      itr - ex vl vx Hlen Hnth.
    * clr - Hnth.
      (* #2.1 Both List is Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #3.1 Solve Scope: constructor *)
      do 2 cns.
    * (* #2.2 Both List is Cons: (destruct + inversion/subst)/simpl/rewrite *)
      des - vl as [| v vl]: ivs - Hlen.
      smp - Hlen.
      rwr - Nat.succ_inj_wd in Hlen.
      (* #3.2 Pose Nth Cons Theorem: pose/destruct *)
      psc - fs_eval_nth_cons as Hnth_cons: e el ex v vl vx Hnth.
      des - Hnth_cons as [IHv Hnth].
      (* #4.2 Specialize Induction Hypothesis: rewrite/specialize *)
      spc - IHvl as Hscope_vl: ex vl vx Hlen Hnth.
      (* #5.2 Destruct Hypothesis: destruct *)
      des - IHv as [kv [Hscope_v _]].
      (* #6.2 Solve Scope: apply + auto *)
      app - scope_cons; ato.
  Qed.






  Theorem fs_eval_nth_to_result :
    forall ident el ex vl' v' vl vx r eff Fs,
        length vl = length el
    ->  Some (r , eff) = create_result ident (vl' ++ v' :: vl) []
    ->  (forall i,
            i < length vl
        ->  ⟨ [], RExp (nth i el ex) ⟩ -->* RValSeq [nth i vl vx])
    ->  exists k,
          ⟨ (FParams ident vl' el) :: Fs, RValSeq [v'] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    itr - ident el.
    (* #1 Induction on Expression List: induction + intro *)
    ind - el as [| e el IHvl];
      itr - ex vl' v' vl vx r eff Fs Hlen Hcrt Hnth.
    * clr - Hnth.
      (* #2.1 Both List is Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #3.1 FrameStack Evaluation: exists/constructor/exact *)
      eei.
      do 2 ens.
      exa - Hcrt.
    * (* #2.2 Both List is Cons: (destruct + inversion/subst)/simpl/rewrite *)
      des - vl as [| v vl]: ivs - Hlen.
      smp - Hlen.
      rwr - Nat.succ_inj_wd in Hlen.
      (* #3.2 Pose Nth Cons Theorem: pose/destruct *)
      psc - fs_eval_nth_cons as Hnth_cons: e el ex v vl vx Hnth.
      des - Hnth_cons as [IHv Hnth].
      (* #4.2 Specialize Induction Hypothesis: rewrite/specialize *)
      rwr - cons_app
            app_assoc
            in Hcrt.
      spc - IHvl: ex (vl' ++ [v']) v vl vx r eff Fs Hlen Hcrt Hnth.
      (* #5.2 Destruct Induction Hypothesis: destruct *)
      des - IHv as [kv [Hscope_v Hstep_v]].
      des - IHvl as [ᵏvs Hstep_vl].
      (* #6.2 FrameStack Evaluation: exists/step *)
      eei.
      step - Hstep_v.
      step - Hstep_vl.
  Qed.






  Theorem fs_eval_nth_to_partial :
    forall ident el e' el' ex vl' v' vl vx,
        length vl = length el
    ->  (forall i,
            i < length vl
        ->  ⟨ [], RExp (nth i (el ++ e' :: el') ex) ⟩ -->*
              RValSeq [nth i vl vx])
    ->  exists k,
          ⟨ [FParams ident vl' (el ++ e' :: el')], RValSeq [v'] ⟩ -[ k ]->
          ⟨ [FParams ident (vl' ++ v' :: vl) el'], RExp e' ⟩.
  Proof.
    itr - ident el.
    (* #1 Induction on Expression List: induction + intro *)
    ind - el as [| e el IHvl];
      itr - e' el' ex vl' v' vl vx Hlen Hnth.
    * clr - Hnth.
      (* #2.1 Both List is Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #3.1 FrameStack Evaluation: exists/step *)
      eei.
      step.
    * (* #2.2 Both List is Cons: (destruct + inversion/subst)/simpl/rewrite *)
      des - vl as [| v vl]: ivs - Hlen.
      smp - Hlen.
      rwr - Nat.succ_inj_wd in Hlen.
      (* #3.2 Pose Nth Cons Theorem: pose/destruct *)
      psc - fs_eval_nth_cons as Hnth_cons: e (el ++ e' :: el') ex v vl vx Hnth.
      des - Hnth_cons as [IHv Hnth].
      (* #4.2 Specialize Induction Hypothesis: specialize/rewrite *)
      spc - IHvl: e' el' ex (vl' ++ [v']) v vl vx Hlen Hnth.
      rwl - app_assoc
            cons_app
            in IHvl.
      (* #5.2 Destruct Induction Hypothesis: destruct *)
      des - IHv as [kv [Hscope_v Hstep_v]].
      des - IHvl as [ᵏvs Hstep_vl].
      (* #6.2 FrameStack Evaluation: exists/step *)
      eei.
      step - Hstep_v.
      step - Hstep_vl.
  Qed.



End FrameStackEvaluation_Nth.






Section FrameStackEvaluation_Create.

  Import SubstSemantics.



  Lemma create_result_ivalues :
    forall v vs eff,
      Some (RValSeq (v :: vs), eff)
    = create_result IValues ([v] ++ vs) eff.
  Proof.
    trv.
  Qed.



  Lemma create_result_ituple :
    forall v vl eff,
      Some (RValSeq [VTuple (v :: vl)], eff)
    = create_result ITuple ([v] ++ vl) eff.
  Proof.
    trv.
  Qed.



  Lemma create_result_imap :
    forall v1 v2 vvs eff,
      Some (RValSeq [VMap (make_val_map ((v1, v2) :: vvs))], eff)
    = create_result IMap ([v1] ++ v2 :: (flatten_list vvs)) eff.
  Proof.
    itr.
    smp.
    pose proof flatten_deflatten vvs as Hvvs.
    bwr - Hvvs.
  Qed.



End FrameStackEvaluation_Create.









(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_SUBST_APPEND //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.






Section EraseSubstAppend_EraserLemmas.



  Lemma eraser_add_keys_get_env_app :
    forall os Γ σ,
        (get_env Γ os).keys ᵏ++ σ
      = os ᵒ++ Γ.keys ᵏ++ σ.
  Proof.
    itr.
    ufl - get_keys
          get_env.
    rwr - map_app.
    rwr - ext_to_env_fst.
    rwr - eraser_add_keys_app_l.
    ufl - eraser_add_ext
          eraser_add_fids
          get_fids.
    bwr - map_map.
  Qed.



  Lemma eraser_get_env_app :
    forall os Γ,
        (get_env Γ os).keys
      = os ᵒ++ Γ.keys.
  Proof.
    itr.
    rwl - eraser_add_keys_nil_r.
    rewrite <- eraser_add_keys_nil_r
          with (ks := (get_env Γ os).keys).
    rwr - eraser_add_keys_get_env_app.
    do 2 rwr - eraser_add_keys_nil_r.
    trv.
  Qed.






  Lemma eraser_add_keys_append_vars_to_env_app :
    forall xs vs Γ σ,
        length xs = length vs
    ->  (append_vars_to_env xs vs Γ).keys ᵏ++ σ
      = xs ˣ++ Γ.keys ᵏ++ σ.
  Proof.
    itr - xs vs Γ σ Hlength.
    ufl - get_keys
          append_vars_to_env.
    rwr - map_app.
    rwr - eraser_add_keys_app_l.
    erewrite length_map_inl in Hlength.
    epose proof zip_fst _ _ _ _ Hlength as Hzip_fst;
      clr - Hlength.
    cwr - Hzip_fst.
    ufl - eraser_add_vars.
    trv.
  Qed.



  Lemma eraser_append_vars_to_env_app :
    forall xs vs Γ,
        length xs = length vs
    ->  (append_vars_to_env xs vs Γ).keys
      = xs ˣ++ Γ.keys.
  Proof.
    itr - xs vs Γ Hlength.
    rwl - eraser_add_keys_nil_r.
    rewrite <- eraser_add_keys_nil_r
          with (ks := (append_vars_to_env xs vs Γ).keys).
    rwr - eraser_add_keys_append_vars_to_env_app.
          2: asm.
          clr - Hlength.
    do 2 rwr - eraser_add_keys_nil_r.
    trv.
  Qed.






  Lemma eraser_add_keys_append_funs_to_env_app :
    forall os n Γ σ,
        (append_funs_to_env os Γ n).keys ᵏ++ σ
      = os ᵒ⁻++ Γ.keys ᵏ++ σ.
  Proof.
    itr.
    ufl - append_funs_to_env.
    rwr - eraser_add_keys_get_env_app.
    ufl - eraser_add_ext_noid
          eraser_add_ext
          eraser_add_fids.
    feq.
    gen - n.
    ind - os as [| [f [xs e]] os IH]:
          smp.
    itr.
    smp.
    feq.
    bpe - IH: (S n).
  Qed.



  Lemma eraser_append_funs_to_env_app :
    forall os n Γ,
        (append_funs_to_env os Γ n).keys
      = os ᵒ⁻++ Γ.keys.
  Proof.
    itr.
    rwl - eraser_add_keys_nil_r.
    rewrite <- eraser_add_keys_nil_r
          with (ks := (append_funs_to_env os Γ n).keys).
    rwr - eraser_add_keys_append_funs_to_env_app.
    do 2 rwr - eraser_add_keys_nil_r.
    trv.
  Qed.






  Lemma eraser_add_keys_append_vars_to_env_get_env_app :
    forall xs vs os Γ σ,
        length xs = length vs
    ->  (append_vars_to_env xs vs (get_env Γ os)).keys ᵏ++ σ
      = xs ˣ++ os ᵒ++ Γ.keys ᵏ++ σ.
  Proof.
    itr - xs vs os Γ σ Hlength.
    rwr - eraser_add_keys_append_vars_to_env_app.
          2: asm.
          clr - Hlength.
    bwr - eraser_add_keys_get_env_app.
  Qed.



  Lemma eraser_append_vars_to_env_get_env_app :
    forall xs vs os Γ,
        length xs = length vs
    ->  (append_vars_to_env xs vs (get_env Γ os)).keys
      = xs ˣ++ os ᵒ++ Γ.keys.
  Proof.
    itr - xs vs os Γ Hlength.
    rwr - eraser_append_vars_to_env_app.
          2: asm.
          clr - Hlength.
    bwr - eraser_get_env_app.
  Qed.



End EraseSubstAppend_EraserLemmas.









Section EraseSubstAppend_SubstLemmas.



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



End EraseSubstAppend_SubstLemmas.









Section EraseSubstAppend_Theorems.




  Theorem erase_subst_append_vars :
    forall Γ xs e vs,
        base.length vs = base.length xs
    ->  (erase_exp
          (append_vars_to_env xs vs Γ).keys
          e)
        .[list_subst
          (map
            (fun v => erase_val v)
            (map snd (append_vars_to_env xs vs Γ)))
          idsubst]
      = (erase_exp
          (eraser_add_vars xs Γ.keys)
          e)
        .[upn (base.length xs)
          (list_subst
            (map
               (fun v => erase_val v)
               (map snd Γ)) idsubst)]
        .[list_subst
          (map
            (fun v => erase_val v) vs)
            idsubst].
  Proof.
    itr -  Γ xs e vs Hlen.
    (* add_keys *)
    sym - Hlen.
    rwr - eraser_append_vars_to_env_app.
    2 : exa - Hlen.
    (* upn to ++ *)
    rwr - subst_comp_exp.
    rwl - length_map_erase_val in Hlen.
    rwr - Hlen.
    rwr - substcomp_list.
    rwr - substcomp_id_l.
    rwr - list_subst_app.
    (* append to ++ *)
    ufl - append_vars_to_env.
    rwr - map_app.
    rwr - length_map_erase_val in Hlen.
    erewrite length_map_inl in Hlen.
    epose proof zip_snd _ _ _ _ Hlen as Hzip_snd;
      clr - Hlen.
    rwr - Hzip_snd.
    bwr - map_app.
  Qed.



End EraseSubstAppend_Theorems.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: EQVIVALENCE_HELPERS //////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.






Section EqvivalenceHelpers_References.



  Lemma get_value_cons_eqb :
    forall k v Γ key val,
        get_value ((k, v) :: Γ) key = Some [val]
    ->  (k = key /\ v = val)
    \/  (get_value Γ key = Some [val] /\ var_funid_eqb key k = false).
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - k v Γ key val Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb.
    * lft.
      rwr - var_funid_eqb_eq in Heqb; sbt.
      ivc - Hcons.
      spl; ato.
    * rgt; spl; ato.
  Qed.



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



  (*not used*)
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



  (*not used*)
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



  (*not used*)
  Lemma get_value_cons :
    forall k v Γ key val,
        get_value ((k, v) :: Γ) key = Some [val]
    ->  get_value [(k, v)] key = Some [val]
    \/  get_value Γ key = Some [val].
  Proof.
    (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
    itr - k v Γ key val Hcons.
    smp *.
    des > (var_funid_eqb key k) as Heqb_key; ato.
  Qed.


  (*not used*)
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



End EqvivalenceHelpers_References.









Section EqvivalenceHelpers_Map.



  Lemma make_map_exps_flatten_list_eq :
    forall ees,
      make_map_exps ees
    = flatten_list ees.
  Proof.
    ind - ees as [| [ke ve] ees IHees].
    * bmp.
    * smp.
      bwr - IHees.
  Qed.






  Theorem combine_key_and_val_lists :
    forall ᵏvs ᵛvs,
        length ᵏvs = length ᵛvs
    ->  make_value_map ᵏvs ᵛvs = (ᵏvs, ᵛvs)
    ->  exists vvs,
          ᵏvs = map fst vvs
       /\ ᵛvs = map snd vvs
       /\ combine ᵏvs ᵛvs = vvs
       /\ make_map_vals ᵏvs ᵛvs = flatten_list vvs.
  Proof.
    itr - ᵏvs ᵛvs Hlen Hmake.
    (* #1 Exists Zip: exists *)
    exi - (zip ᵏvs ᵛvs).
    (* #2 Combine Equal Zip: rewrite/simpl + exact *)
    rwr - zip_combine_eq in *.
    (* #3 Solve First 3: split + symmetry/apply/reflexivity *)
    spl. 1: sym; bpp - zip_fst.
    spl. 1: sym; bpp - zip_snd.
    spl. 1: rfl.
    (* #4 Apply Zip Equality: remember/apply/destruct/rewrite + exact *)
    rem - vvs as Hvvs:
      (zip ᵏvs ᵛvs).
    app + zip_equal as Hzip in Hvvs.
    2: exa - Hlen.
    des - Hzip as [Hfst Hsnd].
    rwr - Hvvs Hfst Hsnd.
    clr - ᵏvs ᵛvs Hlen Hmake Hvvs Hfst Hsnd.
    (* #5 Induction on Value Pair List: induction/simpl/rewrite + simpl*)
    ind - vvs as [| [kv vv] vvs IHvvs]: bmp.
    smp.
    bwr - IHvvs.
  Qed.






  Theorem combine_key_and_val_exc :
    forall ᵏvs ᵛvs k,
        length ᵏvs = k / 2 + k mod 2
    ->  length ᵛvs = k / 2
    ->  exists vvs vo,
          length vvs = k / 2
       /\ length vo = k mod 2
       /\ ᵏvs = map fst vvs ++ vo
       /\ ᵛvs = map snd vvs
       /\ make_map_vals ᵏvs ᵛvs = flatten_list vvs ++ vo.
  Proof.
    itr - ᵏvs ᵛvs k Hlen_k Hlen_v.
    rem - mod2 as Hmod2:
      (k mod 2).
    pse - modulo_2: k.
    sbt.
    des - H as [Heven | Hodd].
    * cwr - Heven in *.
      rwr - Nat.add_0_r in Hlen_k.
      rwl - Hlen_v in *.
      ren - Hlen: Hlen_k.
      clr - Hlen_v k.
      exi - (zip ᵏvs ᵛvs) ([] : list Value).
      do 2 rwr - app_nil_r.
      rem - vvs as Hvvs:
        (zip ᵏvs ᵛvs).
      pose proof zip_equal _ _ vvs ᵏvs ᵛvs Hlen Hvvs as Hzip.
      des - Hzip as [Hzip_fst Hzip_snd].
      cwr - Hzip_fst Hzip_snd in *.
      clr - ᵏvs ᵛvs.
      spl. 1: rwr - Hvvs; bwr - length_map.
      spl. 1: bmp.
      spl. 1: rfl.
      spl. 1: rfl.
      clr - Hlen Hvvs.
      (* #5 Induction on Value Pair List: induction/simpl/rewrite + simpl*)
      ind - vvs as [| [kv vv] vvs IHvvs]: bmp.
      smp.
      bwr - IHvvs.
    * cwr - Hodd in *.
      rem - n as Hn: (k / 2).
      clr - Hn k.
      ren - ᵏvs': ᵏvs.
      pse - length_diff_plus1 as Hlen_eq: Value ᵏvs' ᵛvs n Hlen_k Hlen_v.
      des - Hlen_eq as [ᵏvs [v [Hᵏvs Hlen]]].
      cwr - Hᵏvs in *.
      clr - ᵏvs'.
      (* exists *)
      exi - (zip ᵏvs ᵛvs) ([v] : list Value).
      rem - vvs as Hvvs:
        (zip ᵏvs ᵛvs).
      pose proof zip_equal _ _ vvs ᵏvs ᵛvs Hlen Hvvs as Hzip.
      des - Hzip as [Hzip_fst Hzip_snd].
      cwr - Hzip_fst Hzip_snd in *.
      clr - ᵏvs ᵛvs.
      spl. 1: by rwr - length_map in Hlen_v.
      spl. 1: bmp.
      spl. 1: rfl.
      spl. 1: rfl.
      clr - Hvvs Hlen Hlen_k Hlen_v n.
      (* #5 Induction on Value Pair List: induction/simpl/rewrite + simpl*)
      ind - vvs as [| [kv vv] vvs IHvvs]: bmp.
      smp.
      bwr - IHvvs.
  Qed.



End EqvivalenceHelpers_Map.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: AXIOMS ///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section Axioms.



  Axiom all_bsval_is_wfm :
    forall v,
      wfm_bs_val v.



  Axiom all_fsval_is_wfm :
    forall v,
      wfm_fs_val v.



  Axiom no_modfunc :
    forall modules own_module fid,
      get_own_modfunc own_module fid.1 fid.2 (modules ++ stdlib) = None.



  Axiom result_is_result :
    forall Γ modules own_module e r id id' eff eff',
        (eval_expr Γ modules own_module id e eff id' r eff')
    ->  is_result (erase_result r).



  Axiom eval_try_catch_vars_length :
    forall Γ modules own_module xs₁ xs₂ e₁ e₂ e₃ r id id' eff eff',
        (eval_expr Γ modules own_module id (ETry e₁ xs₁ e₂ xs₂ e₃)
                   eff id' r eff')
    ->  length xs₂ = 3.



  Axiom eval_map_wfm :
    forall Γ modules own_module el vl id id' eff eff',
        (eval_expr Γ modules own_module id (EMap el)
                   eff id' (inl [VMap vl]) eff')
    ->  (forall ᵏvs ᵛvs,
          make_value_map ᵏvs ᵛvs = (ᵏvs, ᵛvs)).



  Axiom erase_subst_rem_vars :
    forall Γ xs e,
       (erase_exp
        (eraser_add_vars xs (env_rem_vars xs Γ).keys)
        e)
      .[upn (base.length xs)
        (list_subst
          (map erase_val (map snd (env_rem_vars xs Γ)))
          idsubst)]
    = (erase_exp
        (eraser_add_vars xs Γ.keys)
        e)
      .[upn (base.length xs)
        (list_subst
          (map erase_val (map snd Γ))
          idsubst)].



End Axioms.









Section Axioms_Lemmas.



  Lemma get_value_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            key v (id : nat) (eff : SideEffectList),
        get_value Γ key = Some [v]
    ->  VALCLOSED (erase_val v).
  Proof.
    itr - Γ modules own_module key v id eff Hget.
    ass > (is_result (RValSeq (map (fun v' => erase_val v') [v]))) as Hscope.
    {
      rem - r as Hr:
            (inl [v] : ValueSequence + Exception).
      des - key as [var | fid].
      * rem - e as He:
              (EVar var).
        pse - result_is_result as Hresult:
              Γ modules own_module e r id id eff eff.
        sbt.
        app - Hresult.
        clr - Hresult.
        bpp - eval_var.
      * rem - e as He:
              (EFunId fid).
        pse - result_is_result as Hresult:
              Γ modules own_module e r id id eff eff.
        sbt.
        app - Hresult.
        clr - Hresult.
        bpp - eval_funid.
    }
    smp - Hscope.
    ivc - Hscope as Hscope: H0.
    ivc - Hscope as Hscope: H1 / H2.
    exa - Hscope.
  Qed.






  Lemma evar_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            x vs (id : nat) (eff : SideEffectList),
        get_value Γ (inl x) = Some vs
    ->  (exists v,
            [v] = vs
        /\  VALCLOSED (erase_val v)).
  Proof.
    itr - Γ modules own_module x vs id eff Hget.
    rem - key as Hkey:
          (inl x : Key).
    pse - get_value_singleton as Hsingle:
          Γ key vs Hget.
    des - Hsingle as [v Hsingle].
    cwr - Hsingle in *; clr - vs.
    exi - v.
    spl.
    rfl.
    pse - get_value_is_result as Hscope:
          Γ modules own_module key v id eff Hget.
    exa - Hscope.
  Qed.






  Lemma efunid_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            f vs (id : nat) (eff : SideEffectList),
        get_value Γ (inr f) = Some vs
    ->  (exists v,
            [v] = vs
        /\  VALCLOSED (erase_val v)).
  Proof.
    itr - Γ modules own_module f vs id eff Hget.
    rem - key as Hkey:
          (inr f : Key).
    pse - get_value_singleton as Hsingle:
          Γ key vs Hget.
    des - Hsingle as [v Hsingle].
    cwr - Hsingle in *; clr - vs.
    exi - v.
    spl.
    rfl.
    pse - get_value_is_result as Hscope:
          Γ modules own_module key v id eff Hget.
    exa - Hscope.
  Qed.






  Lemma efun_is_result :
    forall  Γ (modules : list ErlModule) (own_module : string)
            xs e id (eff : SideEffectList),
      is_result (erase_result (inl [VClos Γ [] id xs e])).
  Proof.
    itr - Γ modules own_module xs e id eff.
    pse - eval_fun as Heval:
          Γ modules own_module xs e eff id.
    bse - result_is_result:
          Γ modules own_module (EFun xs e)
          (inl [VClos Γ [] id xs e] : ValueSequence + Exception)
          id (S id) eff eff Heval.
  Qed.






  Lemma etry_catch_vars_length :
    forall Γ modules own_module (xs₁ : list Var) xs₂ e₁ (e₂ : Expression)
           e₃ q₁ r₃ id id' id'' eff eff' eff'',
        eval_expr Γ modules own_module id e₁ eff id' (inr q₁) eff'
    ->  eval_expr (append_vars_to_env xs₂ (exc_to_vals q₁) Γ)
                  modules own_module id' e₃ eff' id'' r₃ eff''
    ->  length xs₂ = 3.
  Proof.
    itr - Γ modules own_module xs₁ xs₂ e₁ e₂ e₃ q₁ r₃ id id' id''
          eff eff' eff'' IHe₁ IHe₃.
    rwl - exc_to_vals_eq in IHe₃.
    pse - eval_catch as Heval:
          Γ modules own_module xs₁ xs₂ e₁ e₂ e₃ r₃
          eff eff' eff'' id id' id'' q₁ IHe₁ IHe₃.
    bse - eval_try_catch_vars_length:
          Γ modules own_module xs₁ xs₂ e₁ e₂ e₃ r₃
          id id'' eff eff'' Heval.
  Qed.






  Lemma map_is_wfm :
    forall  Γ modules own_module ees ᵏvs ᵛvs kvm vvm vvs
            eff eff' eff'' ids id id',
        length ees = length ᵛvs
    ->  length ees = length ᵏvs
    ->  (length ees) * 2 = length eff
    ->  (length ees) * 2 = length ids
    ->  let es := make_map_exps ees in
        let vs := make_map_vals ᵏvs ᵛvs in
        (forall i,
            i < length es
        ->  (eval_expr Γ modules own_module
              (nth_def ids id 0 i) (nth i es ErrorExp) (nth_def eff eff' [] i)
              (nth_def ids id 0 (S i)) (inl [nth i vs ErrorValue])
              (nth_def eff eff' [] (S i))))
    ->  make_value_map ᵏvs ᵛvs = (kvm, vvm)
    ->  combine kvm vvm = vvs
    ->  eff'' = last eff eff'
    ->  id' = last ids id
    ->  (ᵏvs = kvm /\ ᵛvs = vvm).
  Proof.
    itr - Γ modules own_module ees ᵏvs ᵛvs kvm vvm vvs
          eff eff' eff'' ids id id'.
    itr - Hlen_v Hlen_k Hlen_eff Hlen_id elf vlf
          Hnth Hmake Hcomb Heq_eff Heq_id.
    epose proof eval_map _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      Hlen_v Hlen_k Hlen_eff Hlen_id Hnth Hmake Hcomb Heq_eff Heq_id
      as Heval_map.
    eapply eval_map_wfm in Heval_map.
    rwr - Heval_map in Hmake.
    by erewrite pair_eq in Hmake.
  Qed.



End Axioms_Lemmas.