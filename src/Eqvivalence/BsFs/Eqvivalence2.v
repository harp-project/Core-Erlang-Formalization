From CoreErlang.Eqvivalence.BsFs Require Import Helpers.

Import BigStep.

(** CONTENT:
* EQBSFS_ATOMS (LEMMAS)
  - Nil
  - Lit
* EQBSFS_REFERENCES (LEMMAS)
  - Var
  - FunId
* EQBSFS_SEQUENCES (LEMMAS)
  - Cons
  - Seq
* EQBSFS_FUNCTIONS (LEMMAS)
  - Fun
  - LetRec
* EQBSFS_BINDERS (LEMMAS)
  - Let
  - Try
* EQBSFS_LISTS (LEMMAS)
  - Values
  - Tuple
  - Map
* EQBSFS_ COMPOUNDS (LEMMAS)
  - PrimOp
  - Apply
  - Call
  - Case
* EQBSFS_ COMPOUNDS (LEMMAS)
  - Main
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_ATOMS //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ENil.



  Theorem eq_bsfs_enil :
    forall Γ σ,
      ⟨ [], erase_names σ Γ ENil ⟩
        -->*
      erase_result σ (inl [VNil]).
  Proof.
    itr.
    (* #1 Simplify: simpl*)
    smp.
    (* #2 Scope & Step: start/step *)
    start.
    step.
  Qed.



End ENil.









Section ELit.



  Theorem eq_bsfs_elit :
    forall lit Γ σ,
      ⟨ [], erase_names σ Γ (ELit lit) ⟩
        -->*
      erase_result σ (inl [VLit lit]).
  Proof.
    itr.
    (* #1 Simplify: simpl*)
    smp.
    (* #2 Scope & Step: start/step *)
    start.
    step.
  Qed.



End ELit.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_REFERENCES /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EVar.



  Theorem eq_bsfs_evar :
    forall var v Γ σ,
        get_value Γ (inl var) = Some [v]
    ->  VALCLOSED (erase_val (measure_val v) σ v)
    ->  ⟨ [], erase_names σ Γ (EVar var) ⟩
          -->*
        erase_result σ (inl [v]).
  Proof.
    itr - var v Γ σ Hget Hscope.
    (* #1 Simplify: simpl*)
    smp.
    ind - Γ as [| [k1 v1] Γ IH]: ivs - Hget.
    app + get_value_cons as Hget_cons in Hget.
    des - Hget_cons as [Hget1 | Hgets].
    * clr - IH Hget.
      app - get_value_single_det in Hget1.
      des - Hget1 as [Hk1 Hv1].
      sbt.
      rwr - cons_app.
      do 3 rwr - map_app.
      ufl - list_subst idsubst add_keys.
      unfold add_names.
      unfold add_name.
      smp.
      rwr - String.eqb_refl.
      smp.
      start.
      step.
    * spe - IH: Hgets.
      rwr - cons_app.
      do 3 rwr - map_app.
      ufl - list_subst idsubst add_keys.
      unfold add_names.
      unfold add_name.
      smp.
      des - k1 as [var1 | fid1].
      - des > ((var =? var1)%string) as Hvar.
        + smp - Hget.
          rwr - Hvar in Hget.
          ivc - Hget.
          app - String.eqb_eq in Hvar.
          sbt.
          smp.
          start.
          step.
        + smp.
          app - IH.
      - smp.
        app - IH.
  Qed.



End EVar.









Section EFunId.



  Theorem eq_bsfs_efunid :
    forall fid v Γ σ,
        get_value Γ (inr fid) = Some [v]
    ->  VALCLOSED (erase_val (measure_val v) σ v)
    ->  ⟨ [], erase_names σ Γ (EFunId fid) ⟩
          -->*
        erase_result σ (inl [v]).
  Proof.
    itr - fid v Γ σ Hget Hscope.
    (* #1 Simplify: simpl*)
    smp.
    ind - Γ as [| [k1 v1] Γ IH]: ivs - Hget.
    app + get_value_cons as Hget_cons in Hget.
    des - Hget_cons as [Hget1 | Hgets].
    * clr - IH Hget.
      app - get_value_single_det in Hget1.
      des - Hget1 as [Hk1 Hv1].
      sbt.
      rwr - cons_app.
      do 3 rwr - map_app.
      ufl - list_subst idsubst add_keys.
      unfold add_names.
      unfold add_name.
      smp.
      (* Dif from var*)
      rewrite prod_eqb_refl.
      2: app - String.eqb_refl.
      2: app - Nat.eqb_refl.
      smp.
      start.
      step.
    * spe - IH: Hgets.
      rwr - cons_app.
      do 3 rwr - map_app.
      ufl - list_subst idsubst add_keys.
      unfold add_names.
      unfold add_name.
      smp.
      des - k1 as [var1 | fid1].
      - smp.
        app - IH.
      - des > (funid_eqb fid fid1) as Hfid.
        + smp - Hget.
          rwr - Hfid in Hget.
          ivc - Hget.
          apply prod_eqb_eq in Hfid.
          2: itr; sym; app - String.eqb_eq.
          2: itr; sym; app - Nat.eqb_eq.
          sbt.
          rewrite prod_eqb_refl.
          2: app - String.eqb_refl.
          2: app - Nat.eqb_refl.
          smp.
          start.
          step.
        + smp - Hget.
          rwr - Hfid in Hget.
          unfold funid_eqb in Hfid.
          des - fid as [f n].
          des - fid1 as [f' n'].
          smp.
          rwr - Hfid.
          smp *.
          app - IH.
  Qed.



End EFunId.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_SEQUENCES //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ECons.



  Theorem eq_bsfs_econs :
    forall e1 e2 v1 v2 Γ σ,
        ⟨ [], erase_names σ Γ e1 ⟩
          -->*
        erase_result σ (inl [v1])
    ->  ⟨ [], erase_names σ Γ e2 ⟩
          -->*
        erase_result σ (inl [v2])
    ->  ⟨ [], erase_names σ Γ (ECons e1 e2) ⟩
          -->*
        erase_result σ (inl [VCons v1 v2]).
  Proof.
    itr - e1 e2 v1 v2 Γ σ IHv1 IHv2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' v1' as He1 Hv1:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_val (measure_val v1) σ v1).
    clr - He1 e1.
    mred.
    rem - e2' v2' as He2 Hv2:
      (erase_exp (add_keys (map fst Γ) σ) e2)
      (erase_val (measure_val v2) σ v2).
    clr - He2 e2.
    clr - Hv1 v1 Hv2 v2.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHv1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHv2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_v1 Hscope_v2.
    step - Hstep_v2 / e2' kv2.
    step - Hstep_v1 / e1' kv1 subst'.
    step.
  Qed.



  Theorem eq_bsfs_econs_exc1 :
    forall e1 e2 exc1 v2 Γ σ,
        ⟨ [], erase_names σ Γ e1 ⟩
          -->*
        erase_result σ (inr exc1)
    ->  ⟨ [], erase_names σ Γ e2 ⟩
          -->*
        erase_result σ (inl [v2])
    ->  ⟨ [], erase_names σ Γ (ECons e1 e2) ⟩
          -->*
        erase_result σ (inr exc1).
  Proof.
    itr - e1 e2 exc1 v2 Γ σ IHexc1 IHv2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc1' as He1 Hexc1:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc1).
    clr - He1 e1.
    mred.
    rem - e2' v2' as He2 Hv2:
      (erase_exp (add_keys (map fst Γ) σ) e2)
      (erase_val (measure_val v2) σ v2).
    clr - He2 e2.
    clr - Hexc1 exc1 Hv2 v2.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc1 as [kexc1 [Hscope_exc1 Hstep_exc1]].
    des - IHv2 as [kv2 [_ Hstep_v2]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc1.
    step - Hstep_v2 / e2' kv2.
    step - Hstep_exc1 / e1' kexc1 subst'.
    step.
  Qed.



  Theorem eq_bsfs_econs_exc2 :
    forall e1 e2 exc2 Γ σ,
        ⟨ [], erase_names σ Γ e2 ⟩
          -->*
        erase_result σ (inr exc2)
    ->  ⟨ [], erase_names σ Γ (ECons e1 e2) ⟩
          -->*
        erase_result σ (inr exc2).
  Proof.
    itr - e1 e2 exc2 Γ σ IHexc2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc2' as He1 Hexc2:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc2).
    clr - He1 e1.
    mred.
    rem - e2' as He2:
      (erase_exp (add_keys (map fst Γ) σ) e2).
    clr - He2 e2.
    clr - Hexc2 exc2.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc2 as [kexc2 [Hscope_exc2 Hstep_exc2]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc2.
    step - Hstep_exc2 / kexc2.
    step.
  Qed.



End ECons.









Section ESeq.



  Theorem eq_bsfs_eseq :
    forall e1 e2 v1 res2 Γ σ,
        ⟨ [], erase_names σ Γ e1 ⟩
          -->*
        erase_result σ (inl [v1])
    ->  ⟨ [], erase_names σ Γ e2 ⟩
          -->*
        erase_result σ res2
    ->  ⟨ [], erase_names σ Γ (ESeq e1 e2) ⟩
          -->*
        erase_result σ res2.
  Proof.
    itr - e1 e2 v1 res2 Γ σ IHv1 IHres2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' v1' as He1 Hv1:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_val (measure_val v1) σ v1).
    clr - He1 e1.
    mred.
    rem - e2' res2' as He2 Hres2:
      (erase_exp (add_keys (map fst Γ) σ) e2)
      (erase_result σ res2).
    clr - He2 e2.
    clr - Hv1 v1 Hres2 res2.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHv1 as [kv1 [_ Hstep_v1]].
    des - IHres2 as [kres2 [Hscope_res2 Hstep_res2]].
    (* #5 Scope & Step: start/step *)
    start - Hscope_res2.
    step - Hstep_v1 / e1' kv1.
    step - Hstep_res2.
  Qed.



  Theorem eq_bsfs_eseq_exc :
    forall e1 e2 exc1 Γ σ,
        ⟨ [], erase_names σ Γ e1 ⟩
          -->*
        erase_result σ (inr exc1)
    ->  ⟨ [], erase_names σ Γ (ESeq e1 e2) ⟩
          -->*
        erase_result σ (inr exc1).
  Proof.
    itr - e1 e2 exc1 Γ σ IHexc1.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc1' as He1 Hexc1:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc1).
    clr - He1 e1.
    mred.
    rem - e2' as He2:
      (erase_exp (add_keys (map fst Γ) σ) e2).
    clr - He2 e2.
    clr - Hexc1 exc1.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc1 as [kexc1 [Hscope_exc1 Hstep_exc1]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc1.
    step - Hstep_exc1 / e1' kexc1.
    step.
  Qed.



End ESeq.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_FUNCTIONS //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EFun.



  Theorem eq_bsfs_efun :
    forall vars e id Γ σ,
        rem_vars vars Γ = Γ
    ->  is_result (erase_result σ (inl [VClos Γ [] id vars e]))
    ->  ⟨ [], erase_names σ Γ (EFun vars e) ⟩
          -->*
        erase_result σ (inl [VClos Γ [] id vars e]).
  Proof.
    itr - vars e id Γ σ Hrem Hscope.
    (* #1 Simplify: simpl*)
    smp *.
    rwr - rem_ext_vars_empty in *.
    pse - add_ext_vars_empty as Hempty: vars σ.
    cwr - Hempty in *.
    cwr - Hrem in *.
    (* #3 Use Apply Theorem: rewrite/exact *)
    (* #2 Scope & Step: start/step *)
    start / Hscope.
    step.
    unfold measure_val_env.
    ufl - add_vars.
    rwr - add_keys_app.
    rwr - add_keys_app.
  Admitted.



End EFun.









Section ELetRec.



  Theorem eq_bsfs_eletrec :
    forall ext e id res Γ σ,
        ⟨ [], erase_names σ (append_funs_to_env ext Γ id) e ⟩
          -->*
        erase_result σ res
     -> ⟨ [], erase_names σ Γ (ELetRec ext e) ⟩
          -->*
        erase_result σ res.
  Proof.
    itr - ext e id res Γ σ IHres.
    smp *.
    des - IHres as [kres [Hscope_res Hstep_res]].
    (* #3 Use Apply Theorem: rewrite/exact *)
    (* #2 Scope & Step: start/step *)
    start / Hscope_res.
    step.
  Admitted.



End ELetRec.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_BINDERS ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ELet.



  Theorem eq_bsfs_elet :
    forall vars e1 e2 vs1 res2 Γ σ,
        length vars = base.length vs1
    ->  ⟨ [], erase_names σ Γ e1 ⟩
          -->*
        erase_result σ (inl vs1)
    ->  ⟨ [], erase_names σ (append_vars_to_env vars vs1 Γ) e2 ⟩
          -->*
        erase_result σ res2
    ->  ⟨ [], erase_names σ Γ (ELet vars e1 e2) ⟩
          -->*
        erase_result σ res2.
  Proof.
    itr - vars e1 e2 vs1 res2 Γ σ Hlength IHvs1 IHres2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Use Apply Theorem: rewrite/exact *)
    rwr - erase_exp_append_vars in IHres2.
    2: exa - Hlength.
    (* #4 Measure Reduction & Remember: remember/clear/measure_reduction/
      pose/rename *)
    rem - subst1' as Hsubst1:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    rem - subst2' as Hsubst2:
      (upn (base.length vars) subst1').
    clr - Hsubst1 Hsubst2.
    mred.
    rem - e1' vs1' as He1 Hvs1:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (map (λ v : Value, erase_val (measure_val v) σ v) vs1).
    clr - He1 e1.
    pose proof length_map_eq _ _ _ vars vs1 vs1' _ Hvs1 Hlength.
    clr - Hlength.
    ren - Hlength: H.
    mred.
    rem - e2' res2' as He2 Hres2:
      (erase_exp (add_vars vars (add_keys (map fst Γ) σ)) e2)
      (erase_result σ res2).
    clr - He2 e2.
    clr - Hvs1 vs1 Hres2 res2.
    clr - Γ σ.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHvs1 as [kvs1 [_ Hstep_vs1]].
    des - IHres2 as [kres2 [Hscope_res2 Hstep_res2]].
    (* #6 Scope & Step: start/step *)
    start / Hscope_res2.
    step - Hstep_vs1 / e1' kvs1 subst1'.
    step /  Hlength vars.
    step - Hstep_res2.
  Qed.



  Theorem eq_bsfs_elet_exc :
    forall vars e1 e2 exc1 Γ σ,
        ⟨ [], erase_names σ Γ e1 ⟩
          -->*
        erase_result σ (inr exc1)
    ->  ⟨ [], erase_names σ Γ (ELet vars e1 e2) ⟩
          -->*
        erase_result σ (inr exc1).
  Proof.
    itr - vars e1 e2 exc1 Γ σ IHexc1.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc1' as He1 Hexc1:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc1).
    clr - He1 e1.
    mred.
    rem - e2' as He2:
      (erase_exp (add_vars vars (add_keys (map fst Γ) σ)) e2).
    clr - He2 e2.
    clr - Hexc1 exc1.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc1 as [kexc1 [Hscope_exc1 Hstep_exc1]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc1.
    step - Hstep_exc1 / e1' kexc1.
    step.
  Qed.



End ELet.









Section ETry.

(*

env : Environment
modules : list ErlModule
own_module : string
vl1, vl2 : list Var
e1, e2, e3 : Expression
res : ValueSequence + Exception
vals : ValueSequence
eff1, eff2, eff3 : SideEffectList
id, id', id'' : nat
B1 : | env, modules, own_module, id, e1, eff1 | -e> | id', inl vals, eff2 |
H : base.length vl1 = base.length vals
B2 : | append_vars_to_env vl1 vals env, modules, own_module, id', e2, eff2 | -e> | id'', res, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env e1 ⟩ -->* erase_result σ (inl vals)
IHB2 :
  ∀ σ : NameSub, ⟨ [], erase_names σ (append_vars_to_env vl1 vals env) e2 ⟩ -->* erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ETry e1 vl1 e2 vl2 e3) ⟩ -->* erase_result σ res




env : Environment
modules : list ErlModule
own_module : string
vl1, vl2 : list Var
e1, e2, e3 : Expression
res : ValueSequence + Exception
eff1, eff2, eff3 : SideEffectList
id, id', id'' : nat
ex : Exception
B1 : | env, modules, own_module, id, e1, eff1 | -e> | id', inr ex, eff2 |
B2 :
  | append_try_vars_to_env vl2 [exclass_to_value ex.1.1; ex.1.2; ex.2] env, modules, own_module,
  id', e3, eff2 | -e> | id'', res, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env e1 ⟩ -->* erase_result σ (inr ex)
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ (append_try_vars_to_env vl2 [exclass_to_value ex.1.1; ex.1.2; ex.2] env) e3
    ⟩ -->* erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ETry e1 vl1 e2 vl2 e3) ⟩ -->* erase_result σ res


*)



End ETry.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_LISTS //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EValues.

(*

env : Environment
modules : list ErlModule
own_module : string
exps : list Expression
vals : list Value
eff : list (list (SideEffectId * list Value))
ids : list nat
eff1 : list (SideEffectId * list Value)
id : nat
eff' : list (SideEffectId * list Value)
id' : nat
H : base.length exps = base.length vals
H0 : base.length exps = base.length eff
H1 : base.length exps = base.length ids
H2 :
  ∀ i : nat,
    i < base.length exps
    → | env, modules, own_module, nth_def ids id 0 i, nth i exps ErrorExp, 
      nth_def eff eff1 [] i | -e> | nth_def ids id 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff1 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length exps
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i exps ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : id' = last ids id
H5 : eff' = last eff eff1
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EValues exps) ⟩ -->* erase_result σ (inl vals)





env : Environment
modules : list ErlModule
own_module : string
exps : list Expression
ex : Exception
vals : list Value
eff : list (list (SideEffectId * list Value))
ids : list nat
eff1 : list (SideEffectId * list Value)
id : nat
eff' : SideEffectList
id', i : nat
H : i < base.length exps
H0 : base.length vals = i
H1 : base.length eff = i
H2 : base.length ids = i
H3 :
  ∀ j : nat,
    j < i
    → | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, 
      nth_def eff eff1 [] j | -e> | nth_def ids id 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff1 [] (S j) |
H4 :
  ∀ j : nat,
    j < i
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j exps ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff' |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env (nth i exps ErrorExp) ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EValues exps) ⟩ -->* erase_result σ (inr ex)



*)



End EValues.









Section ETuple.

(*

env : Environment
modules : list ErlModule
own_module : string
exps : list Expression
vals : list Value
eff1, eff2 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id' : nat
H : base.length exps = base.length vals
H0 : base.length exps = base.length eff
H1 : base.length exps = base.length ids
H2 :
  ∀ i : nat,
    i < base.length exps
    → | env, modules, own_module, nth_def ids id 0 i, nth i exps ErrorExp, 
      nth_def eff eff1 [] i | -e> | nth_def ids id 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff1 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length exps
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i exps ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : eff2 = last eff eff1
H5 : id' = last ids id
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ETuple exps) ⟩ -->* erase_result σ (inl [VTuple vals])






env : Environment
modules : list ErlModule
own_module : string
i : nat
exps : list Expression
vals : list Value
ex : Exception
eff1, eff2 : SideEffectList
eff : list SideEffectList
id, id' : nat
ids : list nat
H : i < base.length exps
H0 : base.length vals = i
H1 : base.length eff = i
H2 : base.length ids = i
H3 :
  ∀ j : nat,
    j < i
    → | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, 
      nth_def eff eff1 [] j | -e> | nth_def ids id 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff1 [] (S j) |
H4 :
  ∀ j : nat,
    j < i
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j exps ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env (nth i exps ErrorExp) ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ETuple exps) ⟩ -->* erase_result σ (inr ex)


*)



End ETuple.









Section EMap.

(*

l : list (Expression * Expression)
vvals, kvals, kvals', vvals' : list Value
lv : list (Value * Value)
env : Environment
modules : list ErlModule
own_module : string
eff1, eff2 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id' : nat
H : base.length l = base.length vvals
H0 : base.length l = base.length kvals
H1 : base.length l * 2 = base.length eff
H2 : base.length l * 2 = base.length ids
exps := make_map_exps l : list Expression
vals := make_map_vals kvals vvals : list Value
H3 :
  ∀ i : nat,
    i < base.length exps
    → | env, modules, own_module, nth_def ids id 0 i, nth i exps ErrorExp, 
      nth_def eff eff1 [] i | -e> | nth_def ids id 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff1 [] (S i) |
H4 :
  ∀ i : nat,
    i < base.length exps
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i exps ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H5 : make_value_map kvals vvals = (kvals', vvals')
H6 : combine kvals' vvals' = lv
H7 : eff2 = last eff eff1
H8 : id' = last ids id
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EMap l) ⟩ -->* erase_result σ (inl [VMap lv])





l : list (Expression * Expression)
vvals, kvals : list Value
env : Environment
modules : list ErlModule
own_module : string
i : nat
ex : Exception
eff1, eff2 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id' : nat
H : i < 2 * base.length l
H0 : base.length vvals = i / 2
H1 : base.length kvals = i / 2 + i mod 2
H2 : base.length eff = i
H3 : base.length ids = i
exps := make_map_exps l : list Expression
vals := make_map_vals kvals vvals : list Value
H4 :
  ∀ j : nat,
    j < i
    → | env, modules, own_module, nth_def ids id 0 j, nth j exps ErrorExp, 
      nth_def eff eff1 [] j | -e> | nth_def ids id 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff1 [] (S j) |
H5 :
  ∀ j : nat,
    j < i
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j exps ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env (nth i exps ErrorExp) ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EMap l) ⟩ -->* erase_result σ (inr ex)



*)



End EMap.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_COMPOUNDS //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EPrimOp.

(*

env : Environment
modules : list ErlModule
own_module : string
res : ValueSequence + Exception
params : list Expression
vals : list Value
fname : string
eff1, eff2 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id' : nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
H2 :
  ∀ i : nat,
    i < base.length params
    → | env, modules, own_module, nth_def ids id 0 i, nth i params ErrorExp, 
      nth_def eff eff1 [] i | -e> | nth_def ids id 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff1 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : primop_eval fname vals (last eff eff1) = (res, eff2)
H5 : id' = last ids id
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EPrimOp fname params) ⟩ -->* erase_result σ res





env : Environment
modules : list ErlModule
own_module : string
i : nat
fname : string
params : list Expression
vals : list Value
ex : Exception
eff1, eff2 : SideEffectList
eff : list SideEffectList
id, id' : nat
ids : list nat
H : i < base.length params
H0 : base.length vals = i
H1 : base.length eff = i
H2 : base.length ids = i
H3 :
  ∀ j : nat,
    j < i
    → | env, modules, own_module, nth_def ids id 0 j, nth j params ErrorExp, 
      nth_def eff eff1 [] j | -e> | nth_def ids id 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff1 [] (S j) |
H4 :
  ∀ j : nat,
    j < i
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i params ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EPrimOp fname params) ⟩ -->* erase_result σ (inr ex)

*)



End EPrimOp.









Section EApply.

(*

params : list Expression
vals : list Value
env : Environment
modules : list ErlModule
own_module : string
exp, body : Expression
res : ValueSequence + Exception
var_list : list Var
ref : Environment
ext : list (nat * FunctionIdentifier * FunctionExpression)
n : nat
eff1, eff2, eff3 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'' : nat
H : base.length params = base.length vals
B1 :
  | env, modules, own_module, id, exp, eff1 | -e> | id', inl [VClos ref ext n var_list body], eff2 |
H0 : base.length var_list = base.length vals
H1 : base.length params = base.length eff
H2 : base.length params = base.length ids
H3 :
  ∀ i : nat,
    i < base.length params
    → | env, modules, own_module, nth_def ids id' 0 i, nth i params ErrorExp, 
      nth_def eff eff2 [] i | -e> | nth_def ids id' 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff2 [] (S i) |
H4 :
  ∀ i : nat,
    i < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
B2 :
  | append_vars_to_env var_list vals (get_env ref ext), modules, own_module, 
  last ids id', body, last eff eff2 | -e> | id'', res, eff3 |
IHB1 :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ env exp ⟩ -->* erase_result σ (inl [VClos ref ext n var_list body])
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ (append_vars_to_env var_list vals (get_env ref ext)) body ⟩ -->*
    erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EApp exp params) ⟩ -->* erase_result σ res



params : list Expression
env : Environment
modules : list ErlModule
own_module : string
exp : Expression
ex : Exception
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, exp, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env exp ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EApp exp params) ⟩ -->* erase_result σ (inr ex)



params : list Expression
vals : list Value
env : Environment
modules : list ErlModule
own_module : string
exp : Expression
ex : Exception
i : nat
v : Value
eff1, eff2, eff3 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'' : nat
H : i < base.length params
H0 : base.length vals = i
H1 : base.length eff = i
H2 : base.length ids = i
B1 : | env, modules, own_module, id, exp, eff1 | -e> | id', inl [v], eff2 |
H3 :
  ∀ j : nat,
    j < i
    → | env, modules, own_module, nth_def ids id' 0 j, nth j params ErrorExp, 
      nth_def eff eff2 [] j | -e> | nth_def ids id' 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff2 [] (S j) |
H4 :
  ∀ j : nat,
    j < i
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
B2 :
  | env, modules, own_module, last ids id', nth i params ErrorExp, last eff eff2 | -e> | id'',
  inr ex, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env exp ⟩ -->* erase_result σ (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EApp exp params) ⟩ -->* erase_result σ (inr ex)




params : list Expression
vals : list Value
env : Environment
modules : list ErlModule
own_module : string
v : Value
exp : Expression
eff1, eff2, eff3 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'' : nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
B : | env, modules, own_module, id, exp, eff1 | -e> | id', inl [v], eff2 |
H2 :
  ∀ j : nat,
    j < base.length params
    → | env, modules, own_module, nth_def ids id' 0 j, nth j params ErrorExp, 
      nth_def eff eff2 [] j | -e> | nth_def ids id' 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff2 [] (S j) |
H3 :
  ∀ j : nat,
    j < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
H4 :
  ∀ (ref : list ((Var + FunctionIdentifier) * Value)) (ext : list
                                                               (nat * FunctionIdentifier *
                                                                FunctionExpression)) 
    (var_list : list Var) (body : Expression) (n : nat), v ≠ VClos ref ext n var_list body
H5 : eff3 = last eff eff2
H6 : id'' = last ids id'
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env exp ⟩ -->* erase_result σ (inl [v])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EApp exp params) ⟩ -->* erase_result σ (inr (badfun v))





params : list Expression
vals : list Value
env : Environment
modules : list ErlModule
own_module : string
exp, body : Expression
var_list : list Var
ref : Environment
ext : list (nat * FunctionIdentifier * FunctionExpression)
eff1, eff2, eff3 : SideEffectList
eff : list SideEffectList
n : nat
ids : list nat
id, id', id'' : nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
B :
  | env, modules, own_module, id, exp, eff1 | -e> | id', inl [VClos ref ext n var_list body], eff2 |
H2 :
  ∀ j : nat,
    j < base.length params
    → | env, modules, own_module, nth_def ids id' 0 j, nth j params ErrorExp, 
      nth_def eff eff2 [] j | -e> | nth_def ids id' 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff2 [] (S j) |
H3 :
  ∀ j : nat,
    j < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
H4 : base.length var_list ≠ base.length vals
H5 : eff3 = last eff eff2
H6 : id'' = last ids id'
IHB :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ env exp ⟩ -->* erase_result σ (inl [VClos ref ext n var_list body])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EApp exp params) ⟩ -->*
erase_result σ (inr (badarity (VClos ref ext n var_list body)))





*)



End EApply.









Section ECall.

(*

env : Environment
modules : list ErlModule
own_module : string
res : ValueSequence + Exception
params : list Expression
vals : list Value
mexp, fexp : Expression
mname, fname : string
eff1, eff2, eff3, eff4 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'', id''' : nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
B1 : | env, modules, own_module, id, mexp, eff1 | -e> | id', inl [VLit (Atom mname)], eff2 |
B2 : | env, modules, own_module, id', fexp, eff2 | -e> | id'', inl [VLit (Atom fname)], eff3 |
H2 :
  ∀ i : nat,
    i < base.length params
    → | env, modules, own_module, nth_def ids id'' 0 i, nth i params ErrorExp, 
      nth_def eff eff3 [] i | -e> | nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff3 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : get_modfunc mname fname (base.length vals) (modules ++ stdlib) = None
H5 : eval mname fname vals (last eff eff3) = (res, eff4)
H6 : id''' = last ids id''
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inl [VLit (Atom mname)])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env fexp ⟩ -->* erase_result σ (inl [VLit (Atom fname)])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ res





env : Environment
modules : list ErlModule
own_module : string
res : ValueSequence + Exception
params : list Expression
vals : list Value
mexp, fexp : Expression
mname, fname : string
func : TopLevelFunction
eff1, eff2, eff3, eff4 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'', id''' : nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
B1 : | env, modules, own_module, id, mexp, eff1 | -e> | id', inl [VLit (Atom mname)], eff2 |
B2 : | env, modules, own_module, id', fexp, eff2 | -e> | id'', inl [VLit (Atom fname)], eff3 |
H2 :
  ∀ i : nat,
    i < base.length params
    → | env, modules, own_module, nth_def ids id'' 0 i, nth i params ErrorExp, 
      nth_def eff eff3 [] i | -e> | nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff3 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : get_modfunc mname fname (base.length vals) (modules ++ stdlib) = Some func
B3 :
  | append_vars_to_env (varl func) vals [], modules, mname, last ids id'', 
  body func, last eff eff3 | -e> | id''', res, eff4 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inl [VLit (Atom mname)])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env fexp ⟩ -->* erase_result σ (inl [VLit (Atom fname)])
IHB3 :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ (append_vars_to_env (varl func) vals []) (body func) ⟩ -->*
    erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ res







env : Environment
modules : list ErlModule
own_module : string
i : nat
mexp, fexp : Expression
v, v' : Value
params : list Expression
vals : list Value
ex : Exception
eff1, eff2, eff3, eff4 : SideEffectList
eff : list SideEffectList
id, id', id'', id''' : nat
ids : list nat
H : i < base.length params
H0 : base.length vals = i
H1 : base.length eff = i
H2 : base.length ids = i
B1 : | env, modules, own_module, id, mexp, eff1 | -e> | id', inl [v], eff2 |
B2 : | env, modules, own_module, id', fexp, eff2 | -e> | id'', inl [v'], eff3 |
H3 :
  ∀ j : nat,
    j < i
    → | env, modules, own_module, nth_def ids id'' 0 j, nth j params ErrorExp, 
      nth_def eff eff3 [] j | -e> | nth_def ids id'' 0 (S j), inl [nth j vals ErrorValue],
      nth_def eff eff3 [] (S j) |
H4 :
  ∀ j : nat,
    j < i
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth j params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth j vals ErrorValue])
B3 :
  | env, modules, own_module, last ids id'', nth i params ErrorExp, last eff eff3 | -e> | id''',
  inr ex, eff4 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env fexp ⟩ -->* erase_result σ (inl [v'])
IHB3 : ∀ σ : NameSub, ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ (inr ex)







env : Environment
modules : list ErlModule
own_module : string
mexp, fexp : Expression
params : list Expression
ex : Exception
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, mexp, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ (inr ex)






env : Environment
modules : list ErlModule
own_module : string
mexp, fexp : Expression
v : Value
params : list Expression
ex : Exception
eff1, eff2, eff3 : SideEffectList
id, id', id'' : nat
B1 : | env, modules, own_module, id, mexp, eff1 | -e> | id', inl [v], eff2 |
B2 : | env, modules, own_module, id', fexp, eff2 | -e> | id'', inr ex, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env fexp ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ (inr ex)





env : Environment
modules : list ErlModule
own_module : string
mexp, fexp : Expression
v, v' : Value
params : list Expression
vals : list Value
eff1, eff2, eff3, eff4 : SideEffectList
eff : list SideEffectList
id, id', id'', id''' : nat
ids : list nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
B1 : | env, modules, own_module, id, mexp, eff1 | -e> | id', inl [v], eff2 |
B2 : | env, modules, own_module, id', fexp, eff2 | -e> | id'', inl [v'], eff3 |
H2 :
  ∀ i : nat,
    i < base.length params
    → | env, modules, own_module, nth_def ids id'' 0 i, nth i params ErrorExp, 
      nth_def eff eff3 [] i | -e> | nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff3 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : ∀ mname : string, v ≠ VLit (Atom mname)
H5 : eff4 = last eff eff3
H6 : id''' = last ids id''
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env fexp ⟩ -->* erase_result σ (inl [v'])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ (inr (badarg v))







env : Environment
modules : list ErlModule
own_module : string
mexp, fexp : Expression
mname : string
v' : Value
params : list Expression
vals : list Value
eff1, eff2, eff3, eff4 : SideEffectList
eff : list SideEffectList
id, id', id'', id''' : nat
ids : list nat
H : base.length params = base.length vals
H0 : base.length params = base.length eff
H1 : base.length params = base.length ids
B1 : | env, modules, own_module, id, mexp, eff1 | -e> | id', inl [VLit (Atom mname)], eff2 |
B2 : | env, modules, own_module, id', fexp, eff2 | -e> | id'', inl [v'], eff3 |
H2 :
  ∀ i : nat,
    i < base.length params
    → | env, modules, own_module, nth_def ids id'' 0 i, nth i params ErrorExp, 
      nth_def eff eff3 [] i | -e> | nth_def ids id'' 0 (S i), inl [nth i vals ErrorValue],
      nth_def eff eff3 [] (S i) |
H3 :
  ∀ i : nat,
    i < base.length params
    → ∀ σ : NameSub,
        ⟨ [], erase_names σ env (nth i params ErrorExp) ⟩ -->*
        erase_result σ (inl [nth i vals ErrorValue])
H4 : ∀ fname : string, v' ≠ VLit (Atom fname)
H5 : eff4 = last eff eff3
H6 : id''' = last ids id''
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env mexp ⟩ -->* erase_result σ (inl [VLit (Atom mname)])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names σ env fexp ⟩ -->* erase_result σ (inl [v'])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECall mexp fexp params) ⟩ -->* erase_result σ (inr (badarg v'))


*)



End ECall.









Section ECase.

(*

env : Environment
modules : list ErlModule
own_module : string
guard, exp, e : Expression
vals : ValueSequence
res : ValueSequence + Exception
l : list (list Pattern * Expression * Expression)
bindings : list (Var * Value)
i : nat
eff1, eff2, eff3 : SideEffectList
id, id', id'' : nat
B1 : | env, modules, own_module, id, e, eff1 | -e> | id', inl vals, eff2 |
H : i < base.length l
H0 : match_clause vals l i = Some (guard, exp, bindings)
H1 :
  ∀ j : nat,
    j < i
    → ∀ (gg ee : Expression) (bb : list (Var * Value)),
        match_clause vals l j = Some (gg, ee, bb)
        → | add_bindings bb env, modules, own_module, id', gg, eff2 | -e> | id', 
          inl [ffalse], eff2 |
H2 :
  ∀ j : nat,
    j < i
    → ∀ (gg ee : Expression) (bb : list (Var * Value)),
        match_clause vals l j = Some (gg, ee, bb)
        → ∀ σ : NameSub,
            ⟨ [], erase_names σ (add_bindings bb env) gg ⟩ -->* erase_result σ (inl [ffalse])
B2 :
  | add_bindings bindings env, modules, own_module, id', guard, eff2 | -e> | id', 
  inl [ttrue], eff2 |
B3 : | add_bindings bindings env, modules, own_module, id', exp, eff2 | -e> | id'', res, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env e ⟩ -->* erase_result σ (inl vals)
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ (add_bindings bindings env) guard ⟩ -->* erase_result σ (inl [ttrue])
IHB3 : ∀ σ : NameSub, ⟨ [], erase_names σ (add_bindings bindings env) exp ⟩ -->* erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECase e l) ⟩ -->* erase_result σ res




env : Environment
modules : list ErlModule
own_module : string
e : Expression
ex : Exception
l : list (list Pattern * Expression * Expression)
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, e, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env e ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECase e l) ⟩ -->* erase_result σ (inr ex)




env : Environment
modules : list ErlModule
own_module : string
e : Expression
l : list (list Pattern * Expression * Expression)
vals : ValueSequence
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, e, eff1 | -e> | id', inl vals, eff2 |
H :
  ∀ j : nat,
    j < base.length l
    → ∀ (gg ee : Expression) (bb : list (Var * Value)),
        match_clause vals l j = Some (gg, ee, bb)
        → | add_bindings bb env, modules, own_module, id', gg, eff2 | -e> | id', 
          inl [ffalse], eff2 |
H0 :
  ∀ j : nat,
    j < base.length l
    → ∀ (gg ee : Expression) (bb : list (Var * Value)),
        match_clause vals l j = Some (gg, ee, bb)
        → ∀ σ : NameSub,
            ⟨ [], erase_names σ (add_bindings bb env) gg ⟩ -->* erase_result σ (inl [ffalse])
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env e ⟩ -->* erase_result σ (inl vals)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECase e l) ⟩ -->* erase_result σ (inr if_clause)



env : Environment
modules : list ErlModule
own_module : string
e, guard, exp : Expression
bindings : list (Var * Value)
l : list (list Pattern * Expression * Expression)
i : nat
vals : ValueSequence
ex : Exception
eff1, eff2 : SideEffectList
id, id' : nat
B1 : | env, modules, own_module, id, e, eff1 | -e> | id', inl vals, eff2 |
H : i < base.length l
H0 : match_clause vals l i = Some (guard, exp, bindings)
H1 :
  ∀ j : nat,
    j < i
    → ∀ (gg ee : Expression) (bb : list (Var * Value)),
        match_clause vals l j = Some (gg, ee, bb)
        → | add_bindings bb env, modules, own_module, id', gg, eff2 | -e> | id', 
          inl [ffalse], eff2 |
H2 :
  ∀ j : nat,
    j < i
    → ∀ (gg ee : Expression) (bb : list (Var * Value)),
        match_clause vals l j = Some (gg, ee, bb)
        → ∀ σ : NameSub,
            ⟨ [], erase_names σ (add_bindings bb env) gg ⟩ -->* erase_result σ (inl [ffalse])
B2 : | add_bindings bindings env, modules, own_module, id', guard, eff2 | -e> | id', inr ex, eff2 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env e ⟩ -->* erase_result σ (inl vals)
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names σ (add_bindings bindings env) guard ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ECase e l) ⟩ -->* erase_result σ (inr ex)



*)



End ECase.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_MAIN ///////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Section Main.

  Theorem eq_bsfs :
    forall Γ modules own_module id id' e e' eff eff' σ,
        (eval_expr Γ modules own_module id e eff id' e' eff')
    ->  ⟨ [], (erase_names σ Γ e) ⟩ -->* erase_result σ e'.
  Proof.
    itr - Γ modules own_module id id' e e' eff eff' σ B.
    ind - B; ren - Γ: env.
    (* #1 Atoms: ENil/ENil *)
      (* +1.1 ENil: *)
          3:  by pse - eq_bsfs_enil: Γ σ.
      (* +1.2 ELit: *)
          3:  by pse - eq_bsfs_elit: l Γ σ.
    (* #2 References: EVar/EFunId *)
      (* +2.1 EVar: *)
          3: {
            pse - var_is_result as Hv:
              s res Γ σ modules own_module id eff H.
            des - Hv as [v [Heq Hscope]].
            sbt.
            bse - eq_bsfs_evar: s v Γ σ H Hscope.
          }
      (* +2.2 EFunId: success/modfunc *)
        (* -2.2.1 success: *)
          3: {
            pse - funid_is_result as Hv:
              fid res Γ σ modules own_module id eff H.
            des - Hv as [v [Heq Hscope]].
            sbt.
            bse - eq_bsfs_efunid: fid v Γ σ H Hscope.
          }
        (* -2.2.2 modfunc: *)
          3:  pse - no_modfunc; con.
    (* #3 Sequences: ECons/ESeq *)
      (* +3.1 ECons: success/exception1/exception2 *)
        (* -3.1.1 success: *)
          5:  by pse - eq_bsfs_econs: hd tl hdv tlv Γ σ IHB2 IHB1.
        (* -3.1.2 exception1: *)
          15: by pse - eq_bsfs_econs_exc1: hd tl ex vtl Γ σ IHB2 IHB1.
        (* -3.1.3 exception2: *)
          14: by pse - eq_bsfs_econs_exc2: hd tl ex Γ σ IHB.
      (* +3.2 ESeq: success/exception *)
        (* -3.2.1 success: *)
          11: by pse - eq_bsfs_eseq: e1 e2 v1 v2 Γ σ IHB1 IHB2.
        (* -3.2.2 exception: *)
          30: by pse - eq_bsfs_eseq_exc: e1 e2 ex Γ σ IHB.
    (* #4 Functions: EFun/ELetrec *)
      (* +4.1 EFun: *)
          3: {
            pse - fun_is_result as H: vl e id Γ σ modules own_module eff.
            des - H as [Hscope Hrem].
          } 
      (* +4.2 ELetrec: *)
         10:  admit.
    (* #5 Binders: ELet/ETry *)
      (* +5.1 ELet: success/exception *)
        (* -5.1.1 success: *)
          9:  by pse - eq_bsfs_elet: l e1 e2 vals res Γ σ H IHB1 IHB2.
        (* -5.1.2 exception: *)
          26: by pse - eq_bsfs_elet_exc: vl e1 e2 ex Γ σ IHB.
      (* +5.2 ETry: result1/result2 *)
        (* -5.2.1 result1: *)
          11: admit.
        (* -5.2.2 result: *)
          11: admit.
    (* #6 Lists: EValues/ETuple/EMap *)
      (* +6.1 EValues: valseq/exception *)
        (* -6.1.1 valseq: *)
          1:  admit.
        (* -6.1.2 exception: *)
          1:  admit.
      (* +6.2 ETuple: valseq/exception *)
        (* -6.2.1 valseq: *)
          1:  admit.
        (* -6.2.2 exception: *)
          7:  admit.
      (* +6.3 EMap: valseq/exception *)
        (* -6.3.1 valseq: *)
          6:  admit.
        (* -6.3.2 exception: *)
          19: admit.
    (* #7 Compounds: EPrimOp/EApply/ECall/ECase *)
      (* +7.1 EPrimOp: result/exception *)
        (* -7.1.1 result: *)
          4:  admit.
        (* -7.1.2 exception: *)
          13: admit.
      (* +7.2 EApply: result/exception1/exception2/badfun1/badfun2 *)
        (* -7.2.1 result: *)
          4:  admit.
        (* -7.2.2 exception: *)
          12: admit.
        (* -7.2.3 exception: *)
          12: admit.
        (* -7.2.4 exception: *)
          12: admit.
        (* -7.2.5 exception: *)
          12: admit.
      (* +7.3 ECall: result1/result2/exception1/exception2/exception3/
                     badarg1/badarg2 *)
        (* -7.3.1 result1: *)
          2:  admit.
        (* -7.3.2 result2: *)
          2:  admit.
        (* -7.3.3 exception1: *)
          5:  admit.
        (* -7.3.4 exception2: *)
          5:  admit.
        (* -7.3.5 exception3: *)
          5:  admit.
        (* -7.3.6 badarg1: *)
          5:  admit.
        (* -7.3.7 badarg2: *)
          5:  admit.
      (* +7.4 ECase: result/exception1/exception2/ifclause *)
        (* -7.4.1 result: *)
          1:  admit.
        (* -7.4.2 exception1: *)
          1:  admit.
        (* -7.4.3 exception2: *)
          2:  admit.
        (* -7.4.4 ifclause: *)
          1:  admit.
  Admitted.



End Main.