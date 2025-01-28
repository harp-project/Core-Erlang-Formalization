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
Search nat "comm".


  Ltac mred_le_solver2 :=
    smp;
    try unfold measure_val_list;
    try unfold measure_val_map;
    try unfold measure_val_env;
    try rewrite map_app, list_sum_app;
    (sli + (rewrite Nat.add_comm; slia)).

Ltac mred2 :=
    try (rewrite mred_min; [idtac | mred_le_solver]);
    try (rewrite mred_min_list; [idtac | mred_le_solver]);
    try (rewrite mred_min_map; [idtac | mred_le_solver]).

Ltac mred2_all :=
  repeat (
    mred2;
    try (rewrite mred_min; [idtac | mred_le_solver2]);
    try (rewrite mred_min_list; [idtac | mred_le_solver2]);
    try (rewrite mred_min_map; [idtac | mred_le_solver2])
  ).


Theorem eq_bsfs :
  forall Γ modules own_module id id' e e' eff eff' σ,
      (eval_expr Γ modules own_module id e eff id' e' eff')
  ->  ⟨ [], (erase_names σ Γ e) ⟩ -->* erase_result σ e'.
Proof.
  itr - Γ modules own_module id id' e e' eff eff' σ B.
  gen - σ.
  ind - B; itr.
  10: {
    smp.
    assert ((erase_val (measure_val hdv + measure_val tlv) σ hdv) = (erase_val (measure_val hdv) σ hdv)).
    apply measure_reduction.
    mred2_all.
    mred2.
    rewrite mred_min with (v := tlv).
    eei; spl.
    admit.
    ens.
    cns.
    mred2.
    ens.
    
    do 5 mred2.
    rewrite mred_min.
  }
Admitted. *)








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
    smp.
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
    smp.
    start.
    step.
  Qed.



End ELit.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_REFERENCES /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Section tmp.

(*


env : Environment
modules : list ErlModule
own_module : string
s : Var
eff : SideEffectList
id : nat
res : ValueSequence
H : get_value env (inl s) = Some res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EVar s) ⟩ -->* erase_result σ (inl res)

*)



End tmp.

Section tmp.

(*

env : Environment
modules : list ErlModule
own_module : string
fid : FunctionIdentifier
eff : SideEffectList
res : ValueSequence
id : nat
H : get_value env (inr fid) = Some res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EFunId fid) ⟩ -->* erase_result σ (inl res)




env : Environment
modules : list ErlModule
own_module : string
fid : FunctionIdentifier
eff : SideEffectList
func : TopLevelFunction
body_func : Expression
varl_func : list Var
id : nat
H : get_value env (inr fid) = None
H0 : get_own_modfunc own_module fid.1 fid.2 (modules ++ stdlib) = Some func
H1 : varl_func = varl func
H2 : body_func = body func
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EFunId fid) ⟩ -->*
erase_result σ (inl [VClos env [] id varl_func body_func])

*)



End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_SEQUENCES //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ECons.



  Theorem eq_bsfs_econs :
    forall e1 e2 v1 v2 Γ σ,
        (forall σ,
          ⟨ [], erase_names σ Γ e1 ⟩
            -->*
          erase_result σ (inl [v1]))
    ->  (forall σ,
          ⟨ [], erase_names σ Γ e2 ⟩
            -->*
          erase_result σ (inl [v2]))
    ->  ⟨ [], erase_names σ Γ (ECons e1 e2) ⟩
          -->*
        erase_result σ (inl [VCons v1 v2]).
  Proof.
    itr - e1 e2 v1 v2 Γ σ IHv1 IHv2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Specialize Inductive Hypothesis: specialize *)
    spe - IHv1: σ.
    spe - IHv2: σ.
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
    forall e1 e2 exc v2 Γ σ,
        (forall σ,
          ⟨ [], erase_names σ Γ e1 ⟩
            -->*
          erase_result σ (inr exc))
    ->  (forall σ,
          ⟨ [], erase_names σ Γ e2 ⟩
            -->*
          erase_result σ (inl [v2]))
    ->  ⟨ [], erase_names σ Γ (ECons e1 e2) ⟩
          -->*
        erase_result σ (inr exc).
  Proof.
    itr - e1 e2 exc v2 Γ σ IHexc IHv2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Specialize Inductive Hypothesis: specialize *)
    spe - IHexc: σ.
    spe - IHv2: σ.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc' as He1 Hexc:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc).
    clr - He1 e1.
    mred.
    rem - e2' v2' as He2 Hv2:
      (erase_exp (add_keys (map fst Γ) σ) e2)
      (erase_val (measure_val v2) σ v2).
    clr - He2 e2.
    clr - Hexc exc Hv2 v2.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc as [kexc [Hscope_exc Hstep_exc]].
    des - IHv2 as [kv2 [_ Hstep_v2]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc.
    step - Hstep_v2 / e2' kv2.
    step - Hstep_exc / e1' kexc subst'.
    step.
  Qed.



  Theorem eq_bsfs_econs_exc2 :
    forall e1 e2 exc Γ σ,
        (forall σ,
          ⟨ [], erase_names σ Γ e2 ⟩
            -->*
          erase_result σ (inr exc))
    ->  ⟨ [], erase_names σ Γ (ECons e1 e2) ⟩
          -->*
        erase_result σ (inr exc).
  Proof.
    itr - e1 e2 exc Γ σ IHexc.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Specialize Inductive Hypothesis: specialize *)
    spe - IHexc: σ.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc' as He1 Hexc:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc).
    clr - He1 e1.
    mred.
    rem - e2' as He2:
      (erase_exp (add_keys (map fst Γ) σ) e2).
    clr - He2 e2.
    clr - Hexc exc.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc as [kexc [Hscope_exc Hstep_exc]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc.
    step - Hstep_exc / kexc.
    step.
  Qed.



End ECons.









Section ESeq.



  Theorem eq_bsfs_eseq :
    forall e1 e2 v1 v2 Γ σ,
        (forall σ,
          ⟨ [], erase_names σ Γ e1 ⟩
            -->*
          erase_result σ (inl [v1]))
    ->  (forall σ,
          ⟨ [], erase_names σ Γ e2 ⟩
            -->*
          erase_result σ (inl v2))
    ->  ⟨ [], erase_names σ Γ (ESeq e1 e2) ⟩
          -->*
        erase_result σ (inl v2).
  Proof.
    itr - e1 e2 v1 v2 Γ σ IHv1 IHv2.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Specialize Inductive Hypothesis: specialize *)
    spe - IHv1: σ.
    spe - IHv2: σ.
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
      (map (λ v : Value, erase_val (measure_val v) σ v) v2).
    clr - He2 e2.
    clr - Hv1 v1 Hv2 v2.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHv1 as [kv1 [_ Hstep_v1]].
    des - IHv2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #5 Scope & Step: start/step *)
    start - Hscope_v2.
    step - Hstep_v1 / e1' kv1.
    step - Hstep_v2.
  Qed.



  Theorem eq_bsfs_eseq_exc :
    forall e1 e2 exc Γ σ,
        (forall σ,
          ⟨ [], erase_names σ Γ e1 ⟩
            -->*
          erase_result σ (inr exc))
    ->  ⟨ [], erase_names σ Γ (ESeq e1 e2) ⟩
          -->*
        erase_result σ (inr exc).
  Proof.
    itr - e1 e2 exc Γ σ IHexc.
    (* #1 Simplify: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Specialize Inductive Hypothesis: specialize *)
    spe - IHexc: σ.
    (* #3 Measure Reduction & Remember: remember/clear/measure_reduction *)
    rem - subst' as Hsubst:
      (list_subst
        (map
          (λ v : Value, erase_val (measure_val v) σ v)
          (map snd Γ))
        idsubst).
    clr - Hsubst.
    mred.
    rem - e1' exc' as He1 Hexc:
      (erase_exp (add_keys (map fst Γ) σ) e1)
      (erase_exc σ exc).
    clr - He1 e1.
    mred.
    rem - e2' as He2:
      (erase_exp (add_keys (map fst Γ) σ) e2).
    clr - He2 e2.
    clr - Hexc exc.
    clr - Γ σ.
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHexc as [kexc [Hscope_exc Hstep_exc]].
    (* #5 Scope & Step: start/step *)
    start / Hscope_exc.
    step - Hstep_exc / e1' kexc.
    step.
  Qed.



End ESeq.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_FUNCTIONS //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Section tmp.

(*

env : Environment
modules : list ErlModule
own_module : string
vl : list Var
e : Expression
eff : SideEffectList
id : nat
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (EFun vl e) ⟩ -->* erase_result σ (inl [VClos env [] id vl e])

*)



End tmp.

Section tmp.

(*

env : Environment
modules : list ErlModule
own_module : string
e : Expression
l : list (FunctionIdentifier * (list Var * Expression))
res : ValueSequence + Exception
eff1, eff2 : SideEffectList
id, id' : nat
B :
  | append_funs_to_env l env id, modules, own_module, id + base.length l, e, eff1 | -e> | id', res,
  eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ (append_funs_to_env l env id) e ⟩ -->* erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ELetRec l e) ⟩ -->* erase_result σ res

*)



End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_BINDERS ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Section tmp.

(*

env : Environment
modules : list ErlModule
own_module : string
l : list Var
vals : ValueSequence
e1, e2 : Expression
res : ValueSequence + Exception
eff1, eff', eff'' : SideEffectList
id, id', id'' : nat
B1 : | env, modules, own_module, id, e1, eff1 | -e> | id', inl vals, eff' |
H : base.length l = base.length vals
B2 : | append_vars_to_env l vals env, modules, own_module, id', e2, eff' | -e> | id'', res, eff'' |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names σ env e1 ⟩ -->* erase_result σ (inl vals)
IHB2 :
  ∀ σ : NameSub, ⟨ [], erase_names σ (append_vars_to_env l vals env) e2 ⟩ -->* erase_result σ res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ELet l e1 e2) ⟩ -->* erase_result σ res




env : Environment
modules : list ErlModule
own_module : string
vl : list Var
e1, e2 : Expression
ex : Exception
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, e1, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names σ env e1 ⟩ -->* erase_result σ (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names σ env (ELet vl e1 e2) ⟩ -->* erase_result σ (inr ex)



*)



End tmp.

Section tmp.

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



End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_LISTS //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Section tmp.

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



End tmp.

Section tmp.

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



End tmp.

Section tmp.

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



End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_COMPOUNDS //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Section tmp.

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



End tmp.

Section tmp.

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



End tmp.

Section tmp.

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



End tmp.

Section tmp.

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






End tmp.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_MAIN ///////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Section tmp.



End tmp.


