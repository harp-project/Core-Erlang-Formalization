From CoreErlang.Eqvivalence.BsFs Require Import Helpers.

Import BigStep.

(** CONTENT:
* EQBSFS_ATOMS (THEOREMS)
  - Nil
    + eq_bsfs_enil_to_vnil
  - Lit
    + eq_bsfs_elit_to_vlit
* EQBSFS_REFERENCES (THEOREMS)
  - Var
    + eq_bsfs_evar_to_value
  - FunId
    + eq_bsfs_efunid_to_value
* EQBSFS_SEQUENCES (THEOREMS)
  - Cons
    + eq_bsfs_econs_to_vcons
    + eq_bsfs_econs_to_exception1
    + eq_bsfs_econs_to_exception2
  - Seq
    + eq_bsfs_eseq_to_result
    + eq_bsfs_eseq_to_exception
* EQBSFS_FUNCTIONS (THEOREMS)
  - Fun
    + eq_bsfs_efun_to_vclos
  - LetRec
    + eq_bsfs_eletrec_to_result
* EQBSFS_BINDERS (THEOREMS)
  - Let
    + eq_bsfs_elet_to_result
    + eq_bsfs_elet_to_exception
  - Try
    + eq_bsfs_etry_to_result1
    + eq_bsfs_etry_to_result2
* EQBSFS_LISTS (THEOREMS)
  - Values
  - Tuple
  - Map
* EQBSFS_ COMPOUNDS (THEOREMS)
  - PrimOp
  - Apply
  - Call
  - Case
* EQBSFS_MAIN (THEOREMS)
  - EqBsFs
    + eq_bsfs
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_ATOMS //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ENil.



  Theorem eq_bsfs_enil_to_vnil :
    forall Γ,
      ⟨ [], erase_names Γ ENil ⟩ -->* erase_valseq [VNil].
  Proof.
    itr.
    (* #1 Simplify Expressions: simpl *)
    smp.
    (* #2 Scope & Step: start;step *)
    start.
    step.
  Qed.



End ENil.









Section ELit.



  Theorem eq_bsfs_elit_to_vlit :
    forall Γ lit ,
      ⟨ [], erase_names Γ (ELit lit) ⟩ -->* erase_valseq [VLit lit].
  Proof.
    itr.
    (* #1 Simplify Expressions: simpl *)
    smp.
    (* #2 Scope & Step: start;step *)
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



  Theorem eq_bsfs_evar_to_value :
    forall Γ var v,
        get_value Γ (inl var) = Some [v]
    ->  VALCLOSED (erase_val' v)
    ->  ⟨ [], erase_names Γ (EVar var) ⟩ -->* erase_valseq [v].
  Proof.
    itr - Γ var v Hget Hscope.
    (* #1 Simplify Expressions: simpl *)
    smp.
    (* #2 Induction on Environment: induction + inversion;subst *)
    ind - Γ as [| [k1 v1] Γ IH]: ivs - Hget.
    (* #3 Apply Cons Theorem on Get Value: apply *)
    app - get_value_cons_eqb as Hget_cons in Hget.
    (* #4 Destruct Cons Hypothesis: destruct;subst *)
    des - Hget_cons as [[Hk Hv] | [Hget Heqb]]; sbt.
    * clr - IH.
      (* #5.1 Simplify by Lemmas: rewrite;simpl *)
      rwr - from_env_cons.
      rwr - var_funid_eqb_refl.
      smp.
      (* #6.1 Scope & Step: start;step *)
      start.
      step.
    * (* #5.2 Simplify by Lemmas: rewrite;simpl *)
      rwr - from_env_cons.
      cwr - Heqb.
      smp.
      (* #6.2 Solve by Inductive Hypothesis: specialize;exact *)
      spc - IH: Hget.
      exa - IH.
  Qed.



End EVar.









Section EFunId.



  Theorem eq_bsfs_efunid_to_value :
    forall Γ fid v,
        get_value Γ (inr fid) = Some [v]
    ->  VALCLOSED (erase_val' v)
    ->  ⟨ [], erase_names Γ (EFunId fid) ⟩ -->* erase_valseq [v].
  Proof.
    itr - Γ var v Hget Hscope.
    (* #1 Simplify Expressions: simpl *)
    smp.
    (* #2 Induction on Environment: induction + inversion;subst *)
    ind - Γ as [| [k1 v1] Γ IH]: ivs - Hget.
    (* #3 Apply Cons Theorem on Get Value: apply *)
    app - get_value_cons_eqb as Hget_cons in Hget.
    (* #4 Destruct Cons Hypothesis: destruct;subst *)
    des - Hget_cons as [[Hk Hv] | [Hget Heqb]]; sbt.
    * clr - IH.
      (* #5.1 Simplify by Lemmas: rewrite;simpl *)
      rwr - from_env_cons.
      rwr - var_funid_eqb_refl.
      smp.
      (* #6.1 Scope & Step: start;step *)
      start.
      step.
    * (* #5.2 Simplify by Lemmas: rewrite;simpl *)
      rwr - from_env_cons.
      cwr - Heqb.
      smp.
      (* #6.2 Solve by Inductive Hypothesis: specialize;exact *)
      spc - IH: Hget.
      exa - IH.
  Qed.



End EFunId.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_SEQUENCES //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ECons.



  Theorem eq_bsfs_econs_to_vcons :
    forall Γ e1 e2 v1 v2,
        ⟨ [], erase_names Γ e1 ⟩ -->* erase_valseq [v1]
    ->  ⟨ [], erase_names Γ e2 ⟩ -->* erase_valseq [v2]
    ->  ⟨ [], erase_names Γ (ECons e1 e2) ⟩ -->* erase_valseq [VCons v1 v2].
  Proof.
    itr - Γ e1' e2' v1' v2' IHv1 IHv2.
    (* #1 Simplify Expressions: simpl;unfold;mvr *)
    smp *.
    ufl - erase_names in *.
    do 2 mvr.
    (* #2 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ as Hσ: (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      ((erase_exp σ e1').[ξ])
      ((erase_exp σ e2').[ξ]);
      clr - He1 He2 e1' e2' σ ξ.
    (*Values*)
    rem - v1 v2 as Hv1 Hv2:
      (erase_val' v1')
      (erase_val' v2');
      clr - Hv1 Hv2 v1' v2'.
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHv1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHv2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #4 FrameStack Evaluation: start;step *)
    start / Hscope_v1 Hscope_v2.
    step - Hstep_v2 / e2 kv2.
    step - Hstep_v1 / e1 kv1.
    step.
  Qed.






  Theorem eq_bsfs_econs_to_exception1 :
    forall Γ e1 e2 x1 v2,
        ⟨ [], erase_names Γ e1 ⟩ -->* erase_exc x1
    ->  ⟨ [], erase_names Γ e2 ⟩ -->* erase_valseq [v2]
    ->  ⟨ [], erase_names Γ (ECons e1 e2) ⟩ -->* erase_exc x1.
  Proof.
    itr - Γ e1' e2' x1' v2' IHx1 IHv2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ as Hσ: (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    rem - e1 e2 as He1 He2:
      ((erase_exp σ e1').[ξ])
      ((erase_exp σ e2').[ξ]);
      clr - He1 He2 e1' e2' σ ξ.
    (*Values*)
    rem - x1 v2 as Hx1 Hv2:
      (erase_exc x1')
      (erase_val' v2');
      clr - Hx1 Hv2 x1' v2'.
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHx1 as [kx1 [Hscope_x1 Hstep_x1]].
    des - IHv2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #4 FrameStack Evaluation: start;step *)
    start / Hscope_x1 Hscope_v2.
    step - Hstep_v2 / e2 kv2.
    step - Hstep_x1 / e1 kx1.
    step.
  Qed.






  Theorem eq_bsfs_econs_to_exception2 :
    forall Γ e1 e2 x2,
        ⟨ [], erase_names Γ e2 ⟩ -->* erase_exc x2
    ->  ⟨ [], erase_names Γ (ECons e1 e2) ⟩ -->* erase_exc x2.
  Proof.
    itr - Γ e1' e2' x2' IHx2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ as Hσ: (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      ((erase_exp σ e1').[ξ])
      ((erase_exp σ e2').[ξ]);
      clr - He1 He2 e1' e2' σ ξ.
    (*Values*)
    rem - x2 as Hx2:
      (erase_exc x2');
      clr - Hx2 x2'.
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHx2 as [kx2 [Hscope_x2 Hstep_x2]].
    (* #4 FrameStack Evaluation: start;step *)
    start / Hscope_x2.
    step - Hstep_x2 / e2 kx2.
    step.
  Qed.



End ECons.









Section ESeq.



  Theorem eq_bsfs_eseq_to_result :
    forall Γ e1 e2 v1 r2,
        ⟨ [], erase_names Γ e1 ⟩ -->* erase_valseq [v1]
    ->  ⟨ [], erase_names Γ e2 ⟩ -->* erase_result r2
    ->  ⟨ [], erase_names Γ (ESeq e1 e2) ⟩ -->* erase_result r2.
  Proof.
    itr - Γ e1' e2' v1' r2' IHv1 IHr2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ as Hσ: (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      ((erase_exp σ e1').[ξ])
      ((erase_exp σ e2').[ξ]);
      clr - He1 He2 e1' e2' σ ξ.
    (*Values*)
    rem - v1 r2 as Hv1 Hr2:
      (erase_val' v1')
      (erase_result r2');
      clr - Hv1 Hr2 v1' r2'.
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHv1 as [kv1 [_ Hstep_v1]].
    des - IHr2 as [kr2 [Hscope_r2 Hstep_r2]].
    (* #4 FrameStack Evaluation: start;step *)
    start / Hscope_r2.
    step - Hstep_v1 / e1 kv1.
    step - Hstep_r2.
  Qed.






  Theorem eq_bsfs_eseq_to_exception :
    forall Γ e1 e2 x1,
        ⟨ [], erase_names Γ e1 ⟩ -->* erase_exc x1
    ->  ⟨ [], erase_names Γ (ESeq e1 e2) ⟩ -->* erase_exc x1.
  Proof.
    itr - Γ e1' e2' x1' IHx1.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ as Hσ: (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      ((erase_exp σ e1').[ξ])
      ((erase_exp σ e2').[ξ]);
      clr - He1 He2 e1' e2' σ ξ.
    (*Values*)
    rem - x1 as Hx1:
      (erase_exc x1');
      clr - Hx1 x1'.
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHx1 as [kx1 [Hscope_x1 Hstep_x1]].
    (* #4 FrameStack Evaluation: start;step *)
    start / Hscope_x1.
    step - Hstep_x1 / e1 kx1.
    step.
  Qed.



End ESeq.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_FUNCTIONS //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EFun.



  Theorem eq_bsfs_efun_to_vclos :
    forall Γ vars e id,
        is_result (erase_valseq [VClos Γ [] id vars e])
    ->  ⟨ [], erase_names Γ (EFun vars e) ⟩ -->*
              erase_valseq [VClos Γ [] id vars e].
  Proof.
    itr - Γ vars e id Hscope.
    (* #1 Simplify Expressions: simpl;mvr;rewrite;pose *)
    smp *.
    mvr.
    rwr - rem_ext_vars_empty_ext in *.
    pse - add_ext_vars_empty_ext as Hempty: vars (from_env (rem_vars vars Γ)).
    cwr - Hempty in *.
    rwr - erase_subst_rem_vars in *.
    (* #2 FrameStack Evaluation: start;step *)
    start / Hscope.
    step.
  Qed.



End EFun.









Section ELetRec.



  Theorem eq_bsfs_eletrec_to_result :
    forall Γ ext e id r,
        ⟨ [], erase_names (append_funs_to_env ext Γ id) e ⟩ -->* erase_result r
    ->  ⟨ [], erase_names Γ (ELetRec ext e) ⟩ -->* erase_result r.
  Proof.
    itr - Γ ext e id r IHr.
    (* #1 Simplify: simpl*)
    smp *.
    (* #2 Destruct Inductive Hypothesis: destruct *)
    des - IHr as [kr [Hscope_r Hstep_r]].
    (* #3 Scope & Step: start;step *)
    start / Hscope_r.
    step.
  Admitted.

(*
Hstep_res :
  ⟨ [], erase_names (append_funs_to_env ext Γ id) e ⟩ -[ kres ]-> ⟨ [], erase_result res ⟩
______________________________________(1/1)
⟨ [],
(erase_exp (add_expext ext (from_env Γ)) e).[upn
                                               (base.length
                                                  (map
                                                     (λ '(_, (vars, body)),
                                                        (base.length vars,
                                                         erase_exp
                                                           (add_expext_vars ext vars
                                                              (from_env Γ)) body)) ext))
                                               (list_subst (map erase_val' (map snd Γ))
                                                  idsubst)].[list_subst
                                                               (convert_to_closlist
                                                                (map 
                                                                (λ '(x, y), (0, x, y))
                                                                (map
                                                                (λ '(n, x),
                                                                (n,
                                                                x.[
                                                                upn
                                                                (base.length
                                                                (map
                                                                (λ '(_, (vars, body)),
                                                                (base.length vars,
                                                                erase_exp
                                                                (add_expext_vars ext vars
                                                                (from_env Γ)) body)) ext) + n)
                                                                (list_subst
                                                                (map erase_val' (map snd Γ))
                                                                idsubst)]))
                                                                (map
                                                                (λ '(_, (vars, body)),
                                                                (base.length vars,
                                                                erase_exp
                                                                (add_expext_vars ext vars
                                                                (from_env Γ)) body)) ext))))
                                                               idsubst] ⟩ -[ 
?k ]-> ⟨ [], erase_result res ⟩
*)



End ELetRec.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_BINDERS ////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ELet.



  Theorem eq_bsfs_elet_to_result :
    forall Γ vars1 e1 e2 vs1 r2,
        length vars1 = length vs1
    ->  ⟨ [], erase_names Γ e1 ⟩ -->* erase_valseq vs1
    ->  ⟨ [], erase_names (append_vars_to_env vars1 vs1 Γ) e2 ⟩ -->*
              erase_result r2
    ->  ⟨ [], erase_names Γ (ELet vars1 e1 e2) ⟩ -->* erase_result r2.
  Proof.
    itr - Γ vars1 e1' e2' vs1' r2' Hlength IHvs1 IHr2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Append Theorem: rewrite;exact *)
    rwr - erase_subst_append_vars in IHr2.
    2: exa - Hlength.
    (* #3 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ1 as Hσ1:
      (from_env Γ);
      clr - Hσ1.
    rem - σ2 as Hσ2:
      (add_vars vars1 σ1);
      clr - Hσ2.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      (erase_exp σ1 e1')
      (erase_exp σ2 e2');
      clr - He1 He2 e1' e2' σ1 σ2.
    (*Values*)
    ufl - erase_valseq in *.
    rem - vs1 r2 as Hvs1 Hr2:
      (map erase_val' vs1')
      (erase_result r2');
      clr - Hr2 r2'.
    (* #4 Transform Length Hypothesis: pose;rename;symmetry *)
    pose proof length_map_eq _ _ _ vars1 vs1' vs1 _ Hvs1 Hlength.
    clr - Hlength Hvs1 vs1'.
    ren - Hlength: H.
    sym - Hlength.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHvs1 as [kvs1 [_ Hstep_vs1]].
    des - IHr2 as [kr2 [Hscope_r2 Hstep_r2]].
    (* #6 FrameStack Evaluation: start;step *)
    start / Hscope_r2.
    step - Hstep_vs1 / e1 kvs1.
    step / Hlength.
    step - Hstep_r2.
  Qed.






  Theorem eq_bsfs_elet_exc :
    forall Γ vars1 e1 e2 x1,
        ⟨ [], erase_names Γ e1 ⟩ -->* erase_exc x1
    ->  ⟨ [], erase_names Γ (ELet vars1 e1 e2) ⟩ -->* erase_exc x1.
  Proof.
    itr - Γ vars1 e1' e2' x1' IHx1.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ1 as Hσ1:
      (from_env Γ);
      clr - Hσ1.
    rem - σ2 as Hσ2:
      (add_vars vars1 σ1);
      clr - Hσ2.
    (*Substs*)
    rem - ξ1 as Hξ1:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ1 Γ.
    rem - ξ2 as Hξ2:
      (upn (base.length vars1) ξ1);
      clr - Hξ2.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      ((erase_exp σ1 e1').[ξ1])
      ((erase_exp σ2 e2').[ξ2]);
      clr - He1 He2 e1' e2' σ1 σ2 ξ1 ξ2.
    (*Values*)
    rem - x1 as Hx1:
      (erase_exc x1');
      clr - Hx1 x1'.
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHx1 as [kx1 [Hscope_x1 Hstep_x1]].
    (* #4 FrameStack Evaluation: start;step *)
    start / Hscope_x1.
    step - Hstep_x1 / e1 kx1.
    step.
  Qed.



End ELet.









Section ETry.



  Theorem eq_bsfs_etry_to_result1 :
    forall Γ vars1 vars2 e1 e2 e3 vs1 r2,
        length vars1 = length vs1
    ->  ⟨ [], erase_names Γ e1 ⟩ -->* erase_valseq vs1
    ->  ⟨ [], erase_names (append_vars_to_env vars1 vs1 Γ) e2 ⟩ -->*
              erase_result r2
    ->  ⟨ [], erase_names Γ (ETry e1 vars1 e2 vars2 e3) ⟩ -->* erase_result r2.
  Proof.
    itr - Γ vars1 vars2 e1' e2' e3' vs1' r2' Hlength IHvs1 IHr2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Apply Theorem: rewrite;exact *)
    rwr - erase_subst_append_vars in IHr2.
    2: exa - Hlength.
    (* #3 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ1 as Hσ1:
      (from_env Γ);
      clr - Hσ1.
    rem - σ2 σ3 as Hσ2 Hσ3:
      (add_vars vars1 σ1)
      (add_vars vars2 σ1);
      clr - Hσ2 Hσ3.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 e3 as He1 He2 He3:
      (erase_exp σ1 e1')
      (erase_exp σ2 e2')
      (erase_exp σ3 e3');
      clr - He1 He2 He3 e1' e2' e3' σ1 σ2 σ3.
    (*Values*)
    ufl - erase_valseq in *.
    rem - vs1 r2 as Hvs1 Hr2:
      (map erase_val' vs1')
      (erase_result r2');
      clr - Hr2 r2'.
    (* #4 Transform Length Hypothesis: pose;rename;symmetry *)
    pose proof length_map_eq _ _ _ vars1 vs1' vs1 _ Hvs1 Hlength.
    clr - Hlength Hvs1 vs1'.
    ren - Hlength: H.
    sym - Hlength.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHvs1 as [kvs1 [_ Hstep_vs1]].
    des - IHr2 as [kr2 [Hscope_r2 Hstep_r2]].
    (* #6 FrameStack Evaluation: start;step *)
    start / Hscope_r2.
    step - Hstep_vs1 / e1 kvs1.
    step / Hlength.
    step - Hstep_r2.
  Qed.






  Theorem eq_bsfs_etry_to_result2 :
    forall Γ vars1 vars2 e1 e2 e3 x1 r3,
        length vars2 = 3
    ->  ⟨ [], erase_names Γ e1 ⟩ -->* erase_exc x1
    ->  ⟨ [], erase_names (append_vars_to_env vars2 (exc_to_vals x1) Γ) e3 ⟩
         -->* erase_result r3
    ->  ⟨ [], erase_names Γ (ETry e1 vars1 e2 vars2 e3) ⟩ -->* erase_result r3.
  Proof.
    itr - Γ vars1 vars2 e1' e2' e3' x1' r3' Hlength IHx1 IHr3.
    des - x1' as [[c1' vr1'] vd1'].
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Apply Theorem: rewrite/exact *)
    rwr - erase_subst_append_vars in IHr3.
    2: exa - Hlength.
    cwr - Hlength in *.
    (* #3 Shorten Expressions: remember;simpl *)
    (*Erasers*)
    rem - σ1 as Hσ1:
      (from_env Γ);
      clr - Hσ1.
    rem - σ2 σ3 as Hσ2 Hσ3:
      (add_vars vars1 σ1)
      (add_vars vars2 σ1);
      clr - Hσ2 Hσ3.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 e3 as He1 He2 He3:
      (erase_exp σ1 e1')
      (erase_exp σ2 e2')
      (erase_exp σ3 e3');
      clr - He1 He2 He3 e1' e2' e3' σ1 σ2 σ3.
    (*Values*)
    simpl map in IHr3.
    rem - vc1 vr1 vd1 r3 as Hvc1 Hvr1 Hvd1 Hr3:
      (erase_val' (exclass_to_value c1'))
      (erase_val' vr1')
      (erase_val' vd1')
      (erase_result r3');
      clr - Hvr1 Hvd1 Hr3 vr1' vd1' r3'.
    (*ExceptionClass*)
    rem - c1 as Hc1:
      (convert_class c1').
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHx1 as [kx1 [_ Hstep_x1]].
    des - IHr3 as [kr3 [Hscope_r3 Hstep_r3]].
    (* #5 FrameStack Evaluation: start;step;destruct;simpl;subst *)
    start / Hscope_r3.
    step - Hstep_x1 / e1 kx1.
    step.
    des - c1'; smp *; sbt.
    * step - Hstep_r3.
    * step - Hstep_r3.
    * step - Hstep_r3.
  Qed.



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
        ⟨ [], erase_names env (nth i exps ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : id' = last ids id
H5 : eff' = last eff eff1
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EValues exps) ⟩ -->*erase_result (inl vals)


*)



(*   Theorem eq_bsfs_evalues_to_valseq :
    forall Γ el vs e1 e2 vs1 r2,
        length vars1 = length vs1
    ->  ⟨ [], erase_names Γ e1 ⟩ -->* erase_result (inl vs1)
    ->  ⟨ [], erase_names (append_vars_to_env vars1 vs1 Γ) e2 ⟩ -->*
              erase_result r2
    ->  ⟨ [], erase_names Γ (ELet vars1 e1 e2) ⟩ -->* erase_result r2.
  Proof.
    itr - Γ vars1 e1' e2' vs1' r2' Hlength IHvs1 IHr2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Append Theorem: rewrite;exact *)
    rwr - erase_subst_append_vars in IHr2.
    2: exa - Hlength.
    (* #3 Shorten Expressions: remember *)
    (*Erasers*)
    rem - σ1 as Hσ1:
      (from_env Γ);
      clr - Hσ1.
    rem - σ2 as Hσ2:
      (add_vars vars1 σ1);
      clr - Hσ2.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    (*Expressions*)
    rem - e1 e2 as He1 He2:
      (erase_exp σ1 e1')
      (erase_exp σ2 e2');
      clr - He1 He2 e1' e2' σ1 σ2.
    (*Values*)
    ufl - erase_valseq in *.
    rem - vs1 r2 as Hvs1 Hr2:
      (map erase_val' vs1')
      (erase_result r2');
      clr - Hr2 r2'.
    (* #4 Transform Length Hypothesis: pose;rename;symmetry *)
    pose proof length_map_eq _ _ _ vars1 vs1' vs1 _ Hvs1 Hlength.
    clr - Hlength Hvs1 vs1'.
    ren - Hlength: H.
    sym - Hlength.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHvs1 as [kvs1 [_ Hstep_vs1]].
    des - IHr2 as [kr2 [Hscope_r2 Hstep_r2]].
    (* #6 FrameStack Evaluation: start;step *)
    start / Hscope_r2.
    step - Hstep_vs1 / e1 kvs1.
    step / Hlength.
    step - Hstep_r2.
  Qed. *)


(*


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
        ⟨ [], erase_names env (nth j exps ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff' |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env (nth i exps ErrorExp) ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EValues exps) ⟩ -->*erase_result (inr ex)



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
        ⟨ [], erase_names env (nth i exps ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : eff2 = last eff eff1
H5 : id' = last ids id
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ETuple exps) ⟩ -->*erase_result (inl [VTuple vals])






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
        ⟨ [], erase_names env (nth j exps ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env (nth i exps ErrorExp) ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ETuple exps) ⟩ -->*erase_result (inr ex)


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
        ⟨ [], erase_names env (nth i exps ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H5 : make_value_map kvals vvals = (kvals', vvals')
H6 : combine kvals' vvals' = lv
H7 : eff2 = last eff eff1
H8 : id' = last ids id
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EMap l) ⟩ -->*erase_result (inl [VMap lv])





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
        ⟨ [], erase_names env (nth j exps ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i exps ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env (nth i exps ErrorExp) ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EMap l) ⟩ -->*erase_result (inr ex)



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
        ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : primop_eval fname vals (last eff eff1) = (res, eff2)
H5 : id' = last ids id
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EPrimOp fname params) ⟩ -->*erase_result res





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
        ⟨ [], erase_names env (nth j params ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
B :
  | env, modules, own_module, last ids id, nth i params ErrorExp, last eff eff1 | -e> | id', 
  inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EPrimOp fname params) ⟩ -->*erase_result (inr ex)

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
        ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
B2 :
  | append_vars_to_env var_list vals (get_env ref ext), modules, own_module, 
  last ids id', body, last eff eff2 | -e> | id'', res, eff3 |
IHB1 :
  ∀ σ : NameSub,
    ⟨ [], erase_names env exp ⟩ -->*erase_result (inl [VClos ref ext n var_list body])
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names (append_vars_to_env var_list vals (get_env ref ext)) body ⟩ -->*
   erase_result res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EApp exp params) ⟩ -->*erase_result res



params : list Expression
env : Environment
modules : list ErlModule
own_module : string
exp : Expression
ex : Exception
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, exp, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env exp ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EApp exp params) ⟩ -->*erase_result (inr ex)



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
        ⟨ [], erase_names env (nth j params ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
B2 :
  | env, modules, own_module, last ids id', nth i params ErrorExp, last eff eff2 | -e> | id'',
  inr ex, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env exp ⟩ -->*erase_result (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EApp exp params) ⟩ -->*erase_result (inr ex)




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
        ⟨ [], erase_names env (nth j params ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
H4 :
  ∀ (ref : list ((Var + FunctionIdentifier) * Value)) (ext : list
                                                               (nat * FunctionIdentifier *
                                                                FunctionExpression)) 
    (var_list : list Var) (body : Expression) (n : nat), v ≠ VClos ref ext n var_list body
H5 : eff3 = last eff eff2
H6 : id'' = last ids id'
IHB : ∀ σ : NameSub, ⟨ [], erase_names env exp ⟩ -->*erase_result (inl [v])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EApp exp params) ⟩ -->*erase_result (inr (badfun v))





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
        ⟨ [], erase_names env (nth j params ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
H4 : base.length var_list ≠ base.length vals
H5 : eff3 = last eff eff2
H6 : id'' = last ids id'
IHB :
  ∀ σ : NameSub,
    ⟨ [], erase_names env exp ⟩ -->*erase_result (inl [VClos ref ext n var_list body])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (EApp exp params) ⟩ -->*
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
        ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : get_modfunc mname fname (base.length vals) (modules ++ stdlib) = None
H5 : eval mname fname vals (last eff eff3) = (res, eff4)
H6 : id''' = last ids id''
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inl [VLit (Atom mname)])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env fexp ⟩ -->*erase_result (inl [VLit (Atom fname)])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result res





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
        ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : get_modfunc mname fname (base.length vals) (modules ++ stdlib) = Some func
B3 :
  | append_vars_to_env (varl func) vals [], modules, mname, last ids id'', 
  body func, last eff eff3 | -e> | id''', res, eff4 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inl [VLit (Atom mname)])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env fexp ⟩ -->*erase_result (inl [VLit (Atom fname)])
IHB3 :
  ∀ σ : NameSub,
    ⟨ [], erase_names (append_vars_to_env (varl func) vals []) (body func) ⟩ -->*
   erase_result res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result res







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
        ⟨ [], erase_names env (nth j params ErrorExp) ⟩ -->*
       erase_result (inl [nth j vals ErrorValue])
B3 :
  | env, modules, own_module, last ids id'', nth i params ErrorExp, last eff eff3 | -e> | id''',
  inr ex, eff4 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env fexp ⟩ -->*erase_result (inl [v'])
IHB3 : ∀ σ : NameSub, ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result (inr ex)







env : Environment
modules : list ErlModule
own_module : string
mexp, fexp : Expression
params : list Expression
ex : Exception
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, mexp, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result (inr ex)






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
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env fexp ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result (inr ex)





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
        ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : ∀ mname : string, v ≠ VLit (Atom mname)
H5 : eff4 = last eff eff3
H6 : id''' = last ids id''
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inl [v])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env fexp ⟩ -->*erase_result (inl [v'])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result (inr (badarg v))







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
        ⟨ [], erase_names env (nth i params ErrorExp) ⟩ -->*
       erase_result (inl [nth i vals ErrorValue])
H4 : ∀ fname : string, v' ≠ VLit (Atom fname)
H5 : eff4 = last eff eff3
H6 : id''' = last ids id''
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env mexp ⟩ -->*erase_result (inl [VLit (Atom mname)])
IHB2 : ∀ σ : NameSub, ⟨ [], erase_names env fexp ⟩ -->*erase_result (inl [v'])
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECall mexp fexp params) ⟩ -->*erase_result (inr (badarg v'))


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
            ⟨ [], erase_names (add_bindings bb env) gg ⟩ -->*erase_result (inl [ffalse])
B2 :
  | add_bindings bindings env, modules, own_module, id', guard, eff2 | -e> | id', 
  inl [ttrue], eff2 |
B3 : | add_bindings bindings env, modules, own_module, id', exp, eff2 | -e> | id'', res, eff3 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env e ⟩ -->*erase_result (inl vals)
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names (add_bindings bindings env) guard ⟩ -->*erase_result (inl [ttrue])
IHB3 : ∀ σ : NameSub, ⟨ [], erase_names (add_bindings bindings env) exp ⟩ -->*erase_result res
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECase e l) ⟩ -->*erase_result res




env : Environment
modules : list ErlModule
own_module : string
e : Expression
ex : Exception
l : list (list Pattern * Expression * Expression)
eff1, eff2 : SideEffectList
id, id' : nat
B : | env, modules, own_module, id, e, eff1 | -e> | id', inr ex, eff2 |
IHB : ∀ σ : NameSub, ⟨ [], erase_names env e ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECase e l) ⟩ -->*erase_result (inr ex)




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
            ⟨ [], erase_names (add_bindings bb env) gg ⟩ -->*erase_result (inl [ffalse])
IHB : ∀ σ : NameSub, ⟨ [], erase_names env e ⟩ -->*erase_result (inl vals)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECase e l) ⟩ -->*erase_result (inr if_clause)



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
            ⟨ [], erase_names (add_bindings bb env) gg ⟩ -->*erase_result (inl [ffalse])
B2 : | add_bindings bindings env, modules, own_module, id', guard, eff2 | -e> | id', inr ex, eff2 |
IHB1 : ∀ σ : NameSub, ⟨ [], erase_names env e ⟩ -->*erase_result (inl vals)
IHB2 :
  ∀ σ : NameSub,
    ⟨ [], erase_names (add_bindings bindings env) guard ⟩ -->*erase_result (inr ex)
σ : NameSub
______________________________________(1/1)
⟨ [], erase_names env (ECase e l) ⟩ -->*erase_result (inr ex)



*)



End ECase.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_MAIN ///////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Section EqBsFs.



  Theorem eq_bsfs :
    forall Γ modules own_module id id' e e' eff eff',
        (eval_expr Γ modules own_module id e eff id' e' eff')
    ->  ⟨ [], (erase_names Γ e) ⟩ -->*erase_result e'.
  Proof.
    itr - Γ modules own_module id id' e e' eff eff' B.
    ind - B; itr; ren - Γ: env.
    (* #1 Atoms: ENil/ENil *)
      (* +1.1 ENil: *)
          3: {
            rwr - erase_result_to_valseq.
            bse - eq_bsfs_enil_to_vnil:
                  Γ.
          }
      (* +1.2 ELit: *)
          3: {
            ren - lit: l.
            rwr - erase_result_to_valseq.
            bse - eq_bsfs_elit_to_vlit:
                  Γ lit.
          }
    (* #2 References: EVar/EFunId *)
      (* +2.1 EVar: *)
          3: {
            ren - var r Hget: s res H.
            pse - evar_is_result as Hv:
                  Γ modules own_module var r id eff Hget.
            des - Hv as [v [Heq Hscope]]; sbt.
            rwr - erase_result_to_valseq.
            bse - eq_bsfs_evar_to_value:
                  Γ var v Hget Hscope.
          }
      (* +2.2 EFunId: success/modfunc *)
        (* -2.2.1 success: *)
          3: {
            ren - r Hget: res H.
            pse - efunid_is_result as Hv:
                  Γ modules own_module fid r id eff Hget.
            des - Hv as [v [Heq Hscope]]; sbt.
            rwr - erase_result_to_valseq.
            bse - eq_bsfs_efunid_to_value:
                  Γ fid v Hget Hscope.
          }
        (* -2.2.2 modfunc: *)
          3: {
            pse - no_modfunc; con.
          }
    (* #3 Sequences: ECons/ESeq *)
      (* +3.1 ECons: success/exception1/exception2 *)
        (* -3.1.1 success: *)
          5: {
            ren - e1 e2 v1 v2 IHFv1 IHFv2 IHBv1 IHBv2:
                  hd tl hdv tlv IHB2 IHB1 B2 B1.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_econs_to_vcons:
                  Γ e1 e2 v1 v2 IHFv1 IHFv2.
          }
        (* -3.1.2 exception1: *)
          15: {
            ren - e1 e2 x1 v2 IHFx1 IHFv2 IHBx1 IHBv2:
                  hd tl ex vtl IHB2 IHB1 B2 B1.
            rwr - erase_result_to_valseq in *.
            rwr - erase_result_to_exception in *.
            bse - eq_bsfs_econs_to_exception1:
                  Γ e1 e2 x1 v2 IHFx1 IHFv2.
          }
        (* -3.1.3 exception2: *)
          14: {
            ren - e1 e2 x2 IHFx2 IHBx2:
                  hd tl ex IHB B.
            rwr - erase_result_to_exception in *.
            bse - eq_bsfs_econs_to_exception2:
                  Γ e1 e2 x2 IHFx2.
          }
      (* +3.2 ESeq: success/exception *)
        (* -3.2.1 success: *)
          11: {
            ren - r2 IHFv1 IHFr2 IHBv1 IHBr2:
                  v2 IHB1 IHB2 B1 B2.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_eseq_to_result:
                  Γ e1 e2 v1 r2 IHFv1 IHFr2.
          }
        (* -3.2.2 exception: *)
          30: {
            ren - x1 IHFx1 IHBx1 :
                  ex IHB B.
            rwr - erase_result_to_exception in *.
            bse - eq_bsfs_eseq_to_exception:
                  Γ e1 e2 x1 IHFx1.
          }
    (* #4 Functions: EFun/ELetrec *)
      (* +4.1 EFun: *)
          3: {
            ren - vars:
                  vl.
            pse - efun_is_result as Hscope:
                   Γ modules own_module vars e id eff.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_efun_to_vclos:
                  Γ vars e id Hscope.
          }
      (* +4.2 ELetrec: *)
         10:  admit.
    (* #5 Binders: ELet/ETry *)
      (* +5.1 ELet: success/exception *)
        (* -5.1.1 success: *)
          9: {
            ren - vars1 vs1 r2 Hlen1 IHFvs1 IHFr2 IHBvs1 IHBr2:
                  l vals res H IHB1 IHB2 B1 B2.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_elet_to_result:
                  Γ vars1 e1 e2 vs1 r2 Hlen1 IHFvs1 IHFr2.
          }
        (* -5.1.2 exception: *)
          26: {
            ren - vars1 x1 IHFx1 IHBx1:
                  vl ex IHB B.
            rwr - erase_result_to_exception in *.
            bse - eq_bsfs_elet_exc: Γ vars1 e1 e2 x1 IHFx1.
          }
      (* +5.2 ETry: result1/result2 *)
        (* -5.2.1 result1: *)
          11: {
            ren - vars1 vars2 vs1 r2 Hlen1 IHFvs1 IHFr2 IHBvs1 IHBr2:
                  vl1 vl2 vals res H IHB1 IHB2 B1 B2.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_etry_to_result1:
                  Γ vars1 vars2 e1 e2 e3 vs1 r2 Hlen1 IHFvs1 IHFr2.
          }
        (* -5.2.2 result: *)
          11: {
            ren - vars1 vars2 x1 r3 IHFx1 IHFr3 IHBx1 IHBr3:
                  vl1 vl2 ex res IHB1 IHB2 B1 B2.
            ren - eff eff' eff'':
                  eff1 eff2 eff3.
            rwr - exc_to_vals_eq in *.
            pse - catch_vars_length as Hlen2: 
                  Γ modules own_module vars1 vars2 e1 e2 e3 x1 r3
                  id id' id'' eff eff' eff'' IHBx1 IHBr3.
            rwr - erase_result_to_exception in *.
            bse - eq_bsfs_etry_to_result2:
                  Γ vars1 vars2 e1 e2 e3 x1 r3 Hlen2 IHFx1 IHFr3.
          }
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



End EqBsFs.