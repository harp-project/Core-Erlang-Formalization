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






(**
  Greek Letters:
  α β γ δ ε ζ η θ ι κ λ μ ν ξ ο π ρ σ τ υ φ χ ψ ω
  Α Β Γ Δ Ε Ζ Η Θ Ι Κ Λ Μ Ν Ξ Ο Π Ρ Σ Τ Υ Φ Χ Ψ Ω

  Mathematical Symbols:
  ∀ ∃ ∈ ∉ ∋ ∌ ∅ ∆ ∇ ∈ ∉ ∋ ∌ ∏ ∑ − ∓ ∗ ∘ ∙ √ ∝ ∞
  ∧ ∨ ∩ ∪ ∫ ∴ ∵ ∷ ≠ ≡ ≤ ≥ ⊂ ⊃ ⊆ ⊇ ⊕ ⊗ ⊥ ⋂ ⋃ ⌈ ⌉ ⌊ ⌋ ⟨ ⟩

  Superscripts:
  ⁰ ¹ ² ³ ⁴ ⁵ ⁶ ⁷ ⁸ ⁹ ⁺ ⁻ ⁼ ⁽ ⁾
  ᵃ ᵇ ᶜ ᵈ ᵉ ᶠ ᵍ ʰ ⁱ ʲ ᵏ ˡ ᵐ ⁿ ᵒ ᵖ ʳ ˢ ᵗ ᵘ ᵛ ʷ ˣ ʸ ᶻ
  ᴬ ᴮ ᴰ ᴱ ᴳ ᴴ ᴵ ᴶ ᴷ ᴸ ᴹ ᴺ ᴼ ᴾ ᴿ ᵀ ᵁ ᵂ

  Subscripts:
  ₀ ₁ ₂ ₃ ₄ ₅ ₆ ₇ ₈ ₉ ₊ ₋ ₌ ₍ ₎
  ₐ ₑ ᵦ ᵧ ᵨ ₓ ₔ ₕ ᵢ ⱼ ₖ ₗ ₘ ₙ ₒ ₚ ᵩ ᵪ

  Arrows:
  ← ↑ → ↓ ↔ ↕ ⇐ ⇑ ⇒ ⇓ ⇔ ⇕

  Miscellaneous Symbols:
  © ® ™ ¶ § † ‡ • ‣ ′ ″ ‴ ‵ ‶ ‷ 
  ‖ ‗ ‾ ‿ ⁀ ⁂ ⁃ ⁄ ⁅ ⁆ 
  ⁇ ⁈ ⁉ ⁎ ⁏ ⁐ ⁑ ⁒ ⁓ ⁔ ⁕ 
  ⁖ ⁗ ⁘ ⁙ ⁚ ⁛ ⁜ ⁝ ⁞
**)











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
    forall Γ litᴮ ,
      ⟨ [], erase_names Γ (ELit litᴮ) ⟩ -->* erase_valseq [VLit litᴮ].
  Proof.
    itr.
    (* #1 Simplify Expressions: simpl *)
    smp.
    (* #2 Syntax from BigStep to FrameStack: remember *)
    rem - litᶠ as Hlit:
      (convert_lit litᴮ);
      clr - Hlit litᴮ Γ.
    (* #3 FrameStack Evaluation: start/step *)
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
    itr - Γ vars1 e1' e2' vs1' r2' Hlen1 IHvs1 IHr2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Append Theorem: remember;unfold;symmetry;rewrite;exact *)
    rwr - erase_subst_append_vars in IHr2.
    2: exa - Hlen1.
    sym - Hlen1.
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
    erewrite length_map_erase_val_eq in Hlen1.
    2: exa - Hvs1.
    clr - Hvs1.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHvs1 as [kvs1 [_ Hstep_vs1]].
    des - IHr2 as [kr2 [Hscope_r2 Hstep_r2]].
    (* #6 FrameStack Evaluation: start;step *)
    start / Hscope_r2.
    step - Hstep_vs1 / e1 kvs1.
    step / Hlen1.
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
    itr - Γ vars1 vars2 e1' e2' e3' vs1' r2' Hlen1 IHvs1 IHr2.
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Apply Theorem: rewrite;exact *)
    rwr - erase_subst_append_vars in IHr2.
    2: exa - Hlen1.
    sym - Hlen1.
    (* #3 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
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
    erewrite length_map_erase_val_eq in Hlen1.
    2: exa - Hvs1.
    clr - Hvs1.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHvs1 as [kvs1 [_ Hstep_vs1]].
    des - IHr2 as [kr2 [Hscope_r2 Hstep_r2]].
    (* #6 FrameStack Evaluation: start;step *)
    start / Hscope_r2.
    step - Hstep_vs1 / e1 kvs1.
    step / Hlen1.
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
    itr - Γ vars1 vars2 e1' e2' e3' x1' r3' Hlen2 IHx1 IHr3.
    des - x1' as [[c1' vr1'] vd1'].
    (* #1 Simplify Expressions: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Apply Theorem: rewrite/exact *)
    rwr - erase_subst_append_vars in IHr3.
    2: exa - Hlen2.
    cwr - Hlen2 in *.
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



  Theorem eq_bsfs_evalues_to_valseq :
    forall Γ el vl,
        length el = length vl
    ->  (forall i,
            i < length el
        ->  ⟨ [], erase_names Γ (nth i el ErrorExp) ⟩ -->* 
                  erase_valseq [nth i vl ErrorValue])
    ->  ⟨ [], erase_names Γ (EValues el) ⟩ -->* erase_valseq vl.
  Proof.
    itr - Γ el' vl' Hlen IHnth'.
    (* #0 Pre: rewrite/symmetry *)
    rwr - Hlen in IHnth'.
    sym - Hlen.
    (* #1 Simplify Expressions: simpl/unfold/rewrite *)
    smp *.
    ufl - erase_names in *.
    ufl - erase_valseq.
    rwr - map_map.
    (* #2 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
    (*Erasers*)
    rem - σ as Hσ:
      (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth: σ ξ el' vl' IHnth'.
    (*Expressions*)
    rem - el ex as Hel Hex:
      (map (fun e => (erase_exp σ e).[ξ]) el')
      (erase_exp σ ErrorExp);
      clr - Hex.
    erewrite length_map_erase_exp_eq in Hlen.
    2: exa - Hel.
    clr - Hel el' σ ξ.
    (*Value*)
    rem - vl vx as Hvl Hvx:
      (map erase_val' vl')
      (erase_val' ErrorValue);
      clr - Hvx.
    erewrite length_map_erase_val_eq in *.
    2-3: exa - Hvl.
    clr - Hvl vl'.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscope: el ex vl vx Hlen IHnth.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - el as [| e el].
    { (* - Empty List Branch *)
      clr - IHnth.
      (* #4.1 Both List Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #4.2 FrameStack Evaluation: start/step *)
      start.
      step.
    } (* - Cons List Branch *)
    (* #5 Both List Cons: destruct + inversion/subst *)
    des - vl as [| v vl]: ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    psc - fs_eval_nth_cons as Hnth_cons: e el ex v vl vx IHnth.
    des - Hnth_cons as [IHv Hnth].
    (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
    smp - Hlen.
    rwr - Nat.succ_inj_wd in Hlen.
    pose proof create_result_ivalues
      v vl [] as Hcrt.
    pose proof fs_eval_nth_to_result
      IValues el ex [] v vl vx (RValSeq (v :: vl)) [] [] Hlen Hcrt Hnth
      as IHvl.
    clr - Hlen Hcrt Hnth.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHv as [kv [_ Hstep_v]].
    des - IHvl as [kvl Hstep_vl].
    (* #9 FrameStack Evaluation: start/step *)
    start / Hscope.
    step - Hstep_v.
    step - Hstep_vl.
  Qed.






  Theorem eq_bsfs_evalues_to_exception :
    forall Γ el vl xk,
        length vl < length el
    ->  (forall i,
            i < length vl
        ->  ⟨ [], erase_names Γ (nth i el ErrorExp) ⟩ -->* 
                  erase_valseq [nth i vl ErrorValue])
    ->  ⟨ [], erase_names Γ (nth (length vl) el ErrorExp) ⟩ -->* erase_exc xk
    ->  ⟨ [], erase_names Γ (EValues el) ⟩ -->* erase_exc xk.
  Proof.
    itr - Γ el' vl' xk' Hlen IHnth' IHxk.
    (* #1 Simplify Expressions: simpl/unfold/rewrite *)
    smp *.
    ufl - erase_names in *.
    rwr - map_map.
    (* #2 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
    (*Erasers*)
    rem - σ as Hσ:
      (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      clr - Hξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth: σ ξ el' vl' IHnth'.
    rwr - fs_eval_nth_map_erase_single in IHxk.
    (*Expressions*)
    rem - el ex as Hel Hex:
      (map (fun e => (erase_exp σ e).[ξ]) el')
      (erase_exp σ ErrorExp);
      clr - Hex.
    erewrite length_map_erase_exp_eq in Hlen.
    2: exa - Hel.
    clr - Hel el' σ ξ.
    (*Value*)
    rem - vl vx xk as Hvl Hvx Hxk:
      (map erase_val' vl')
      (erase_val' ErrorValue)
      (erase_exc xk');
      clr - Hvx Hxk.
    erewrite length_map_erase_val_eq in *.
    2-4: exa - Hvl.
    clr - Hvl vl'.
    (* #3 Split Expression List: pose/destruct *)
    psc - length_lt_split_middle as Hsplit: Val Exp vl el Hlen.
    des - Hsplit as [el1 [ek [el2 [Hel Hlen]]]].
    sbt.
    (* #4 Simplify Exception Hypothesis: *)
    rwr - Hlen in IHxk.
    smp - IHxk.
    rwr - nth_middle in IHxk.
    (* #5 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - el1 as [| e el1].
    { (* - Empty List Branch *)
      clr - IHnth.
      (* #5.1 Both List Empty: simpl/rewrite/subst/simpl *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      smp.
      (* #5.2 Destruct Inductive Hypothesis: destruct *)
      des - IHxk as [kv [Hscope_xk Hstep_xk]].
      (* #5.3 FrameStack Evaluation: start/step *)
      start / Hscope_xk.
      step - Hstep_xk.
      step.
    } (* - Cons List Branch *)
    (* #6 Both List Cons: destruct + inversion/subst *)
    des - vl as [| v vl]: ivs - Hlen.
    (* #7 Pose Nth Cons Theorem: rewrite/pose/destruct *)
    rewrite cons_app with (l := el1) in IHnth.
    rwl - app_assoc in IHnth.
    do 2 rwl - cons_app in IHnth.
    psc - fs_eval_nth_cons as Hnth_cons:
      e (el1 ++ ek :: el2) ex v vl vx IHnth.
    des - Hnth_cons as [IHv Hnth].
    (* #8 Pose From Nth to Result: simpl/rewrite/pose *)
    smp - Hlen.
    rwr - Nat.succ_inj_wd in Hlen.
    pose proof fs_eval_nth_to_partial
      IValues el1 ek el2 ex [] v vl vx Hlen Hnth
      as IHvl.
    clr - Hlen Hnth.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - IHv as [kv [_ Hstep_v]].
    des - IHvl as [kvs Hstep_vl].
    des - IHxk as [kxk [Hscope_xk Hstep_xk]].
    (* #10 FrameStack Evaluation: start/step *)
    start / Hscope_xk.
    step - Hstep_v.
    step - Hstep_vl.
    step - Hstep_xk.
    step.
  Qed.



End EValues.









Section ETuple.



  Theorem eq_bsfs_etuple_to_vtuple :
    forall Γ el vl,
        length el = length vl
    ->  (forall i,
            i < length el
        ->  ⟨ [], erase_names Γ (nth i el ErrorExp) ⟩ -->* 
                  erase_valseq [nth i vl ErrorValue])
    ->  ⟨ [], erase_names Γ (ETuple el) ⟩ -->* erase_valseq [VTuple vl].
  Proof.
    itr - Γ el' vl' Hlen IHnth'.
    (* #0 Pre: rewrite/symmetry *)
    rwr - Hlen in IHnth'.
    sym - Hlen.
    (* #1 Simplify Expressions: simpl/unfold/rewrite/mvr *)
    smp *.
    ufl - erase_names in *.
    ufl - erase_valseq.
    rwr - map_map.
    mvr.
    (* #2 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
    (*Erasers*)
    rem - σ as Hσ:
      (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth: σ ξ el' vl' IHnth'.
    (*Expressions*)
    rem - el ex as Hel Hex:
      (map (fun e => (erase_exp σ e).[ξ]) el')
      (erase_exp σ ErrorExp);
      clr - Hex.
    erewrite length_map_erase_exp_eq in Hlen.
    2: exa - Hel.
    clr - Hel el' σ ξ.
    (*Value*)
    rem - vl vx as Hvl Hvx:
      (map erase_val' vl')
      (erase_val' ErrorValue);
      clr - Hvx.
    erewrite length_map_erase_val_eq in *.
    2-3: exa - Hvl.
    clr - Hvl vl'.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscope': el ex vl vx Hlen IHnth.
    psc - scope_list_to_tuple as Hscope: vl Hscope'.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - el as [| e el].
    { (* - Empty List Branch *)
      clr - IHnth.
      (* #4.1 Both List Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      (* #4.2 FrameStack Evaluation: start/step *)
      start.
      step.
    } (* - Cons List Branch *)
    (* #5 Both List Cons: destruct + inversion/subst *)
    des - vl as [| v vl]: ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    psc - fs_eval_nth_cons as Hnth_cons: e el ex v vl vx IHnth.
    des - Hnth_cons as [IHv Hnth].
    (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
    smp - Hlen.
    rwr - Nat.succ_inj_wd in Hlen.
    pose proof create_result_ituple
      v vl [] as Hcrt.
    pose proof fs_eval_nth_to_result
      ITuple el ex [] v vl vx (RValSeq [Syntax.VTuple (v :: vl)])
      [] [] Hlen Hcrt Hnth
      as IHvl.
    clr - Hlen Hcrt Hnth.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHv as [kv [_ Hstep_v]].
    des - IHvl as [kvs Hstep_vl].
    (* #9 FrameStack Evaluation: start/step *)
    start / Hscope.
    step - Hstep_v.
    step - Hstep_vl.
  Qed.






  Theorem eq_bsfs_etuple_to_exception :
    forall Γ el vl xk,
        length vl < length el
    ->  (forall i,
            i < length vl
        ->  ⟨ [], erase_names Γ (nth i el ErrorExp) ⟩ -->* 
                  erase_valseq [nth i vl ErrorValue])
    ->  ⟨ [], erase_names Γ (nth (length vl) el ErrorExp) ⟩ -->* erase_exc xk
    ->  ⟨ [], erase_names Γ (ETuple el) ⟩ -->* erase_exc xk.
  Proof.
    itr - Γ el' vl' xk' Hlen IHnth' IHxk.
    (* #1 Simplify Expressions: simpl/unfold/rewrite *)
    smp *.
    ufl - erase_names in *.
    rwr - map_map.
    (* #2 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
    (*Erasers*)
    rem - σ as Hσ:
      (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      clr - Hξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth: σ ξ el' vl' IHnth'.
    rwr - fs_eval_nth_map_erase_single in IHxk.
    (*Expressions*)
    rem - el ex as Hel Hex:
      (map (fun e => (erase_exp σ e).[ξ]) el')
      (erase_exp σ ErrorExp);
      clr - Hex.
    erewrite length_map_erase_exp_eq in Hlen.
    2: exa - Hel.
    clr - Hel el' σ ξ.
    (*Value*)
    rem - vl vx xk as Hvl Hvx Hxk:
      (map erase_val' vl')
      (erase_val' ErrorValue)
      (erase_exc xk');
      clr - Hvx Hxk.
    erewrite length_map_erase_val_eq in *.
    2-4: exa - Hvl.
    clr - Hvl vl'.
    (* #3 Split Expression List: pose/destruct *)
    psc - length_lt_split_middle as Hsplit: Val Exp vl el Hlen.
    des - Hsplit as [el1 [ek [el2 [Hel Hlen]]]].
    sbt.
    (* #4 Simplify Exception Hypothesis: *)
    rwr - Hlen in IHxk.
    smp - IHxk.
    rwr - nth_middle in IHxk.
    (* #5 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - el1 as [| e el1].
    { (* - Empty List Branch *)
      clr - IHnth.
      (* #5.1 Both List Empty: simpl/rewrite/subst/simpl *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      smp.
      (* #5.2 Destruct Inductive Hypothesis: destruct *)
      des - IHxk as [kv [Hscope_xk Hstep_xk]].
      (* #5.3 FrameStack Evaluation: start/step *)
      start / Hscope_xk.
      step - Hstep_xk.
      step.
    } (* - Cons List Branch *)
    (* #6 Both List Cons: destruct + inversion/subst *)
    des - vl as [| v vl]: ivs - Hlen.
    (* #7 Pose Nth Cons Theorem: rewrite/pose/destruct *)
    rewrite cons_app with (l := el1) in IHnth.
    rwl - app_assoc in IHnth.
    do 2 rwl - cons_app in IHnth.
    psc - fs_eval_nth_cons as Hnth_cons:
      e (el1 ++ ek :: el2) ex v vl vx IHnth.
    des - Hnth_cons as [IHv Hnth].
    (* #8 Pose From Nth to Result: simpl/rewrite/pose *)
    smp - Hlen.
    rwr - Nat.succ_inj_wd in Hlen.
    pose proof fs_eval_nth_to_partial
      ITuple el1 ek el2 ex [] v vl vx Hlen Hnth
      as IHvl.
    clr - Hlen Hnth.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - IHv as [kv [_ Hstep_v]].
    des - IHvl as [kvs Hstep_vl].
    des - IHxk as [kxk [Hscope_xk Hstep_xk]].
    (* #10 FrameStack Evaluation: start/step *)
    start / Hscope_xk.
    step - Hstep_v.
    step - Hstep_vl.
    step - Hstep_xk.
    step.
  Qed.



End ETuple.









Section EMap.



  Theorem eq_bsfs_emap_to_vmap :
    forall Γ ell kvl vvl,
        length ell = length kvl
    ->  length ell = length vvl
    ->  make_value_map kvl vvl = (kvl, vvl)
    ->  (forall i,
            i < length (make_map_exps ell)
        ->  ⟨ [], erase_names Γ (nth i (make_map_exps ell) ErrorExp) ⟩ -->* 
                  erase_valseq [nth i (make_map_vals kvl vvl) ErrorValue])
    ->  ⟨ [], erase_names Γ (EMap ell) ⟩ -->*
              erase_valseq [VMap (combine kvl vvl)].
  Proof.
    itr - Γ ell' kvl vvl Hlen_k Hlen_v Hmake IHnth'.
    (* #1 Rewrite Combine Keys-Vals Theorem: 
          symmetry/assert/pose/destruct/rewrite + lia*)
    sym - Hlen_k Hlen_v.
    ass > (length kvl = length vvl) as Hlen: lia.
    pse - combine_key_and_val_lists as Hcomb: kvl vvl Hlen Hmake.
    des - Hcomb as [vll' [Hkvl [Hvvl [Hvll Hflat]]]].
    cwr - Hvll Hflat Hkvl Hvvl in *.
    clr - kvl vvl Hmake.
    (* # 2 Rewrite MakeMapExps Faletten Lemma: *)
    rwr - make_map_exps_flatten_list_eq in *.
    (* #3 Adjust Lengths: rename/rewrite/pose + reflexivity *)
    clr - Hlen Hlen_v.
    ren - Hlen: Hlen_k.
    rwr - length_map in Hlen.
    pose proof f_equal2_mult
      (length vll') (length ell') 2 2 Hlen eq_refl as Hlen2.
    do 2 rewrite <- length_flatten_list in Hlen2.
    ren - Hlen_flat: Hlen2.
    cwl - Hlen_flat in IHnth'.
    (* #1 Simplify Expressions: simpl/unfold/rewrite/mvr *)
    pose proof flatten_deflatten ell' as Hell'.
    pose proof flatten_deflatten vll' as Hvll'.
    cwl - Hell' Hvll'.
    smp *.
    do 3 rwr - deflatten_map.
    rwr - map_map.
    mvr.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
    (*Erasers*)
    rem - σ as Hσ:
      (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth:
      σ ξ (flatten_list ell') (flatten_list vll') IHnth'.
    do 2 rwr - flatten_map in *.
    (*Expressions*)
    rem - ell ex as Hell Hex:
      (map (λ '(x, y), ((erase_exp σ x).[ξ], (erase_exp σ y).[ξ])) ell')
      (erase_exp σ ErrorExp);
      clr - Hex.
    epose proof length_map_from_eq  _ _ _ _ _ Hell as Hlen_ell.
    cwr - Hlen_ell in *.
    clr - Hell ell' σ ξ.
    (*Value*)
    rem - vll vx as Hvl Hvx:
      (map (λ '(x, y), (erase_val' x, erase_val' y)) vll')
      (erase_val' ErrorValue);
      clr - Hvx.
    rewrite length_flatten_list in IHnth.
    epose proof length_map_from_eq  _ _ _ _ _ Hvl as Hlen_vll.
    cwr - Hlen_vll in *.
    rewrite <- length_flatten_list in IHnth.
    clr - Hvl vll'.
    (* # After Touch: *)
    pose proof flatten_deflatten ell as Hell.
    pose proof flatten_deflatten vll as Hvll.
    cwr - Hell Hvll.
    pose proof f_equal2_mult
      (length vll) (length ell) 2 2 Hlen eq_refl as Hlen2.
    do 2 rewrite <- length_flatten_list in Hlen2.
    clr - Hlen.
    ren - Hlen: Hlen2.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscope':
      (flatten_list ell) ex (flatten_list vll) vx Hlen IHnth.
    psc - scope_list_to_map as Hscope: vll Hscope'.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - ell as [| [e1 e2] ell].
    { (* - Empty List Branch *)
      clr - IHnth Hscope.
      (* #4.1 Both List Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      pose proof flatten_deflatten vll as Hvll.
      rwr - Hlen in Hvll.
      smp *.
      sbt.
      clr - Hlen.
      (* #4.2 FrameStack Evaluation: start/step *)
      start.
      step.
    } (* - Cons List Branch *)
    (* #5 Both List Cons: destruct + inversion/subst *)
    des - vll as [| [v1 v2] vll]: ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    do 2 rwr - flatten_cons in *.
    psc - fs_eval_nth_cons as Hnth_cons:
      e1 (e2 :: flatten_list ell) ex v1 (v2 :: flatten_list vll) vx IHnth.
    des - Hnth_cons as [IHv1 IHnth].
    psc - fs_eval_nth_cons as Hnth_cons:
      e2 (flatten_list ell) ex v2 (flatten_list vll) vx IHnth.
    des - Hnth_cons as [IHv2 Hnth].
    (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
    smp - Hlen.
    do 2 rwr - Nat.succ_inj_wd in Hlen.
    pose proof create_result_imap
      v1 v2 vll [] as Hcrt.
    pse - all_fsval_is_wfm as Hwfm: (Syntax.VMap ((v1, v2) :: vll)).
    des - Hwfm as [Hwfm _].
    cwl - Hwfm in Hcrt.
    pose proof fs_eval_nth_to_result
      IMap (flatten_list ell) ex [v1] v2 (flatten_list vll) vx
      (RValSeq [Syntax.VMap ((v1, v2) :: vll)]) [] [] Hlen Hcrt Hnth
      as IHvll.
    clr - Hlen Hcrt Hnth.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHv1 as [kv1 [_ Hstep_v1]].
    des - IHv2 as [kv2 [_ Hstep_v2]].
    des - IHvll as [kvll Hstep_vll].
    (* #9 FrameStack Evaluation: start/step *)
    start / Hscope.
    step - Hstep_v1.
    step - Hstep_v2.
    step - Hstep_vll.
  Qed.






  Theorem eq_bsfs_emap_to_exception :
    forall Γ ell kvl vvl xk k,
        k < 2 * length ell
    ->  length kvl = k / 2 + k mod 2
    ->  length vvl = k / 2
    ->  (forall i,
            i < k
        ->  ⟨ [], erase_names Γ (nth i (make_map_exps ell) ErrorExp) ⟩ -->* 
                  erase_valseq [nth i (make_map_vals kvl vvl) ErrorValue])
    ->  ⟨ [], erase_names Γ (nth k (make_map_exps ell) ErrorExp) ⟩ -->*
              erase_result (inr xk)
    ->  ⟨ [], erase_names Γ (EMap ell) ⟩ -->*
              erase_exc xk.
  Proof.
    itr - Γ ell' kvl vvl xk k Hlen_ell Hlen_k Hlen_v IHnth' IHxk.
    (* #1 Rewrite Combine Keys-Vals Theorem: 
          symmetry/assert/pose/destruct/rewrite + lia*)
    pse - combine_key_and_val_exc as Hcomb: kvl vvl k Hlen_k Hlen_v.
    des - Hcomb as [vll' [ov' [Hlen_vll [Hlen_ov [Hkvl [Hvvl Hflat]]]]]].
    cwr - Hkvl Hvvl Hflat in *.
    clr - Hlen_k Hlen_v.
    (* # 2 Rewrite MakeMapExps Faletten Lemma: *)
    rwr - make_map_exps_flatten_list_eq in *.
    (* #3 Adjust Lengths: rename/rewrite/pose + reflexivity *)
    rwr - Nat.mul_comm in Hlen_ell.
    ass > (k =  (length ((flatten_list vll') ++ ov'))) as Hk.
    {
      clr - IHnth' Hlen_ell.
      rwr - length_app.
      pose proof length_flatten_list vll' as Hflat.
      rwr - Nat.mul_comm in Hflat.
      rwr - Hflat.
      rewrite Hlen_vll.
      rewrite Hlen_ov.
      apply Nat.div_mod.
      con.
    }
    cwr - Hk in IHnth' IHxk Hlen_ell.
    (* rewrite <- length_flatten_list in Hlen_ell. *)
    (* #1 Simplify Expressions: simpl/unfold/rewrite/mvr *)
    pose proof flatten_deflatten ell' as Hell'.
    cwl - Hell'.
    smp.
    do 2 rwr - deflatten_map.
    rwr - map_map.
    mvr.
    ufl - erase_names in *.
    (* #2 Shorten Expressions: remember;unfold;symmetry;rewrite;exact *)
    (*Erasers*)
    rem - σ as Hσ:
      (from_env Γ);
      clr - Hσ.
    (*Substs*)
    rem - ξ as Hξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Hξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth:
      σ ξ (flatten_list ell') (flatten_list vll' ++ ov') IHnth'.
    rwr - fs_eval_nth_map_erase_single in IHxk.
    rwr - map_app in IHnth.
    rwr - flatten_map in *.
    rwr - flatten_map in IHnth.
    (*Expressions*)
    rem - ell ex as Hell Hex:
      (map (λ '(x, y), ((erase_exp σ x).[ξ], (erase_exp σ y).[ξ])) ell')
      (erase_exp σ ErrorExp);
      clr - Hex.
    epose proof length_map_from_eq  _ _ _ _ _ Hell as Hlen_ell'.
    cwr - Hlen_ell' in *.
    rewrite <- length_flatten_list in Hlen_ell.
    clr - Hell ell' σ ξ.
    (*Value*)
    rem - vll ov vx as Hvll Hov Hvx:
      (map (λ '(x, y), (erase_val' x, erase_val' y)) vll')
      (map erase_val' ov')
      (erase_val' ErrorValue);
      clr - Hvx.
    rwr - length_app in *.
    rewrite length_flatten_list in *.
    epose proof length_map_from_eq  _ _ _ _ _ Hvll as Hlen_vll'.
    cwr - Hlen_vll' in *.
    epose proof length_map_from_eq  _ _ _ _ _ Hov as Hlen_vo'.
    cwr - Hlen_vo' in *.
    rewrite <- length_flatten_list in *.
    rwl - length_app in *.
    clr - Hvll Hov vll' ov'.
    (* # After Touch: *)
    pose proof flatten_deflatten ell as Hell.
    cwr - Hell.
    (* pose proof f_equal2_mult
      (length vll) (length ell) 2 2 Hlen eq_refl as Hlen2.
    do 2 rewrite <- length_flatten_list in Hlen2.
    clr - Hlen.
    ren - Hlen: Hlen2. *)
    (* #3 Scope From Nth: pose *)
    (* #3 Split Expression List: pose/destruct *)
    ass > (length vll < length ell) as Hlen.
    { 
      rwr - length_app in Hlen_ell.
      do 2 rewrite length_flatten_list in Hlen_ell.
      lia.
    }
    epose proof length_lt_split_middle _ _ vll ell Hlen as Hsplit.
    des - Hsplit as [ell1 [[ekev ekod] [ell2 [Hell Hlen']]]].
    sbt.
    clr - Hlen.
    ren - Hlen: Hlen'.
    do 2 rwr - flatten_app in *.
    rwr - flatten_cons in *.
    smp - Hlen_ell IHxk IHnth.
    (* #4 Simplify Exception and Option Hypothesis: *)
    spe + IHnth as IHov: (length (flatten_list ell1)).
    pose proof f_equal2_mult
      (length vll) (length ell1) 2 2 Hlen eq_refl as Hlen2.
    do 2 rewrite <- length_flatten_list in Hlen2.
    rwr - length_app in IHov IHxk.
    rwr - Hlen2 in IHov IHxk.
    rwr - app_nth2_plus in IHxk.
    (* ass >
      (length (flatten_list ell1) < length (flatten_list ell1) + base.length ov)
      as Hle. lia.
    specialize (IHov lia). *)
    pose proof kmod2list_is_either_empty_or_single _ _ _ Hlen_ov as Hov.
    clr - Hlen_ov.
    des - Hov as [Hempty | Hsingle].
    * (*xk*)
      sbt.
      smp *.
      rwr - app_nil_r in *.
      clr - IHov Hlen Hlen_ell Hlen_vll.
      ren - Hlen: Hlen2.
      (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
      des - ell1 as [| [e1 e2] ell1].
      { (* - Empty List Branch *)
        clr - IHnth Hlen.
        smp.
        des - IHxk as [kxk [Hscope_xk Hstep_xk]].
        start / Hscope_xk.
        step - Hstep_xk.
        step.
      } (* - Cons List Branch *)
      (* #5 Both List Cons: destruct + inversion/subst *)
      des - vll as [| [v1 v2] vll]: ivs - Hlen.
      (* #6 Pose Nth Cons Theorem: pose/destruct *)
      do 2 rwr - flatten_cons in *.
      psc - fs_eval_nth_cons as Hnth_cons:
        e1 (e2 :: flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v1 (v2 :: flatten_list vll) vx IHnth.
      des - Hnth_cons as [IHv1 IHnth].
      psc - fs_eval_nth_cons as Hnth_cons:
        e2 (flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v2 (flatten_list vll) vx IHnth.
      des - Hnth_cons as [IHv2 Hnth].
      (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
      smp - Hlen.
      do 2 rwr - Nat.succ_inj_wd in Hlen.
      pose proof fs_eval_nth_to_partial
        IMap (flatten_list ell1) ekev (ekod :: flatten_list ell2) ex
        [v1] v2 (flatten_list vll) vx Hlen Hnth
        as IHvll.
      clr - Hlen Hnth.
      rwl - cons_app in *.
      (* #8 Destruct Inductive Hypothesis: destruct *)
      des - IHv1 as [kv1 [_ Hstep_v1]].
      des - IHv2 as [kv2 [_ Hstep_v2]].
      des - IHvll as [kvll Hstep_vll].
      des - IHxk as [kxk [Hscope_xk Hstep_xk]].
      (* #9 FrameStack Evaluation: start/step *)
      start / Hscope_xk.
      step - Hstep_v1.    rwr - flatten_app.
      step - Hstep_v2.
      step - Hstep_vll.
      step - Hstep_xk.
      step.
    * (*ov*)
      sbt.
      des - Hsingle as [vkev Hov].
      sbt.
      ass >
        (length (flatten_list ell1) <
         length (flatten_list ell1) + length [vkev])
         as Hle: sli.
      spc - IHov: Hle.
      ass >
        (length (flatten_list ell1) = length (flatten_list ell1) + 0)
        as Hr0: lia.
      cwr - Hr0 in IHov.
      rwr - app_nth2_plus in IHov.
      rwl - Hlen2 in IHov.
      rwr - app_nth2_plus in IHov.
      smp - IHov.
      (*xk*)
      smp - IHxk.
      clr - Hlen Hlen_vll Hlen_ell.
      ren - Hlen: Hlen2.
      (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
      des - ell1 as [| [e1 e2] ell1].
      { (* - Empty List Branch *)
        clr - IHnth Hlen.
        smp.
        des - IHov as [kv_even [Hscope_v_even Hstep_v_even]].
        des - IHxk as [kx_odd [Hscope_x_odd Hstep_x_odd]].
        start / Hscope_x_odd.
        step - Hstep_v_even.
        step - Hstep_x_odd.
        step.
      } (* - Cons List Branch *)
      (* #5 Both List Cons: destruct + inversion/subst *)
      des - vll as [| [v1 v2] vll]: ivs - Hlen.
      (* #6 Pose Nth Cons Theorem: pose/destruct *)
      do 2 rwr - flatten_cons in *.
      psc - fs_eval_nth_cons as Hnth_cons:
        e1 (e2 :: flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v1 (v2 :: flatten_list vll ++ [vkev]) vx IHnth.
      des - Hnth_cons as [IHv1 IHnth].
      psc - fs_eval_nth_cons as Hnth_cons:
        e2 (flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v2 (flatten_list vll ++ [vkev]) vx IHnth.
      des - Hnth_cons as [IHv2 Hnth].
      (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
      smp - Hlen.
      do 2 rwr - Nat.succ_inj_wd in Hlen.
      ass >
        (length (flatten_list vll ++ [vkev]) =
         length (flatten_list ell1 ++ [ekev]))
         as Hlen1:
        do 2 rwr - length_app; sli.
      Check cons_app.
      rewrite cons_app with (x := ekev) in Hnth.
      rwr - app_assoc in Hnth.
      pose proof fs_eval_nth_to_partial
        IMap (flatten_list ell1 ++ [ekev]) ekod (flatten_list ell2) ex
        [v1] v2 (flatten_list vll ++ [vkev]) vx Hlen1 Hnth
        as IHvll.
      rwl - app_assoc in IHvll.
      clr - Hlen Hnth.
      rwl - cons_app in *.
      (* #8 Destruct Inductive Hypothesis: destruct *)
      des - IHv1 as [kv1 [_ Hstep_v1]].
      des - IHv2 as [kv2 [_ Hstep_v2]].
      des - IHvll as [kvll Hstep_vll].
      des - IHov as [kov [Hscope_ov Hstep_ov]].
      des - IHxk as [kxk [Hscope_xk Hstep_xk]].
      (* #9 FrameStack Evaluation: start/step *)
      start / Hscope_xk.
      step - Hstep_v1.    rwr - flatten_app.
      step - Hstep_v2.
      step - Hstep_vll.
      step - Hstep_xk.
      step.
  Qed.



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
            pse - etry_catch_vars_length as Hlen2: 
                  Γ modules own_module vars1 vars2 e1 e2 e3 x1 r3
                  id id' id'' eff eff' eff'' IHBx1 IHBr3.
            rwr - erase_result_to_exception in *.
            bse - eq_bsfs_etry_to_result2:
                  Γ vars1 vars2 e1 e2 e3 x1 r3 Hlen2 IHFx1 IHFr3.
          }
    (* #6 Lists: EValues/ETuple/EMap *)
      (* +6.1 EValues: valseq/exception *)
        (* -6.1.1 valseq: *)
          1: {
            ren - el vl Hlen IHFnth:
                  exps vals H H3.
            bse - eq_bsfs_evalues_to_valseq:
                  Γ el vl Hlen IHFnth.
          }
        (* -6.1.2 exception: *)
          1:  {
            ren - el vl xk Hlen IHFnth IHFxk:
                  exps vals ex H H4 IHB.
            subst.
            bse - eq_bsfs_evalues_to_exception:
                  Γ el vl xk Hlen IHFnth IHFxk.
          }
      (* +6.2 ETuple: valseq/exception *)
        (* -6.2.1 valseq: *)
          1:  {
            ren - el vl Hlen IHFnth:
                  exps vals H H3.
            bse - eq_bsfs_etuple_to_vtuple:
                  Γ el vl Hlen IHFnth.
          }
        (* -6.2.2 exception: *)
          7:  {
            ren - el vl xk Hlen IHFnth IHFxk:
                  exps vals ex H H4 IHB.
            subst.
            bse - eq_bsfs_etuple_to_exception:
                  Γ el vl xk Hlen IHFnth IHFxk.
          }
      (* +6.3 EMap: valseq/exception *)
        (* -6.3.1 valseq: *)
          6: {
            ren - ell vll kvl vvl kvm vvm eff' eff'':
                  l lv kvals vvals kvals' vvals' eff1 eff2.
            ren - Hlen_v Hlen_k Hlen_eff Hlen_id IHFnth IHBnth Hmake Hcomb:
                   H H0 H1 H2 H4 H3 H5 H6.
            ren - Heq_eff Heq_id:
                  H7 H8.
            pse - map_is_wfm as Hwfm:
                  Γ modules own_module ell kvl vvl kvm vvm vll
                  eff eff' eff'' ids id id'.
            spe - Hwfm: Hlen_v Hlen_k Hlen_eff Hlen_id
                  IHBnth Hmake Hcomb Heq_eff Heq_id.
            des - Hwfm as [Hkvl Hvvl].
            cwl - Hkvl Hvvl in *.
            subst exps vals.
            subst.
            bse - eq_bsfs_emap_to_vmap:
                  Γ ell kvl vvl Hlen_k Hlen_v Hmake IHFnth.
          }
        (* -6.3.2 exception: *)
          19: {
            ren - ell xi k kvl vvl Hlen_ell Hlen_k Hlen_v IHFnth IHFxi:
                  l ex i kvals vvals H H1 H0 H5 IHB.
            subst exps vals.
            bse - eq_bsfs_emap_to_exception:
                  Γ ell kvl vvl xi k Hlen_ell Hlen_k Hlen_v IHFnth IHFxi.
          }
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



(*   Definition fexp (e : Exp) : Expression :=
  match e with 
  | _ => ENil
  end.
  
  Definition fval (v : Val) : Value :=
  match v with
  | _ => VNil
  end.
  
  Definition fredex (r : Redex) : (ValueSequence + Exception) :=
  inl ([]).

  Theorem eq_fsbs :
    forall Γ modules own_module id id' e r eff eff' ,
        ⟨ [], RExp e ⟩ -->* r
    ->  (eval_expr Γ modules own_module id (fexp e) eff id' (fredex r) eff').
  Proof.
    itr.
    ind - e.
    - ind - e.
      + ivc - H.
        des - H0.
        ivc - H0.
        smp.
  Admitted. *)


End EqBsFs.