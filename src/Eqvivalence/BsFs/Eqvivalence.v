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
    (* #1 Unfold Converters: simpl *)
    smp; clr - Γ.
    (* #2 FrameStack Evaluation: open/step *)
    open.
    step.
  Qed.



End ENil.




Section ELit.



  Theorem eq_bsfs_elit_to_vlit :
    forall Γ litᴮ ,
      ⟨ [], erase_names Γ (ELit litᴮ) ⟩ -->* erase_valseq [VLit litᴮ].
  Proof.
    itr.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - litᶠ as Hlit:
      (convert_lit litᴮ);
      clr - Hlit litᴮ Γ.
    (* #3 FrameStack Evaluation: open/step *)
    open.
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
    forall Γ xᴮ vᴮ,
        get_value Γ (inl xᴮ) = Some [vᴮ]
    ->  VALCLOSED (erase_val' vᴮ)
    ->  ⟨ [], erase_names Γ (EVar xᴮ) ⟩ -->* erase_valseq [vᴮ].
  Proof.
    itr - Γ xᴮ vᴮ Hget Hscp.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - vᶠ as Heqv_v:
      (erase_val' vᴮ).
    (* #3 Induction on Environment: induction + inversion/subst *)
    ind - Γ as [| [k₁ᴮ v₁ᴮ] Γ IHΓ]: ivs - Hget.
    (* #4 Apply Cons Theorem on Get Value: apply *)
    app - get_value_cons_eqb as Hget_cons in Hget.
    (* #5 Destruct Cons Hypothesis: destruct *)
    des - Hget_cons as [[Hk Hv] | [Hget Heqb]].
    * (* +I. Get Value in the Head: *)
      clr - IHΓ.
      (* #I/1 Rewrite Eqvivalences*)
      cwr - Hk Hv / k₁ᴮ v₁ᴮ.
      (* #I/2 Simplify by Lemmas: rewrite/simpl *)
      rwr - from_env_cons.
      rwr - var_funid_eqb_refl.
      smp / Γ xᴮ.
      cwl - Heqv_v / vᴮ.
      (* #I/3 FrameStack Evaluation: open/step *)
      open.
      step.
    * (* +II. Get Value in the Tail: *)
      clr - Hscp Heqv_v.
      (* #II/1 Simplify by Lemmas: rewrite/simpl *)
      rwr - from_env_cons.
      cwr - Heqb.
      smp / k₁ᴮ v₁ᴮ.
      (* #II/2 Solve by Inductive Hypothesis: specialize/exact *)
      spc - IHΓ: Hget / vᴮ.
      exa - IHΓ.
  Qed.



End EVar.









Section EFunId.



  Theorem eq_bsfs_efunid_to_value :
    forall Γ fᴮ vᴮ,
        get_value Γ (inr fᴮ) = Some [vᴮ]
    ->  VALCLOSED (erase_val' vᴮ)
    ->  ⟨ [], erase_names Γ (EFunId fᴮ) ⟩ -->* erase_valseq [vᴮ].
  Proof.
    itr - Γ fᴮ vᴮ Hget Hscp.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - vᶠ as Heqv_v:
      (erase_val' vᴮ).
    (* #3 Induction on Environment: induction + inversion/subst *)
    ind - Γ as [| [k₁ᴮ v₁ᴮ] Γ IHΓ]: ivs - Hget.
    (* #4 Apply Cons Theorem on Get Value: apply *)
    app - get_value_cons_eqb as Hget_cons in Hget.
    (* #5 Destruct Cons Hypothesis: destruct *)
    des - Hget_cons as [[Hk Hv] | [Hget Heqb]].
    * (* +I. Get Value in the Head: *)
      clr - IHΓ.
      (* #I/1 Rewrite Eqvivalences*)
      cwr - Hk Hv / k₁ᴮ v₁ᴮ.
      (* #I/2 Simplify by Lemmas: rewrite/simpl *)
      rwr - from_env_cons.
      rwr - var_funid_eqb_refl.
      smp / Γ fᴮ.
      cwl - Heqv_v / vᴮ.
      (* #I/3 FrameStack Evaluation: open/step *)
      open.
      step.
    * (* +II. Get Value in the Tail: *)
      clr - Hscp Heqv_v.
      (* #II/1 Simplify by Lemmas: rewrite/simpl *)
      rwr - from_env_cons.
      cwr - Heqb.
      smp / k₁ᴮ v₁ᴮ.
      (* #II/2 Solve by Inductive Hypothesis: specialize/exact *)
      spc - IHΓ: Hget / vᴮ.
      exa - IHΓ.
  Qed.



End EFunId.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_SEQUENCES //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section ECons.



  Theorem eq_bsfs_econs_to_vcons :
    forall Γ e₁ᴮ e₂ᴮ v₁ᴮ v₂ᴮ,
        ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_valseq [v₁ᴮ]
    ->  ⟨ [], erase_names Γ e₂ᴮ ⟩ -->* erase_valseq [v₂ᴮ]
    ->  ⟨ [], erase_names Γ (ECons e₁ᴮ e₂ᴮ) ⟩ -->* erase_valseq [VCons v₁ᴮ v₂ᴮ].
  Proof.
    itr - Γ e₁ᴮ e₂ᴮ v₁ᴮ v₂ᴮ IHFse_v₁ IHFse_v₂.
    (* #1 Unfold Converters: simpl/unfold/mvr *)
    smp *.
    ufl - erase_names in *.
    do 2 mvr.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - v₁ᶠ v₂ᶠ as Heqv_v₁ Heqv_v₂ / Heqv_v₁ Heqv_v₂ v₁ᴮ v₂ᴮ:
      (erase_val' v₁ᴮ)
      (erase_val' v₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [Hscp_v₁ Hstp_v₁]].
    des - IHFse_v₂ as [k_v₂ [Hscp_v₂ Hstp_v₂]].
    (* #4 FrameStack Evaluation: open;step *)
    open / Hscp_v₁ Hscp_v₂.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step.
  Qed.






  Theorem eq_bsfs_econs_to_exception1 :
    forall Γ e₁ᴮ e₂ᴮ q₁ᴮ v₂ᴮ,
        ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_exc q₁ᴮ
    ->  ⟨ [], erase_names Γ e₂ᴮ ⟩ -->* erase_valseq [v₂ᴮ]
    ->  ⟨ [], erase_names Γ (ECons e₁ᴮ e₂ᴮ) ⟩ -->* erase_exc q₁ᴮ.
  Proof.
    itr - Γ e₁ᴮ e₂ᴮ q₁ᴮ v₂ᴮ IHFse_q₁ IHFse_v₂.
    (* #1 Unfold Converters: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - q₁ᶠ v₂ᶠ as Heqv_q₁ Heqv_v₂ / Heqv_q₁ Heqv_v₂ q₁ᴮ v₂ᴮ:
      (erase_exc q₁ᴮ)
      (erase_val' v₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_q₁ as [k_q₁ [Hscp_q₁ Hstp_q₁]].
    des - IHFse_v₂ as [k_v₂ [Hscp_v₂ Hstp_v₂]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_q₁ Hscp_v₂.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    step - Hstp_q₁ / e₁ᶠ k_q₁.
    step.
  Qed.






  Theorem eq_bsfs_econs_to_exception2 :
    forall Γ e₁ᴮ e₂ᴮ q₂ᴮ,
        ⟨ [], erase_names Γ e₂ᴮ ⟩ -->* erase_exc q₂ᴮ
    ->  ⟨ [], erase_names Γ (ECons e₁ᴮ e₂ᴮ) ⟩ -->* erase_exc q₂ᴮ.
  Proof.
    itr - Γ e₁ᴮ e₂ᴮ q₂ᴮ IHFse_q₂.
    (* #1 Unfold Converters: simpl/unfold *)
    smp.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - q₂ᶠ as Heqv_q₂ / Heqv_q₂ q₂ᴮ:
      (erase_exc q₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_q₂ as [k_q₂ [Hscp_q₂ Hstp_q₂]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_q₂.
    step - Hstp_q₂ / e₂ᶠ k_q₂.
    step.
  Qed.



End ECons.









Section ESeq.



  Theorem eq_bsfs_eseq_to_result :
    forall Γ e₁ᴮ e₂ᴮ v₁ᴮ r₂ᴮ,
        ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_valseq [v₁ᴮ]
    ->  ⟨ [], erase_names Γ e₂ᴮ ⟩ -->* erase_result r₂ᴮ
    ->  ⟨ [], erase_names Γ (ESeq e₁ᴮ e₂ᴮ) ⟩ -->* erase_result r₂ᴮ.
  Proof.
    itr - Γ e₁ᴮ e₂ᴮ v₁ᴮ r₂ᴮ IHFse_v₁ IHFse_r₂.
    (* #1 Unfold Converters: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - v₁ᶠ r₂ᶠ as Heqv_v₁ Heqv_r₂ / Heqv_v₁ Heqv_r₂ v₁ᴮ r₂ᴮ:
      (erase_val' v₁ᴮ)
      (erase_result r₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [_       Hstp_v₁]].
    des - IHFse_r₂ as [k_r₂ [Hscp_r₂ Hstp_r₂]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_r₂.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step - Hstp_r₂.
  Qed.






  Theorem eq_bsfs_eseq_to_exception :
    forall Γ e₁ᴮ e₂ᴮ q₁ᴮ,
        ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_exc q₁ᴮ
    ->  ⟨ [], erase_names Γ (ESeq e₁ᴮ e₂ᴮ) ⟩ -->* erase_exc q₁ᴮ.
  Proof.
    itr - Γ e₁ᴮ e₂ᴮ q₁ᴮ IHFse_q₁.
    (* #1 Unfold Converters: simpl/unfold *)
    smp.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - q₁ᶠ as Heqv_q₁ / Heqv_q₁ q₁ᴮ:
      (erase_exc q₁ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_q₁ as [k_q₁ [Hscp_q₁ Hstp_q₁]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_q₁.
    step - Hstp_q₁ / e₁ᶠ k_q₁.
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
    forall Γ xsᴮ eᴮ id,
        is_result (erase_valseq [VClos Γ [] id xsᴮ eᴮ])
    ->  ⟨ [], erase_names Γ (EFun xsᴮ eᴮ) ⟩ -->*
              erase_valseq [VClos Γ [] id xsᴮ eᴮ].
  Proof.
    itr - Γ xsᴮ eᴮ id Hscp.
    (* #1 Unfold Converters: simpl/mvr *)
    smp *.
    mvr.
    (* #2 Simplify Expression: rewrite/pose *)
    rwr - rem_ext_vars_empty_ext in *.
    pse - add_ext_vars_empty_ext as Hempty: xsᴮ (from_env (rem_vars xsᴮ Γ)).
    cwr - Hempty in *.
    (* #3 Use Remove Vars Theorem: rewrite/pose *)
    rwr - erase_subst_rem_vars in *.
    (* #4 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (add_vars xsᴮ (from_env Γ)).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (upn (base.length xsᴮ)
           (list_subst (map erase_val' (map snd Γ)) idsubst)).
      (* Variables *)
    rem - xsᶠ as Heqv_xs / Heqv_xs:
      (base.length xsᴮ).
      (* Expressions *)
    rem - eᶠ as Heqv_e / Heqv_e eᴮ σ ξ:
      ((erase_exp σ eᴮ).[ξ]).
    (* #5 FrameStack Evaluation: open/step *)
    open / Hscp.
    step.
  Qed.



End EFun.









Section ELetRec.



  Theorem eq_bsfs_eletrec_to_result :
    forall Γ extᴮ eᴮ id rᴮ,
        ⟨ [], erase_names (append_funs_to_env extᴮ Γ id) eᴮ ⟩ -->*
              erase_result rᴮ
    ->  ⟨ [], erase_names Γ (ELetRec extᴮ eᴮ) ⟩ -->* erase_result rᴮ.
  Proof.
    itr - Γ extᴮ eᴮ id rᴮ IHFse_r.
    (* #1 Unfold Converters: simpl*)
    smp *.
    (* #2 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_r as [k_r [Hscp_r Hstp_r]].
    (* #3 Scope & Step: open/step *)
    open / Hscp_r.
    step.
  Admitted.

(*
Hstp_res :
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
    forall Γ xs₁ᴮ e₁ᴮ e₂ᴮ vs₁ᴮ r₂ᴮ,
        length xs₁ᴮ = length vs₁ᴮ
    ->  ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_valseq vs₁ᴮ
    ->  ⟨ [], erase_names (append_vars_to_env xs₁ᴮ vs₁ᴮ Γ) e₂ᴮ ⟩ -->*
              erase_result r₂ᴮ
    ->  ⟨ [], erase_names Γ (ELet xs₁ᴮ e₁ᴮ e₂ᴮ) ⟩ -->* erase_result r₂ᴮ.
  Proof.
    itr - Γ xs₁ᴮ e₁ᴮ e₂ᴮ vs₁ᴮ r₂ᴮ Hlen₁ IHFse_vs₁ IHFse_r₂.
    (* #0 Pre Formalize Hypothesis: symmetry *)
    sym - Hlen₁.
    (* #1 Unfold Converters: simpl/unfold *)
    smp.
    ufl - erase_names in *.
    (* #2 Use Append Theorem: rewrite + exact *)
    rwr - erase_subst_append_vars in IHFse_r₂.
    2: exa - Hlen₁.
    (* #3 Convert Syntax from BigStep to FrameStack:
          remember/unfold/rewrite + exact *)
      (* Erasers *)
    rem - σ₁ as Heqv_σ₁ / Heqv_σ₁:
      (from_env Γ).
    rem - σ₂ as Heqv_σ₂ / Heqv_σ₂:
      (add_vars xs₁ᴮ σ₁).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ₁ σ₂:
      (erase_exp σ₁ e₁ᴮ)
      (erase_exp σ₂ e₂ᴮ).
      (* Values *)
    ufl - erase_valseq in *.
    rem - vs₁ᶠ r₂ᶠ as Heqv_vs₁ Heqv_r₂ / Heqv_r₂ r₂ᴮ:
      (map erase_val' vs₁ᴮ)
      (erase_result r₂ᴮ).
    erewrite length_map_erase_val_eq in Hlen₁.
    2: exa - Heqv_vs₁.
    clr - Heqv_vs₁ vs₁ᴮ.
      (* Variables *)
    rem - xsᶠ as Heqv_xs / Heqv_xs xs₁ᴮ:
      (base.length xs₁ᴮ).
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_vs₁ as [k_vs₁ [_       Hstp_vs₁]].
    des - IHFse_r₂  as [k_r₂  [Hscp_r₂ Hstp_r₂]].
    (* #6 FrameStack Evaluation: open;step *)
    open / Hscp_r₂.
    step - Hstp_vs₁ / e₁ᶠ k_vs₁.
    step / Hlen₁.
    step - Hstp_r₂.
  Qed.






  Theorem eq_bsfs_elet_exc :
    forall Γ xs₁ᴮ e₁ᴮ e₂ᴮ q₁ᴮ,
        ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_exc q₁ᴮ
    ->  ⟨ [], erase_names Γ (ELet xs₁ᴮ e₁ᴮ e₂ᴮ) ⟩ -->* erase_exc q₁ᴮ.
  Proof.
    itr - Γ xs₁ᴮ e₁ᴮ e₂ᴮ q₁ᴮ IHFse_q₁.
    (* #1 Unfold Converters: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ₁ as Heqv_σ₁ / Heqv_σ₁:
      (from_env Γ).
    rem - σ₂ as Heqv_σ₂ / Heqv_σ₂:
      (add_vars xs₁ᴮ σ₁).
      (* Substs *)
    rem - ξ1 as Heqv_ξ1 / Heqv_ξ1 Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
    rem - ξ2 as Heqv_ξ2 / Heqv_ξ2:
      (upn (base.length xs₁ᴮ) ξ1).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ₁ σ₂ ξ1 ξ2:
      ((erase_exp σ₁ e₁ᴮ).[ξ1])
      ((erase_exp σ₂ e₂ᴮ).[ξ2]).
      (* Values *)
    rem - q₁ᶠ as Heqv_q₁ / Heqv_q₁ q₁ᴮ:
      (erase_exc q₁ᴮ).
      (* Variables *)
    rem - xs₁ᶠ as Heqv_xs / Heqv_xs xs₁ᴮ:
      (base.length xs₁ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_q₁ as [k_q₁ [Hscp_q₁ Hstp_q₁]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_q₁.
    step - Hstp_q₁ / e₁ᶠ k_q₁.
    step.
  Qed.



End ELet.









Section ETry.



  Theorem eq_bsfs_etry_to_result1 :
    forall Γ xs₁ᴮ xs₂ᴮ e₁ᴮ e₂ᴮ e₃ᴮ vs₁ᴮ r₂ᴮ,
        length xs₁ᴮ = length vs₁ᴮ
    ->  ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_valseq vs₁ᴮ
    ->  ⟨ [], erase_names (append_vars_to_env xs₁ᴮ vs₁ᴮ Γ) e₂ᴮ ⟩ -->*
              erase_result r₂ᴮ
    ->  ⟨ [], erase_names Γ (ETry e₁ᴮ xs₁ᴮ e₂ᴮ xs₂ᴮ e₃ᴮ) ⟩ -->*
              erase_result r₂ᴮ.
  Proof.
    itr - Γ xs₁ᴮ xs₂ᴮ e₁ᴮ e₂ᴮ e₃ᴮ vs₁ᴮ r₂ᴮ Hlen₁ IHFse_vs₁ IHFse_r₂.
    (* #0 Pre Formalize Hypothesis: symmetry *)
    sym - Hlen₁.
    (* #1 Unfold Converters: simpl/unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Apply Theorem: rewrite + exact *)
    rwr - erase_subst_append_vars in IHFse_r₂.
    2: exa - Hlen₁.
    (* #3 Convert Syntax from BigStep to FrameStack:
          remember/unfold/rewrite + exact *)
      (* Erasers *)
    rem - σ₁ as Heqv_σ₁ / Heqv_σ₁:
      (from_env Γ).
    rem - σ₂ σ₃ as Heqv_σ₂ Heqv_σ₃ / Heqv_σ₂ Heqv_σ₃:
      (add_vars xs₁ᴮ σ₁)
      (add_vars xs₂ᴮ σ₁).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ e₃ᶠ as Heqv_e₁ Heqv_e₂ Heqv_e₃
      / Heqv_e₁ Heqv_e₂ Heqv_e₃ e₁ᴮ e₂ᴮ e₃ᴮ σ₁ σ₂ σ₃:
      (erase_exp σ₁ e₁ᴮ)
      (erase_exp σ₂ e₂ᴮ)
      (erase_exp σ₃ e₃ᴮ).
      (* Values *)
    ufl - erase_valseq in *.
    rem - vs₁ᶠ r₂ᶠ as Heqv_vs₁ Heqv_r₂ / Heqv_r₂ r₂ᴮ:
      (map erase_val' vs₁ᴮ)
      (erase_result r₂ᴮ).
    erewrite length_map_erase_val_eq in Hlen₁.
    2: exa - Heqv_vs₁.
    clr - Heqv_vs₁ vs₁ᴮ.
      (* Variables *)
    rem - xs₁ᶠ xs₂ᶠ as Heqv_xs₁ Heqv_xs₂
      / Heqv_xs₁ Heqv_xs₂ xs₁ᴮ xs₂ᴮ:
      (base.length xs₁ᴮ)
      (base.length xs₂ᴮ).
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_vs₁ as [k_vs₁ [_       Hstp_vs₁]].
    des - IHFse_r₂  as [k_r₂  [Hscp_r₂ Hstp_r₂]].
    (* #6 FrameStack Evaluation: open/step *)
    open / Hscp_r₂.
    step - Hstp_vs₁ / e₁ᶠ k_vs₁.
    step / Hlen₁.
    step - Hstp_r₂.
  Qed.






  Theorem eq_bsfs_etry_to_result2 :
    forall Γ xs₁ᴮ xs₂ᴮ e₁ᴮ e₂ᴮ e₃ᴮ q₁ᴮ r₃ᴮ,
        length xs₂ᴮ = 3
    ->  ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_exc q₁ᴮ
    ->  ⟨ [], erase_names (append_vars_to_env xs₂ᴮ (exc_to_vals q₁ᴮ) Γ) e₃ᴮ ⟩
         -->* erase_result r₃ᴮ
    ->  ⟨ [], erase_names Γ (ETry e₁ᴮ xs₁ᴮ e₂ᴮ xs₂ᴮ e₃ᴮ) ⟩ -->*
              erase_result r₃ᴮ.
  Proof.
    itr - Γ xs₁ᴮ xs₂ᴮ e₁ᴮ e₂ᴮ e₃ᴮ q₁ᴮ r₃ᴮ Hlen₂ IHFse_q₁ IHFse_r₃.
    (* #0 Pre Formalize Hypothesis: destruct/symmetry*)
    des - q₁ᴮ as [[c₁ᴮ vʳ₁ᴮ] vᵈ₁ᴮ].
    sym - Hlen₂.
    (* #1 Unfold Converters: simpl;unfold *)
    smp *.
    ufl - erase_names in *.
    (* #2 Use Apply Theorem: rewrite/exact *)
    rwr - erase_subst_append_vars in IHFse_r₃.
    2: exa - Hlen₂.
    cwl - Hlen₂ in *.
    (* #3 Convert Syntax from BigStep to FrameStack: remember/simpl *)
      (* Erasers *)
    rem - σ₁ as Heqv_σ₁ / Heqv_σ₁:
      (from_env Γ).
    rem - σ₂ σ₃ as Heqv_σ₂ Heqv_σ₃ / Heqv_σ₂ Heqv_σ₃ xs₂ᴮ:
      (add_vars xs₁ᴮ σ₁)
      (add_vars xs₂ᴮ σ₁).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val' (map snd Γ)) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ e₃ᶠ as Heqv_e₁ Heqv_e₂ Heqv_e₃
      / Heqv_e₁ Heqv_e₂ Heqv_e₃ e₁ᴮ e₂ᴮ e₃ᴮ σ₁ σ₂ σ₃:
      (erase_exp σ₁ e₁ᴮ)
      (erase_exp σ₂ e₂ᴮ)
      (erase_exp σ₃ e₃ᴮ).
      (* Values *)
    smp ~ map - IHFse_r₃.
    rem - vᶜ₁ᶠ vʳ₁ᶠ vᵈ₁ᶠ r₃ᶠ as Heqv_vᶜ₁ Heqv_vʳ₁ Heqv_vᵈ₁ Heqv_r₃
      / Heqv_vʳ₁ Heqv_vᵈ₁ Heqv_r₃ vʳ₁ᴮ vᵈ₁ᴮ r₃ᴮ:
      (erase_val' (exclass_to_value c₁ᴮ))
      (erase_val' vʳ₁ᴮ)
      (erase_val' vᵈ₁ᴮ)
      (erase_result r₃ᴮ).
    (*ExceptionClass*)
    rem - c₁ᶠ as Heqv_c₁:
      (convert_class c₁ᴮ).
      (* Variables *)
    rem - xs₁ᶠ as Heqv_xs₁ / Heqv_xs₁ xs₁ᴮ:
      (base.length xs₁ᴮ).
    (* #4 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_q₁ as [k_q₁ [_       Hstp_q₁]].
    des - IHFse_r₃ as [k_r₃ [Hscp_r₃ Hstp_r₃]].
    (* #5 FrameStack Evaluation: open/step/destruct/simpl/unfold/subst *)
    open / Hscp_r₃.
    step - Hstp_q₁ / e₁ᶠ k_q₁.
    step / xs₁ᶠ e₂ᶠ.
    des - c₁ᴮ; smp *; ufl - Syntax.exclass_to_value; sbt.
    * step - Hstp_r₃.
    * step - Hstp_r₃.
    * step - Hstp_r₃.
  Qed.



End ETry.












(*
////////////////////////////////////////////////////////////////////////////////
//// EQBSFS_LISTS //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EValues.



  Theorem eq_bsfs_evalues_to_valseq :
    forall Γ elᴮ eₓᴮ vlᴮ vₓᴮ,
        length elᴮ = length vlᴮ
    ->  (forall i,
            i < length elᴮ
        ->  ⟨ [], erase_names Γ (nth i elᴮ eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i vlᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (EValues elᴮ) ⟩ -->* erase_valseq vlᴮ.
  Proof.
    itr - Γ elᴮ eₓᴮ vlᴮ vₓᴮ Hlen IHFse_nth.
    (* #0 Pre Formalize Hypothesis: rewrite/symmetry *)
    rwr - Hlen in IHFse_nth.
    sym - Hlen.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names
          erase_valseq in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack:
          remember/pose/rewrite + exact *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val' (map snd Γ)) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ elᴮ eₓᴮ vlᴮ vₓᴮ IHFse_nth.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - elᶠ eₓᶠ as Heqv_el Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) elᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in Hlen.
          2: exa - Heqv_el.
          clr - Heqv_el elᴮ σ ξ.
      (* Values *)
    rem - vlᶠ vₓᶠ as Heqv_vl Heqv_vₓ / Heqv_vₓ vₓᴮ:
          (map erase_val' vlᴮ)
          (erase_val' vₓᴮ).
    erewrite length_map_erase_val_eq in *.
          2-3: exa - Heqv_vl.
          clr - Heqv_vl vlᴮ.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp:
          elᶠ eₓᶠ vlᶠ vₓᶠ Hlen IHFse_nth.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - elᶠ as [| eᶠ elᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth Hscp eₓᶠ vₓᶠ.
          (* #4.1 Both List Empty: apply/subst *)
          app - length_empty_fst in Hlen.
          sbt.
          (* #4.2 FrameStack Evaluation: open/step *)
          open.
          step.
    } (* - Cons List Branch *)
    (* #5 Both List Cons: destruct + inversion/subst *)
    des - vlᶠ as [| vᶠ vlᶠ]:
          ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          eᶠ elᶠ eₓᶠ vᶠ vlᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v IHFse_nth].
    (* #7 Pose From Nth to Result: apply/pose *)
    app - length_cons in Hlen.
    pose proof create_result_ivalues
          vᶠ vlᶠ [] as Hcrt.
    pose proof fs_eval_nth_to_result
          IValues elᶠ eₓᶠ [] vᶠ vlᶠ vₓᶠ (RValSeq (vᶠ :: vlᶠ))
          [] [] Hlen Hcrt IHFse_nth
          as IHFse_vl.
    clr - Hlen Hcrt IHFse_nth eₓᶠ vₓᶠ.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v  as [k_v [_ Hstp_v]].
    des - IHFse_vl as [k_vl   Hstp_vl].
    (* #9 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_v / eᶠ k_v.
    step - Hstp_vl.
  Qed.






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






  Theorem eq_bsfs_evalues_to_exception :
    forall Γ elᴮ eₓᴮ vlᴮ vₓᴮ qₖᴮ,
        length vlᴮ < length elᴮ
    ->  (forall i,
            i < length vlᴮ
        ->  ⟨ [], erase_names Γ (nth i elᴮ eₓᴮ) ⟩ -->*
                  erase_valseq [nth i vlᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (nth (length vlᴮ) elᴮ eₓᴮ) ⟩ -->* erase_exc qₖᴮ
    ->  ⟨ [], erase_names Γ (EValues elᴮ) ⟩ -->* erase_exc qₖᴮ.
  Proof.
    itr - Γ elᴮ eₓᴮ vlᴮ vₓᴮ qₖᴮ Hlen IHFse_nth IHFse_qₖ.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack:
          remember/pose/rewrite + exact *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val' (map snd Γ)) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ elᴮ eₓᴮ vlᴮ vₓᴮ IHFse_nth.
    rwr - fs_eval_nth_map_erase_single in IHFse_qₖ.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - elᶠ eₓᶠ as Heqv_el Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) elᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in Hlen.
          2: exa - Heqv_el.
          clr - Heqv_el elᴮ σ ξ.
    (*Value*)
    rem - vlᶠ vₓᶠ qₖᶠ as Heqv_vl Heqv_vₓ Heqv_qₖ / Heqv_vₓ Heqv_qₖ vₓᴮ qₖᴮ:
          (map erase_val' vlᴮ)
          (erase_val' vₓᴮ)
          (erase_exc qₖᴮ).
    erewrite length_map_erase_val_eq in *.
          2-4: exa - Heqv_vl.
          clr - Heqv_vl vlᴮ.
    (* #3 Split Expression List: pose/destruct/subst *)
    psc - length_lt_split_middle as Hsplit:
          Val Exp vlᶠ elᶠ Hlen.
    des - Hsplit as [el₁ᶠ [eₖᶠ [el₂ᶠ [Hel Hlen]]]].
    sbt.
    (* #4 Simplify Hypothesis: *)
    rwr - Hlen in IHFse_qₖ.
    smp - IHFse_qₖ.
    rwr - nth_middle in IHFse_qₖ.
    (* #5 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - el₁ᶠ as [| eᶠ el₁ᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth eₓᶠ vₓᶠ.
          (* #5.1 Both List Empty: rewrite/subst/simpl *)
          app - length_empty_fst in Hlen.
          sbt.
          smp.
          (* #5.2 Destruct Inductive Hypothesis: destruct *)
          des - IHFse_qₖ as [k_qₖ [Hscp_qₖ Hstp_qₖ]].
          (* #5.3 FrameStack Evaluation: open/step *)
          open / Hscp_qₖ.
          step - Hstp_qₖ / eₖᶠ k_qₖ.
          step.
    } (* - Cons List Branch *)
    (* #6 Both List Cons: destruct + inversion/subst *)
    des - vlᶠ as [| vᶠ vlᶠ]:
          ivs - Hlen.
    (* #7 Pose Nth Cons Theorem: rewrite/pose/destruct *)
    rewrite cons_app with (l := el₁ᶠ) in IHFse_nth.
    rwl - app_assoc in IHFse_nth.
    do 2 rwl - cons_app in IHFse_nth.
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          eᶠ (el₁ᶠ ++ eₖᶠ :: el₂ᶠ) eₓᶠ vᶠ vlᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v IHFse_nth].
    (* #8 Pose From Nth to Result: apply/pose/simple *)
    app - length_cons in Hlen.
    pose proof fs_eval_nth_to_partial
          IValues el₁ᶠ eₖᶠ el₂ᶠ eₓᶠ [] vᶠ vlᶠ vₓᶠ Hlen IHFse_nth
          as IHFse_vl.
    smp / Hlen IHFse_nth eₓᶠ vₓᶠ.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v  as [k_v  [_       Hstp_v]].
    des - IHFse_vl as [k_vl          Hstp_vl].
    des - IHFse_qₖ as [k_qₖ [Hscp_qₖ Hstp_qₖ]].
    (* #10 FrameStack Evaluation: open/step *)
    open / Hscp_qₖ.
    step - Hstp_v  / eᶠ k_v.
    step - Hstp_vl / el₁ᶠ k_vl.
    step - Hstp_qₖ / k_qₖ.
    step.
  Qed.



End EValues.









Section ETuple.



  Theorem eq_bsfs_etuple_to_vtuple :
    forall Γ elᴮ eₓᴮ vlᴮ vₓᴮ,
        length elᴮ = length vlᴮ
    ->  (forall i,
            i < length elᴮ
        ->  ⟨ [], erase_names Γ (nth i elᴮ eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i vlᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (ETuple elᴮ) ⟩ -->* erase_valseq [VTuple vlᴮ].
  Proof.
    itr - Γ elᴮ eₓᴮ vlᴮ vₓᴮ Hlen IHFse_nth.
    (* #0 Pre Formalize Hypothesis: rewrite/symmetry *)
    rwr - Hlen in IHFse_nth.
    sym - Hlen.
    (* #1 Unfold Converters: simpl/unfold/rewrite/mvr *)
    smp.
    ufl - erase_names
          erase_valseq in *.
    rwr - map_map.
    mvr.
    (* #2 Convert Syntax from BigStep to FrameStack:
          remember/pose/rewrite + exact *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val' (map snd Γ)) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ elᴮ eₓᴮ vlᴮ vₓᴮ IHFse_nth.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - elᶠ eₓᶠ as Heqv_el Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) elᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in Hlen.
          2: exa - Heqv_el.
          clr - Heqv_el elᴮ σ ξ.
      (* Values *)
    rem - vlᶠ vₓᶠ as Heqv_vl Heqv_vₓ / Heqv_vₓ vₓᴮ:
          (map erase_val' vlᴮ)
          (erase_val' vₓᴮ).
    erewrite length_map_erase_val_eq in *.
          2-3: exa - Heqv_vl.
          clr - Heqv_vl vlᴮ.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp':
          elᶠ eₓᶠ vlᶠ vₓᶠ Hlen IHFse_nth.
    psc - scope_list_to_tuple as Hscp: vlᶠ Hscp'.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - elᶠ as [| eᶠ elᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth Hscp eₓᶠ vₓᶠ.
          (* #4.1 Both List Empty: apply/subst *)
          app - length_empty_fst in Hlen.
          sbt.
          (* #4.2 FrameStack Evaluation: open/step *)
          open.
          step.
    } (* - Cons List Branch *)
    (* #5 Both List Cons: destruct + inversion/subst *)
    des - vlᶠ as [| vᶠ vlᶠ]:
          ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          eᶠ elᶠ eₓᶠ vᶠ vlᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v IHFse_nth].
    (* #7 Pose From Nth to Result: apply/pose *)
    app - length_cons in Hlen.
    pose proof create_result_ituple
          vᶠ vlᶠ [] as Hcrt.
    pose proof fs_eval_nth_to_result
          ITuple elᶠ eₓᶠ [] vᶠ vlᶠ vₓᶠ (RValSeq [Syntax.VTuple (vᶠ :: vlᶠ)])
          [] [] Hlen Hcrt IHFse_nth
          as IHFse_vl.
    clr - Hlen Hcrt IHFse_nth eₓᶠ vₓᶠ.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v  as [k_v [_ Hstp_v]].
    des - IHFse_vl as [k_vl   Hstp_vl].
    (* #9 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_v / eᶠ k_v.
    step - Hstp_vl.
  Qed.






  Theorem eq_bsfs_etuple_to_exception :
    forall Γ elᴮ eₓᴮ vlᴮ vₓᴮ qₖᴮ,
        length vlᴮ < length elᴮ
    ->  (forall i,
            i < length vlᴮ
        ->  ⟨ [], erase_names Γ (nth i elᴮ eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i vlᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (nth (length vlᴮ) elᴮ eₓᴮ) ⟩ -->* erase_exc qₖᴮ
    ->  ⟨ [], erase_names Γ (ETuple elᴮ) ⟩ -->* erase_exc qₖᴮ.
  Proof.
    itr - Γ elᴮ eₓᴮ vlᴮ vₓᴮ qₖᴮ Hlen IHFse_nth IHFse_qₖ.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack:
          remember/pose/rewrite + exact *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (from_env Γ).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val' (map snd Γ)) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ elᴮ eₓᴮ vlᴮ vₓᴮ IHFse_nth.
    rwr - fs_eval_nth_map_erase_single in IHFse_qₖ.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - elᶠ eₓᶠ as Heqv_el Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) elᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in Hlen.
          2: exa - Heqv_el.
          clr - Heqv_el elᴮ σ ξ.
    (*Value*)
    rem - vlᶠ vₓᶠ qₖᶠ as Heqv_vl Heqv_vₓ Heqv_qₖ / Heqv_vₓ Heqv_qₖ vₓᴮ qₖᴮ:
          (map erase_val' vlᴮ)
          (erase_val' vₓᴮ)
          (erase_exc qₖᴮ).
    erewrite length_map_erase_val_eq in *.
          2-4: exa - Heqv_vl.
          clr - Heqv_vl vlᴮ.
    (* #3 Split Expression List: pose/destruct/subst *)
    psc - length_lt_split_middle as Hsplit:
          Val Exp vlᶠ elᶠ Hlen.
    des - Hsplit as [el₁ᶠ [eₖᶠ [el₂ᶠ [Hel Hlen]]]].
    sbt.
    (* #4 Simplify Hypothesis: *)
    rwr - Hlen in IHFse_qₖ.
    smp - IHFse_qₖ.
    rwr - nth_middle in IHFse_qₖ.
    (* #5 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - el₁ᶠ as [| eᶠ el₁ᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth eₓᶠ vₓᶠ.
          (* #5.1 Both List Empty: rewrite/subst/simpl *)
          app - length_empty_fst in Hlen.
          sbt.
          smp.
          (* #5.2 Destruct Inductive Hypothesis: destruct *)
          des - IHFse_qₖ as [k_qₖ [Hscp_qₖ Hstp_qₖ]].
          (* #5.3 FrameStack Evaluation: open/step *)
          open / Hscp_qₖ.
          step - Hstp_qₖ / eₖᶠ k_qₖ.
          step.
    } (* - Cons List Branch *)
    (* #6 Both List Cons: destruct + inversion/subst *)
    des - vlᶠ as [| vᶠ vlᶠ]:
          ivs - Hlen.
    (* #7 Pose Nth Cons Theorem: rewrite/pose/destruct *)
    rewrite cons_app with (l := el₁ᶠ) in IHFse_nth.
    rwl - app_assoc in IHFse_nth.
    do 2 rwl - cons_app in IHFse_nth.
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          eᶠ (el₁ᶠ ++ eₖᶠ :: el₂ᶠ) eₓᶠ vᶠ vlᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v IHFse_nth].
    (* #8 Pose From Nth to Result: apply/pose/simple *)
    app - length_cons in Hlen.
    pose proof fs_eval_nth_to_partial
          ITuple el₁ᶠ eₖᶠ el₂ᶠ eₓᶠ [] vᶠ vlᶠ vₓᶠ Hlen IHFse_nth
          as IHFse_vl.
    smp / Hlen IHFse_nth eₓᶠ vₓᶠ.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v  as [k_v  [_       Hstp_v]].
    des - IHFse_vl as [k_vl          Hstp_vl].
    des - IHFse_qₖ as [k_qₖ [Hscp_qₖ Hstp_qₖ]].
    (* #10 FrameStack Evaluation: open/step *)
    open / Hscp_qₖ.
    step - Hstp_v  / eᶠ k_v.
    step - Hstp_vl / el₁ᶠ k_vl.
    step - Hstp_qₖ / k_qₖ.
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
      (length vll') (length ell') 2 2 Hlen eq_refl as Hlen₂.
    do 2 rewrite <- length_flatten_list in Hlen₂.
    ren - Hlen_flat: Hlen₂.
    cwl - Hlen_flat in IHnth'.
    (* #1 Unfold Converters: simpl/unfold/rewrite/mvr *)
    pose proof flatten_deflatten ell' as Hell'.
    pose proof flatten_deflatten vll' as Hvll'.
    cwl - Hell' Hvll'.
    smp *.
    do 3 rwr - deflatten_map.
    rwr - map_map.
    mvr.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember;unfold;symmetry;rewrite;exact *)
      (* Erasers *)
    rem - σ as Heqv_σ:
      (from_env Γ);
      clr - Heqv_σ.
      (* Substs *)
    rem - ξ as Heqv_ξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Heqv_ξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth:
      σ ξ (flatten_list ell') ErrorExp (flatten_list vll') ErrorValue IHnth'.
    do 2 rwr - flatten_map in *.
      (* Expressions *)
    rem - ell ex as Hell Hex:
      (map (λ '(x, y), ((erase_exp σ x).[ξ], (erase_exp σ y).[ξ])) ell')
      ((erase_exp σ ErrorExp).[ξ]);
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
      (length vll) (length ell) 2 2 Hlen eq_refl as Hlen₂.
    do 2 rewrite <- length_flatten_list in Hlen₂.
    clr - Hlen.
    ren - Hlen: Hlen₂.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp':
      (flatten_list ell) ex (flatten_list vll) vx Hlen IHnth.
    psc - scope_list_to_map as Hscp: vll Hscp'.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - ell as [| [e₁ e₂] ell].
    { (* - Empty List Branch *)
      clr - IHnth Hscp.
      (* #4.1 Both List Empty: simpl/rewrite/subst *)
      smp - Hlen.
      rwr - length_zero_iff_nil in Hlen.
      pose proof flatten_deflatten vll as Hvll.
      rwr - Hlen in Hvll.
      smp *.
      sbt.
      clr - Hlen.
      (* #4.2 FrameStack Evaluation: open/step *)
      open.
      step.
    } (* - Cons List Branch *)
    (* #5 Both List Cons: destruct + inversion/subst *)
    des - vll as [| [v₁ v₂] vll]: ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    do 2 rwr - flatten_cons in *.
    psc - fs_eval_nth_cons as Hnth_cons:
      e₁ (e₂ :: flatten_list ell) ex v₁ (v₂ :: flatten_list vll) vx IHnth.
    des - Hnth_cons as [IHeqv_v₁ IHnth].
    psc - fs_eval_nth_cons as Hnth_cons:
      e₂ (flatten_list ell) ex v₂ (flatten_list vll) vx IHnth.
    des - Hnth_cons as [IHeqv_v₂ Hnth].
    (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
    smp - Hlen.
    do 2 rwr - Nat.succ_inj_wd in Hlen.
    pose proof create_result_imap
      v₁ v₂ vll [] as Hcrt.
    pse - all_fsval_is_wfm as Hwfm: (Syntax.VMap ((v₁, v₂) :: vll)).
    des - Hwfm as [Hwfm _].
    cwl - Hwfm in Hcrt.
    pose proof fs_eval_nth_to_result
      IMap (flatten_list ell) ex [v₁] v₂ (flatten_list vll) vx
      (RValSeq [Syntax.VMap ((v₁, v₂) :: vll)]) [] [] Hlen Hcrt Hnth
      as IHvll.
    clr - Hlen Hcrt Hnth.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHeqv_v₁ as [kv₁ [_ Hstp_v₁]].
    des - IHeqv_v₂ as [kv₂ [_ Hstp_v₂]].
    des - IHvll as [kvll Hstp_vll].
    (* #9 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_v₁.
    step - Hstp_v₂.
    step - Hstp_vll.
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
    (* #1 Unfold Converters: simpl/unfold/rewrite/mvr *)
    pose proof flatten_deflatten ell' as Hell'.
    cwl - Hell'.
    smp.
    do 2 rwr - deflatten_map.
    rwr - map_map.
    mvr.
    ufl - erase_names in *.
    (* #2 Convert Syntax from BigStep to FrameStack: remember;unfold;symmetry;rewrite;exact *)
      (* Erasers *)
    rem - σ as Heqv_σ:
      (from_env Γ);
      clr - Heqv_σ.
      (* Substs *)
    rem - ξ as Heqv_ξ:
      (list_subst (map erase_val' (map snd Γ)) idsubst);
      clr - Heqv_ξ Γ.
    psc - fs_eval_nth_map_erase_forall as IHnth:
      σ ξ (flatten_list ell') ErrorExp (flatten_list vll' ++ ov') ErrorValue IHnth'.
    rwr - fs_eval_nth_map_erase_single in IHxk.
    rwr - map_app in IHnth.
    rwr - flatten_map in *.
    rwr - flatten_map in IHnth.
      (* Expressions *)
    rem - ell ex as Hell Hex:
      (map (λ '(x, y), ((erase_exp σ x).[ξ], (erase_exp σ y).[ξ])) ell')
      ((erase_exp σ ErrorExp).[ξ]);
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
      (length vll) (length ell) 2 2 Hlen eq_refl as Hlen₂.
    do 2 rewrite <- length_flatten_list in Hlen₂.
    clr - Hlen.
    ren - Hlen: Hlen₂. *)
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
      (length vll) (length ell1) 2 2 Hlen eq_refl as Hlen₂.
    do 2 rewrite <- length_flatten_list in Hlen₂.
    rwr - length_app in IHov IHxk.
    rwr - Hlen₂ in IHov IHxk.
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
      ren - Hlen: Hlen₂.
      (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
      des - ell1 as [| [e₁ e₂] ell1].
      { (* - Empty List Branch *)
        clr - IHnth Hlen.
        smp.
        des - IHxk as [kxk [Hscp_xk Hstp_xk]].
        open / Hscp_xk.
        step - Hstp_xk.
        step.
      } (* - Cons List Branch *)
      (* #5 Both List Cons: destruct + inversion/subst *)
      des - vll as [| [v₁ v₂] vll]: ivs - Hlen.
      (* #6 Pose Nth Cons Theorem: pose/destruct *)
      do 2 rwr - flatten_cons in *.
      psc - fs_eval_nth_cons as Hnth_cons:
        e₁ (e₂ :: flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v₁ (v₂ :: flatten_list vll) vx IHnth.
      des - Hnth_cons as [IHeqv_v₁ IHnth].
      psc - fs_eval_nth_cons as Hnth_cons:
        e₂ (flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v₂ (flatten_list vll) vx IHnth.
      des - Hnth_cons as [IHeqv_v₂ Hnth].
      (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
      smp - Hlen.
      do 2 rwr - Nat.succ_inj_wd in Hlen.
      pose proof fs_eval_nth_to_partial
        IMap (flatten_list ell1) ekev (ekod :: flatten_list ell2) ex
        [v₁] v₂ (flatten_list vll) vx Hlen Hnth
        as IHvll.
      clr - Hlen Hnth.
      rwl - cons_app in *.
      (* #8 Destruct Inductive Hypothesis: destruct *)
      des - IHeqv_v₁ as [kv₁ [_ Hstp_v₁]].
      des - IHeqv_v₂ as [kv₂ [_ Hstp_v₂]].
      des - IHvll as [kvll Hstp_vll].
      des - IHxk as [kxk [Hscp_xk Hstp_xk]].
      (* #9 FrameStack Evaluation: open/step *)
      open / Hscp_xk.
      step - Hstp_v₁.    rwr - flatten_app.
      step - Hstp_v₂.
      step - Hstp_vll.
      step - Hstp_xk.
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
      rwl - Hlen₂ in IHov.
      rwr - app_nth2_plus in IHov.
      smp - IHov.
      (*xk*)
      smp - IHxk.
      clr - Hlen Hlen_vll Hlen_ell.
      ren - Hlen: Hlen₂.
      (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
      des - ell1 as [| [e₁ e₂] ell1].
      { (* - Empty List Branch *)
        clr - IHnth Hlen.
        smp.
        des - IHov as [kv_even [Hscp_v_even Hstp_v_even]].
        des - IHxk as [kx_odd [Hscp_x_odd Hstp_x_odd]].
        open / Hscp_x_odd.
        step - Hstp_v_even.
        step - Hstp_x_odd.
        step.
      } (* - Cons List Branch *)
      (* #5 Both List Cons: destruct + inversion/subst *)
      des - vll as [| [v₁ v₂] vll]: ivs - Hlen.
      (* #6 Pose Nth Cons Theorem: pose/destruct *)
      do 2 rwr - flatten_cons in *.
      psc - fs_eval_nth_cons as Hnth_cons:
        e₁ (e₂ :: flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v₁ (v₂ :: flatten_list vll ++ [vkev]) vx IHnth.
      des - Hnth_cons as [IHeqv_v₁ IHnth].
      psc - fs_eval_nth_cons as Hnth_cons:
        e₂ (flatten_list ell1 ++ ekev :: ekod :: flatten_list ell2)
        ex v₂ (flatten_list vll ++ [vkev]) vx IHnth.
      des - Hnth_cons as [IHeqv_v₂ Hnth].
      (* #7 Pose From Nth to Result: simpl/rewrite/pose *)
      smp - Hlen.
      do 2 rwr - Nat.succ_inj_wd in Hlen.
      ass >
        (length (flatten_list vll ++ [vkev]) =
         length (flatten_list ell1 ++ [ekev]))
         as Hlen₁:
        do 2 rwr - length_app; sli.
      Check cons_app.
      rewrite cons_app with (x := ekev) in Hnth.
      rwr - app_assoc in Hnth.
      pose proof fs_eval_nth_to_partial
        IMap (flatten_list ell1 ++ [ekev]) ekod (flatten_list ell2) ex
        [v₁] v₂ (flatten_list vll ++ [vkev]) vx Hlen₁ Hnth
        as IHvll.
      rwl - app_assoc in IHvll.
      clr - Hlen Hnth.
      rwl - cons_app in *.
      (* #8 Destruct Inductive Hypothesis: destruct *)
      des - IHeqv_v₁ as [kv₁ [_ Hstp_v₁]].
      des - IHeqv_v₂ as [kv₂ [_ Hstp_v₂]].
      des - IHvll as [kvll Hstp_vll].
      des - IHov as [kov [Hscp_ov Hstp_ov]].
      des - IHxk as [kxk [Hscp_xk Hstp_xk]].
      (* #9 FrameStack Evaluation: open/step *)
      open / Hscp_xk.
      step - Hstp_v₁.    rwr - flatten_app.
      step - Hstp_v₂.
      step - Hstp_vll.
      step - Hstp_xk.
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
    forall Γ modules own_module id id' eᴮ rᴮ eff eff',
        (eval_expr Γ modules own_module id eᴮ eff id' rᴮ eff')
    ->  ⟨ [], (erase_names Γ eᴮ) ⟩ -->*erase_result rᴮ.
  Proof.
    itr - Γ modules own_module id id' eᴮ rᴮ eff eff' B.
    ind - B;
      itr; ren - Γ: env;
      try rwr - erase_result_to_valseq in *;
      try rwr - erase_result_to_exception in *.
    (* #1 Atoms: ENil/ENil *)
      (* +1.1 ENil: *)
          3: {
            clr - modules own_module eff id.
            bse - eq_bsfs_enil_to_vnil:
                  Γ.
          }
      (* +1.2 ELit: *)
          3: {
            clr - modules own_module eff id.
            ren - litᴮ: l.
            bse - eq_bsfs_elit_to_vlit:
                  Γ litᴮ.
          }
    (* #2 References: EVar/EFunId *)
      (* +2.1 EVar: *)
          3: {
            ren - xᴮ rᴮ Hget: s res H.
            pse - evar_is_result as Hv:
                  Γ modules own_module xᴮ rᴮ id eff Hget;
                  clr - modules own_module id eff.
            des - Hv as [vᴮ [Heq Hscp]]; sbt.
            bse - eq_bsfs_evar_to_value:
                  Γ xᴮ vᴮ Hget Hscp.
          }
      (* +2.2 EFunId: success/modfunc *)
        (* -2.2.1 success: *)
          3: {
            ren - fᴮ rᴮ Hget: fid res H.
            pse - efunid_is_result as Hv:
                  Γ modules own_module fᴮ rᴮ id eff Hget;
                  clr - modules own_module id eff.
            des - Hv as [vᴮ [Heq Hscp]]; sbt.
            bse - eq_bsfs_efunid_to_value:
                  Γ fᴮ vᴮ Hget Hscp.
          }
        (* -2.2.2 modfunc: *)
          3: {
            clr - eff H H1 H2.
            pse - no_modfunc; con.
          }
    (* #3 Sequences: ECons/ESeq *)
      (* +3.1 ECons: success/exception1/exception2 *)
        (* -3.1.1 success: *)
          5: {
            ren - e1 e2 v1 v2 IHFv1 IHFv2 IHBv1 IHBv2:
                  hd tl hdv tlv IHB2 IHB1 B2 B1.
            bse - eq_bsfs_econs_to_vcons:
                  Γ e1 e2 v1 v2 IHFv1 IHFv2.
          }
        (* -3.1.2 exception1: *)
          15: {
            ren - e₁ e2 q₁ v2 IHFq₁ IHFv2 IHBq₁ IHBv2:
                  hd tl ex vtl IHB2 IHB1 B2 B1.
            bse - eq_bsfs_econs_to_exception1:
                  Γ e₁ e2 q₁ v2 IHFq₁ IHFv2.
          }
        (* -3.1.3 exception2: *)
          14: {
            ren - e₁ e2 q₂ IHFq₂ IHBq₂:
                  hd tl ex IHB B.
            bse - eq_bsfs_econs_to_exception2:
                  Γ e₁ e2 q₂ IHFq₂.
          }
      (* +3.2 ESeq: success/exception *)
        (* -3.2.1 success: *)
          11: {
            ren - r₂ IHFv1 IHFr₂ IHBv1 IHBr₂:
                  v2 IHB1 IHB2 B1 B2.
            bse - eq_bsfs_eseq_to_result:
                  Γ e1 e2 v1 r₂ IHFv1 IHFr₂.
          }
        (* -3.2.2 exception: *)
          30: {
            ren - q₁ IHFq₁ IHBq₁ :
                  ex IHB B.
            bse - eq_bsfs_eseq_to_exception:
                  Γ e1 e2 q₁ IHFq₁.
          }
    (* #4 Functions: EFun/ELetrec *)
      (* +4.1 EFun: *)
          3: {
            ren - vars:
                  vl.
            pse - efun_is_result as Hscp:
                   Γ modules own_module vars e id eff.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_efun_to_vclos:
                  Γ vars e id Hscp.
          }
      (* +4.2 ELetrec: *)
         10:  admit.
    (* #5 Binders: ELet/ETry *)
      (* +5.1 ELet: success/exception *)
        (* -5.1.1 success: *)
          9: {
            ren - xs₁ vs₁ r₂ Hlen₁ IHFvs₁ IHFr₂ IHBvs₁ IHBr₂:
                  l vals res H IHB1 IHB2 B1 B2.
            bse - eq_bsfs_elet_to_result:
                  Γ xs₁ e1 e2 vs₁ r₂ Hlen₁ IHFvs₁ IHFr₂.
          }
        (* -5.1.2 exception: *)
          26: {
            ren - xs₁ q₁ IHFq₁ IHBq₁:
                  vl ex IHB B.
            bse - eq_bsfs_elet_exc: Γ xs₁ e1 e2 q₁ IHFq₁.
          }
      (* +5.2 ETry: result1/result2 *)
        (* -5.2.1 result1: *)
          11: {
            ren - xs₁ xs₂ vs₁ r₂ Hlen₁ IHFvs₁ IHFr₂ IHBvs₁ IHBr₂:
                  vl1 vl2 vals res H IHB1 IHB2 B1 B2.
            bse - eq_bsfs_etry_to_result1:
                  Γ xs₁ xs₂ e1 e2 e3 vs₁ r₂ Hlen₁ IHFvs₁ IHFr₂.
          }
        (* -5.2.2 result: *)
          11: {
            ren - xs₁ xs₂ q₁ r₃ IHFq₁ IHFr₃ IHBq₁ IHBr₃:
                  vl1 vl2 ex res IHB1 IHB2 B1 B2.
            ren - eff eff' eff'':
                  eff1 eff2 eff3.
            rwr - exc_to_vals_eq in *.
            pse - etry_catch_vars_length as Hlen₂:
                  Γ modules own_module xs₁ xs₂ e1 e2 e3 q₁ r₃
                  id id' id'' eff eff' eff'' IHBq₁ IHBr₃.
            bse - eq_bsfs_etry_to_result2:
                  Γ xs₁ xs₂ e1 e2 e3 q₁ r₃ Hlen₂ IHFq₁ IHFr₃.
          }
    (* #6 Lists: EValues/ETuple/EMap *)
      (* +6.1 EValues: valseq/exception *)
        (* -6.1.1 valseq: *)
          1: {
            ren - el vl Hlen IHFnth:
                  exps vals H H3.
            bse - eq_bsfs_evalues_to_valseq:
                  Γ el ErrorExp vl ErrorValue Hlen IHFnth.
          }
        (* -6.1.2 exception: *)
          1:  {
            ren - el vl xk Hlen IHFnth IHFxk:
                  exps vals ex H H4 IHB.
            subst.
            bse - eq_bsfs_evalues_to_exception:
                  Γ el ErrorExp vl ErrorValue xk Hlen IHFnth IHFxk.
          }
      (* +6.2 ETuple: valseq/exception *)
        (* -6.2.1 valseq: *)
          1:  {
            ren - el vl Hlen IHFnth:
                  exps vals H H3.
            bse - eq_bsfs_etuple_to_vtuple:
                  Γ el ErrorExp vl ErrorValue Hlen IHFnth.
          }
        (* -6.2.2 exception: *)
          7:  {
            ren - el vl xk Hlen IHFnth IHFxk:
                  exps vals ex H H4 IHB.
            subst.
            bse - eq_bsfs_etuple_to_exception:
                  Γ el ErrorExp vl ErrorValue xk Hlen IHFnth IHFxk.
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