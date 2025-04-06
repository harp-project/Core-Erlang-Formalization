From CoreErlang.Eqvivalence.BsFs Require Import B4Helpers.

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
    + eq_bsfs_evalues_to_valseq
    + eq_bsfs_evalues_to_exception
  - Tuple
    + eq_bsfs_etuple_to_vtuple
    + eq_bsfs_etuple_to_exception
  - Map
    + eq_bsfs_emap_to_vmap
    + eq_bsfs_emap_to_exception
* EQBSFS_ COMPOUNDS (THEOREMS)
  - PrimOp
    + eq_bsfs_eprimop_to_result
    + eq_bsfs_eprimop_to_exception
  - Apply
    + eq_bsfs_eapply_to_result
    + eq_bsfs_eapply_to_exception1
    + eq_bsfs_eapply_to_exception2
    + eq_bsfs_eapply_to_badfun1
    + eq_bsfs_eapply_to_badfun2
  - Call
    + eq_bsfs_ecall_to_result1
    + eq_bsfs_ecall_to_result2
    + eq_bsfs_ecall_to_exception1
    + eq_bsfs_ecall_to_exception2
    + eq_bsfs_ecall_to_exception3
    + eq_bsfs_ecall_to_badarg1
    + eq_bsfs_ecall_to_badarg2
  - Case
    + eq_bsfs_ecase_to_result
    + eq_bsfs_ecase_to_exception1
    + eq_bsfs_ecase_to_exception2
    + eq_bsfs_ecase_to_ifclause
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



(*
⟨ [], ᴱ′(δₑᶠ(ᵉ[]ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([ᵛ[]ᴮ]))

*)
(*Empty list evaluates to a value sequence in frame stack*)
(*bsfs.enil*)
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



(*
⟨ [], ᴱ′(δₑᶠ(ᵉᴸlᴮᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([ᵛᴸlᴮᴮ]))
*)
(*Literal evaluates to a value sequence in frame stack:*)
(*bsfs.elit*)
  Theorem eq_bsfs_elit_to_vlit :
    forall Γ lᴮ ,
      ⟨ [], erase_names Γ (ELit lᴮ) ⟩ -->* erase_valseq [VLit lᴮ].
  Proof.
    itr.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - lᶠ as Hl / Hl lᴮ Γ:
      (convert_lit lᴮ).
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


(*
Hget : Γ[↤ xᴮ] = Some [vᴮ]
Hscp : VALCLOSED δᵥᶠ(vᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉˣxᴮᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([vᴮ]))
*)
(*Variable evaluates to a value sequence in frame stack:*)
(*bsfs.evar*)
  Theorem eq_bsfs_evar_to_value :
    forall Γ xᴮ vᴮ,
        get_value Γ (inl xᴮ) = Some [vᴮ]
    ->  VALCLOSED (erase_val vᴮ)
    ->  ⟨ [], erase_names Γ (EVar xᴮ) ⟩ -->* erase_valseq [vᴮ].
  Proof.
    itr - Γ xᴮ vᴮ Hget Hscp.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - vᶠ as Heqv_v:
      (erase_val vᴮ).
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
      rwr - apply_eraser_cons.
      rwr - var_funid_eqb_refl.
      smp / Γ xᴮ.
      cwl - Heqv_v / vᴮ.
      (* #I/3 FrameStack Evaluation: open/step *)
      open.
      step.
    * (* +II. Get Value in the Tail: *)
      clr - Hscp Heqv_v.
      (* #II/1 Simplify by Lemmas: rewrite/simpl *)
      rwr - apply_eraser_cons.
      cwr - Heqb.
      smp / k₁ᴮ v₁ᴮ.
      (* #II/2 Solve by Inductive Hypothesis: specialize/exact *)
      spc - IHΓ: Hget / vᴮ.
      exa - IHΓ.
  Qed.



End EVar.















Section EFunId.



(*
Hget : Γ[fᴮ ↦] = Some [vᴮ]
Hscp : VALCLOSED δᵥᶠ(vᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉᶠfᴮᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([vᴮ]))
*)
(*Function identifier evaluates to a value sequence in frame stack:*)
(*bsfs.efunid*)
  Theorem eq_bsfs_efunid_to_value :
    forall Γ fᴮ vᴮ,
        get_value Γ (inr fᴮ) = Some [vᴮ]
    ->  VALCLOSED (erase_val vᴮ)
    ->  ⟨ [], erase_names Γ (EFunId fᴮ) ⟩ -->* erase_valseq [vᴮ].
  Proof.
    itr - Γ fᴮ vᴮ Hget Hscp.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - vᶠ as Heqv_v:
      (erase_val vᴮ).
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
      rwr - apply_eraser_cons.
      rwr - var_funid_eqb_refl.
      smp / Γ fᴮ.
      cwl - Heqv_v / vᴮ.
      (* #I/3 FrameStack Evaluation: open/step *)
      open.
      step.
    * (* +II. Get Value in the Tail: *)
      clr - Hscp Heqv_v.
      (* #II/1 Simplify by Lemmas: rewrite/simpl *)
      rwr - apply_eraser_cons.
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


(*
IHFse_v₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([v₁ᴮ]))
IHFse_v₂ : ⟨ [], ᴱ′(δₑᶠ(e₂ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([v₂ᴮ]))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ[e₁ᴮ|e₂ᴮ]ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([ᵛ[v₁ᴮ|v₂ᴮ]ᴮ]))
*)
(*List evaluates to a value sequence in frame stack:*)
(*bsfs.econs.vs*)
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
      (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - v₁ᶠ v₂ᶠ as Heqv_v₁ Heqv_v₂ / Heqv_v₁ Heqv_v₂ v₁ᴮ v₂ᴮ:
      (erase_val v₁ᴮ)
      (erase_val v₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [Hscp_v₁ Hstp_v₁]].
    des - IHFse_v₂ as [k_v₂ [Hscp_v₂ Hstp_v₂]].
    (* #4 FrameStack Evaluation: open;step *)
    open / Hscp_v₁ Hscp_v₂.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step.
  Qed.






(*
IHFse_q₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
IHFse_v₂ : ⟨ [], ᴱ′(δₑᶠ(e₂ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([v₂ᴮ]))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ[e₁ᴮ|e₂ᴮ]ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
*)
(*List evaluates to the exception of head in frame stack:*)
(*bsfs.econs.exc.head*)
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
      (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - q₁ᶠ v₂ᶠ as Heqv_q₁ Heqv_v₂ / Heqv_q₁ Heqv_v₂ q₁ᴮ v₂ᴮ:
      (erase_exc q₁ᴮ)
      (erase_val v₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_q₁ as [k_q₁ [Hscp_q₁ Hstp_q₁]].
    des - IHFse_v₂ as [k_v₂ [Hscp_v₂ Hstp_v₂]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_q₁ Hscp_v₂.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    step - Hstp_q₁ / e₁ᶠ k_q₁.
    step.
  Qed.






(*
IHFse_q₂ : ⟨ [], ᴱ′(δₑᶠ(e₂ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₂ᴮ))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ[e₁ᴮ|e₂ᴮ]ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₂ᴮ))
*)
(*List evaluates to the exception of tail in frame stack:*)
(*bsfs.econs.exc.tail*)
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
      (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
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



(*
IHFse_v₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([v₁ᴮ]))
IHFse_r₂ : ⟨ [], ᴱ′(δₑᶠ(e₂ᴮ ⇓ Γ)) ⟩ -->* δᶠ(r₂ᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉdoᴮ e₁ᴮ e₂ᴮ ⇓ Γ)) ⟩ -->* δᶠ(r₂ᴮ)
*)
(*Sequence evaluates to the result of second in frame stack: *)
(*bsfs.eseq.result.second*)
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
      (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - v₁ᶠ r₂ᶠ as Heqv_v₁ Heqv_r₂ / Heqv_v₁ Heqv_r₂ v₁ᴮ r₂ᴮ:
      (erase_val v₁ᴮ)
      (erase_result r₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [_       Hstp_v₁]].
    des - IHFse_r₂ as [k_r₂ [Hscp_r₂ Hstp_r₂]].
    (* #4 FrameStack Evaluation: open/step *)
    open / Hscp_r₂.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step - Hstp_r₂.
  Qed.






(*
IHFse_q₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉdoᴮ e₁ᴮ e₂ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
*)
(*Sequence evaluates to the exception of first in frame stack:*)
(*bsfs.eseq.exc.first*)
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
      (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
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



(*
Hscp : is_result ᵛˢ′(δᵥₗᶠ([ᵛ⟨id : [], xsᴮ, eᴮ, Γ⟩ᴮ]))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉfunᴮ(xsᴮ) -> eᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([ᵛ⟨id : [], xsᴮ, eᴮ, Γ⟩ᴮ]))
*)
(*Function evaluates to a value sequence in frame stack:*)
(*bsfs.efun.vs*)
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
    rwr - env_rem_ext_vars_nil_r
          eraser_add_ext_vars_nil_l
          in *.
    (* #3 Use Remove Vars Theorem: rewrite/pose *)
    rwr - erase_subst_rem_vars in *.
    (* #4 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (eraser_add_vars xsᴮ (Γ.keys)).
      (* Substs *)
    ufl - get_vals.
    rem - ξ as Heqv_ξ / Heqv_ξ:
      (upn (base.length xsᴮ)
           (list_subst (map erase_val (map snd Γ)) idsubst)).
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



(*
IHFse_r : ⟨ [], ᴱ′(δₑᶠ(eᴮ ⇓ append_funs_to_env extᴮ Γ id)) ⟩ -->* δᶠ(rᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉletrecᴮ extᴮ in eᴮ ⇓ Γ)) ⟩ -->* δᶠ(rᴮ)
*)
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
(erase_exp (add_expext ext (Γ.keys)) e).[upn
                                               (base.length
                                                  (map
                                                     (λ '(_, (vars, body)),
                                                        (base.length vars,
                                                         erase_exp
                                                           (add_expext_vars ext vars
                                                              (Γ.keys)) body)) ext))
                                               (list_subst (map erase_val Γ.vals)
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
                                                                (Γ.keys)) body)) ext) + n)
                                                                (list_subst
                                                                (map erase_val Γ.vals)
                                                                idsubst)]))
                                                                (map
                                                                (λ '(_, (vars, body)),
                                                                (base.length vars,
                                                                erase_exp
                                                                (add_expext_vars ext vars
                                                                (Γ.keys)) body)) ext))))
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



(*
Hlen₁ : ˡ|xs₁ᴮ| = ˡ|vs₁ᴮ|
IHFse_vs₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ(vs₁ᴮ))
IHFse_r₂ : ⟨ [], ᴱ′(δₑᶠ(e₂ᴮ ⇓ append_vars_to_env xs₁ᴮ vs₁ᴮ Γ)) ⟩ -->* δᶠ(r₂ᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉletᴮ<xs₁ᴮ> = e₁ᴮ in e₂ᴮ ⇓ Γ)) ⟩ -->* δᶠ(r₂ᴮ)
*)
(*Let evaluates to the result of second in frame stack:*)
(*bsfs.elet.result.second*)
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
      (Γ.keys).
    rem - σ₂ as Heqv_σ₂ / Heqv_σ₂:
      (eraser_add_vars xs₁ᴮ σ₁).
      (* Substs *)
    rwr - get_vals_eq in *.
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ₁ σ₂:
      (erase_exp σ₁ e₁ᴮ)
      (erase_exp σ₂ e₂ᴮ).
      (* Values *)
    ufl - erase_valseq in *.
    rem - vs₁ᶠ r₂ᶠ as Heqv_vs₁ Heqv_r₂ / Heqv_r₂ r₂ᴮ:
      (map erase_val vs₁ᴮ)
      (erase_result r₂ᴮ).
    erewrite length_map_erase_val_eq in Hlen₁.
    2: exa - Heqv_vs₁.
    clr - Heqv_vs₁ vs₁ᴮ.
      (* Variables *)
    rem - xsᶠ as Heqv_xs / Heqv_xs xs₁ᴮ:
      (base.length xs₁ᴮ).
    (* rem - e1 as He1 / He1 e₁ᶠ:
      (e₁ᶠ.[ξ]).
    rem - e2 as He2 / He2 e₂ᶠ ξ:
      (e₂ᶠ.[upn xsᶠ ξ]). *)
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_vs₁ as [k_vs₁ [_       Hstp_vs₁]].
    des - IHFse_r₂  as [k_r₂  [Hscp_r₂ Hstp_r₂]].
    (* #6 FrameStack Evaluation: open;step *)
    open / Hscp_r₂.
    step - Hstp_vs₁ / e₁ᶠ k_vs₁.
    step / Hlen₁.
    step - Hstp_r₂.
  Qed.






(*
IHFse_q₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉletᴮ<xs₁ᴮ> = e₁ᴮ in e₂ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
*)
(*Let evaluates to the exception of first in frame stack:*)
(*bsfs.elet.exc.first*)
  Theorem eq_bsfs_elet_exception :
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
      (Γ.keys).
    rem - σ₂ as Heqv_σ₂ / Heqv_σ₂:
      (eraser_add_vars xs₁ᴮ σ₁).
      (* Substs *)
    rem - ξ1 as Heqv_ξ1 / Heqv_ξ1 Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
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



(*
Hlen₁ : ˡ|xs₁ᴮ| = ˡ|vs₁ᴮ|
IHFse_vs₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ(vs₁ᴮ))
IHFse_r₂ : ⟨ [], ᴱ′(δₑᶠ(e₂ᴮ ⇓ append_vars_to_env xs₁ᴮ vs₁ᴮ Γ)) ⟩ -->* δᶠ(r₂ᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉtryᴮ e₁ᴮ of <xs₁ᴮ> -> e₂ᴮ catch <xs₂ᴮ> -> e₃ᴮ ⇓ Γ)) ⟩ -->* δᶠ(r₂ᴮ)
*)
(*Try evaluates to the result of second in frame stack:*)
(*bsfs.etry.result.second*)
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
      (Γ.keys).
    rem - σ₂ σ₃ as Heqv_σ₂ Heqv_σ₃ / Heqv_σ₂ Heqv_σ₃:
      (eraser_add_vars xs₁ᴮ σ₁)
      (eraser_add_vars xs₂ᴮ σ₁).
      (* Substs *)
    rwr - get_vals_eq in *.
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ e₃ᶠ as Heqv_e₁ Heqv_e₂ Heqv_e₃
      / Heqv_e₁ Heqv_e₂ Heqv_e₃ e₁ᴮ e₂ᴮ e₃ᴮ σ₁ σ₂ σ₃:
      (erase_exp σ₁ e₁ᴮ)
      (erase_exp σ₂ e₂ᴮ)
      (erase_exp σ₃ e₃ᴮ).
      (* Values *)
    ufl - erase_valseq in *.
    rem - vs₁ᶠ r₂ᶠ as Heqv_vs₁ Heqv_r₂ / Heqv_r₂ r₂ᴮ:
      (map erase_val vs₁ᴮ)
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






(*
Hlen₂ : ˡ|xs₂ᴮ| = 3
IHFse_q₁ : ⟨ [], ᴱ′(δₑᶠ(e₁ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(q₁ᴮ))
IHFse_r₃ : ⟨ [], ᴱ′(δₑᶠ(e₃ᴮ ⇓ append_vars_to_env xs₂ᴮ (q₁ᴮ ᶻ⇒ᵛˢ) Γ)) ⟩ -->* δᶠ(r₃ᴮ)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉtryᴮ e₁ᴮ of <xs₁ᴮ> -> e₂ᴮ catch <xs₂ᴮ> -> e₃ᴮ ⇓ Γ)) ⟩ -->* δᶠ(r₃ᴮ)
*)
(*Try evaluates to the result of third in frame stack:*)
(*bsfs.etry.result.third*)
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
      (Γ.keys).
    rem - σ₂ σ₃ as Heqv_σ₂ Heqv_σ₃ / Heqv_σ₂ Heqv_σ₃ xs₂ᴮ:
      (eraser_add_vars xs₁ᴮ σ₁)
      (eraser_add_vars xs₂ᴮ σ₁).
      (* Substs *)
    rwr - get_vals_eq in *.
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
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
      (erase_val (exclass_to_value c₁ᴮ))
      (erase_val vʳ₁ᴮ)
      (erase_val vᵈ₁ᴮ)
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



(*
Hlen : ˡ|esᴮ| = ˡ|vsᴮ|
IHFse_nth :
  ∀ i : nat,
    i < ˡ|esᴮ|
    → ⟨ [], ᴱ′(δₑᶠ(nth i esᴮ eₓᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([nth i vsᴮ vₓᴮ]))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ<esᴮ>ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ(vsᴮ))
*)
(*Values expression evaluates to a value sequence in frame stack:*)
(*bsfs.evalues.valseq*)
  Theorem eq_bsfs_evalues_to_valseq :
    forall Γ esᴮ eₓᴮ vsᴮ vₓᴮ,
        length esᴮ = length vsᴮ
    ->  (forall i,
            i < length esᴮ
        ->  ⟨ [], erase_names Γ (nth i esᴮ eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i vsᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (EValues esᴮ) ⟩ -->* erase_valseq vsᴮ.
  Proof.
    itr - Γ esᴮ eₓᴮ vsᴮ vₓᴮ Hlen IHFse_nth.
    (* #0 Pre Formalize Hypothesis: rewrite/symmetry *)
    rwr - Hlen in IHFse_nth.
    sym - Hlen.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names
          erase_valseq in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ esᴮ eₓᴮ vsᴮ vₓᴮ IHFse_nth.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - esᶠ eₓᶠ as Heqv_es Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) esᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in *.
          2: exa - Heqv_es.
          clr - Heqv_es esᴮ σ ξ.
      (* Values *)
    rem - vsᶠ vₓᶠ as Heqv_vs Heqv_vₓ / Heqv_vₓ vₓᴮ:
          (map erase_val vsᴮ)
          (erase_val vₓᴮ).
    erewrite length_map_erase_val_eq in *.
          2-3: exa - Heqv_vs.
          clr - Heqv_vs vsᴮ.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp:
          esᶠ eₓᶠ vsᶠ vₓᶠ Hlen IHFse_nth.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - esᶠ as [| e₁ᶠ esᶠ].
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
    des - vsᶠ as [| v₁ᶠ vsᶠ]:
          ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          e₁ᶠ esᶠ eₓᶠ v₁ᶠ vsᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v₁ IHFse_nth].
    (* #7 Pose From Nth to Result: apply/pose *)
    app - length_cons_eq in Hlen.
    pose proof create_result_ivalues
          v₁ᶠ vsᶠ [] as Hcrt.
    pose proof fs_eval_nth_to_result
          IValues esᶠ eₓᶠ [] v₁ᶠ vsᶠ vₓᶠ (RValSeq (v₁ᶠ :: vsᶠ))
          [] [] Hlen Hcrt IHFse_nth
          as IHFse_vs.
    clr - Hlen Hcrt IHFse_nth eₓᶠ vₓᶠ.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [_ Hstp_v₁]].
    des - IHFse_vs as [k_vs    Hstp_vs].
    (* #9 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step - Hstp_vs.
  Restart.
    itr - Γ esᴮ eₓᴮ vsᴮ vₓᴮ Hlen IHFse_nth.
    (* #0 Pre Formalize Hypothesis: rewrite/symmetry *)
    rwr - Hlen in IHFse_nth.
    sym - Hlen.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names
          erase_valseq in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ esᴮ eₓᴮ vsᴮ vₓᴮ IHFse_nth.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - esᶠ eₓᶠ as Heqv_es Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) esᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in *.
          2: exa - Heqv_es.
          clr - Heqv_es esᴮ σ ξ.
      (* Values *)
    rem - vsᶠ vₓᶠ as Heqv_vs Heqv_vₓ / Heqv_vₓ vₓᴮ:
          (map erase_val vsᴮ)
          (erase_val vₓᴮ).
    erewrite length_map_erase_val_eq in *.
          2-3: exa - Heqv_vs.
          clr - Heqv_vs vsᴮ.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp:
          esᶠ eₓᶠ vsᶠ vₓᶠ Hlen IHFse_nth.
    (* #4 Pose From Nth to Result Full: ass/pose *)
    ass > (IValues <> IMap) as Hident: con.
    ass > (create_result IValues vsᶠ [] = Some (RValSeq vsᶠ, [])) as Hcrt: trv.
    pose proof fs_eval_nth_to_result_full
          IValues esᶠ eₓᶠ vsᶠ vₓᶠ (RValSeq vsᶠ)
          [] [] Hident Hlen Hcrt IHFse_nth
          as IHFse_vs;
          clr - Hident Hcrt IHFse_nth.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_vs as [k_vs Hstp_vs].
    (* #6 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_vs.
  Qed.






(*
Hlen : ˡ|vsᴮ| < ˡ|esᴮ|
IHFse_nth :
  ∀ i : nat,
    i < ˡ|vsᴮ|
    → ⟨ [], ᴱ′(δₑᶠ(nth i esᴮ eₓᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([nth i vsᴮ vₓᴮ]))
IHFse_qₖ : ⟨ [], ᴱ′(δₑᶠ(nth ˡ|vsᴮ| esᴮ eₓᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(qₖᴮ))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ<esᴮ>ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(qₖᴮ))
*)
(*Values expression evaluates to an exception in frame stack:*)
(*bsfs.evalues.exception*)
  Theorem eq_bsfs_evalues_to_exception :
    forall Γ esᴮ eₓᴮ vsᴮ vₓᴮ qₖᴮ,
        length vsᴮ < length esᴮ
    ->  (forall i,
            i < length vsᴮ
        ->  ⟨ [], erase_names Γ (nth i esᴮ eₓᴮ) ⟩ -->*
                  erase_valseq [nth i vsᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (nth (length vsᴮ) esᴮ eₓᴮ) ⟩ -->* erase_exc qₖᴮ
    ->  ⟨ [], erase_names Γ (EValues esᴮ) ⟩ -->* erase_exc qₖᴮ.
  Proof.
    itr - Γ esᴮ eₓᴮ vsᴮ vₓᴮ qₖᴮ Hlen IHFse_nth IHFse_qₖ.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ esᴮ eₓᴮ vsᴮ vₓᴮ IHFse_nth;
          ren - IHFse_nth: IHFse_nth'.
    rwr - fs_eval_nth_map_erase_single in IHFse_qₖ.
      (* Expressions *)
    rem - esᶠ eₓᶠ as Heqv_es Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) esᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in *.
          2: exa - Heqv_es.
          clr - Heqv_es esᴮ σ ξ.
    (*Value*)
    rem - vsᶠ vₓᶠ qₖᶠ as Heqv_vs Heqv_vₓ Heqv_qₖ / Heqv_vₓ Heqv_qₖ vₓᴮ qₖᴮ:
          (map erase_val vsᴮ)
          (erase_val vₓᴮ)
          (erase_exc qₖᴮ).
    erewrite length_map_erase_val_eq in *.
          2-4: exa - Heqv_vs.
          clr - Heqv_vs vsᴮ.
    (* #3 Split Expression List: pose/destruct/subst *)
    psc - length_lt_split_middle as Hsplit:
          Val Exp vsᶠ esᶠ Hlen.
    des - Hsplit as [es₁ᶠ [eₖᶠ [es₂ᶠ [Hes Hlen]]]].
    sbt.
    (* #4 Simplify Hypothesis: *)
    rwr - Hlen in IHFse_qₖ.
    smp - IHFse_qₖ.
    rwr - nth_middle in IHFse_qₖ.
    (* #5 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - es₁ᶠ as [| e₁ᶠ es₁ᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth eₓᶠ vₓᶠ.
          (* #5.1 Both List Empty: apply/subst/simpl *)
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
    des - vsᶠ as [| v₁ᶠ vsᶠ]:
          ivs - Hlen.
    (* #7 Pose Nth Cons Theorem: rewrite/pose/destruct *)
    rewrite cons_app with (l := es₁ᶠ) in IHFse_nth.
    rwl - app_assoc in IHFse_nth.
    do 2 rwl - cons_app in IHFse_nth.
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          e₁ᶠ (es₁ᶠ ++ eₖᶠ :: es₂ᶠ) eₓᶠ v₁ᶠ vsᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v₁ IHFse_nth].
    (* #8 Pose From Nth to Result: apply/pose/simple *)
    app - length_cons_eq in Hlen.
    pose proof fs_eval_nth_to_partial
          IValues es₁ᶠ eₖᶠ es₂ᶠ eₓᶠ [] v₁ᶠ vsᶠ vₓᶠ Hlen IHFse_nth
          as IHFse_vs.
    smp / Hlen IHFse_nth eₓᶠ vₓᶠ.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁  [_      Hstp_v₁]].
    des - IHFse_vs as [k_vs          Hstp_vs].
    des - IHFse_qₖ as [k_qₖ [Hscp_qₖ Hstp_qₖ]].
    (* #10 FrameStack Evaluation: open/step *)
    open / Hscp_qₖ.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step - Hstp_vs / es₁ᶠ k_vs.
    step - Hstp_qₖ / k_qₖ.
    step.
  Qed.



End EValues.















Section ETuple.



(*
Hlen : ˡ|esᴮ| = ˡ|vsᴮ|
IHFse_nth :
  ∀ i : nat,
    i < ˡ|esᴮ|
    → ⟨ [], ᴱ′(δₑᶠ(nth i esᴮ eₓᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([nth i vsᴮ vₓᴮ]))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ{esᴮ}ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([ᵛ{vsᴮ}ᴮ]))
*)
(*Tuple expression evaluates to a value sequence in frame stack:*)
(*bsfs.etuple.valseq*)
  Theorem eq_bsfs_etuple_to_vtuple :
    forall Γ esᴮ eₓᴮ vsᴮ vₓᴮ,
        length esᴮ = length vsᴮ
    ->  (forall i,
            i < length esᴮ
        ->  ⟨ [], erase_names Γ (nth i esᴮ eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i vsᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (ETuple esᴮ) ⟩ -->* erase_valseq [VTuple vsᴮ].
  Proof.
    itr - Γ esᴮ eₓᴮ vsᴮ vₓᴮ Hlen IHFse_nth.
    (* #0 Pre Formalize Hypothesis: rewrite/symmetry *)
    rwr - Hlen in IHFse_nth.
    sym - Hlen.
    (* #1 Unfold Converters: simpl/unfold/rewrite/mvr *)
    smp.
    ufl - erase_names
          erase_valseq in *.
    rwr - map_map.
    mvr.
    (* #2 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ esᴮ eₓᴮ vsᴮ vₓᴮ IHFse_nth.
          ren - IHFse_nth: IHFse_nth'.
      (* Expressions *)
    rem - esᶠ eₓᶠ as Heqv_es Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) esᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in *.
          2: exa - Heqv_es.
          clr - Heqv_es esᴮ σ ξ.
      (* Values *)
    rem - vsᶠ vₓᶠ as Heqv_vs Heqv_vₓ / Heqv_vₓ vₓᴮ:
          (map erase_val vsᴮ)
          (erase_val vₓᴮ).
    erewrite length_map_erase_val_eq in *.
          2-3: exa - Heqv_vs.
          clr - Heqv_vs vsᴮ.
    (* #3 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp':
          esᶠ eₓᶠ vsᶠ vₓᶠ Hlen IHFse_nth.
    psc - scope_list_to_tuple as Hscp: vsᶠ Hscp'.
    (* #4 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - esᶠ as [| e₁ᶠ esᶠ].
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
    des - vsᶠ as [| v₁ᶠ vsᶠ]:
          ivs - Hlen.
    (* #6 Pose Nth Cons Theorem: pose/destruct *)
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          e₁ᶠ esᶠ eₓᶠ v₁ᶠ vsᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v₁ IHFse_nth].
    (* #7 Pose From Nth to Result: apply/pose *)
    app - length_cons_eq in Hlen.
    pose proof create_result_ituple
          v₁ᶠ vsᶠ [] as Hcrt.
    pose proof fs_eval_nth_to_result
          ITuple esᶠ eₓᶠ [] v₁ᶠ vsᶠ vₓᶠ (RValSeq [Syntax.VTuple (v₁ᶠ :: vsᶠ)])
          [] [] Hlen Hcrt IHFse_nth
          as IHFse_vs.
    clr - Hlen Hcrt IHFse_nth eₓᶠ vₓᶠ.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [_ Hstp_v₁]].
    des - IHFse_vs as [k_vs    Hstp_vs].
    (* #9 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step - Hstp_vs.
  Qed.






(*
Hlen : ˡ|vsᴮ| < ˡ|esᴮ|
IHFse_nth :
  ∀ i : nat,
    i < ˡ|vsᴮ|
    → ⟨ [], ᴱ′(δₑᶠ(nth i esᴮ eₓᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([nth i vsᴮ vₓᴮ]))
IHFse_qₖ : ⟨ [], ᴱ′(δₑᶠ(nth ˡ|vsᴮ| esᴮ eₓᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(qₖᴮ))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ{esᴮ}ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(qₖᴮ))
*)
(*Tuple expression evaluates to an exception in frame stack:*)
(*bsfs.etuple.exception*)
  Theorem eq_bsfs_etuple_to_exception :
    forall Γ esᴮ eₓᴮ vsᴮ vₓᴮ qₖᴮ,
        length vsᴮ < length esᴮ
    ->  (forall i,
            i < length vsᴮ
        ->  ⟨ [], erase_names Γ (nth i esᴮ eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i vsᴮ vₓᴮ])
    ->  ⟨ [], erase_names Γ (nth (length vsᴮ) esᴮ eₓᴮ) ⟩ -->* erase_exc qₖᴮ
    ->  ⟨ [], erase_names Γ (ETuple esᴮ) ⟩ -->* erase_exc qₖᴮ.
  Proof.
    itr - Γ esᴮ eₓᴮ vsᴮ vₓᴮ qₖᴮ Hlen IHFse_nth IHFse_qₖ.
    (* #1 Unfold Converters: simpl/unfold/rewrite *)
    smp.
    ufl - erase_names in *.
    rwr - map_map.
    (* #2 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ esᴮ eₓᴮ vsᴮ vₓᴮ IHFse_nth;
          ren - IHFse_nth: IHFse_nth'.
    rwr - fs_eval_nth_map_erase_single in IHFse_qₖ.
      (* Expressions *)
    rem - esᶠ eₓᶠ as Heqv_es Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun e => (erase_exp σ e).[ξ]) esᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_eq in *.
          2: exa - Heqv_es.
          clr - Heqv_es esᴮ σ ξ.
    (*Value*)
    rem - vsᶠ vₓᶠ qₖᶠ as Heqv_vs Heqv_vₓ Heqv_qₖ / Heqv_vₓ Heqv_qₖ vₓᴮ qₖᴮ:
          (map erase_val vsᴮ)
          (erase_val vₓᴮ)
          (erase_exc qₖᴮ).
    erewrite length_map_erase_val_eq in *.
          2-4: exa - Heqv_vs.
          clr - Heqv_vs vsᴮ.
    (* #3 Split Expression List: pose/destruct/subst *)
    psc - length_lt_split_middle as Hsplit:
          Val Exp vsᶠ esᶠ Hlen.
    des - Hsplit as [es₁ᶠ [eₖᶠ [es₂ᶠ [Hes Hlen]]]].
    sbt.
    (* #4 Simplify Hypothesis: *)
    rwr - Hlen in IHFse_qₖ.
    smp - IHFse_qₖ.
    rwr - nth_middle in IHFse_qₖ.
    (* #5 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - es₁ᶠ as [| e₁ᶠ es₁ᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth eₓᶠ vₓᶠ.
          (* #5.1 Both List Empty: apply/subst/simpl *)
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
    des - vsᶠ as [| v₁ᶠ vsᶠ]:
          ivs - Hlen.
    (* #7 Pose Nth Cons Theorem: rewrite/pose/destruct *)
    rewrite cons_app with (l := es₁ᶠ) in IHFse_nth.
    rwl - app_assoc in IHFse_nth.
    do 2 rwl - cons_app in IHFse_nth.
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          e₁ᶠ (es₁ᶠ ++ eₖᶠ :: es₂ᶠ) eₓᶠ v₁ᶠ vsᶠ vₓᶠ IHFse_nth.
    des - IHFse_nth_cons as [IHFse_v₁ IHFse_nth].
    (* #8 Pose From Nth to Result: apply/pose/simple *)
    app - length_cons_eq in Hlen.
    pose proof fs_eval_nth_to_partial
          ITuple es₁ᶠ eₖᶠ es₂ᶠ eₓᶠ [] v₁ᶠ vsᶠ vₓᶠ Hlen IHFse_nth
          as IHFse_vs.
    smp / Hlen IHFse_nth eₓᶠ vₓᶠ.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [_       Hstp_v₁]].
    des - IHFse_vs as [k_vs          Hstp_vs].
    des - IHFse_qₖ as [k_qₖ [Hscp_qₖ Hstp_qₖ]].
    (* #10 FrameStack Evaluation: open/step *)
    open / Hscp_qₖ.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step - Hstp_vs / es₁ᶠ k_vs.
    step - Hstp_qₖ / k_qₖ.
    step.
  Qed.



End ETuple.















Section EMap.



(*
Hlen_k : ˡ|eesᴮ| = ˡ|ᵏvsᴮ|
Hlen_v : ˡ|eesᴮ| = ˡ|ᵛvsᴮ|
Hmake : make_value_map ᵏvsᴮ ᵛvsᴮ = (ᵏvsᴮ, ᵛvsᴮ)
IHFse_nth :
  ∀ i : nat,
    i < ˡ|make_map_exps eesᴮ|
    → ⟨ [], ᴱ′(δₑᶠ(nth i (make_map_exps eesᴮ) eₓᴮ ⇓ Γ)) ⟩ -->*
      ᵛˢ′(δᵥₗᶠ([nth i (make_map_vals ᵏvsᴮ ᵛvsᴮ) vₓᴮ]))
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ∼{eesᴮ}∼ᴮ ⇓ Γ)) ⟩ -->* ᵛˢ′(δᵥₗᶠ([ᵛ∼{combine ᵏvsᴮ ᵛvsᴮ}∼ᴮ]))
*)
(*Map expression evaluates to a value sequence in frame stack:*)
(*bsfs.emap.valseq*)
  Theorem eq_bsfs_emap_to_vmap :
    forall Γ eesᴮ eₓᴮ ᵏvsᴮ ᵛvsᴮ vₓᴮ,
        length eesᴮ = length ᵏvsᴮ
    ->  length eesᴮ = length ᵛvsᴮ
    ->  make_value_map ᵏvsᴮ ᵛvsᴮ = (ᵏvsᴮ, ᵛvsᴮ)
    ->  (forall i,
            i < length (make_map_exps eesᴮ)
        ->  ⟨ [], erase_names Γ (nth i (make_map_exps eesᴮ) eₓᴮ) ⟩ -->*
                  erase_valseq [nth i (make_map_vals ᵏvsᴮ ᵛvsᴮ) vₓᴮ])
    ->  ⟨ [], erase_names Γ (EMap eesᴮ) ⟩ -->*
              erase_valseq [VMap (combine ᵏvsᴮ ᵛvsᴮ)].
  Proof.
    itr - Γ eesᴮ eₓᴮ ᵏvsᴮ ᵛvsᴮ vₓᴮ Hlen_k Hlen_v Hmake IHFse_nth.
    (* #1 Rewrite Combine Keys-Vals Theorem: rewrite/symmetry/pose/destruct *)
    rwr - make_map_exps_flatten_list_eq in *.
    sym - Hlen_k Hlen_v.
    pose proof length_match2 _ _ _ _ _ _ Hlen_k Hlen_v as Hlen.
    pse - combine_key_and_val_lists as Hcomb: ᵏvsᴮ ᵛvsᴮ Hlen Hmake.
    des - Hcomb as [vvsᴮ [Hᵏvs [Hᵛvs [Hvvs Hflat]]]].
    cwr - Hvvs Hflat Hᵏvs Hᵛvs / Hlen Hlen_v Hmake ᵏvsᴮ ᵛvsᴮ;
          ren - Hlen: Hlen_k.
    rwl - length_map_fst in Hlen.
    rwr - length_flatten_both_eq in Hlen.
    rwl - Hlen in IHFse_nth.
    (* #2 Unfold Converters: pose/rewrite/simpl/unfold/mvr *)
    pose proof flatten_deflatten eesᴮ as Hees.
    pose proof flatten_deflatten vvsᴮ as Hvvs.
    cwl - Hees Hvvs.
    smp *.
    ufl - erase_names in *.
    do 3 rwr - deflatten_map.
    rwr - map_map.
    mvr.
    (* #3 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ (flatten_list eesᴮ) eₓᴮ (flatten_list vvsᴮ) vₓᴮ IHFse_nth;
          ren - IHFse_nth: IHFse_nth'.
    do 2 rwr - flatten_map in *.
      (* Expressions *)
    rem - eesᶠ eₓᶠ as Heqv_ees Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun '(x, y) => ((erase_exp σ x).[ξ], (erase_exp σ y).[ξ])) eesᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_flatten_eq in *.
          2: exa - Heqv_ees.
          clr - Heqv_ees eesᴮ σ ξ.
      (* Values *)
    rem - vvsᶠ vₓᶠ as Heqv_vvs Heqv_vₓ / Heqv_vₓ vₓᴮ:
          (map (fun '(x, y) => (erase_val x, erase_val y)) vvsᴮ)
          (erase_val vₓᴮ).
    erewrite length_map_erase_val_flatten_eq in *.
          2-3: exa - Heqv_vvs.
          clr - Heqv_vvs vvsᴮ.
    (* #4 Flatten-Deflatten: pose/rewrite *)
    pose proof flatten_deflatten eesᶠ as Hees.
    pose proof flatten_deflatten vvsᶠ as Hvvs.
    cwr - Hees Hvvs.
    (* #5 Scope From Nth: pose *)
    pse - fs_eval_nth_to_scope as Hscp':
          (flatten_list eesᶠ) eₓᶠ (flatten_list vvsᶠ) vₓᶠ Hlen IHFse_nth.
    psc - scope_list_to_map as Hscp:
          vvsᶠ Hscp'.
    (* #6 Destruct on Expression List and Solve Empty Branch: destruct *)
    des - eesᶠ as [| [ᵏe₁ᶠ ᵛe₁ᶠ] eesᶠ].
    { (* - Empty List Branch *)
          clr - IHFse_nth Hscp eₓᶠ vₓᶠ.
          (* #6.1 Both List Empty: rewrite/apply/subst *)
          rwl - length_flatten_both_eq in Hlen.
          app - length_empty_fst in Hlen.
          sbt.
          (* #6.2 FrameStack Evaluation: open/step *)
          open.
          step.
    } (* - Cons List Branch *)
    (* #7 Both List Cons: destruct + inversion/subst *)
    des - vvsᶠ as [| [ᵏv₁ᶠ ᵛv₁ᶠ] vvsᶠ]:
          ivs - Hlen.
    (* #8 Pose Nth Cons Theorem: pose/destruct *)
    do 2 rwr - flatten_cons in *.
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          ᵏe₁ᶠ (ᵛe₁ᶠ :: flatten_list eesᶠ) eₓᶠ
          ᵏv₁ᶠ (ᵛv₁ᶠ :: flatten_list vvsᶠ) vₓᶠ
          IHFse_nth.
    des - IHFse_nth_cons as [IHFse_ᵏv₁ IHFse_nth].
    psc - fs_eval_nth_cons as IHFse_nth_cons:
          ᵛe₁ᶠ (flatten_list eesᶠ) eₓᶠ
          ᵛv₁ᶠ (flatten_list vvsᶠ) vₓᶠ
          IHFse_nth.
    des - IHFse_nth_cons as [IHFse_ᵛv₁ IHFse_nth].
    (* #9 Pose From Nth to Result: apply/pose/destruct/rewrite *)
    do 2 app - length_cons_eq in Hlen.
    pose proof create_result_imap
          ᵏv₁ᶠ ᵛv₁ᶠ vvsᶠ [] as Hcrt.
    pse - all_fsval_is_wfm as Hwfm:
          (Syntax.VMap ((ᵏv₁ᶠ, ᵛv₁ᶠ) :: vvsᶠ)).
    des - Hwfm as [Hwfm _].
    cwl - Hwfm in Hcrt.
    pose proof fs_eval_nth_to_result
          IMap (flatten_list eesᶠ) eₓᶠ [ᵏv₁ᶠ] ᵛv₁ᶠ (flatten_list vvsᶠ) vₓᶠ
          (RValSeq [Syntax.VMap ((ᵏv₁ᶠ, ᵛv₁ᶠ) :: vvsᶠ)]) [] []
          Hlen Hcrt IHFse_nth
          as IHFse_vvs;
          clr - Hlen Hcrt IHFse_nth eₓᶠ vₓᶠ.
    (* #10 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_ᵏv₁ as [k_ᵏv₁ [_ Hstp_ᵏv₁]].
    des - IHFse_ᵛv₁ as [k_ᵛv₁ [_ Hstp_ᵛv₁]].
    des - IHFse_vvs as [k_vvs    Hstp_vvs].
    (* #11 FrameStack Evaluation: open/step *)
    open / Hscp.
    step - Hstp_ᵏv₁ / ᵏe₁ᶠ k_ᵏv₁.
    step - Hstp_ᵛv₁ / ᵛe₁ᶠ k_ᵛv₁.
    step - Hstp_vvs.
  Qed.






(*
Hlen : k < 2 * ˡ|eesᴮ|
Hlen_k : ˡ|ᵏvsᴮ| = k `div` 2 + k % 2
Hlen_v : ˡ|ᵛvsᴮ| = k `div` 2
IHFse_nth :
  ∀ i : nat,
    i < k
    → ⟨ [], ᴱ′(δₑᶠ(nth i (make_map_exps eesᴮ) eₓᴮ ⇓ Γ)) ⟩ -->*
      ᵛˢ′(δᵥₗᶠ([nth i (make_map_vals ᵏvsᴮ ᵛvsᴮ) vₓᴮ]))
IHFse_qₖ₂ : ⟨ [], ᴱ′(δₑᶠ(nth k (make_map_exps eesᴮ) eₓᴮ ⇓ Γ)) ⟩ -->* δᶠ(qₖ₂ᴮ ↦)
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(ᵉ∼{eesᴮ}∼ᴮ ⇓ Γ)) ⟩ -->* ᵉˣᶜ′(δₓᶠ(qₖ₂ᴮ))
*)
(*Map expression evaluates to an exception in frame stack:*)
(*bsfs.emap.exception*)
  Theorem eq_bsfs_emap_to_exception :
    forall Γ eesᴮ eₓᴮ ᵏvsᴮ ᵛvsᴮ vₓᴮ qₖ₂ᴮ k,
        k < 2 * length eesᴮ
    ->  length ᵏvsᴮ = k / 2 + k mod 2
    ->  length ᵛvsᴮ = k / 2
    ->  (forall i,
            i < k
        ->  ⟨ [], erase_names Γ (nth i (make_map_exps eesᴮ) eₓᴮ) ⟩ -->* 
                  erase_valseq [nth i (make_map_vals ᵏvsᴮ ᵛvsᴮ) vₓᴮ])
    ->  ⟨ [], erase_names Γ (nth k (make_map_exps eesᴮ) eₓᴮ) ⟩ -->*
              erase_result (inr qₖ₂ᴮ)
    ->  ⟨ [], erase_names Γ (EMap eesᴮ) ⟩ -->*
              erase_exc qₖ₂ᴮ.
  Proof.
    itr - Γ eesᴮ eₓᴮ ᵏvsᴮ ᵛvsᴮ vₓᴮ qₖ₂ᴮ k
          Hlen Hlen_k Hlen_v IHFse_nth IHFse_qₖ₂.
    (* #1 Rewrite Combine Keys-Vals Theorem: rewrite/pose/destruct/apply *)
    rwr - make_map_exps_flatten_list_eq in *.
    pse - combine_key_and_val_exc as Hcomb:
          ᵏvsᴮ ᵛvsᴮ k Hlen_k Hlen_v.
    des - Hcomb as [vvsᴮ [vsᴮ [Hlen_vvs [Hlen_vs [Hᵏvs [Hᵛvs Hflat]]]]]].
    cwr - Hflat Hᵏvs Hᵛvs / Hlen_k Hlen_v ᵏvsᴮ ᵛvsᴮ.
    pse - kmod2length_combined as Hlen_comb:
          Value vvsᴮ vsᴮ k Hlen_vvs Hlen_vs;
          clr - Hlen_vvs.
    psc - kmod2list_is_either_empty_or_single as Hvs:
          Value vsᴮ k Hlen_vs.
    app - erase_val_empty_or_single_also in Hvs.
    cwl - Hlen_comb / k.
    rwr - Nat.mul_comm in Hlen.
    rewrite <- length_flatten_list in Hlen.
    app - length_app_le in Hlen.
    (* #2 Unfold Converters: pose/rewrite/simpl/unfold *)
    pose proof flatten_deflatten eesᴮ as Hees.
    cwl - Hees.
    smp *.
    ufl - erase_names in *.
    do 2 rwr - deflatten_map.
    rwr - map_map.
    (* #3 Convert Syntax from BigStep to FrameStack: remember/pose/rewrite *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
          (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
          (list_subst (map erase_val Γ.vals) idsubst).
    psc - fs_eval_nth_map_erase_forall as IHFse_nth':
          σ ξ (flatten_list eesᴮ) eₓᴮ (flatten_list vvsᴮ ++ vsᴮ) vₓᴮ IHFse_nth;
          ren - IHFse_nth: IHFse_nth'.
    rwr - fs_eval_nth_map_erase_single in IHFse_qₖ₂.
    rwr - map_app in IHFse_nth.
    do 2 rwr - flatten_map in *.
      (* Expressions *)
    rem - eesᶠ eₓᶠ as Heqv_ees Heqv_eₓ / Heqv_eₓ eₓᴮ:
          (map (fun '(x, y) => ((erase_exp σ x).[ξ], (erase_exp σ y).[ξ])) eesᴮ)
          ((erase_exp σ eₓᴮ).[ξ]).
    erewrite length_map_erase_exp_flatten_eq in *.
          2: exa - Heqv_ees.
          clr - Heqv_ees eesᴮ σ ξ.
      (* Values *)
    rem - vvsᶠ vsᶠ vₓᶠ qₖ₂ᶠ as Heqv_vvs Heqv_vs Heqv_vₓ Heqv_qₖ₂
          / Heqv_vₓ Heqv_qₖ₂ vₓᴮ qₖ₂ᴮ:
          (map (fun '(x, y) => (erase_val x, erase_val y)) vvsᴮ)
          (map erase_val vsᴮ)
          (erase_val vₓᴮ)
          (erase_exc qₖ₂ᴮ).
    rewrite length_app in *.
    erewrite length_map_erase_val_flatten_eq in *.
          2-4: exa - Heqv_vvs.
          clr - Heqv_vvs vvsᴮ.
    erewrite length_map_erase_val_eq in *.
          2-3: exa - Heqv_vs.
          clr - Heqv_vs vsᴮ.
    rewrite <- length_app in *.
    (* #4 Flatten-Deflatten List: pose/rewrite *)
    pose proof flatten_deflatten eesᶠ as Hees.
    cwr - Hees.
    rwl - length_flatten_both_lt in Hlen.
    (* #5 Split Expression List: pose/destruct/subst/rewrite/simpl *)
    epose proof length_lt_split_middle
          _ _ vvsᶠ eesᶠ Hlen
          as Hsplit;
          clr - Hlen.
    des - Hsplit as [ees₁ᶠ [[ᵏeₖ₂ᶠ ᵛeₖ₂ᶠ] [ees₂ᶠ [Hes Hlen]]]].
    sbt.
    smp *.
    (* #6 Flatten List: rewrite *)
    rwr - length_flatten_both_eq in Hlen.
    rwr - flatten_app in *.
    rewrite flatten_cons in *.
    (* #7 Destruct Empty or Single: destruct/subst *)
    des - Hvs as [Hempty | [ᵏvₖ₂ᶠ Hsingle]]; sbt.
    * (* +I. Rest is Empty: *)
      (* #I/1 Simplify Hypothesis: rename/rewrite *)
      ren - IHFse_ᵏqₖ₂ ᵏqₖ₂ᶠ: IHFse_qₖ₂ qₖ₂ᶠ.
      rwr - app_nil_r in *.
      rwr - Hlen in IHFse_ᵏqₖ₂.
      rwr - nth_middle in IHFse_ᵏqₖ₂.
      (* #I/2 Destruct on Expression List and Solve Empty Branch: destruct *)
      des - ees₁ᶠ as [| [ᵏe₁ᶠ ᵛe₁ᶠ] ees₁ᶠ].
      { (* - Empty List Branch *)
            clr - IHFse_nth eₓᶠ vₓᶠ.
            (* #I/2.1 Both List Empty: rewrite/apply/subst/simpl *)
            rwl - length_flatten_both_eq in Hlen.
            app - length_empty_fst in Hlen.
            sbt.
            smp.
            (* #I/2.2 Destruct Inductive Hypothesis: destruct *)
            des - IHFse_ᵏqₖ₂ as [k_ᵏqₖ₂ [Hscp_ᵏqₖ₂ Hstp_ᵏqₖ₂]].
            (* #I/2.3 FrameStack Evaluation: open/step *)
            open / Hscp_ᵏqₖ₂.
            step - Hstp_ᵏqₖ₂ / ᵏeₖ₂ᶠ k_ᵏqₖ₂.
            step.
      } (* - Cons List Branch *)
      (* #I/3 Both List Cons: destruct + inversion/subst *)
      des - vvsᶠ as [| [ᵏv₁ᶠ ᵛv₁ᶠ] vvsᶠ]:
            ivs - Hlen.
      (* #I/4 Pose Nth Cons Theorem: rewrite/pose/destruct *)
      do 2 rwr - flatten_cons in *.
      do 2 rwl - app_comm_cons in *.
      psc - fs_eval_nth_cons as IHFse_nth_cons:
            ᵏe₁ᶠ (ᵛe₁ᶠ :: flatten_list ees₁ᶠ
              ++ ᵏeₖ₂ᶠ :: ᵛeₖ₂ᶠ :: flatten_list ees₂ᶠ) eₓᶠ
            ᵏv₁ᶠ (ᵛv₁ᶠ :: flatten_list vvsᶠ) vₓᶠ
            IHFse_nth.
      des - IHFse_nth_cons as [IHFse_ᵏv₁ IHFse_nth].
      psc - fs_eval_nth_cons as IHFse_nth_cons:
            ᵛe₁ᶠ (flatten_list ees₁ᶠ
              ++ ᵏeₖ₂ᶠ :: ᵛeₖ₂ᶠ :: flatten_list ees₂ᶠ) eₓᶠ
            ᵛv₁ᶠ (flatten_list vvsᶠ) vₓᶠ
            IHFse_nth.
      des - IHFse_nth_cons as [IHFse_ᵛv₁ IHFse_nth].
      (* #I/5 Pose From Nth to Result: apply/pose/rewrite *)
      do 2 app - length_cons_eq in Hlen.
      pose proof fs_eval_nth_to_partial
            IMap (flatten_list ees₁ᶠ) ᵏeₖ₂ᶠ (ᵛeₖ₂ᶠ :: flatten_list ees₂ᶠ) eₓᶠ
            [ᵏv₁ᶠ] ᵛv₁ᶠ (flatten_list vvsᶠ) vₓᶠ
            Hlen IHFse_nth
            as IHFse_vvs;
            clr - Hlen IHFse_nth eₓᶠ vₓᶠ.
      rwl - flatten_cons in *.
      rwl - flatten_app in *.
      (* #I/6 Destruct Inductive Hypothesis: destruct *)
      des - IHFse_ᵏv₁  as [k_ᵏv₁   [_         Hstp_ᵏv₁]].
      des - IHFse_ᵛv₁  as [k_ᵛv₁   [_         Hstp_ᵛv₁]].
      des - IHFse_vvs  as [k_vvs              Hstp_vvs].
      des - IHFse_ᵏqₖ₂ as [k_ᵏqₖ₂  [Hscp_ᵏqₖ₂ Hstp_ᵏqₖ₂]].
      (* #I/7 FrameStack Evaluation: open/step *)
      open / Hscp_ᵏqₖ₂.
      step - Hstp_ᵏv₁  / ᵏe₁ᶠ  k_ᵏv₁.
      step - Hstp_ᵛv₁  / ᵛe₁ᶠ  k_ᵛv₁.
      step - Hstp_vvs  / ees₁ᶠ k_vvs.
      step - Hstp_ᵏqₖ₂ / ᵏeₖ₂ᶠ k_ᵏqₖ₂.
      step.
    * (* +II. Rest is Single: *)
      (* #II/1 Simplify Hypothesis: rename/rewrite *)
      ren - IHFse_ᵛqₖ₂ ᵛqₖ₂ᶠ: IHFse_qₖ₂ qₖ₂ᶠ.
      rewrite length_app in *.
      rwr - Hlen in *.
      rewrite cons_app with (x := ᵏeₖ₂ᶠ) in IHFse_ᵛqₖ₂.
      pose proof length_app_end_any
            _ _ _ (flatten_list ees₁ᶠ) ᵏvₖ₂ᶠ ᵏeₖ₂ᶠ
            as Hlen_swap.
      rwr - Hlen_swap in *.
      rewrite <- length_app in *.
      rwr - app_assoc in *.
      rwr - nth_middle in IHFse_ᵛqₖ₂.
      rewrite length_app in IHFse_nth.
      pse - length_add_end_le as Hle:
            Exp (flatten_list ees₁ᶠ) ᵏeₖ₂ᶠ.
      spc + IHFse_nth as IHFse_ᵏvₖ₂:
            (length (flatten_list ees₁ᶠ)) Hle.
      rwr - nth_middle in IHFse_ᵏvₖ₂.
      rewrite <- length_app in IHFse_nth.
      cwl - Hlen_swap in IHFse_nth.
      rwl - Hlen in IHFse_nth.
      rewrite <- length_app in IHFse_nth.
      (* #II/2 Destruct on Expression List and Solve Empty Branch: destruct *)
      des - ees₁ᶠ as [| [ᵏe₁ᶠ ᵛe₁ᶠ] ees₁ᶠ].
      { (* - Empty List Branch *)
            clr - IHFse_nth eₓᶠ.
            (* #II/2.1 Both List Empty: rewrite/apply/subst/simpl *)
            rwl - length_flatten_both_eq in Hlen.
            app - length_empty_fst in Hlen.
            sbt.
            smp *.
            (* #II/2.2 Destruct Inductive Hypothesis: destruct *)
            des - IHFse_ᵏvₖ₂ as [k_ᵏvₖ₂ [_         Hstp_ᵏvₖ₂]].
            des - IHFse_ᵛqₖ₂ as [k_ᵛqₖ₂ [Hscp_ᵛqₖ₂ Hstp_ᵛqₖ₂]].
            (* #II/2.3 FrameStack Evaluation: open/step *)
            open / Hscp_ᵛqₖ₂.
            step - Hstp_ᵏvₖ₂ / ᵏeₖ₂ᶠ k_ᵏvₖ₂.
            step - Hstp_ᵛqₖ₂ / ᵛeₖ₂ᶠ k_ᵛqₖ₂.
            step.
      } (* - Cons List Branch *)
      (* #I/3 Both List Cons: destruct + inversion/subst *)
      clr - IHFse_ᵏvₖ₂.
      des - vvsᶠ as [| [ᵏv₁ᶠ ᵛv₁ᶠ] vvsᶠ]:
            ivs - Hlen.
      (* #I/4 Pose Nth Cons Theorem: rewrite/pose/destruct *)
      do 2 rwr - flatten_cons in *.
      do 2 rwl - app_comm_cons in *.
      psc - fs_eval_nth_cons as IHFse_nth_cons:
            ᵏe₁ᶠ (ᵛe₁ᶠ :: flatten_list ees₁ᶠ
              ++ ᵏeₖ₂ᶠ :: ᵛeₖ₂ᶠ :: flatten_list ees₂ᶠ) eₓᶠ
            ᵏv₁ᶠ (ᵛv₁ᶠ :: flatten_list vvsᶠ ++ [ᵏvₖ₂ᶠ]) vₓᶠ
            IHFse_nth.
      des - IHFse_nth_cons as [IHFse_ᵏv₁ IHFse_nth].
      psc - fs_eval_nth_cons as IHFse_nth_cons:
            ᵛe₁ᶠ (flatten_list ees₁ᶠ
              ++ ᵏeₖ₂ᶠ :: ᵛeₖ₂ᶠ :: flatten_list ees₂ᶠ) eₓᶠ
            ᵛv₁ᶠ (flatten_list vvsᶠ ++ [ᵏvₖ₂ᶠ]) vₓᶠ
            IHFse_nth.
      des - IHFse_nth_cons as [IHFse_ᵛv₁ IHFse_nth].
      (* #I/5 Pose From Nth to Result: apply/simply/pose/rewrite *)
      app - length_cons_eq in Hlen.
      smp - Hlen.
      psc - length_succ_add_end as Hlen':
            Val Exp (flatten_list vvsᶠ) ᵏvₖ₂ᶠ (flatten_list ees₁ᶠ) ᵏeₖ₂ᶠ Hlen;
            ren - Hlen: Hlen'.
      rewrite cons_app with (x := ᵏeₖ₂ᶠ) in IHFse_nth.
      rwr - app_assoc in IHFse_nth.
      pose proof fs_eval_nth_to_partial
            IMap (flatten_list ees₁ᶠ ++ [ᵏeₖ₂ᶠ]) ᵛeₖ₂ᶠ (flatten_list ees₂ᶠ) eₓᶠ
            [ᵏv₁ᶠ] ᵛv₁ᶠ (flatten_list vvsᶠ ++ [ᵏvₖ₂ᶠ]) vₓᶠ
            Hlen IHFse_nth
            as IHFse_vvs;
            clr - Hlen IHFse_nth eₓᶠ vₓᶠ.
      rwl - app_assoc in IHFse_vvs.
      smp - IHFse_vvs.
      rwl - flatten_cons in IHFse_vvs.
      rwl - flatten_app in IHFse_vvs.
      (* #I/6 Destruct Inductive Hypothesis: destruct *)
      des - IHFse_ᵏv₁  as [k_ᵏv₁   [_         Hstp_ᵏv₁]].
      des - IHFse_ᵛv₁  as [k_ᵛv₁   [_         Hstp_ᵛv₁]].
      des - IHFse_vvs  as [k_vvs              Hstp_vvs].
      des - IHFse_ᵛqₖ₂ as [k_ᵛqₖ₂  [Hscp_ᵛqₖ₂ Hstp_ᵛqₖ₂]].
      (* #I/7 FrameStack Evaluation: open/step *)
      open / Hscp_ᵛqₖ₂.
      step - Hstp_ᵏv₁  / ᵏe₁ᶠ  k_ᵏv₁.
      step - Hstp_ᵛv₁  / ᵛe₁ᶠ  k_ᵛv₁.
      step - Hstp_vvs  / ees₁ᶠ k_vvs.
      step - Hstp_ᵛqₖ₂ / ᵛeₖ₂ᶠ k_ᵛqₖ₂.
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



(*
B : | Γ, modules, own_module, id, eᴮ, eff | -e> | id', rᴮ, eff' |
______________________________________(1/1)
⟨ [], ᴱ′(δₑᶠ(eᴮ ⇓ Γ)) ⟩ -->* δᶠ(rᴮ)
*)
(*Big-step implies frame stack semantics:*)
(*bsfs*)
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
      (* +2.2 EFunId: value/modfunc *)
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
      (* +3.1 ECons: vcons/exception1/exception2 *)
        (* -3.1.1 vcons: *)
          5: {
            clr - modules own_module id id' id'' eff1 eff2 eff3 B1 B2.
            ren - e₁ e₂ v₁ v₂ IHFse_v₁ IHFse_v₂:
                  hd tl hdv tlv IHB2 IHB1.
            bse - eq_bsfs_econs_to_vcons:
                  Γ e₁ e₂ v₁ v₂ IHFse_v₁ IHFse_v₂.
          }
        (* -3.1.2 exception1: *)
          15: {
            clr - modules own_module id id' id'' eff1 eff2 eff3 B1 B2.
            ren - e₁ e₂ q₁ v₂ IHFse_q₁ IHFse_v₂:
                  hd tl ex vtl IHB2 IHB1.
            bse - eq_bsfs_econs_to_exception1:
                  Γ e₁ e₂ q₁ v₂ IHFse_q₁ IHFse_v₂.
          }
        (* -3.1.3 exception2: *)
          14: {
            clr - modules own_module id id' eff1 eff2 B.
            ren - e₁ e₂ q₂ IHFse_q₂:
                  hd tl ex IHB.
            bse - eq_bsfs_econs_to_exception2:
                  Γ e₁ e₂ q₂ IHFse_q₂.
          }
      (* +3.2 ESeq: result/exception *)
        (* -3.2.1 result: *)
          11: {
            clr - modules own_module id id' id'' eff1 eff2 eff3 B1 B2.
            ren - e₁ e₂ v₁ r₂ IHFse_v₁ IHFse_r₂:
                  e1 e2 v1 v2 IHB1 IHB2.
            bse - eq_bsfs_eseq_to_result:
                  Γ e₁ e₂ v₁ r₂ IHFse_v₁ IHFse_r₂.
          }
        (* -3.2.2 exception: *)
          30: {
            clr - modules own_module id id' eff1 eff2 B.
            ren - e₁ e₂ q₁ IHFse_q₁:
                  e1 e2 ex IHB.
            bse - eq_bsfs_eseq_to_exception:
                  Γ e₁ e₂ q₁ IHFse_q₁.
          }
    (* #4 Functions: EFun/ELetrec *)
      (* +4.1 EFun: *)
          3: {
            ren - xs:
                  vl.
            pse - efun_is_result as Hscp:
                   Γ modules own_module xs e id eff;
                   clr - modules own_module eff.
            rwr - erase_result_to_valseq in *.
            bse - eq_bsfs_efun_to_vclos:
                  Γ xs e id Hscp.
          }
      (* +4.2 ELetrec: *)
         10:  admit.
    (* #5 Binders: ELet/ETry *)
      (* +5.1 ELet: result/exception *)
        (* -5.1.1 result: *)
          9: {
            clr - modules own_module id id' id'' eff1 eff' eff'' B1 B2.
            ren - xs₁ e₁ e₂ vs₁ r₂ Hlen₁ IHFse_vs₁ IHFse_r₂:
                  l e1 e2 vals res H IHB1 IHB2.
            bse - eq_bsfs_elet_to_result:
                  Γ xs₁ e₁ e₂ vs₁ r₂ Hlen₁ IHFse_vs₁ IHFse_r₂.
          }
        (* -5.1.2 exception: *)
          26: {
            clr - modules own_module id id' eff1 eff2 B.
            ren - xs₁ e₁ e₂ q₁ IHFse_q₁:
                  vl e1 e2 ex IHB.
            bse - eq_bsfs_elet_exception:
                  Γ xs₁ e₁ e₂ q₁ IHFse_q₁.
          }
      (* +5.2 ETry: result1/result2 *)
        (* -5.2.1 result1: *)
          11: {
            clr - modules own_module id id' id'' eff1 eff2 eff3 B1 B2.
            ren - xs₁ xs₂ e₁ e₂ e₃ vs₁ r₂ Hlen₁ IHFse_vs₁ IHFse_r₂:
                  vl1 vl2 e1 e2 e3 vals res H IHB1 IHB2.
            bse - eq_bsfs_etry_to_result1:
                  Γ xs₁ xs₂ e₁ e₂ e₃ vs₁ r₂ Hlen₁ IHFse_vs₁ IHFse_r₂.
          }
        (* -5.2.2 result2: *)
          11: {
            ren - xs₁ xs₂ e₁ e₂ e₃ q₁ r₃ eff eff' eff'':
                  vl1 vl2 e1 e2 e3 ex res eff1 eff2 eff3.
            ren - IHFse_q₁ IHFse_r₃ IHBse_q₁ IHBse_r₃:
                  IHB1 IHB2 B1 B2.
            rwr - exc_to_vals_eq in *.
            pse - etry_catch_vars_length as Hlen₂:
                  Γ modules own_module xs₁ xs₂ e₁ e₂ e₃ q₁ r₃
                  id id' id'' eff eff' eff'' IHBse_q₁ IHBse_r₃.
            bse - eq_bsfs_etry_to_result2:
                  Γ xs₁ xs₂ e₁ e₂ e₃ q₁ r₃ Hlen₂ IHFse_q₁ IHFse_r₃.
          }
    (* #6 Lists: EValues/ETuple/EMap *)
      (* +6.1 EValues: valseq/exception *)
        (* -6.1.1 valseq: *)
          1: {
            clr - modules own_module id id' ids eff eff1 eff' H0 H1 H2 H4 H5.
            ren - es vs Hlen IHFse_nth:
                  exps vals H H3.
            rem - eₓ vₓ as He Hv / He Hv:
                  ErrorExp
                  ErrorValue.
            bse - eq_bsfs_evalues_to_valseq:
                  Γ es eₓ vs vₓ Hlen IHFse_nth.
          }
        (* -6.1.2 exception: *)
          1:  {
            clr - modules own_module id id' ids eff eff1 eff' H1 H2 H3 B.
            ren - es vs qₖ Hlen IHFse_nth IHFse_qₖ:
                  exps vals ex H H4 IHB.
            subst.
            rem - eₓ vₓ as He Hv / He Hv:
                  ErrorExp
                  ErrorValue.
            bse - eq_bsfs_evalues_to_exception:
                  Γ es eₓ vs vₓ qₖ Hlen IHFse_nth IHFse_qₖ.
          }
      (* +6.2 ETuple: vtuple/exception *)
        (* -6.2.1 vtuple: *)
          1:  {
            clr - modules own_module id id' ids eff eff1 eff2 H0 H1 H2 H4 H5.
            ren - es vs Hlen IHFse_nth:
                  exps vals H H3.
            rem - eₓ vₓ as He Hv / He Hv:
                  ErrorExp
                  ErrorValue.
            bse - eq_bsfs_etuple_to_vtuple:
                  Γ es eₓ vs vₓ Hlen IHFse_nth.
          }
        (* -6.2.2 exception: *)
          7:  {
            clr - modules own_module id id' ids eff eff1 eff2 H1 H2 H3 B.
            ren - es vs qₖ Hlen IHFse_nth IHFse_qₖ:
                  exps vals ex H H4 IHB.
            subst.
            rem - eₓ vₓ as He Hv / He Hv:
                  ErrorExp
                  ErrorValue.
            bse - eq_bsfs_etuple_to_exception:
                  Γ es eₓ vs vₓ qₖ Hlen IHFse_nth IHFse_qₖ.
          }
      (* +6.3 EMap: vmap/exception *)
        (* -6.3.1 vmap: *)
          6: {
            ren - ees vvs ᵏvs ᵛvs kvm vvm eff' eff'':
                  l lv kvals vvals kvals' vvals' eff1 eff2.
            ren - Hlen_v Hlen_k Hlen_eff Hlen_id IHFse_nth IHBse_nth:
                  H H0 H1 H2 H4 H3.
            ren - Hmake Hcomb Heq_eff Heq_id:
                  H5 H6 H7 H8.
            pse - map_is_wfm as Hwfm:
                  Γ modules own_module ees ᵏvs ᵛvs kvm vvm vvs
                  eff eff' eff'' ids id id'.
            spe - Hwfm:
                  Hlen_v Hlen_k Hlen_eff Hlen_id
                  IHBse_nth Hmake Hcomb Heq_eff Heq_id;
                  clr - IHBse_nth Hlen_id Hlen_eff Heq_eff Heq_id;
                  clr - modules own_module ids id id' eff eff' eff''.
            des - Hwfm as [Hᵏvs Hᵛvs].
            cwl - Hᵏvs Hᵛvs in *.
            subst exps vals.
            subst.
            rem - eₓ vₓ as He Hv / He Hv:
                  ErrorExp
                  ErrorValue.
            bse - eq_bsfs_emap_to_vmap:
                  Γ ees eₓ ᵏvs ᵛvs vₓ Hlen_k Hlen_v Hmake IHFse_nth.
          }
        (* -6.3.2 exception: *)
          19: {
            clr - modules own_module eff eff1 eff2 id id' ids H2 H3 H4 B.
            ren - ees qₖ k ᵏvs ᵛvs Hlen_ees Hlen_k Hlen_v IHFse_nth IHFse_qₖ:
                  l ex i kvals vvals H H1 H0 H5 IHB.
            subst exps vals.
            rem - eₓ vₓ as He Hv / He Hv:
                  ErrorExp
                  ErrorValue.
            bse - eq_bsfs_emap_to_exception:
                  Γ ees eₓ ᵏvs ᵛvs vₓ qₖ k
                  Hlen_ees Hlen_k Hlen_v IHFse_nth IHFse_qₖ.
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
        (* -7.2.2 exception1: *)
          12: admit.
        (* -7.2.3 exception2: *)
          12: admit.
        (* -7.2.4 badfun1: *)
          12: admit.
        (* -7.2.5 badfun2: *)
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