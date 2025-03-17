From CoreErlang.Eqvivalence.BsFs Require Export BX5Eqvivalence.
From CoreErlang.Eqvivalence.BsFs Require Export BX4Helpers.

Import BX5Eqvivalence.
Import BigStep.

Check map.
Check fmap.
Check map_nth.
Search "∘".
Check compose.
Print transitive_eval.
Check frame_indep_core.
Print exclass_to_value.
Print map.

  Notation "\EraseFun{v}" := (erase_val)
    (at level 1,
      format "\EraseFun{v}" ).

  Notation "\EraseFun{e}" := (erase_exp)
    (at level 1,
      format "\EraseFun{e}" ).

  Notation "\EraseResult{ r }" := (erase_result r)
    (at level 1,
      format "\EraseResult{ r }" ).

  Notation "\EraseExc{ q }" := (erase_exc q)
    (at level 1,
      format "\EraseExc{ q }" ).

  Notation "\ErasePat{ p }" := (erase_pat p)
    (at level 1,
      format "\ErasePat{ p }" ).

  Notation "\EraseVal{ v }" := (erase_val v)
    (at level 1,
      format "\EraseVal{ v }" ).

  Notation "\EraseExp{ e }{ σ }" := (erase_exp σ e)
    (at level 1,
      format "\EraseExp{ e }{ σ }" ).

  Notation "\EraseExpSubst{ e }{ Γ }" := (erase_names Γ e)
    (at level 1,
      format "\EraseExpSubst{ e }{ Γ }" ).

  Notation "\erase{ k }{ σ }" := (apply_eraser σ k)
    (at level 1,
      format "\erase{ k }{ σ }" ).






  Definition clostitem_to_keyval
      (o : ClosureItem)
      (os : Extension)
      (Γ : Environment)
      : (Key * Value)
      :=
   match o with
   | (n, fid, (vars, e)) => ((inr fid), (VClos Γ os n vars e))
   end.

  Notation "\variableOccurances{ p }" := (variable_occurances p)
    (at level 20,
      format "\variableOccurances{ p }").

  Notation "\varsOfPatternList{ ps }" := (vars_of_pattern_list ps)
    (at level 20,
      format "\varsOfPatternList{ ps }").

  Notation "\excToVals{ q }" := (exc_to_vals q)
    (at level 20,
      format "\excToVals{ q }").

  Notation "\exclassToValue{ c }" := (exclass_to_value c)
    (at level 20,
      format "\exclassToValue{ c }").

  Notation "\exclassToValue{ c }" := (exclass_to_value c)
    (at level 20,
      format "\exclassToValue{ c }").

  Notation "\ClosItemToKV{ o }{ os }{ Γ }" := (clostitem_to_keyval o os Γ)
    (at level 20,
      format "\ClosItemToKV{ o }{ os }{ Γ }").






  Notation "\getKeys{ Γ }" := (get_keys Γ)
    (at level 20,
      format "\getKeys{ Γ }").

  Notation "\getVals{ Γ }" := (get_vals Γ)
    (at level 20,
      format "\getVals{ Γ }").

  Notation "\getFids{ os }" := (get_fids os)
    (at level 20,
      format "\getFids{ os }").

  Notation "\getFids'{ os }" := (get_fids_noid os)
    (at level 20,
      format "\getFids'{ os }").

  Notation "\getValue{ Γ }{ k }" := (get_value Γ k)
    (at level 20,
      format "\getValue{ Γ }{ k }").

  Notation "\varFunidEqb{ k }{ k' }" := (var_funid_eqb k k')
    (at level 20,
      format "\varFunidEqb{ k }{ k' }").






  Notation "\envRemKeySingle{ kv }{ k }" := (env_rem_key_one kv k)
    (at level 20,
      format "\envRemKeySingle{ kv }{ k }").

  Notation "\envRemKey{ Γ }{ k }" := (env_rem_key Γ k)
    (at level 20,
      format "\envRemKey{ Γ }{ k }").

  Notation "\envRemKeys{ Γ }{ ks }" := (env_rem_keys Γ ks)
    (at level 20,
      format "\envRemKeys{ Γ }{ ks }").

  Notation "\envRemVars{ Γ }{ xs }" := (env_rem_vars Γ xs)
    (at level 20,
      format "\envRemVars{ Γ }{ xs }").

  Notation "\envRemFids{ Γ }{ fs }" := (env_rem_fids Γ fs)
    (at level 20,
      format "\envRemFids{ Γ }{ fs }").

  Notation "\envRemExt{ Γ }{ os }" := (env_rem_ext Γ os)
    (at level 20,
      format "\envRemExt{ Γ }{ os }").



  Notation "\eraserAddKeys{ ks }{ σ }" := (eraser_add_keys ks σ)
    (at level 20,
      format "\eraserAddKeys{ ks }{ σ }").

  Notation "\eraserAddVars{ xs }{ σ }" := (eraser_add_vars xs σ)
    (at level 20,
      format "\eraserAddVars{ xs }{ σ }").

  Notation "\eraserAddFids{ fs }{ σ }" := (eraser_add_fids fs σ)
    (at level 20,
      format "\eraserAddFids{ fs }{ σ }").

  Notation "\eraserAddExt{ os }{ σ }" := (eraser_add_ext os σ)
    (at level 20,
      format "\eraserAddExt{ os }{ σ }").



  Notation "\appendVarsToEnv{ xs }{ vs }{ Γ }" := (append_vars_to_env xs vs Γ)
    (at level 20,
      format "\appendVarsToEnv{ xs }{ vs }{ Γ }").

  Notation "\appendFunsToEnv{ os }{ Γ }" := (append_funs_to_env os Γ)
    (at level 20,
      format "\appendFunsToEnv{ os }{ Γ }").

  Notation "\appendFunsToEnv'{ os }{ Γ }" := (get_env os Γ)
    (at level 20,
      format "\appendFunsToEnv'{ os }{ Γ }").






  Notation "\subst{ ξ }{ e }" := (subst ξ e)
    (at level 20,
      format "\subst{ ξ }{ e }").

  Notation "\scons{ v }{ ξ }" := (scons v ξ)
    (at level 20,
      format "\scons{ v }{ ξ }").

  Notation "\substcomp{ ξ }{ ξ' }" := (subst ξ ξ')
    (at level 20,
      format "\substcomp{ ξ }{ ξ' }").

  Notation "\idsubst" := (idsubst)
    (at level 20,
      format "\idsubst").

  Notation "\upnSB{ n }" := (upn n)
    (at level 20,
      format "\upnSB{ n }").

  Notation "\upn{ n }{ ξ }" := (upn n ξ)
    (at level 20,
      format "\upn{ n }{ ξ }").

  Notation "\listSubst{ vs }{ ξ }" := (list_subst vs ξ)
    (at level 20,
      format "\listSubst{ vs }{ ξ }").






  Notation "\flattenList{ l }" := (flatten_list l)
    (at level 20,
      format "\flattenList{ l }").

  Notation "\deflattenList{ l }" := (deflatten_list l)
    (at level 20,
      format "\deflattenList{ l }").

  Notation "\length{ l }" := (length l)
    (at level 20,
      format "\length{ l }").

  Notation "\zip{ l }{ l' }" := (zip l l')
    (at level 20,
      format "\zip{ l }{ l' }").

  Notation "\Mod{ a }{ b }" := (a mod b)
    (at level 20,
      format "\Mod{ a }{ b }").

  Notation "\MAP{ f }{ l }" := (map f l)
    (at level 20,
      format "\MAP{ f }{ l }").






  Notation "\evalExpr{ env }{ e }{ e' }" :=
          (eval_expr env  _  _ _  e  _ _  e'  _)
    (at level 20,
      format "\evalExpr{ env }{ e }{ e' }").


  Notation "\stepAny{ fs }{ e }{ r }" :=
          (step_any fs e r)
    (at level 20,
      format "\stepAny{ fs }{ e }{ r }").


  Notation "\stepRT{ fs }{ e }{ k }{ fs' }{ e' }" :=
          (step_rt fs e k fs' e')
    (at level 20,
      format "\stepRT{ fs }{ e }{ k }{ fs' }{ e' }").

























(*
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\\
*)

Print env_rem_key_one.


Check eq_bsfs_econs_to_vcons.
  Theorem eq_bsfs_econs_to_vcons2 :
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
    do_step.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    do_step.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    do_step.
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
    do_step.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    do_step.
    step - Hstp_q₁ / e₁ᶠ k_q₁.
    do_step.
    step.
  Qed.

Check transitive_eval.
Check frame_indep_core.

  Theorem eq_bsfs_evar_to_value2 :
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
