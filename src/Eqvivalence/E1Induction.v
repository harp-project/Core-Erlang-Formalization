From CoreErlang.BigStep Require BigStep.
From CoreErlang Require SubstSemantics.

(** CONTENT:
* INDUCTION_BIGSTEP
  - Induction_BigStep_Value
    + ind_bs_val
  - Induction_BigStep_Expression
    + ind_bs_exp
* INDUCTION_FRAMESTACK
  - Induction_FrameStack_Value
    + ind_fs_val
  - Induction_FrameStack_Expression
    + ind_fs_exp
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: INDUCTION_BIGSTEP ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.






Section Induction_BigStep_Value.



  Variables
    (P : Value -> Prop).



  Hypotheses
    (HVNil :
          P VNil)

    (HVLit :
      forall l,
          P (VLit l))

    (HVCons :
      forall v₁ v₂,
          P v₁
      ->  P v₂
      ->  P (VCons v₁ v₂))

    (HVClos :
      forall Γ os id xs e,
          Forall (fun kv => P (snd kv)) Γ
      ->  P (VClos Γ os id xs e))

    (HVTuple :
      forall vs,
          Forall (fun v => P v) vs
      ->  P (VTuple vs))

    (HVMap :
      forall vvs,
          Forall (fun vv => P (fst vv) /\ P (snd vv)) vvs
      ->  P (VMap vvs)).



  Theorem ind_bs_val :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall (fun v => P v))
      (R := Forall (fun vv => P (fst vv) /\ P (snd vv)))
      (W := Forall (fun kv => P (snd kv)));
      intuition.
  Defined.



End Induction_BigStep_Value.









Section Induction_BigStep_Expression.



  Variables
    (P : Expression -> Prop).



  Hypotheses
    (HEValues :
      forall es,
          Forall (fun e => P e) es
      ->  P (EValues es))

    (HENil :
          P ENil)

    (HELit :
      forall l,
          P (ELit l))

    (HEVar :
      forall x,
          P (EVar x))

    (HEFunId :
      forall f,
          P (EFunId f))

    (HEFun :
      forall xs e,
          P e
      ->  P (EFun xs e))

    (HECons :
      forall e₁ e₂,
          P e₁
      ->  P e₂
      ->  P (ECons e₁ e₂))

    (HETuple :
      forall es,
          Forall (fun e => P e) es
      ->  P (ETuple es))

    (HECall :
      forall ᵐe ᶠe es,
          P ᵐe
      ->  P ᶠe
      ->  Forall (fun e => P e) es
      ->  P (ECall ᵐe ᶠe es))

    (HEPrimOp :
      forall a es,
          Forall (fun e => P e) es
      ->  P (EPrimOp a es))

    (HEApp :
      forall ᶠe es,
          P ᶠe
      ->  Forall (fun e => P e) es
      ->  P (EApp ᶠe es))

    (HECase :
      forall e us,
          P e
      ->  Forall (fun psee => P (snd (fst psee)) /\ P (snd psee)) us
      ->  P (ECase e us))

    (HELet :
      forall xs₁ e₁ e₂,
          P e₁
      ->  P e₂
      ->  P (ELet xs₁ e₁ e₂))

    (HESeq :
      forall e₁ e₂,
          P e₁
      ->  P e₂
      ->  P (ESeq e₁ e₂))

    (HELetRec :
      forall os e,
          P e
      ->  Forall (fun fxse => P (snd (snd fxse))) os
      ->  P (ELetRec os e))

    (HEMap :
      forall ees,
          Forall (fun ee => P (fst ee) /\ P (snd ee)) ees
      ->  P (EMap ees))

    (HETry :
      forall e₁ xs₁ e₂ xsₓ e₃,
          P e₁
      ->  P e₂
      ->  P e₃
      ->  P (ETry e₁ xs₁ e₂ xsₓ e₃)).



  Theorem ind_bs_exp :
    forall e, P e.
  Proof.
    induction e using Expression_ind2 with
      (Q := Forall (fun e => P e))
      (R := Forall (fun ee => P (fst ee) /\ P (snd ee)))
      (W := Forall (fun psee => P (snd (fst psee)) /\ P (snd psee)))
      (Z := Forall (fun fxse => P (snd (snd fxse))));
      intuition.
  Defined.



End Induction_BigStep_Expression.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: INDUCTION_FRAMESTACK /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import SubstSemantics.



Section Induction_FrameStack_Value.



  Variables
    (P : Val -> Prop).



  Hypotheses
    (HVNil :
          P VNil)

    (HVLit :
      forall l,
          P (VLit l))

    (HVPid :
      forall p,
          P (VPid p))

    (HVVar :
      forall x,
          P (VVar x))

    (HVFunId :
      forall f,
          P (VFunId f))

    (HVCons :
      forall v₁ v₂,
          P v₁
      ->  P v₂
      ->  P (VCons v₁ v₂))

    (HVClos :
      forall os id n e,
        P (VClos os id n e))

    (HVTuple :
      forall vs,
          Forall (fun v => P v) vs
      ->  P (VTuple vs))

    (HVMap :
      forall vvs,
          Forall (fun vv => P (fst vv) /\ P (snd vv)) vvs
      ->  P (VMap vvs)).



  Theorem ind_fs_val :
    forall v, P v.
  Proof.
    induction v using Val_ind_weakened with
      (Q := Forall (fun v => P v))
      (R := Forall (fun vv => P (fst vv) /\ P (snd vv)));
      intuition.
  Defined.



End Induction_FrameStack_Value.









Section Induction_FrameStack_Expression.



  Variables
    (P : Exp -> Prop).



  Hypotheses
    (HEValues :
      forall el,
          Forall P el
      ->  P (EValues el))

    (HEFun :
      forall n e,
          P e
      ->  P (EFun n e))

    (HECons :
      forall e₁ e₂,
          P e₁
      ->  P e₂
      ->  P (ECons e₁ e₂))

    (HETuple :
      forall es,
          Forall (fun e => P e) es
      ->  P (ETuple es))

    (HECall :
      forall ᵐe ᶠe es,
          P ᵐe
      ->  P ᶠe
      ->  Forall (fun e => P e) es
      ->  P (ECall ᵐe ᶠe es))

    (HEPrimOp :
      forall a es,
          Forall (fun e => P e) es
      ->  P (EPrimOp a es))

    (HEApp :
      forall ᶠe es,
          P ᶠe
      ->  Forall (fun e => P e) es
      ->  P (EApp ᶠe es))

    (HECase :
      forall e us,
          P e
      ->  Forall (fun psee => P (snd (fst psee)) /\ P (snd psee)) us
      ->  P (ECase e us))

    (HELet :
      forall n₁ e₁ e₂,
          P e₁
      ->  P e₂
      ->  P (ELet n₁ e₁ e₂))

    (HESeq :
      forall e₁ e₂,
          P e₁
      ->  P e₂
      ->  P (ESeq e₁ e₂))

    (HELetRec :
      forall os e,
          P e
      ->  Forall (fun ne => P (snd ne)) os
      ->  P (ELetRec os e))

    (HEMap :
      forall ees,
          Forall (fun ee => P (fst ee) /\ P (snd ee)) ees
      ->  P (EMap ees))

    (HETry :
      forall e₁ n₁ e₂ nₓ e₃,
          P e₁
      ->  P e₂
      ->  P e₃
      ->  P (ETry e₁ n₁ e₂ nₓ e₃))

    (HVNil :
          P (˝VNil))

    (HVLit :
      forall l,
          P (˝VLit l))

    (HVPid :
      forall p,
          P (˝VPid p))

    (HVVar :
      forall x,
          P (˝VVar x))

    (HVFunId :
      forall f,
        P (˝VFunId f))

    (HVCons :
      forall v₁ v₂,
          P (˝v₁)
      ->  P (˝v₂)
      ->  P (˝VCons v₁ v₂))

    (HVClos :
      forall os id n e,
          P e
      ->  Forall (fun idne => P (snd idne)) os
      ->  P (˝VClos os id n e))

    (HVTuple :
      forall vs,
          Forall (fun v => P (˝v)) vs
      ->  P (˝(VTuple vs)))

    (HVMap :
      forall vvs,
          Forall (fun vv => P (˝fst vv) /\ P (˝snd vv)) vvs
      ->  P (˝(VMap vvs))).



  Theorem ind_fs_exp :
    forall e, P e.
  Proof.
    induction e using Exp_ind2 with
      (PV := fun v => P (˝v))
      (PE := fun e => P (°e))
      (Q  := Forall (fun e => P e))
      (QV := Forall (fun v => P (˝v)))
      (R  := Forall (fun ee => P (fst ee) /\ P (snd ee)))
      (RV := Forall (fun vv => P (˝fst vv) /\ P (˝snd vv)))
      (VV := Forall (fun idne => P (snd idne)))
      (W  := Forall (fun psee => P (snd (fst psee)) /\ P (snd psee)))
      (Z  := Forall (fun ne => P (snd ne)));
      intuition.
  Defined.



End Induction_FrameStack_Expression.