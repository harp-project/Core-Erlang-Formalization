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
    (HNil : P VNil)

    (HLit :
      forall l,
        P (VLit l))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (VCons hd tl))

    (HClos :
      forall ref ext id params body,
          Forall (fun x => P (snd x)) ref
      ->  P (VClos ref ext id params body))

    (HTuple :
      forall l,
          Forall P l
      ->  P (VTuple l))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (VMap l)).



  Theorem ind_bs_val :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd x)));
      intuition.
  Defined.



End Induction_BigStep_Value.









Section Induction_BigStep_Expression.



  Variables
    (P : Expression -> Prop).



  Hypotheses
    (HValues :
      forall el,
          Forall P el
      ->  P (EValues el))

    (HNil : P ENil)

    (HLit :
      forall l,
          P (ELit l))

    (HVar :
      forall v,
          P (EVar v))

    (HFunId :
      forall f,
        P (EFunId f))

    (HFun :
      forall vl e,
          P e
      ->  P (EFun vl e))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (ECons hd tl))

    (HTuple :
      forall l,
          Forall P l
      ->  P (ETuple l))

    (HCall :
      forall m f l,
          P m
      ->  P f
      ->  Forall P l
      ->  P (ECall m f l))

    (HPrimOp :
      forall f l,
          Forall P l
      ->  P (EPrimOp f l))

    (HApp :
      forall exp l,
          P exp
      ->  Forall P l
      ->  P (EApp exp l))

    (HCase :
      forall e l,
          P e
      ->  Forall (fun x => P (snd (fst x)) /\ P (snd x)) l
      ->  P (ECase e l))

    (HLet :
      forall l e1 e2,
          P e1
      ->  P e2
      ->  P (ELet l e1 e2))

    (HSeq :
      forall e1 e2,
          P e1
      ->  P e2
      ->  P (ESeq e1 e2))

    (HLetRec :
      forall l e,
          P e
      ->  Forall (fun x => P (snd (snd x))) l
      ->  P (ELetRec l e))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (EMap l))

    (HTry :
      forall e1 vl1 e2 vl2 e3,
          P e1
      ->  P e2
      ->  P e3
      ->  P (ETry e1 vl1 e2 vl2 e3)).



  Theorem ind_vs_exp :
    forall e, P e.
  Proof.
    induction e using Expression_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd (fst x)) /\ P (snd x)))
      (Z := Forall (fun x => P (snd (snd x)))); intuition.
  Defined.



End Induction_BigStep_Expression.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: INDUCTION_FRAMESTACK /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import SubstSemantics.