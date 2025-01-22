From CoreErlang.Eq.Tactics Require Export T1ParamZero.
From CoreErlang.Eq.Tactics Require Export T2ParamSingle.
From CoreErlang.Eq.Tactics Require Export T3ParamMultiple.
From CoreErlang.Eq.Tactics Require Export T4Name.
From CoreErlang.Eq.Tactics Require Export T5Transform.
From CoreErlang.Eq.Tactics Require Export T6Destruct.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.





Import BigStep.

Section Induction_Value.



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
      forall ref ext id params body funid,
          Forall (fun x => P (snd x)) ref
      ->  P (VClos ref ext id params body funid))

    (HTuple :
      forall l,
          Forall P l
      ->  P (VTuple l))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (VMap l)).



  Theorem ind_val :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd x)));
      intuition.
  Defined.



End Induction_Value.






Section Induction_Expression.



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


  (** DOCUMENTATION:
  * FULL NAME:
    - Induction on BigStep Expression
  * OLD NAME:
    - derived_Expression_ind, expression_ind, val_exp
  * USING:
    - Project:
      + Lemmas: Expression_ind2
  * USED AT:
    - SubstitueLemmas:
      + subst_env_empty [Not Using]
    - MeasureLemmas:
      + mexp_val
    - ConverterLemmas:
      + bexp_to_fexp_add_vars_comm
      + bexp_to_fexp_add_vars
  * HISTORY:
    - First created for 'subst_env_empty',
      because the regular induction on expression wasn't enought
    - Later I found out, that I doesn't need 'subst_env_empty',
      but creating ind_exp wasn't useless, becasuse later I need it,
      in different necessary theorems
  *)
  Theorem ind_exp :
    forall e, P e.
  Proof.
    induction e using Expression_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd (fst x)) /\ P (snd x)))
      (Z := Forall (fun x => P (snd (snd x)))); intuition.
  Defined.



End Induction_Expression.
































































(*
subs_list_app ?
*)




Lemma cons_app :
  forall (T : Type) (x : T) (l : list T),
    x :: l = [x] ++ l.
Proof.
  trv.
Qed.

(* 
Lemma upren_smp :
    (fun x =>
      match x with
      | 0 => inr 0
      | S x' => inr (S x')
      end)
  = (fun x => inr x). *)
(* Lemma match_smp :
  forall x : nat,
    (match x with
    | 0 => (inr 0) : (Val + nat)
    | S x' => (inr (S x')) : (Val + nat)
    end) : (Val + nat)
  = (inr x) : (Val + nat). *)
  
(*NOTUSED*)
Lemma uprenS :
  forall n,
  upren id n = id n.
Proof.
  itr.
  ufl - upren.
  unfold id.
  des - n; ato.
Qed.



(* Lemma upren_idsubst :
  forall n,
  upren id n = id n.
Proof.
  itr.
  ufl - upren.
  unfold id.
  des - n; ato.
Qed. *)


Lemma exp_idsubst_is_id :
  forall e,
    e.[idsubst] = e.
Proof.
  pse - idsubst_is_id.
  des - H as [Hid _].
  trv.
Qed.


Lemma nval_idsubst_is_id :
  forall e,
    e.[idsubst]ₑ = e.
Proof.
  pse - idsubst_is_id.
  des - H as [_ [Hid _]].
  trv.
Qed.


Lemma val_idsubst_is_id :
  forall e,
    e.[idsubst]ᵥ = e.
Proof.
  pse - idsubst_is_id.
  des - H as [_ [_ Hid]].
  trv.
Qed.





Lemma up_subst_idsubst_forall :
  forall n,
  up_subst idsubst n = idsubst n.
Proof.
  itr.
  ufl - up_subst.
  unfold idsubst.
  des - n: trv.
  ufl - Manipulation.shift.
  trv.
Qed.

Lemma up_subst_idsubst :
  up_subst idsubst = idsubst.
Proof.
  itr.
  pse - up_subst_idsubst_forall.
  ufl - up_subst in *.
  apply functional_extensionality.
  intro n.
  apply H.
Qed.


Lemma upn_one :
  forall e v,
    e.[upn (length [v]) idsubst]
     .[list_subst [v] idsubst]
  = e.[list_subst [v] idsubst].
Proof.
  itr.
  smp.
  rwr - up_subst_idsubst.
  rwr - exp_idsubst_is_id.
  trv.
Qed.


Lemma upn_two :
  forall e v1 v2,
    e.[upn (length [v1]) (list_subst [v2] idsubst)]
     .[list_subst [v1] idsubst]
  = e.[list_subst ([v1] ++ [v2]) idsubst].
Proof.
  admit.
Admitted.


Lemma upn_all :
  forall e v s,
    e.[upn (length [v]) s]
     .[list_subst [v] idsubst]
  = e.[list_subst [v] s].
Proof.
  itr.
  smp.
  des - e.
  * (* ind ~ ind_val - e. *)
    ind - e.
    - bmp.
    - bmp.
    - bmp.
    - smp.
      do 2 feq.
      + by injection IHe1.
      + by injection IHe2.
    - admit.
    - admit.
    - smp.
      do 1 feq.
      ind - n.
      + bmp.
      + smp *.
      unfold scons.
      unfold up_subst.
      unfold Manipulation.shift.
Admitted.





(*IMPORTANT*)
Lemma list_subst_cons :
  forall v vs ξ,
    list_subst [v] (list_subst vs ξ)
  = list_subst (v::vs) ξ.
Proof.
  trv.
Qed.

(*IMPORTANT*)
Lemma list_subst_fold_right :
  forall vs ξ,
    fold_right (fun v σ => v .: σ) ξ vs
  = list_subst vs ξ.
Proof.
  trv.
Qed.

(*IMPORTANT*)
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




(* Theorem list_subst_app_upn :
  forall e vs1 vs2,
    e.[list_subst (vs1 ++ vs2) idsubst]
  = e.[upn (length vs1)
      (list_subst vs2 idsubst)]
     .[list_subst vs1 idsubst].
Proof.
  itr.
  ind - vs1.
  * smp.
    pse - idsubst_is_id.
    des - H as [Hid _].
    bwr - Hid.
  * rwr - cons_app.
Restart.
  itr.
  gen - vs1.
  ind - vs2 as [| v2 vs2 IH]; itr.
  * smp.
    rwr - app_nil_r.
    Search (_ ++ []).
    pse - idsubst_is_id.
    des - H as [Hid _].
    (* rwr - Hid. *)
Admitted.  *)
















Lemma subst_transitive :
  forall e1 e2 e3 vs1 vs2,
      e1.[list_subst vs1 idsubst] = e2
  ->  e2.[list_subst vs2 idsubst] = e3
  ->  e1.[list_subst (vs1 ++ vs2) idsubst] = e3.
Proof.
  itr - e1.
  des - e1 as [v1 | v2].
  * ind - v1; itr -  e2 e3 vs1 vs2 HStep1 HStep2.
    - smp *.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      exa - HStep2.
    - smp *.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      exa - HStep2.
    - smp *.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      exa - HStep2.
    - smp *.
      des - e2 as [v2 | e2].
      2: des - e2 :- con.
      des - v2 :- con.
      smp *.
      des - e3 as [v3 | e3].
      2: des - e3 :- con.
      des - v3 :- con.
      ivr - HStep1 as Hv1_1 Hv1_2: H0 H1 / HStep1.
      ivr - HStep2 as Hv2_1 Hv2_2: H0 H1 / HStep2.
      psc - f_equal as He1_1:
        Val Exp VVal (v1_1.[list_subst vs1 idsubst]ᵥ) v2_1 Hv1_1.
      psc - f_equal as He1_2:
        Val Exp VVal (v1_2.[list_subst vs1 idsubst]ᵥ) v2_2 Hv1_2.
      psc - f_equal as He2_1:
        Val Exp VVal (v2_1.[list_subst vs2 idsubst]ᵥ) v3_1 Hv2_1.
      psc - f_equal as He2_2:
        Val Exp VVal (v2_2.[list_subst vs2 idsubst]ᵥ) v3_2 Hv2_2.
      specialize (IHv1_1 _ _ _ _ He1_1 He2_1).
      specialize (IHv1_2 _ _ _ _ He1_2 He2_2).
      do 2 feq.
      + ivc - IHv1_1.
        ivc - He2_1.
        rfl.
      + ivc - IHv1_2.
        ivc - He2_2.
        rfl.
    - admit.
    - admit.
    - smp *.
      rwl - list_subst_app.
      rwl - HStep2 HStep1.
      ind - vs2.
      + smp.
        bwr - val_idsubst_is_id.
      + admit.      
Admitted.



Lemma subst_transitive1 :
  forall e1 e2 vs1 vs2,
      e2 = e1.[list_subst (vs1 ++ vs2) idsubst]
  ->  e2 = e1.[list_subst vs1 idsubst].[list_subst vs2 idsubst].
Proof.
  itr - e1.
  des - e1.
  * ren - v1: e.
    smp.
    ind - v1; itr.
    - smp *; trv.
    - smp *; trv.
    - smp *; trv.
    - admit.
    - admit.
    - admit.
    - smp *.
      rwl - list_subst_app in H.
      rem - s: (list_subst vs2 idsubst).
      admit.
Admitted.

Print compose.
Print subst_ren.

Lemma subst_transitive2 :
  forall e1 e2 vs1 vs2,
      e2 = (subst σ_2 (subst σ_1 e1))
  ->  e2 = (subst σ e1).
Proof.
  itr.










Lemma subst_transitive2 :
  forall e1 e2 e3 vs1 vs2 ξ,
      e1.[list_subst vs1 ξ] = e2
  ->  e2.[list_subst vs2 ξ] = e3
  ->  e1.[list_subst (vs1 ++ vs2) ξ] = e3.
Proof.
  itr - e1.
  des - e1 as [v1 | v2].
  * ind - v1; itr -  e2 e3 vs1 vs2 ξ HStep1 HStep2.
    - smp *.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      exa - HStep2.
    - smp *.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      exa - HStep2.
    - smp *.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      exa - HStep2.
    - smp *.
      ivr - HStep1.
      rwl - HStep1 in HStep2.
      smp - HStep2.
      (* exa - HStep2. *)
Admitted.
(* Lemma subst_unfold :
  forall s σ,
    s .[ σ ]
  = subst σ s.
Proof.
  trv.
Qed.

Lemma scons_unfold :
  forall s (σ : Substitution),
    s .: σ 
  = scons (inl s) σ.
Proof.
  itr.
  unfold scons.
  fold scons.
  rewrite <- (scons (inl s) σ).
  trv.
Qed. *)

Lemma list_subst_trans :
  forall e vs1 vs2,
    e.[list_subst vs1 idsubst].[list_subst vs2 idsubst]
  = e.[list_subst (vs1 ++ vs2) idsubst].
Proof.
  itr.
  rem  - e' as He':
    (e.[list_subst vs1 idsubst]).
  rem  - e'' as He'':
    (e'.[list_subst vs2 idsubst]).
  (* rewrite subst_unfold.
  smp.
  ufl - list_subst.
  unfold scons.
  unfold idsubst.
  (* unfold subst. *)
  rwr - foldr_app.
  
  
  Search "foldr" "app".
  smp. *)
Admitted.
(* Lemma subst_trans :
  forall s1 s2 s3 ,
 *)  


Lemma upn_cons :
  forall e v vs,
    e.[upn (length [v]) (list_subst vs idsubst)]
     .[list_subst [v] idsubst]
  = e.[list_subst [v] (list_subst vs idsubst)].
Proof.
  itr.
  smp.
  rem - s as Hs: (list_subst vs idsubst).
  unfold scons.
  unfold up_subst.
  unfold Manipulation.shift.
  unfold idsubst.
  feq.
  ufl - list_subst.
  smp.
Admitted.


Lemma upn_idsubst_cons :
  forall e v s,
    e.[upn (length [v]) s]
     .[list_subst [v] idsubst]
  = e.[list_subst [v] s].
Proof.
  itr.
  smp.
  unfold scons.
  unfold up_subst.
  unfold Manipulation.shift.
(*   rwr - up_subst_idsubst.
  rwr - exp_idsubst_is_id.
  trv. *)
Admitted.



Lemma upn_self_one :
  forall e v vs,
    e.[upn 1 (list_subst vs idsubst)]
     .[list_subst [v] idsubst]
  = e.[list_subst (v::vs) idsubst].
Proof.
  itr.
  gen - v.
  pse - idsubst_is_id.
  des - H as [Hid _].
  ind - vs as [| v1 vs IHvs]; itr.
  * smp.
    bwr - up_subst_idsubst Hid.
  * rewrite <- list_subst_cons with (vs := (v1 :: vs)).
    (* rewrite cons_app with (l := v1 :: vs).
    rewrite cons_app with (l := vs).
    rewrite cons_app with (l := vs) in IHvs. *)
Restart.
  itr.
  rewrite <- list_subst_cons with (vs := vs).
  
Admitted.

Lemma upn_self :
  forall e vs,
    e.[upn (length vs) idsubst].[list_subst vs idsubst]
  = e.[list_subst vs idsubst].
Proof.
  itr.
  pse - idsubst_is_id.
  des - H as [Hid _].
  ind - vs as [| v vs IHvs].
  * smp.
    by do 2 rwr - Hid.
  * rwr - cons_app.
Admitted.

Theorem list_subst_app1 :
  forall e vs1 vs2,
    e.[list_subst (vs1 ++ vs2) idsubst]
  = e.[upn (length vs1)
      (list_subst vs2 idsubst)]
     .[list_subst vs1 idsubst].
Proof.
  itr.
  ind - vs1.
  * smp.
    pse - idsubst_is_id.
    des - H as [Hid _].
    bwr - Hid.
  * rwr - cons_app.
Restart.
  itr.
  gen - vs1.
  ind - vs2 as [| v2 vs2 IH]; itr.
  * smp.
    rwr - app_nil_r.
    Search (_ ++ []).
    pse - idsubst_is_id.
    des - H as [Hid _].
    (* rwr - Hid. *)
Admitted. 