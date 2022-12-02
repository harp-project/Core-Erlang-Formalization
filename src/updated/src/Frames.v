Require Export ScopingLemmas.

Import ListNotations.

(** FrameStack *)
(** Based on Pitts' work: https://www.cl.cam.ac.uk/~amp12/papers/opespe/opespe-lncs.pdf *)
(*
Inductive Frame : Set :=
| FApp1 (l : list Exp) (* apply □(e₁, e₂, ..., eₙ) *)
| FApp2 (v : Exp) (l1 l2 : list Exp) (* apply v(v₁, v₂, ... vᵢ₋₁, □, eᵢ₊₁, ..., eₙ) *)
| FLet (v : Var) (e2 : Exp) (* let v = □ in e2 *)
| FPlus1 (e2 : Exp) (* □ + e2 *)
| FPlus2 (v : Exp) (* (p : is_value v) *) (* v + □ *)
| FCase (p : Pat) (e2 e3 : Exp) (* if □ then e2 else e3 *)
| FCons1 (e1 : Exp) (* [e1 | □] *)
| FCons2 (v2 : Exp) (* [□ | v2] *).
*)

Inductive Frame : Set :=

| FValues (lv : list ValueExpression) (le : list Expression)
(* EValues (v, ..., v, _, e, ..., e) *)

| FCons1 (hd : Expression)
(* ECons hd _ *) (* Here the evaluation starts from the second expression. *)

| FCons2 (tl : ValueExpression)
(* ECons _ tl *)

| FTuple (lv : list ValueExpression) (le : list Expression)
(* ETuple (v, ..., v, _, e, ..., e) *)

| FMap1 (lv : list (ValueExpression * ValueExpression))
          (sn : Expression)
          (le : list (Expression * Expression))
(* EMap ((v,v), ..., (v,v), (_,sn), (e,e), ..., (e,e)) *)

| FMap2 (lv : list (ValueExpression * ValueExpression))
          (fs : ValueExpression)
          (le : list (Expression * Expression))
(* EMap ((v,v), ..., (v,v), (fs,_), (e,e), ..., (e,e)) *)

| FCall   (f : string) (lv : list ValueExpression) (le : list Expression)
(* ECall f (v, ..., v, _, e, ..., e) *)

| FPrimOp (f : string) (lv : list ValueExpression) (le : list Expression)
(* FPrimOp f (v, ..., v, _, e, ..., e) *)

| FApp1 (l : list Expression)
(* EApp _ (e, ..., e) *)

| FApp2 (v : ValueExpression) (lv : list ValueExpression) (le : list Expression)
(* EApp v (v, ..., v, _, e, ..., e) *)

| FCase1 (l : list ((list Pattern) * Expression * Expression))
(* ECase _ ((pl, e, e) ..., (lp, e, e)) *)

(*| FCase2_p (v : ValueExpression)
           (lp : list Pattern)
           (ex : Expression)
           (le : list ((list Pattern) * Expression * Expression)) *)
| FCase2   (lv : list ValueExpression)
           (lp : list Pattern)
           (ex : Expression)
           (le : list ((list Pattern) * Expression * Expression))
           (lvp : list ValueExpression) (* the result of the pattern matching, only needed in the reduction rules *)
(* ECase v ((lp, _, ex), ..., (lp, e, e)) *)
(* FCase2_p means that the pattern matching was not done yet so the current guard expression (referenced by "_" or called the hole) does not need to be evaluated yet. *)
(* FCase2_g means that the last pattern matched so the current guard needs to be evaluated, so tha guard expression does not need to be evaluated yet. *)


| FLet   (l : nat) (e : Expression)
(* ELet l _ e *)

| FSeq   (e : Expression)
(* ESeq _ e *)

| FTry (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
(* ETry _ vl1 e2 vl2 e3 *)

.

(* Not needed*)
(*
Inductive frame_wf : Frame -> Prop :=
| wf_app1 l : frame_wf (FApp1 l)
| wf_app2 vl b l1 l2 :  Forall (fun v => VALCLOSED v) l2 -> frame_wf (FApp2 (EFun vl b) l1 l2)
| wf_let v e : frame_wf (FLet v e)
| wf_plus1 e : frame_wf (FPlus1 e)
| wf_plus2 v : VALCLOSED v -> frame_wf (FPlus2 v)
| wf_if p e2 e3 : frame_wf (FCase p e2 e3)
| wf_cons1 e : frame_wf (FCons1 e)
| wf_cons2 v : VALCLOSED v -> frame_wf (FCons2 v).
*)

(* Fill the hole in the frame *)
(*Definition plug_f (F : Frame) (e : Exp) : Exp :=
match F with
 | FApp1 l => EApp e l
 | FApp2 v l1 l2 => EApp v (l2 ++ [e] ++ l1)
 | FLet v e2 => ELet v e e2
 | FPlus1 e2 => EPlus e e2
 | FPlus2 v => EPlus v e
 | FCase p e2 e3 => ECase e p e2 e3
 | FCons1 e1 => ECons e1 e
 | FCons2 v2 => ECons e v2
end.*)


Definition plug_f (F : Frame) (e : Expression) : Expression :=
match F with
 | FValues lv le   => Exp (EValues ((map Val lv) ++ (cons e nil) ++ le))
 | FCons1 hd       => Exp (ECons hd e)
 | FCons2 tl       => Exp (ECons e (Val tl))
 | FTuple lv le    => Exp (ETuple ((map Val lv) ++ (cons e nil) ++ le))
 
 | FMap1 lv sn le  => 
        Exp (EMap ((map (fun '(v1,v2) => (Val v1, Val v2)) lv) ++ (cons (e,sn) nil) ++ le))
 | FMap2 lv fs le  => 
        Exp (EMap ((map (fun '(v1,v2) => (Val v1, Val v2)) lv) ++ (cons (Val fs, e) nil) ++ le))
 
 | FCall f lv le   => Exp (ECall f ((map Val lv) ++ (cons e nil) ++ le))
 | FPrimOp f lv le => Exp (EPrimOp f ((map Val lv) ++ (cons e nil) ++ le))
 | FApp1 l         => Exp (EApp e l)
 | FApp2 v lv le   => Exp (EApp (Val v) ((map Val lv) ++ (cons e nil) ++ le))
 | FCase1 l        => Exp (ECase e l)
 | FCase2 lv lp ex le lvp => (*TODO: if vl is a list how do we plug it into an expression*)
        Exp (ECase (Exp (EValues (map Val lv))) ((cons (lp,e,ex) nil) ++ le))
 (*| FCase2 v lp ex le lv => (* lv only carries information needed in the evaluation of ex *)
        Exp (ECase (Val v) ((cons (lp,e,ex) nil) ++ le))*)
 (*| FCase2_g v lp ex le =>
        Exp (ECase (Val v) ((cons (lp,e,ex) nil) ++ le)) *)

 | FLet l ex            => Exp (ELet l e ex)
 | FSeq ex              => Exp (ESeq e ex)
 | FTry vl1 e2 vl2 e3   => Exp (ETry e vl1 e2 vl2 e3)
end.

Definition FrameStack := list Frame.

(* All Exp Closed *)
(*Inductive FCLOSED : Frame -> Prop :=
| fclosed_app1 l:
  Forall (fun e => EXPCLOSED e) l
->
  FCLOSED (FApp1 l)
| fclosed_app2 v l1 l2:
  VALCLOSED v -> Forall (fun e => EXPCLOSED e) l1 -> Forall (fun e => VALCLOSED e) l2
->
  FCLOSED (FApp2 v l1 l2)
| fclosed_let e2 v :
  EXP 1 ⊢ e2
->
  FCLOSED (FLet v e2)
| fclosed_plus1 e2:
  EXPCLOSED e2
->
  FCLOSED (FPlus1 e2)
| fclosed_plus2 v1:
  VALCLOSED v1
->
  FCLOSED (FPlus2 v1)
| fclosed_if e2 e3 p:
  EXP pat_vars p ⊢ e2 -> EXPCLOSED e3
->
  FCLOSED (FCase p e2 e3)
| fclosed_cons1 e1:
  EXPCLOSED e1
->
  FCLOSED (FCons1 e1)
| fclosed_cons2 v:
  VALCLOSED v
->
  FCLOSED (FCons2 v). *)

Inductive FCLOSED : Frame -> Prop :=
| FCLOSED_FValues lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FValues lv le)

| FCLOSED_FCons1 hd :
  EXPCLOSED hd
  ->
  FCLOSED (FCons1 hd)

| FCLOSED_FCons2 tl :
  VALCLOSED tl
  ->
  FCLOSED (FCons2 tl)

| FCLOSED_FTuple lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FTuple lv le)

| FCLOSED_FMap1 lv sn le :
  (forall i, i < length lv -> VALCLOSED (nth i (map fst lv) (VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i (map snd lv) (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map fst le) (Val VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd le) (Val VNil))) ->
  EXPCLOSED sn
  ->
  FCLOSED (FMap1 lv sn le)

| FCLOSED_FMap2 lv fs le :
  (forall i, i < length lv -> VALCLOSED (nth i (map fst lv) (VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i (map snd lv) (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map fst le) (Val VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd le) (Val VNil))) ->
  VALCLOSED fs
  ->
  FCLOSED (FMap2 lv fs le)

| FCLOSED_FCall f lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FCall f lv le)

| FCLOSED_FPrimOp f lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FPrimOp f lv le)

| FCLOSED_FApp1 l :
  (forall i, i < length l -> EXPCLOSED (nth i l (Val VNil)))
  ->
  FCLOSED (FApp1 l)

| FCLOSED_FApp2 v lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil))) ->
  VALCLOSED v
  ->
  FCLOSED (FApp2 v lv le)

| FCLOSED_FCase1 l :
  (forall i, i < length l -> EXP (patternListScope (nth i (map fst (map fst l)) nil)) ⊢ (nth i (map snd (map fst l)) (Val VNil))) ->
  (forall i, i < length l -> EXP (patternListScope (nth i (map fst (map fst l)) nil)) ⊢ (nth i (map snd l) (Val VNil)))
  ->
  FCLOSED (FCase1 l)
  
  
| FCLOSED_FCase2 lv lp ex le lvp :
  (forall i, i < length le -> EXP (patternListScope (nth i (map fst (map fst le)) nil)) ⊢ (nth i (map snd (map fst le)) (Val VNil))) ->
  (forall i, i < length le -> EXP (patternListScope (nth i (map fst (map fst le)) nil)) ⊢ (nth i (map snd le) (Val VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length lvp -> VALCLOSED (nth i lvp (VNil))) -> (*TODO it will stay for now, but not sure if needed *)
  EXP (patternListScope lp) ⊢ ex
  ->
  FCLOSED (FCase2 lv lp ex le lvp)
(*
| FCLOSED_FCase2 v lp ex le lv:
  (forall i, i < length le -> EXP (patternListScope (nth i (map fst (map fst le)) nil)) ⊢ (nth i (map snd (map fst le)) (Val VNil))) ->
  (forall i, i < length le -> EXP (patternListScope (nth i (map fst (map fst le)) nil)) ⊢ (nth i (map snd le) (Val VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  VALCLOSED v  ->
  EXP (patternListScope lp) ⊢ ex
  ->
  FCLOSED (FCase2 v lp ex le lv)*)
(*
| FCLOSED_FCase2_g v lp ex le :
  (forall i, i < length le -> EXP (patternListScope (nth i (map fst (map fst le)) nil)) ⊢ (nth i (map snd (map fst le)) (Val VNil))) ->
  (forall i, i < length le -> EXP (patternListScope (nth i (map fst (map fst le)) nil)) ⊢ (nth i (map snd le) (Val VNil))) ->
  VALCLOSED v  ->
  EXP (patternListScope lp) ⊢ ex
  ->
  FCLOSED (FCase2_g v lp ex le) *)

| FCLOSED_FLet l ex :
  EXP l ⊢ ex
  ->
  FCLOSED (FLet l ex)


| FCLOSED_FSeq ex :
  EXPCLOSED ex
  ->
  FCLOSED (FSeq ex)

| FCLOSED_FTry vl1 e2 vl2 e3 :
  EXP vl1 ⊢ e2 ->
  EXP vl2 ⊢ e3
  ->
  FCLOSED (FTry vl1 e2 vl2 e3)
.

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.
(* TODO: Should I use this definition, and what should be the default element? *)
(* Definition FSCLOSED (fs : FrameStack) := (forall i, (i < length fs) -> FCLOSED (nth i fs (FValues [] []))). *)

Lemma scoped_list_subscoped :
  forall vals Γ ξ Γ', Forall (fun v => VAL Γ ⊢ v) vals -> SUBSCOPE Γ' ⊢ ξ ∷ Γ ->
  SUBSCOPE length vals + Γ' ⊢ list_subst vals ξ ∷ Γ.
Proof.
  induction vals; intros; simpl; auto.
  simpl. inversion H. intro. intros. destruct v.
  * simpl. apply H3.
  * simpl. specialize (IHvals _ _ _ H4 H0 v). apply IHvals. lia.
Qed.

Lemma scoped_list_idsubst :
  forall vals Γ, Forall (fun v => VAL Γ ⊢ v) vals ->
  SUBSCOPE length vals ⊢ list_subst vals idsubst ∷ Γ.
Proof.
  induction vals; intros. simpl.
  unfold idsubst. intro. intros. inversion H0.
  simpl. inversion H. intro. intros. destruct v.
  * simpl. apply H2.
  * simpl. apply IHvals; auto. lia.
Qed.

Lemma substcomp_scoped :
  forall ξ σ Γ Δ Ω, SUBSCOPE Γ ⊢ ξ ∷ Δ -> SUBSCOPE Δ ⊢ σ ∷ Ω
->
  SUBSCOPE Γ ⊢ ξ >> σ ∷ Ω.
Proof.
  intros. intro. intros. unfold subscoped in H.
  unfold ">>".
  specialize (H v H1).
  destruct (ξ v) eqn:D1.
  * apply -> subst_preserves_scope_val; eassumption.
  * specialize (H0 n H). auto.
Qed.

(* Needs help *)
(*
Theorem match_pattern_scoped : forall p v l Γ,
  VAL Γ ⊢ v -> match_pattern p v = Some l
->
  Forall (fun v => VAL Γ ⊢ v) l.
Proof.
  induction p; intros.
  * simpl in *. destruct v; inversion H0. break_match_hyp; inversion H0. auto.
  * simpl in *. destruct v; inversion H0; subst; auto.
  * simpl in *. destruct v; inversion H0. subst. auto.
  * simpl. simpl in H0. destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion H0.
    subst. apply Forall_app. split.
    - inversion H. subst. eapply IHp1. exact H3. auto.
    - inversion H. subst. eapply IHp2. exact H4. auto.
Qed.
*)

(* Not needed *)
(*
Ltac inversion_is_value :=
match goal with
| [ H: VAL _ ⊢ (ELet _ _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (ELetRec _ _ _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EPlus _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (ECase _ _ _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EApp _ _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EVar _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (EFunId _) |- _ ] => inversion H
| [ H: VAL _ ⊢ (ECons _ _) |- _ ] => inversion H
end.
*)