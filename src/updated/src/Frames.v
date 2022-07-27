Require Export ScopingLemmas.

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

| FEValues (lv : list ValueExpression) (le : list Expression)
(* EValues (v, ..., v, _, e, ..., e) *)

| FECons1 (tl : Expression)
(* ECons _ tl *)

| FECons2 (hd : ValueExpression)
(* ECons hd _ *)

| FETuple (lv : list ValueExpression) (le : list Expression)
(* ETuple (v, ..., v, _, e, ..., e) *)

| FEMap1 (lv : list (ValueExpression * ValueExpression))
          (sn : Expression)
          (le : list (Expression * Expression))
(* EMap ((v,v), ..., (v,v), (_,sn), (e,e), ..., (e,e)) *)

| FEMap2 (lv : list (ValueExpression * ValueExpression))
          (fs : ValueExpression)
          (le : list (Expression * Expression))
(* EMap ((v,v), ..., (v,v), (fs,_), (e,e), ..., (e,e)) *)

| FECall   (f : string) (lv : list ValueExpression) (le : list Expression)
(* ECall f (v, ..., v, _, e, ..., e) *)

| FEPrimOp (f : string) (lv : list ValueExpression) (le : list Expression)
(* FPrimOp f (v, ..., v, _, e, ..., e) *)

| FEApp1 (l : list Expression)
(* EApp _ (e, ..., e) *)

| FEApp2 (v : ValueExpression) (lv : list ValueExpression) (le : list Expression)
(* EApp v (v, ..., v, _, e, ..., e) *)

| FECase1 (l : list ((list Pattern) * Expression * Expression))
(* ECase _ ((pl, e, e) ..., (lp, e, e)) *)

| FECase2a (v : ValueExpression)
           (lv : list ((list Pattern) * ValueExpression * ValueExpression))
           (lp : list Pattern)
           (ex : Expression)
           (le : list ((list Pattern) * Expression * Expression))
(* ECase v ((pl, v, v) ..., (pl, _, ex), ..., (lp, e, e)) *)

| FECase2b (v : ValueExpression)
           (lv : list ((list Pattern) * ValueExpression * ValueExpression))
           (lp : list Pattern)
           (vx : ValueExpression)
           (le : list ((list Pattern) * Expression * Expression))
(* ECase v ((pl, v, v) ..., (pl, v, _), ..., (lp, e, e)) *)

| FELet1   (l : nat) (e : Expression)
(* ELet l _ e *)

| FELet2   (l : nat) (v : ValueExpression)
(* ELet l v _ *)

| FESeq1   (e : Expression)
(* ESeq _ e *)

| FESeq2   (v : ValueExpression)
(* ESeq v _ *)

| FETry (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
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

Search "++".

Definition plug_f (F : Frame) (e : Expression) : Expression :=
match F with
 | FEValues lv le   => Exp (EValues ((map Val lv) ++ (cons e nil) ++ le))
 | FECons1 tl       => Exp (ECons e tl)
 | FECons2 hd       => Exp (ECons (Val hd) e)
 | FETuple lv le    => Exp (ETuple ((map Val lv) ++ (cons e nil) ++ le))
 
 | FEMap1 lv sn le  => 
        Exp (EMap ((map (fun '(v1,v2) => (Val v1, Val v2)) lv) ++ (cons (e,sn) nil) ++ le))
 | FEMap2 lv fs le  => 
        Exp (EMap ((map (fun '(v1,v2) => (Val v1, Val v2)) lv) ++ (cons (Val fs, e) nil) ++ le))
 
 | FECall f lv le   => Exp (ECall f ((map Val lv) ++ (cons e nil) ++ le))
 | FEPrimOp f lv le => Exp (EPrimOp f ((map Val lv) ++ (cons e nil) ++ le))
 | FEApp1 l         => Exp (EApp e l)
 | FEApp2 v lv le   => Exp (EApp (Val v) ((map Val lv) ++ (cons e nil) ++ le))
 | FECase1 l        => Exp (ECase e l)
 
 | FECase2a v lv lp ex le =>
        Exp (ECase (Val v) ((map (fun '(p,v1,v2) => (p, Val v1, Val v2)) lv) ++ (cons (lp,e,ex) nil) ++ le))
 | FECase2b v lv lp vx le =>
        Exp (ECase (Val v) ((map (fun '(p,v1,v2) => (p, Val v1, Val v2)) lv) ++ (cons (lp,Val v,e) nil) ++ le))

 | FELet1 l ex            => Exp (ELet l e ex)
 | FELet2 l v             => Exp (ELet l (Val v) e)
 | FESeq1 ex              => Exp (ESeq e ex)
 | FESeq2 v               => Exp (ESeq (Val v) e)
 | FETry vl1 e2 vl2 e3    => Exp (ETry e vl1 e2 vl2 e3)
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
| FCLOSED_FEValues lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FEValues lv le)

| FCLOSED_FECons1 tl :
  EXPCLOSED tl
  ->
  FCLOSED (FECons1 tl)

| FCLOSED_FECons2 hd :
  VALCLOSED hd
  ->
  FCLOSED (FECons2 hd)

| FCLOSED_FETuple lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FETuple lv le)

| FCLOSED_FEMap1 lv sn le :
  (forall i, i < length lv -> VALCLOSED (nth i (map fst lv) (VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i (map snd lv) (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map fst le) (Val VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd le) (Val VNil))) ->
  EXPCLOSED sn
  ->
  FCLOSED (FEMap1 lv sn le)

| FCLOSED_FEMap2 lv fs le :
  (forall i, i < length lv -> VALCLOSED (nth i (map fst lv) (VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i (map snd lv) (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map fst le) (Val VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd le) (Val VNil))) ->
  VALCLOSED fs
  ->
  FCLOSED (FEMap2 lv fs le)

| FCLOSED_FECall f lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FECall f lv le)

| FCLOSED_FEPrimOp f lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil)))
  ->
  FCLOSED (FEPrimOp f lv le)

| FCLOSED_FEApp1 l :
  (forall i, i < length l -> EXPCLOSED (nth i l (Val VNil)))
  ->
  FCLOSED (FEApp1 l)

| FCLOSED_FEApp2 v lv le :
  (forall i, i < length lv -> VALCLOSED (nth i lv (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i le (Val VNil))) ->
  VALCLOSED v
  ->
  FCLOSED (FEApp2 v lv le)

| FCLOSED_FECase1 l :
  (forall i, i < length l -> EXPCLOSED (nth i (map snd (map fst l)) (Val VNil))) ->
  (forall i, i < length l -> EXPCLOSED (nth i (map snd l) (Val VNil)))
  ->
  FCLOSED (FECase1 l)

| FCLOSED_FECase2a v lv lp ex le :
  (forall i, i < length lv -> VALCLOSED (nth i (map snd (map fst lv)) (VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i (map snd lv) (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd (map fst le)) (Val VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd le) (Val VNil))) ->
  VALCLOSED v  ->
  EXPCLOSED ex
  ->
  FCLOSED (FECase2a v lv lp ex le)

| FCLOSED_FECase2b v lv lp vx le :
  (forall i, i < length lv -> VALCLOSED (nth i (map snd (map fst lv)) (VNil))) ->
  (forall i, i < length lv -> VALCLOSED (nth i (map snd lv) (VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd (map fst le)) (Val VNil))) ->
  (forall i, i < length le -> EXPCLOSED (nth i (map snd le) (Val VNil))) ->
  VALCLOSED v  ->
  VALCLOSED vx
  ->
  FCLOSED (FECase2b v lv lp vx le)

| FCLOSED_FELet1 l ex :
  EXPCLOSED ex
  ->
  FCLOSED (FELet1 l ex)

| FCLOSED_FELet2 l v :
  VALCLOSED v
  ->
  FCLOSED (FELet2 l v)

| FCLOSED_FESeq1 ex :
  EXPCLOSED ex
  ->
  FCLOSED (FESeq1 ex)

| FCLOSED_FESeq2 v :
  VALCLOSED v
  ->
  FCLOSED (FESeq2 v)

| FCLOSED_FETry vl1 e2 vl2 e3 :
  EXPCLOSED e2 ->
  EXPCLOSED e3
  ->
  FCLOSED (FETry vl1 e2 vl2 e3)
.

Definition FSCLOSED (fs : FrameStack) := Forall FCLOSED fs.

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