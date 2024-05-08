From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.
Import ListNotations.

Definition LiteralToLit (l : Literal) : Lit :=
match l with
 | BigStep.Syntax.Atom s => s
 | BigStep.Syntax.Integer x => x
end.

Fixpoint eraseNamesPat (p : Pattern) : Pat :=
match p with
 | BigStep.Syntax.PVar v => PVar
 | BigStep.Syntax.PLit l => PLit (LiteralToLit l)
 | BigStep.Syntax.PCons hd tl => PCons (eraseNamesPat hd) (eraseNamesPat tl)
 | BigStep.Syntax.PTuple l => PTuple (map eraseNamesPat l)
 | BigStep.Syntax.PMap l => PMap (map (fun '(x, y) => (eraseNamesPat x, eraseNamesPat y)) l)
 | BigStep.Syntax.PNil => PNil
end.


Definition NameSub {T} {dec : T -> T -> bool} := T -> nat.

Definition addName {T dec} (v : T) (σ : @NameSub _ dec) :=
  fun x => if dec x v
           then 0
           else S (σ x).

Definition addNames {T} {dec : T -> T -> bool} (vl : list T) (σ : NameSub) : NameSub :=
  fold_right (@addName _ dec) σ vl.

Definition varsOfPatternList (l : list Pattern) : list BigStep.Syntax.Var :=
  fold_right (fun x acc => variable_occurances x ++ acc) nil l
.

Definition sum_eqb {A B : Type} (eqbA : A -> A -> bool) (eqbB : B -> B -> bool) (a b : A + B) : bool :=
match a, b with
| inl a', inl b' => eqbA a' b'
| inr a', inr b' => eqbB a' b'
| _, _ => false
end.

Definition addVars (vl : list string) (σ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb)) :=
  addNames (map inl vl) σ.

Definition addFids (vl : list FunctionIdentifier) (σ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb)) :=
  addNames (map inr vl) σ.

Fixpoint eraseNames (σᵥ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) (* (: @NameSub (string * nat) (prod_eqb eqb Nat.eqb)) *)
  (e : Expression) : Exp :=
match e with
 | BigStep.Syntax.EValues el => EValues (map (eraseNames σᵥ) el)
 | ENil => ˝VNil
 | ELit l => ˝VLit (LiteralToLit l)
 | EVar v => ˝VVar (σᵥ (inl v))
 | EFunId f => ˝VFunId ((σᵥ (inr f)), snd f)
 | BigStep.Syntax.EFun vl e => EFun (length vl) (eraseNames (addVars vl σᵥ) e)
 | BigStep.Syntax.ECons hd tl => ECons (eraseNames σᵥ hd) (eraseNames σᵥ tl)
 | BigStep.Syntax.ETuple l => ETuple (map (eraseNames σᵥ) l)
 | BigStep.Syntax.ECall m f l => ECall (eraseNames σᵥ m) (eraseNames σᵥ f) (map (eraseNames σᵥ) l)
 | BigStep.Syntax.EPrimOp f l => EPrimOp f (map (eraseNames σᵥ) l)
 | BigStep.Syntax.EApp exp l => EApp (eraseNames σᵥ exp) (map (eraseNames σᵥ) l)
 | BigStep.Syntax.ECase e l => ECase (eraseNames σᵥ e) (map (fun '(pl, g, b) =>
                                     ((map eraseNamesPat pl), eraseNames (addVars (varsOfPatternList pl) σᵥ) g, eraseNames (addVars (varsOfPatternList pl) σᵥ) b))
                                     l)
 | BigStep.Syntax.ELet l e1 e2 => ELet (length l) (eraseNames σᵥ e1) (eraseNames (addVars l σᵥ) e2)
 | BigStep.Syntax.ESeq e1 e2 => ESeq (eraseNames σᵥ e1) (eraseNames σᵥ e2)
 | BigStep.Syntax.ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) =>
                                           (length vl, eraseNames (addNames (map (inr ∘ fst) l ++ map inl vl) σᵥ) e)
                                         ) l)
                                          (eraseNames (addFids (map fst l) σᵥ) e)
 | BigStep.Syntax.EMap l => EMap (map (fun '(x, y) => (eraseNames σᵥ x, eraseNames σᵥ y)) l)
 | BigStep.Syntax.ETry e1 vl1 e2 vl2 e0 => ETry (eraseNames σᵥ e1)
                                                (length vl1) (eraseNames (addVars vl1 σᵥ) e2)
                                                (length vl2) (eraseNames (addVars vl1 σᵥ) e0)
end.

Inductive well_formed_Expression : Expression -> Prop := (*TODO*).

Open Scope string_scope.

Goal eraseNames (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"])) =
  ELet 2 (EValues [˝VLit 0%Z; ˝VLit 1%Z]) (ETuple [˝VVar 0; ˝VVar 1]).
Proof.
  cbn. reflexivity.
Qed.

Goal eraseNames (fun _ => 0) (BigStep.Syntax.ELet ["X"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0)]) (BigStep.Syntax.ETuple [EVar "X"])) =
  ELet 1 (EValues [˝VLit 0%Z]) (ETuple [˝VVar 0]).
Proof.
  cbn. reflexivity.
Qed.

Goal eraseNames (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"; "Z"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1); ELit (BigStep.Syntax.Integer 2)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"; EVar "Z"])) =
  ELet 3 (EValues [˝VLit 0%Z; ˝VLit 1%Z; ˝VLit 2%Z]) (ETuple [˝VVar 0; ˝VVar 1; ˝VVar 2]).
Proof.
  cbn. reflexivity.
Qed.

Goal eraseNames (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"; "Z"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1); ELit (BigStep.Syntax.Integer 2)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Z"; EVar "Y"])) =
  ELet 3 (EValues [˝VLit 0%Z; ˝VLit 1%Z; ˝VLit 2%Z]) (ETuple [˝VVar 0; ˝VVar 2; ˝VVar 1]).
Proof.
  cbn. reflexivity.
Qed.

Goal eraseNames (fun _ => 0) (BigStep.Syntax.ELet ["X"; "Y"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 0); ELit (BigStep.Syntax.Integer 1)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"; EVar "X"])) =
  ELet 2 (EValues [˝VLit 0%Z; ˝VLit 1%Z]) (ETuple [˝VVar 0; ˝VVar 1; ˝VVar 0]).
Proof.
  cbn. reflexivity.
Qed.

(*
Goal eraseNames (fun _ => 1) (BigStep.Syntax.ELet ["Y"] (BigStep.Syntax.EValues [ELit (BigStep.Syntax.Integer 1)]) (BigStep.Syntax.ETuple [EVar "X"; EVar "Y"; EVar "X"])) =
  ELet 1 (EValues [˝VLit 1%Z]) (ETuple [˝VVar 1; ˝VVar 0; ˝VVar 1]).
Proof.
  cbn. reflexivity.
Qed.
*)