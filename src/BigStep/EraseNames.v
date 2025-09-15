(**
  This file contains the transformation of the big-step syntax into the frame
  stack approach.
*)

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

Definition addVars (vl : list string) (σ : @NameSub (string + FunctionIdentifier) (sum_eqb String.eqb (prod_eqb String.eqb Nat.eqb))) : @NameSub (string + FunctionIdentifier) (sum_eqb String.eqb (prod_eqb String.eqb Nat.eqb)) :=
  addNames (map inl vl) σ.

Definition addFids (vl : list FunctionIdentifier) (σ : @NameSub (string + FunctionIdentifier) (sum_eqb String.eqb (prod_eqb String.eqb Nat.eqb))) : @NameSub (string + FunctionIdentifier) (sum_eqb String.eqb (prod_eqb String.eqb Nat.eqb)) :=
  addNames (map inr vl) σ.

Fixpoint eraseNames (σᵥ : @NameSub (string + FunctionIdentifier) (sum_eqb String.eqb (prod_eqb String.eqb Nat.eqb))) (* (: @NameSub (string * nat) (prod_eqb eqb Nat.eqb)) *)
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
                                           (length vl, eraseNames (addNames (map (inr ∘ fst) l ++ map inl vl) σᵥ) b)
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

Import BigStep.

Definition cica := ELetRec [(("f"%string, 2),(["_0"%string;"_1"%string], ((ECase (EValues [(EVar "_0"%string);(EVar "_1"%string)]) [([(PVar "X"%string);(PVar "N"%string)], ((ELit (Atom "true"%string))), ((ELet ["_2"%string] ((ECall ((ELit (Atom "erlang"%string))) ((ELit (Atom "integer_to_list"%string))) [((EVar "N"%string))])) ((ELet ["_3"%string] ((ECall ((ELit (Atom "erlang"%string))) ((ELit (Atom "++"%string))) [((EVar "X"%string));((EVar "_2"%string))])) ((ESeq ((ECall ((ELit (Atom "erlang"%string))) ((ELit (Atom "list_to_atom"%string))) [((EVar "_3"%string))])) ((ELet ["_4"%string] ((ECall ((ELit (Atom "erlang"%string))) ((ELit (Atom "+"%string))) [((EVar "N"%string));((ELit (Integer (1))))])) ((EApp ((EFunId ("f"%string, 2))) [((EVar "X"%string));((EVar "_4"%string))])))))))))));([(PVar "_6"%string);(PVar "_5"%string)], ((ELit (Atom "true"%string))), ((EPrimOp "match_fail"%string [((ETuple [((ELit (Atom "function_clause"%string)));((EVar "_6"%string));((EVar "_5"%string))]))])))]))));(("module_info"%string, 0),([], ((ECase (EValues []) [([], ((ELit (Atom "true"%string))), ((ECall ((ELit (Atom "erlang"%string))) ((ELit (Atom "get_module_info"%string))) [((ELit (Atom "exhaustion"%string)))])));([], ((ELit (Atom "true"%string))), ((EPrimOp "match_fail"%string [((ETuple [((ELit (Atom "function_clause"%string)))]))])))]))));(("module_info"%string, 1),(["_0"%string], ((ECase ((EVar "_0"%string)) [([(PVar "X"%string)], ((ELit (Atom "true"%string))), ((ECall ((ELit (Atom "erlang"%string))) ((ELit (Atom "get_module_info"%string))) [((ELit (Atom "exhaustion"%string)));((EVar "X"%string))])));([(PVar "_1"%string)], ((ELit (Atom "true"%string))), ((EPrimOp "match_fail"%string [((ETuple [((ELit (Atom "function_clause"%string)));((EVar "_1"%string))]))])))]))))] (EApp (EFunId ("main"%string,0)) []).

Compute cica.
Compute eraseNames (fun _ => 0) cica.



