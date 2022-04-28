Require Export ExpSyntax.

Fixpoint patternScope (p : Pattern) : nat :=
match p with
 | PVar v => 1
 | PLit l => 0
 | PCons hd tl => patternScope hd + patternScope tl
 | PTuple l => fold_right (fun x y => (patternScope x) + y) 0 l
 | PMap l => fold_right (fun '(a,b) y => (patternScope a) + (patternScope b) + y) 0 l
 | PNil => 0
end
.

Definition patternListScope (pl : list Pattern) : nat :=
fold_right (fun x y => (patternScope x) + y) 0 pl
.

(** For language elements involving lists (e.g. tuples) we originally used Forall in the constructors (which lead to nested induction), this was easier to read, but Coq can not generate strong enough induction hypothesises for proofs, so we ended up using indexing witch is a bit harder to read in the definition, but Coq can use it to generate the needed hypothesises. *)
Inductive ExpScoped : Expression -> nat -> Prop :=
| scoped_val (v : ValueExpression) (n : nat)    : ValExpScoped v n    -> ExpScoped (Val v) n
| scoped_exp (e : NonValueExpression) (n : nat) : NonValExpScoped e n -> ExpScoped (Exp e) n

with ValExpScoped : ValueExpression -> nat -> Prop :=
| scoped_nil (n : nat)                                : ValExpScoped VNil n
| scoped_lit (l : Literal) (n : nat)                  : ValExpScoped (VLit l) n
| scoped_var (v : nat) (n : nat)                      : n > v -> ValExpScoped (VVar v) n
| scoped_funId (fi : nat) (n : nat)                   : n > fi -> ValExpScoped (VFunId fi) n
(*| scoped_vtuple (l : list ValueExpression) (n : nat)  : Forall (fun x => ValExpScoped x n) l -> ValExpScoped (VTuple l) (n) *)
| scoped_vtuple (l : list ValueExpression) (n : nat)  : (forall i, i < length l -> ValExpScoped (nth i l VNil) n) -> ValExpScoped (VTuple l) (n)
| scoped_vcons (hd tl : ValueExpression) (n : nat)    : ValExpScoped hd n -> ValExpScoped tl n -> ValExpScoped (VCons hd tl) (n)
(*| scoped_vmap (l : list (ValueExpression * ValueExpression)) (n : nat) : 
  Forall (fun x => ValExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ValExpScoped x n) (map (fun '(x,y) => y) l)
  -> ValExpScoped (VMap l) n*)
| scoped_vmap (l : list (ValueExpression * ValueExpression)) (n : nat) : 
  (forall i, i< length l -> ValExpScoped (fst (nth i l (VNil,VNil))) n) ->
  (forall i, i< length l -> ValExpScoped (snd (nth i l (VNil,VNil))) n)
  -> ValExpScoped (VMap l) n
(*| scoped_vvalues (el : list ValueExpression) (n : nat)   : Forall (fun x => ValExpScoped x n) el -> ValExpScoped (VValues el) (n)*)
| scoped_vvalues (el : list ValueExpression) (n : nat)   : (forall i, i < length el -> ValExpScoped (nth i el VNil) n) -> ValExpScoped (VValues el) (n)
(*| scoped_vclos (ext : list (nat * nat * Expression)) (id : nat) (vl : nat) (e : Expression) (n m : nat) :
  Forall (fun x => x <= m) (map (fun '(a,b,x) => b) ext) ->
  Forall (fun x => ExpScoped x (m + length ext)) (map (fun '(a,b,x) => x) ext) ->
  ExpScoped e (vl + length ext) ->
  ValExpScoped (VClos ext id vl e) n*)
| scoped_vclos (ext : list (nat * nat * Expression)) (id : nat) (vl : nat) (e : Expression) (n m : nat) :
  (forall i, i < length ext -> ExpScoped (snd (nth i ext (0,0,Val VNil))) (length ext + (snd(fst (nth i ext (0,0,Val VNil)))) + n) ) ->
  ExpScoped e (length ext + vl + n) ->
  ValExpScoped (VClos ext id vl e) n

with NonValExpScoped : NonValueExpression -> nat -> Prop :=
| scoped_efun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (vl + n) -> NonValExpScoped (EFun vl e) (n)
(* | scoped_etuple (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (ETuple l) (n)) *)
| scoped_etuple (l : list Expression) (n : nat) : (forall i, i < length l -> ExpScoped (nth i l (Val VNil)) n) -> NonValExpScoped (ETuple l) (n)
| scoped_econs (hd tl : Expression) (n : nat)   : ExpScoped hd n -> ExpScoped tl n -> NonValExpScoped (ECons hd tl) (n)
(*| scoped_emap (l : list (Expression * Expression)) (n : nat) : 
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => y) l)
  -> NonValExpScoped (EMap l) n *)
| scoped_emap (l : list (Expression * Expression)) (n : nat) : 
  (forall i, i< length l -> ExpScoped (fst (nth i l (Val VNil,Val VNil))) n) ->
  (forall i, i< length l -> ExpScoped (snd (nth i l (Val VNil,Val VNil))) n)
  -> NonValExpScoped (EMap l) n
(* | scoped_evalues (el : list Expression) (n : nat)   : Forall (fun x => ExpScoped x n) el -> NonValExpScoped (EValues el) (n) *)
| scoped_evalues (el : list Expression) (n : nat)   : (forall i, i < length el -> ExpScoped (nth i el (Val VNil)) n) -> NonValExpScoped (EValues el) (n)
(*| scoped_call (f : string) (l : list Expression) (n : nat)      : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (ECall f l) (n) *)
| scoped_call (f : string) (l : list Expression) (n : nat)      : (forall i, i < length l -> ExpScoped (nth i l (Val VNil)) n) -> NonValExpScoped (ECall f l) (n)
(* | scoped_primOp (f : string) (l : list Expression) (n : nat)    : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (EPrimOp f l) (n) *)
| scoped_primOp (f : string) (l : list Expression) (n : nat)    : (forall i, i < length l -> ExpScoped (nth i l (Val VNil)) n) -> NonValExpScoped (EPrimOp f l) (n)
(* | scoped_app (exp: Expression) (l : list Expression) (n : nat)  : ExpScoped exp n -> Forall (fun x => ExpScoped x n) l -> NonValExpScoped (EApp exp l) (n) *)
| scoped_app (exp: Expression) (l : list Expression) (n : nat)  : ExpScoped exp n -> (forall i, i < length l -> ExpScoped (nth i l (Val VNil)) n) -> NonValExpScoped (EApp exp l) (n)
(* | scoped_case (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (m n : nat) : 
  ExpScoped e n -> 
  Forall (fun x => patternListScope x <= m) (map (fun '(x,y,z) => x) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => y) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => z) l)
  -> NonValExpScoped (ECase e l) (n) *)
| scoped_case (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (n : nat) : 
  ExpScoped e n -> 
  (forall i, i< length l -> ExpScoped (snd(fst(nth i l (nil, Val VNil, Val VNil)))) ((patternListScope (fst(fst(nth i l (nil, Val VNil, Val VNil))))) + n)) ->
  (forall i, i< length l -> ExpScoped (snd(nth i l (nil, Val VNil, Val VNil))) ((patternListScope (fst(fst(nth i l (nil, Val VNil, Val VNil))))) + n))
  -> NonValExpScoped (ECase e l) (n)
| scoped_let (l : nat) (e1 e2 : Expression) (n : nat) : 
  ExpScoped e1 n -> ExpScoped e2 (l+n)
  -> NonValExpScoped (ELet l e1 e2) n
| scoped_seq (e1 e2 : Expression) (n : nat) : ExpScoped e1 n -> ExpScoped e2 n -> NonValExpScoped (ESeq e1 e2) n

(*| scoped_letRec (l : list (nat * Expression)) (e : Expression) (m n : nat) :
  Forall (fun x => x <= m) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x (S(m) + n)) (map (fun '(x,y) => y) l) ->
  (*in m + n we may need +(length l) as well because of function definitions in letRec *)
  ExpScoped e (n + (length l))
  -> NonValExpScoped (ELetRec l e) n *)
  
| scoped_letRec (l : list (nat * Expression)) (e : Expression) (n : nat) :
  (forall i, i < length l -> ExpScoped (snd(nth i l (0,Val VNil))) ((length l) + (fst(nth i l (0,Val VNil))) + n)) ->
  ExpScoped e ((length l) + n)
  -> NonValExpScoped (ELetRec l e) n
  
| scoped_try (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression) (n : nat) : 
  ExpScoped e1 n -> 
  ExpScoped e2 (vl1 + n) ->
  ExpScoped e3 (vl2 + n)
  -> NonValExpScoped (ETry e1 vl1 e2 vl2 e3) n
.

Notation "'NVAL' Γ ⊢ e" := (NonValExpScoped e Γ)
         (at level 69, no associativity).
Notation "'VAL' Γ ⊢ v" := (ValExpScoped v Γ)
         (at level 69, no associativity).
Notation "'EXP' Γ ⊢ e" := (ExpScoped e Γ)
         (at level 69, no associativity).

Notation "'EXPCLOSED' e" := (EXP 0 ⊢ e) (at level 5).
Notation "'VALCLOSED' v" := (VAL 0 ⊢ v) (at level 5).

Scheme ExpScoped_ind2     := Induction for ExpScoped Sort Prop
  with ValScoped_ind2     := Induction for ValExpScoped Sort Prop
  with NonValScoped_ind2  := Induction for NonValExpScoped Sort Prop.
Combined Scheme scoped_ind from ExpScoped_ind2, ValScoped_ind2, NonValScoped_ind2.

Check scoped_ind.