From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Logic.FunctionalExtensionality.
From Coq Require Import FunctionalExtensionality PropExtensionality.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.

Import ListNotations.

Definition Var : Set := string.

Inductive Literal : Set :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Set :=
| PVar     (v : Var)
| PLit (l : Literal)
| PCons  (hd tl : Pattern)
| PTuple (l : list Pattern)
| PMap (l : list (Pattern * Pattern))
| PNil.

Definition FunctionIdentifier : Set := nat * nat.

Inductive Expression : Set :=
| Val (e : ValueExpression)
| Exp (e : NonValueExpression)

with ValueExpression : Set := 
| VNil
| VLit    (l : Literal)
| VFun    (vl : nat) (e : Expression)
| VCons   (hd tl : ValueExpression)
| VTuple  (l : list ValueExpression)
| VMap    (l : list (ValueExpression * ValueExpression))
| VValues (el : list ValueExpression)
| EVar    (n : nat)
| EFunId  (n : nat)

with NonValueExpression : Set :=
| EValues (el : list Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
| EMap    (l : list (Expression * Expression))
| ECall   (f : string)    (l : list Expression)
| EPrimOp (f : string)    (l : list Expression)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : nat) (e1 e2 : Expression)
| ESeq    (e1 e2 : Expression)
(*| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression) *)
| ELetRec (l : list (nat * Expression)) (e : Expression)
| ETry    (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
.

(*
Scheme Expression_ind2_old         := Induction for Expression Sort Prop
  with ValueExpression_ind2    := Induction for ValueExpression Sort Prop
  with NonValueExpression_ind2 := Induction for NonValueExpression Sort Prop
.

Combined Scheme Expression_ind3_old from Expression_ind2, ValueExpression_ind2, NonValueExpression_ind2.
Check Expression_ind3.
*)

Check  VLit ( Integer 10 ).
Check  Val ( VLit ( Integer 10 ) ).
Check  ESeq (Val (VLit ( Integer 10 ))) (Val (VLit ( Integer 10 ))).
Check  Exp ( ESeq (Val (VLit ( Integer 10 ))) (Val (VLit ( Integer 10 ))) ) .

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

Inductive ExpScoped : Expression -> nat -> Prop :=
| scoped_val (v : ValueExpression) (n : nat)    : ValExpScoped v n    -> ExpScoped (Val v) n
| scoped_exp (e : NonValueExpression) (n : nat) : NonValExpScoped e n -> ExpScoped (Exp e) n

with ValExpScoped : ValueExpression -> nat -> Prop :=
| scoped_nil (n : nat)                                : ValExpScoped VNil n
| scoped_lit (l : Literal) (n : nat)                  : ValExpScoped (VLit l) n
| scoped_var (v : nat) (n : nat)                      : n > v -> ValExpScoped (EVar v) n
| scoped_funId (fi : nat) (n : nat)                   : n > fi -> ValExpScoped (EFunId fi) n
| scoped_vtuple (l : list ValueExpression) (n : nat)  : Forall (fun x => ValExpScoped x n) l -> ValExpScoped (VTuple l) (n)
| scoped_vcons (hd tl : ValueExpression) (n : nat)    : ValExpScoped hd n -> ValExpScoped tl n -> ValExpScoped (VCons hd tl) (n)
| scoped_vmap (l : list (ValueExpression * ValueExpression)) (n : nat) : 
  Forall (fun x => ValExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ValExpScoped x n) (map (fun '(x,y) => y) l)
  -> ValExpScoped (VMap l) n
| scoped_vvalues (el : list ValueExpression) (n : nat)   : Forall (fun x => ValExpScoped x n) el -> ValExpScoped (VValues el) (n)
| scoped_fun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (S(vl) + n) -> ValExpScoped (VFun vl e) (n)

with NonValExpScoped : NonValueExpression -> nat -> Prop :=
| scoped_etuple (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (ETuple l) (n)
| scoped_econs (hd tl : Expression) (n : nat)   : ExpScoped hd n -> ExpScoped tl n -> NonValExpScoped (ECons hd tl) (n)
| scoped_emap (l : list (Expression * Expression)) (n : nat) : 
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => y) l)
  -> NonValExpScoped (EMap l) n
| scoped_evalues (el : list Expression) (n : nat)   : Forall (fun x => ExpScoped x n) el -> NonValExpScoped (EValues el) (n)
| scoped_call (f : string) (l : list Expression) (n : nat)      : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (ECall f l) (n)
| scoped_primOp (f : string) (l : list Expression) (n : nat)    : Forall (fun x => ExpScoped x n) l -> NonValExpScoped (EPrimOp f l) (n)
| scoped_app (exp: Expression) (l : list Expression) (n : nat)  : ExpScoped exp n -> Forall (fun x => ExpScoped x n) l -> NonValExpScoped (EApp exp l) (n)
| scoped_case (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (m n : nat) : 
  ExpScoped e n -> 
  Forall (fun x => patternListScope x <= m) (map (fun '(x,y,z) => x) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => y) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => z) l)
  -> NonValExpScoped (ECase e l) (n)
| scoped_let (l : nat) (e1 e2 : Expression) (n : nat) : 
  ExpScoped e1 n -> ExpScoped e2 (l+n)
  -> NonValExpScoped (ELet l e1 e2) n
| scoped_seq (e1 e2 : Expression) (n : nat) : ExpScoped e1 n -> ExpScoped e2 n -> NonValExpScoped (ESeq e1 e2) n
| scoped_letRec (l : list (nat * Expression)) (e : Expression) (m n : nat) :
  Forall (fun x => x <= m) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x (S(m) + n)) (map (fun '(x,y) => y) l) -> (*in m + n we may need +(length l) as well because of function definitions in letRec *)
  ExpScoped e (n + (length l))
  -> NonValExpScoped (ELetRec l e) n
| scoped_try (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression) (n : nat) : 
  ExpScoped e1 n -> 
  ExpScoped e2 (n + vl1) ->
  ExpScoped e3 (n + vl2)
  -> NonValExpScoped (ETry e1 vl1 e2 vl2 e3) n
.

Definition Renaming : Type := nat -> nat.

Definition upren (ρ : Renaming) : Renaming :=
  fun n =>
    match n with
    | 0 => 0
    | S n' => S (ρ n')
    end.

Fixpoint iterate {A : Type} (f : A -> A) n a :=
  match n with
    | 0 => a
    | S n' => f (iterate f n' a)
  end.

Notation uprenn := (iterate upren).

Check Renaming.
Check upren.
Check iterate.
Check uprenn.

Fixpoint rename (ρ : Renaming) (ex : Expression) : Expression :=
match ex with
 | Val e => Val (renameValue ρ e)
 | Exp e => Exp (renameNonValue ρ e)
end
with renameValue (ρ : Renaming) (ex : ValueExpression) : ValueExpression :=
match ex with
 | VNil         => ex
 | VLit l       => ex
 | VFun vl e    => VFun vl (rename (uprenn (S(vl)) ρ) e)
 | VCons hd tl  => VCons (renameValue ρ hd) (renameValue ρ tl)
 | VTuple l     => VTuple (map (fun x => renameValue ρ x) l)
 | VMap l       => VMap (map (fun '(x,y) => (renameValue ρ x, renameValue ρ y)) l)
 | VValues el   => VValues (map (fun x => renameValue ρ x) el)
 | EVar n       => EVar (ρ n)
 | EFunId n     => EFunId (ρ n)
end
with renameNonValue (ρ : Renaming) (ex : NonValueExpression) : NonValueExpression :=
match ex with
 | EValues el       => EValues (map (fun x => rename ρ x) el)
 | ECons   hd tl    => ECons (rename ρ hd) (rename ρ tl)
 | ETuple  l        => ETuple (map (fun x => rename ρ x) l)
 | EMap    l        => EMap (map (fun '(x,y) => (rename ρ x, rename ρ y)) l)
 | ECall   f l      => ECall f (map (fun x => rename ρ x) l)
 | EPrimOp f l      => EPrimOp f (map (fun x => rename ρ x) l)
 | EApp    e l      => EApp (rename ρ e) (map (fun x => rename ρ x) l)
 | ECase   e l      => ECase (rename ρ e) (map (fun '(p,x,y) => (p, rename (uprenn(patternListScope p) ρ) x, rename (uprenn(patternListScope p) ρ) y)) l)
 | ELet    l e1 e2  => ELet l (rename ρ e1) (rename (uprenn (l) ρ) e2)
 | ESeq    e1 e2    => ESeq (rename ρ e1) (rename ρ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, rename (uprenn (S(n)) ρ) x)) l) (rename (uprenn (length l) ρ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (rename ρ e1) vl1 (rename (uprenn (vl1) ρ) e2) vl2 (rename (uprenn (vl2) ρ) e3)
end
.


Definition Substitution := nat -> ValueExpression + nat. (** We need to have the names for the
                                                  identity elements explicitly, because 
                                                  of the shiftings (up, upn) *)
Definition idsubst : Substitution := fun x => inr x.

Definition shift (ξ : Substitution) : Substitution := 
fun s =>
  match ξ s with
  | inl exp => inl (renameValue (fun n => S n) exp)
  | inr num => inr (S num)
  end.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

Notation upn := (iterate up_subst).

Check Substitution.
Check idsubst.
Check up_subst.
Check upn.

Fixpoint subst (ξ : Substitution) (base : Expression) : Expression :=
match base with
  | Val v => Val (substVal ξ v)
  | Exp e => Exp (substNonVal ξ e)
end
with substVal (ξ : Substitution) (ex : ValueExpression) : ValueExpression :=
match ex with
 | VNil         => ex
 | VLit l       => ex
 | VFun vl e    => VFun vl (subst (upn (S(vl)) ξ) e)
 | VCons hd tl  => VCons (substVal ξ hd) (substVal ξ tl)
 | VTuple l     => VTuple (map (fun x => substVal ξ x) l)
 | VMap l       => VMap (map (fun '(x,y) => (substVal ξ x, substVal ξ y)) l)
 | VValues el   => VValues (map (fun x => substVal ξ x) el)
 | EVar n       => match ξ n with
                     | inl exp => exp
                     | inr num => EVar num
                     end
 | EFunId n     => match ξ n with
                     | inl exp => exp
                     | inr num => EFunId num
                     end
end
with substNonVal (ξ : Substitution) (ex : NonValueExpression) : NonValueExpression :=
match ex with
 | EValues el       => EValues (map (fun x => subst ξ x) el)
 | ECons   hd tl    => ECons (subst ξ hd) (subst ξ tl)
 | ETuple  l        => ETuple (map (fun x => subst ξ x) l)
 | EMap    l        => EMap (map (fun '(x,y) => (subst ξ x, subst ξ y)) l)
 | ECall   f l      => ECall f (map (fun x => subst ξ x) l)
 | EPrimOp f l      => EPrimOp f (map (fun x => subst ξ x) l)
 | EApp    e l      => EApp (subst ξ e) (map (fun x => subst ξ x) l)
 | ECase   e l      => ECase (subst ξ e) (map (fun '(p,x,y) => (p, subst (upn(patternListScope p) ξ) x, subst (upn(patternListScope p) ξ) y)) l)
 | ELet    l e1 e2  => ELet l (subst ξ e1) (subst (upn (l) ξ) e2)
 | ESeq    e1 e2    => ESeq (subst ξ e1) (subst ξ e2)
 | ELetRec l e      => ELetRec (map (fun '(n,x) => (n, subst (upn (S(n)) ξ) x)) l) (subst (upn (length l) ξ) e)
 | ETry    e1 vl1 e2 vl2 e3 => ETry (subst ξ e1) vl1 (subst (upn (vl1) ξ) e2) vl2 (subst (upn (vl2) ξ) e3)
end
.

(*----------------------Proofs-------------------------------------------*)

Section correct_pattern_ind.

Variables
  (P : Pattern -> Prop)(Q : list Pattern -> Prop)(R : list (Pattern * Pattern) -> Prop).

Hypotheses
 (H : P PNil)
 (H0 : forall (l : Literal), P (PLit l))
 (H1 : forall (s : Var), P (PVar s))
 (H2 : forall (hd : Pattern), P hd -> forall (tl : Pattern), P tl -> P (PCons hd tl))
 (H3 : forall (l:list Pattern), Q l -> P (PTuple l))
 (H4 : forall (l:list (Pattern * Pattern)), R l -> P (PMap l))
 (H' : forall v : Pattern, P v -> forall l:list Pattern, Q l -> Q (v :: l))
 (H0' : forall (v1 : Pattern), P v1 -> forall (v2 : Pattern), P v2 -> forall l:list (Pattern * Pattern), R l -> R ((v1, v2) :: l))
 (H1' : Q [])
 (H2' : R []).

Fixpoint Pattern_ind2 (v : Pattern) : P v :=
  match v as x return P x with
  | PNil => H
  | PLit l => H0 l
  | PVar s => H1 s
  | PCons hd tl => H2 hd (Pattern_ind2 hd) tl (Pattern_ind2 tl)
  | PTuple l => H3 l ((fix l_ind (l':list Pattern) : Q l' :=
                       match l' as x return Q x with
                       | [] => H1'
                       | v::xs => H' v (Pattern_ind2 v) xs (l_ind xs)
                       end) l)
  | PMap l => H4 l ((fix l_ind (l' : list (Pattern * Pattern)) : R l' :=
                      match l' as x return R x with
                      | [] => H2'
                      | (v1, v2)::xs => H0' v1 (Pattern_ind2 v1) v2 (Pattern_ind2 v2) xs (l_ind xs)
                      end) l)
  end.

End correct_pattern_ind.


Section correct_exp_ind.

  Variables
    (P  : Expression -> Prop)
    (PV : ValueExpression -> Prop)
    (PE : NonValueExpression -> Prop)
    (Q  : list Expression -> Prop)
    (QV : list ValueExpression-> Prop)
    (R  : list (Expression * Expression) -> Prop)
    (RV : list (ValueExpression * ValueExpression) -> Prop)
    (W : list ((list Pattern) * Expression * Expression) -> Prop)
    (Z : list (nat * Expression) -> Prop).

  Hypotheses
   (HV : forall (e : ValueExpression), PV e -> P (Val e))
   (HE : forall (e : NonValueExpression), PE e -> P (Exp e))
   
   (HV1 : PV VNil)
   (HV2 : forall (l : Literal), PV (VLit l))
   (HV3 : forall (n : nat) (e : Expression), P e -> PV (VFun n e))
   (HV4 : forall (hd : ValueExpression), PV hd -> forall (tl : ValueExpression), PV tl ->  PV (VCons hd tl))
   (HV5 : forall (l : list ValueExpression), QV l -> PV (VTuple l))
   (HV6 : forall (l : list (ValueExpression * ValueExpression)), RV l -> PV (VMap l))
   (HV7 : forall (el : list ValueExpression), QV el -> PV (VValues el))
   (HV8 : forall (n : nat), PV(EVar n))
   (HV9 : forall (n : nat), PV(EFunId n))
   
   (HE1 : forall (el : list Expression), Q el -> PE (EValues el))
   (HE2 : forall (hd : Expression), P hd -> forall (tl : Expression), P tl -> PE (ECons hd tl))
   (HE3 : forall (l : list Expression), Q l -> PE (ETuple l))
   (HE4 : forall (l : list (Expression * Expression)), R l -> PE (EMap l))
   (HE5 : forall (f : string) (l : list Expression), Q l -> PE (ECall f l))
   (HE6 : forall (f : string) (l : list Expression), Q l -> PE (EPrimOp f l))
   (HE7 : forall (e: Expression), P e -> forall (l : list Expression), Q l -> PE (EApp e l))
   (HE8 : forall (e : Expression), P e -> forall (l : list ((list Pattern) * Expression * Expression)), W l -> PE (ECase e l) )
   (HE9 : forall (l : nat) (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 -> PE (ELet l e1 e2))
   (HE10: forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 -> PE (ESeq e1 e2))
   (HE11: forall (e : Expression), P e -> forall (l : list (nat * Expression)), Z l -> PE (ELetRec l e))
   (HE12: forall (e1 : Expression), P e1 -> forall (vl1 : nat) (e2 : Expression), P e2 -> 
   forall (vl2 : nat) (e3 : Expression), P e3 -> PE (ETry e1 vl1 e2 vl2 e3))
   
   (HQ1 : Q [])
   (HQ2 : forall (e : Expression), P e -> forall (el : list Expression), Q el -> Q (e::el))
   (HQV1: QV [])
   (HQV2: forall (e : ValueExpression), PV e -> forall (el : list ValueExpression), QV el -> QV (e::el))
   (HR1 : R [])
   (HR2 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 -> 
   forall (el : list (Expression * Expression)), R el -> R ((e1,e2)::el))
   (HRV1: RV [])
   (HRV2: forall (e1 : ValueExpression), PV e1 -> forall (e2 : ValueExpression), PV e2 -> 
   forall (el : list (ValueExpression * ValueExpression)), RV el -> RV ((e1,e2)::el))
   (HW1 : W [])
   (HW2 : forall (l : list Pattern) (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 ->
    forall (lv : list ((list Pattern) * Expression * Expression)), W lv -> 
    W ((l,e1,e2)::lv))
   (HZ1 : Z [])
   (HZ2 : forall (n : nat) (e : Expression), P e -> forall (el : list (nat * Expression)), Z el -> Z ((n,e)::el))
   (*(HW2 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 ->
    forall (lv : list ((list Pattern) * Expression * Expression)), W lv -> 
    forall (l : list Pattern), W ((l,e1,e2)::lv) ) *)
   .

  Check list_ind.
  
  Fixpoint Expression_ind2 (e : Expression) : P e :=
  
  match e as x return P x with
  | Val ve => HV ve (ValueExpression_ind2 ve)
  | Exp nve => HE nve (NonValueExpression_ind2 nve)
  end
  
  with NonValueExpression_ind2 (nve : NonValueExpression) : PE nve :=
  match nve as x return PE x with
  
  | EValues el => HE1 el (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) el)
  | ECons hd tl => HE2 hd (Expression_ind2 hd) tl (Expression_ind2 tl)
  | ETuple l => HE3 l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | EMap l => HE4 l (list_ind R HR1 (fun '(e1,e2) ls => HR2 e1 (Expression_ind2 e1) e2 (Expression_ind2 e2) ls) l)
  | ECall f l => HE5 f l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | EPrimOp f l => HE6 f l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | EApp exp l => HE7 exp (Expression_ind2 exp) l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | ECase e l => HE8 e (Expression_ind2 e) l 
  (list_ind W HW1 (fun '(lp, e1, e2) ls => (HW2 lp e1 (Expression_ind2 e1) e2 (Expression_ind2 e2) ls)) l)
  | ELet l e1 e2 => HE9 l e1 (Expression_ind2 e1) e2 (Expression_ind2 e2)
  | ESeq e1 e2 => HE10 e1 (Expression_ind2 e1) e2 (Expression_ind2 e2)
  | ELetRec l e => HE11 e (Expression_ind2 e) l (list_ind Z HZ1 (fun '(n,e) ls => HZ2 n e (Expression_ind2 e) ls) l)
  | ETry e1 vl1 e2 vl2 e3 => HE12 e1 (Expression_ind2 e1) vl1 e2 (Expression_ind2 e2) vl2 e3 (Expression_ind2 e3)
  end
  
  with ValueExpression_ind2 (ve : ValueExpression) : PV ve :=
  match ve as x return PV x with
  | VNil => HV1
  | VLit l => HV2 l
  | VFun vl e => HV3 vl e (Expression_ind2 e)
  | VCons hd tl => HV4 hd (ValueExpression_ind2 hd) tl (ValueExpression_ind2 tl)
  | VTuple l => HV5 l (list_ind QV HQV1 (fun e ls => HQV2 e (ValueExpression_ind2 e) ls) l)
  | VMap l => HV6 l (list_ind RV HRV1 (fun '(e1,e2) ls => HRV2 e1 (ValueExpression_ind2 e1) e2 (ValueExpression_ind2 e2) ls) l)
  | VValues el => HV7 el (list_ind QV HQV1 (fun e ls => HQV2 e (ValueExpression_ind2 e) ls) el)
  | EVar n => HV8 n
  | EFunId n => HV9 n
  end
  .
  Combined Scheme Exp_ind from Expression_ind2, NonValueExpression_ind2, ValueExpression_ind2.

End correct_exp_ind.
Check Expression_ind2.
Check ValueExpression_ind2.
Check Exp_ind.

Definition scons {X : Type} (s : X) (σ : nat -> X) (x : nat) : X :=
  match x with 
  | S y => σ y
  | _ => s
  end.
Notation "s .: σ" := (scons (inl s) σ) (at level 55, σ at level 56, right associativity).
Notation "s .:: σ" := (scons s σ) (at level 55, σ at level 56, right associativity).
Notation "s .[ σ ]" := (subst σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]" ).
Notation "s .[ t /]" := (subst (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]").
Notation "s .[ t1 , t2 , .. , tn /]" :=
  (subst (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity,
   format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").
   
(* ValueExpression *)
Notation "s .[ σ ]ᵥ" := (substVal σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]ᵥ" ).
Notation "s .[ t /]ᵥ" := (substVal (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]ᵥ").
Notation "s .[ t1 , t2 , .. , tn /]ᵥ" :=
  (substVal (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity).
  (* format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'").*)

(* NonValueExpression *)
Notation "s .[ σ ]ₑ" := (substNonVal σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]ₑ" ).
Notation "s .[ t /]ₑ" := (substNonVal (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]ₑ").
Notation "s .[ t1 , t2 , .. , tn /]ₑ" :=
  (substNonVal (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity).
  (*format "s '[ ' .[ t1 , '/' t2 , '/' .. , '/' tn /] ']'ₑ").*)

Compute scons (inl (VLit (Integer 1))) idsubst 3.
Compute ((VLit (Integer 1)).:idsubst) 3.
Compute (Exp ( ECons (Val( EVar 0 )) (Val( EVar 1 )) )).[ (VLit (Integer 1)), (VLit (Integer 2)) /].

Definition composition {A B C} (f : A -> B) (g : B -> C) : A -> C := fun x => g (f x).
Notation "f >>> g" := (composition f g)
  (at level 56, left associativity).

Definition list_subst (l : list ValueExpression) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.

(** Examples *)

Definition XVar : Var := "X"%string.
(**
Definition inc (n : Z) := ELet XVar (VLit n) (EPlus (EVar 0) (ELit 1)).
*)
(** Tests: *)
(**
Goal (inc 1).[VLit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (inc 1).[ELit 0/] = inc 1. Proof. reflexivity. Qed.
Goal (EApp (EVar 0) [EVar 0; ELet XVar (EVar 0) (EVar 0)]).[VLit 0/]
  = (EApp (VLit 0) [VLit 0; ELet XVar (VLit 0) (EVar 0)]). Proof. reflexivity. Qed.
*)
Check (Integer 0).

Compute (VLit (Integer 0) .: VLit (Integer 0) .: idsubst) 3.

Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match ξ x with
    | inl exp => inl (substVal η exp)
    | inr n   => η n
    end.

Ltac fold_upn :=
match goal with
| |- context G [up_subst (upn ?n ?ξ)] => replace (up_subst (upn n ξ)) with (upn (S n) ξ) by auto
| |- context G [upren (uprenn ?n ?ξ)] => replace (upren (uprenn n ξ)) with (uprenn (S n) ξ) by auto
end.

Ltac fold_upn_hyp :=
match goal with
| [ H : context G [up_subst (upn ?n ?ξ)] |- _ ] => replace (up_subst (upn n ξ)) with (upn (S n) ξ) in H by auto
| [ H : context G [upren (uprenn ?n ?ξ)] |- _ ] => replace (upren (uprenn n ξ)) with (uprenn (S n) ξ) in H by auto
end.

Definition ren (ρ : Renaming) : Substitution :=
  fun x => inr (ρ x).

Theorem ren_up ρ :
  ren (upren ρ) = up_subst (ren ρ).
Proof.
  extensionality x. unfold ren, upren, up_subst.
  destruct x; reflexivity.
Qed.

Corollary renn_up : forall n ρ,
  ren (uprenn n ρ) = upn n (ren ρ).
Proof.
  induction n; intros; try reflexivity.
  cbn. rewrite ren_up. rewrite IHn. auto.
Qed.

Check Expression_ind2.

Check Exp_ind.
Theorem renaming_is_subst2 : 
     (forall e ρ, rename ρ e = e.[ren ρ])
  /\ (forall e ρ, renameNonValue ρ e = e.[ren ρ]ₑ)
  /\ (forall e ρ, renameValue ρ e = e.[ren ρ]ᵥ).
Proof. Print Forall.
  apply Exp_ind with
    (QV := fun l => (* forall ve ρ, In ve l -> renameValue ρ ve = ve.[ren ρ]ᵥ *)
                    (* forall i ρ, i < length l -> renameValue ρ (nth i l VNil) = (nth i l VNil).[ren ρ]ᵥ *)
                    forall ρ, Forall (fun ve => renameValue ρ ve = ve.[ren ρ]ᵥ) l)
    (Q := fun l => forall ρ, Forall (fun e => rename ρ e = e.[ren ρ]) l)
    (R := fun l => forall ρ, Forall (fun (x : Expression * Expression) =>
      (let (e1, e2) := x in (rename ρ e1, rename ρ e2)) = (let (e1, e2) := x in (e1.[ren ρ], e2.[ren ρ]))) l)
    (RV := fun l => forall ρ, Forall (fun (x : ValueExpression * ValueExpression) =>
      (let (e1, e2) := x in (renameValue ρ e1, renameValue ρ e2)) = (let (e1, e2) := x in (e1.[ren ρ]ᵥ, e2.[ren ρ]ᵥ))) l)
    (W := fun l => forall ρ, Forall (fun (x : list Pattern * Expression * Expression) =>
      (let '(pl, e1, e2) := x in (pl, rename (uprenn (patternListScope pl) ρ) e1,
                                      rename (uprenn (patternListScope pl) ρ) e2)) =
      (let '(pl, e1, e2) := x in (pl, e1.[upn (patternListScope pl) (ren ρ)],
                                      e2.[upn (patternListScope pl) (ren ρ)]))) l)
    (Z := fun l => forall ρ, Forall (fun x : nat * Expression =>
                      (let (n, e) := x in (n, rename (uprenn (S n) ρ) e)) =
                      (let (n, e) := x in (n, e.[upn (S n) (ren ρ)]))) l); intros.
  (* Expression *)
  * simpl. rewrite H. reflexivity.
  * simpl. rewrite H. reflexivity.
  (* ValueExpression *)
  * reflexivity.
  * reflexivity.
  * simpl. rewrite H. rewrite ren_up. rewrite renn_up. reflexivity.
  * simpl. rewrite H, H0. reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  (* NonValueExpression *)
  * reflexivity.
  * reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. rewrite H, H0. reflexivity.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. rewrite H. erewrite map_ext_Forall. reflexivity. simpl. auto.
  * simpl. rewrite H. erewrite map_ext_Forall. reflexivity. simpl. apply H0.
    (* induction l.
    - constructor.
    - constructor.
      + destruct a, p. inversion H0. subst.
        ... (* doable *)
        rewrite renn_up.
      + apply IHl. inversion H0. subst. apply H4. *)
  * simpl. rewrite H, H0. rewrite renn_up. reflexivity.
  * simpl. rewrite H, H0. reflexivity.
  * simpl. rewrite H. rewrite renn_up. erewrite map_ext_Forall. reflexivity. apply H0. 
    (* revert ρ. exact H0. *)
  * simpl. rewrite H, H0, H1. do 2 rewrite renn_up. reflexivity.
  (* Lists *)
  * apply Forall_nil. Print Forall.
  * apply Forall_cons; auto.
  * constructor.
  * constructor; auto.
  * constructor.
  * constructor; auto. rewrite H, H0. reflexivity.
  * constructor.
  * constructor; auto. rewrite H, H0. reflexivity.
  * constructor.
  * constructor; auto. rewrite H, H0. rewrite renn_up. reflexivity.
  * constructor.
  * constructor; auto. rewrite H. rewrite renn_up. reflexivity.
Qed.


Theorem renaming_is_subst : forall e ρ,
  rename ρ e = e.[ren ρ]
  with renaming_is_subst_value : forall e ρ, renameValue ρ e = e.[ren ρ]ᵥ
  with renaming_is_subst_nonvalue : forall e ρ, renameNonValue ρ e = e.[ren ρ]ₑ.
Proof.
  * apply renaming_is_subst.
  * apply renaming_is_subst_value.
  * apply renaming_is_subst_nonvalue.
  (* not gonna work *)
Abort.

Theorem renaming_is_subst : forall e ρ,
  rename ρ e = e.[ren ρ].
Proof.
  induction e using Expression_ind2 with (Q := fun l => forall ρ, Forall (fun e => rename ρ e = e.[ren ρ]) l); intros; try reflexivity; cbn.
  * rewrite IHe, ren_up, renn_up. auto.
  * rewrite IHe. erewrite map_ext_Forall. reflexivity. auto.
  * rewrite IHe1. rewrite <- ren_up, IHe2. auto.
  * rewrite <- ren_up, <- renn_up, IHe1, IHe2, <- ren_up. auto.
  * rewrite IHe1, IHe2. auto.
  * rewrite IHe1, IHe3, <- renn_up, IHe2. auto.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
  * constructor; auto.
  * constructor.
Qed.


Theorem idrenaming_up : upren id = id.
Proof.
  extensionality x. destruct x; auto.
Qed.

Corollary idrenaming_upn n : uprenn n id = id.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idrenaming_up. auto.
Qed.

(*
Theorem idrenaming_is_id : forall e, rename id e = e.
Proof.
  induction e using Exp_ind2 with (Q := fun l => Forall (fun e => rename id e = e) l); intros; cbn; try rewrite idrenaming_upn; try rewrite idrenaming_up; try rewrite IHe; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try reflexivity.
  2-3: constructor; auto.
  rewrite map_ext_Forall with (g := id); auto. rewrite map_id. auto.
Qed.
*)

Theorem idsubst_up : up_subst idsubst = idsubst.
Proof.
  extensionality x. unfold up_subst. destruct x; auto.
Qed.

Corollary idsubst_upn n : upn n idsubst = idsubst.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idsubst_up. auto.
Qed.

(*
Theorem idsubst_is_id : forall e, e.[idsubst] = e.
Proof.
  induction e using Exp_ind2 with (Q := fun l => Forall (fun e => e.[idsubst] = e) l); intros; cbn; try rewrite idsubst_upn; try rewrite idsubst_up; try rewrite IHe; try rewrite IHe1; try rewrite IHe2; try rewrite IHe3; try reflexivity.
  2-3: constructor; auto.
  rewrite map_ext_Forall with (g := id); auto. rewrite map_id. auto.
Qed.
*)


Lemma up_get_inl ξ x y:
  ξ x = inl y -> up_subst ξ (S x) = inl (renameValue (fun n => S n) y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.


Lemma up_get_inr ξ x y:
  ξ x = inr y -> up_subst ξ (S x) = inr (S y).
Proof.
  intros. unfold up_subst. unfold shift. rewrite H. auto.
Qed.

Lemma renaming_fold m :
  (fun n => m + n) = iterate (fun x => S x) m.
Proof.
  extensionality x. induction m; cbn; auto.
Qed.

Lemma upren_subst_up : forall σ ξ,
  upren σ >>> up_subst ξ = up_subst (σ >>> ξ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>>".
  destruct x; auto.
Qed.

Corollary uprenn_subst_upn n : forall σ ξ,
  uprenn n σ >>> upn n ξ = upn n (σ >>> ξ).
Proof.
  induction n; intros; auto.
  cbn. rewrite <- IHn, upren_subst_up. auto.
Qed.

(*
Lemma subst_ren (σ : Renaming) (ξ : Substitution) e :
  e.[ren σ].[ξ] = e.[σ >>> ξ].
Proof.
  revert ξ σ. induction e using Exp_ind2 with (Q := fun l => forall ξ σ, Forall (fun e => e.[ren σ].[ξ] = e.[σ >>> ξ]) l); simpl; intros; auto.
  * rewrite <- renn_up, <- ren_up. rewrite IHe, upren_subst_up, uprenn_subst_upn. auto.
  * rewrite IHe. erewrite map_map, map_ext_Forall. reflexivity. auto.
  * rewrite <- ren_up, IHe1, IHe2, upren_subst_up. auto.
  * rewrite <- renn_up, <- ren_up. rewrite IHe1, upren_subst_up, uprenn_subst_upn.
    rewrite <- ren_up, IHe2, upren_subst_up. auto.
  * rewrite IHe1, IHe2. auto.
  * now rewrite IHe1, IHe3, <- renn_up, IHe2, uprenn_subst_upn.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
Qed.
*)

Notation "σ >> ξ" := (substcomp σ ξ) (at level 56, left associativity).

Theorem upren_comp : forall σ ρ,
  upren σ >>> upren ρ = upren (σ >>> ρ).
Proof.
  intros. unfold upren, ">>>". extensionality n. destruct n; auto.
Qed.

Corollary uprenn_comp : forall n σ ρ,
  uprenn n σ >>> uprenn n ρ = uprenn n (σ >>> ρ).
Proof.
  induction n; intros; auto. simpl. rewrite upren_comp, IHn. auto.
Qed.

(*
Theorem rename_up : forall e n σ ρ,
  rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e.
Proof.
  induction e using Exp_ind2 with
    (Q := fun l => forall n σ ρ, Forall (fun e => rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e) l);
  intros; simpl; auto.
  * rewrite <- uprenn_comp. reflexivity.
  * rewrite <- uprenn_comp. reflexivity.
  * repeat fold_upn. rewrite IHe, uprenn_comp. auto.
  * erewrite IHe, map_map, map_ext_Forall. reflexivity. auto.
  * rewrite IHe1. do 2 fold_upn. rewrite IHe2. auto.
  * repeat fold_upn. rewrite IHe1, IHe2, uprenn_comp. auto.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2, IHe3, <- uprenn_comp.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
Qed.
*)

(*
Theorem rename_comp :
  forall e σ ρ, rename σ (rename ρ e) = rename (ρ >>> σ) e.
Proof.
  induction e using Exp_ind2 with (Q := fun l => forall σ ρ, Forall (fun e => rename σ (rename ρ e) = rename (ρ >>> σ) e) l); intros; auto; cbn.
  * do 3 fold_upn. now rewrite rename_up.
  * now erewrite IHe, map_map, map_ext_Forall.
  * now rewrite IHe1, IHe2, upren_comp.
  * do 2 fold_upn. now rewrite IHe1, IHe2, uprenn_comp, upren_comp.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe3, rename_up.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
Qed.
*)

(*
Lemma subst_up_upren : forall σ ξ,
  up_subst ξ >> ren (upren σ) = up_subst (ξ >> ren σ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>", shift.
  destruct x; auto. destruct (ξ x) eqn:P; auto.
  rewrite <- renaming_is_subst, <- renaming_is_subst. f_equiv.
  replace (fun n : nat => match n with
                       | 0 => 0
                       | S n' => S (σ n')
                       end) with (upren σ) by auto.
  rewrite rename_comp, rename_comp. f_equiv.
Qed.
*)

(*
Lemma subst_upn_uprenn : forall n σ ξ,
  upn n ξ >> ren (uprenn n σ) = upn n (ξ >> ren σ).
Proof.
  induction n; intros; auto. simpl.
  rewrite subst_up_upren, IHn. auto.
Qed.
*)

(*
Lemma ren_subst (ξ : Substitution) (σ : Renaming) e :
  e.[ξ].[ren σ] = e.[ξ >> ren σ].
Proof.
  revert ξ σ. induction e using Exp_ind2
    with (Q := fun l => forall ξ σ, Forall (fun e => e.[ξ].[ren σ] = e.[ξ >> ren σ]) l);
  simpl; intros; auto.
  * unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * do 3 fold_upn. now rewrite <- renn_up, <- subst_upn_uprenn, IHe.
  * now erewrite IHe, map_map, map_ext_Forall.
  * now rewrite <- ren_up, <- subst_up_upren, IHe1, IHe2.
  * do 2 fold_upn. rewrite <- renn_up, <- subst_upn_uprenn, IHe1.
    replace (up_subst (ξ >> ren σ)) with (up_subst ξ >> ren (upren σ)) by apply subst_up_upren. (* rewrite does not work here for some reason *)
    now rewrite <- IHe2, <- ren_up, <-subst_up_upren.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, <- renn_up, <- subst_upn_uprenn, IHe2, IHe3.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
Qed.
*)

(*
Lemma up_comp ξ η :
  up_subst ξ >> up_subst η = up_subst (ξ >> η).
Proof.
  extensionality x.
  unfold ">>". cbn. unfold up_subst, shift. destruct x; auto.
  destruct (ξ x) eqn:P; auto.
  do 2 rewrite renaming_is_subst. rewrite ren_subst, subst_ren.
  unfold ren. f_equiv. f_equiv. extensionality n.
  unfold ">>>", ">>", up_subst, shift. destruct (η n) eqn:P0; auto.
  rewrite renaming_is_subst. auto.
Qed.
*)

Corollary upn_comp : forall n ξ η,
  upn n ξ >> upn n η = upn n (ξ >> η).
Proof.
  induction n; intros; auto. simpl. rewrite <- IHn, up_comp. auto.
Qed.

Lemma subst_comp ξ η e :
  e.[ξ].[η] = e.[ξ >> η].
Proof.
  revert ξ η. induction e using Exp_ind2 with (Q := fun l => forall ξ η,
     Forall (fun e => e.[ξ].[η] = e.[ξ >> η]) l); simpl; intros; auto.
  * unfold ">>". break_match_goal; auto.
  * unfold ">>". break_match_goal; auto.
  * do 3 fold_upn. now rewrite IHe, upn_comp.
  * now erewrite IHe, map_map, map_ext_Forall.
  * now rewrite IHe1, IHe2, up_comp.
  * do 3 fold_upn. now rewrite IHe1, IHe2, upn_comp, up_comp.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2, upn_comp, IHe3.
  * now rewrite IHe1, IHe2.
  * now rewrite IHe1, IHe2.
Qed.

Theorem rename_subst_core : forall e v,
  (rename (fun n : nat => S n) e).[v .:: idsubst] = e.
Proof.
  intros.
  rewrite renaming_is_subst, subst_comp. cbn.
  unfold substcomp, ren. cbn. rewrite idsubst_is_id. reflexivity.
Qed.

Theorem rename_subst : forall e v,
  (rename (fun n : nat => S n) e).[v/] = e.
Proof.
  intros. apply rename_subst_core.
Qed.

Lemma scons_substcomp_core v ξ η :
  (v .:: ξ) >> η = match v with 
                   | inl exp => inl (exp.[η])
                   | inr n => η n
                   end .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp. now destruct x.
Qed.

Lemma scons_substcomp v ξ η :
  (v .: ξ) >> η = v.[η] .: (ξ >> η).
Proof.
  apply scons_substcomp_core.
Qed.

Lemma scons_substcomp_list ξ η vals :
  (list_subst vals ξ) >> η = list_subst (map (subst η) vals) (ξ >> η).
Proof.
  induction vals; simpl. auto.
  rewrite scons_substcomp, IHvals. auto.
Qed.

Lemma substcomp_scons_core v ξ η :
  up_subst ξ >> v .:: η = v .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp, up_subst. destruct x; auto.
  unfold shift. destruct (ξ x) eqn:P; auto.
  rewrite renaming_is_subst, subst_comp. f_equiv.
Qed.

Lemma substcomp_scons v ξ η :
  up_subst ξ >> v .: η = v .: (ξ >> η).
Proof.
  apply substcomp_scons_core.
Qed.

Corollary substcomp_list l ξ η :
  upn (length l) ξ >> list_subst l η = list_subst l (ξ >> η).
Proof.
  induction l; simpl; auto.
  * now rewrite substcomp_scons, IHl.
Qed.

Theorem subst_extend_core : forall ξ v,
  (up_subst ξ) >> (v .:: idsubst) = v .:: ξ.
Proof.
  intros. unfold substcomp. extensionality x. destruct x; auto.
  cbn. break_match_goal.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. rewrite rename_subst_core. auto.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. cbn. reflexivity.
Qed.

Theorem subst_extend : forall ξ v,
  (up_subst ξ) >> (v .: idsubst) = v .: ξ.
Proof.
  intros. apply subst_extend_core.
Qed.

Corollary subst_list_extend : forall n ξ vals, length vals = n ->
  (upn n ξ) >> (list_subst vals idsubst) = list_subst vals ξ.
Proof.
  induction n; intros.
  * apply length_zero_iff_nil in H. subst. cbn. unfold substcomp. extensionality x.
    break_match_goal; try rewrite idsubst_is_id; try reflexivity.
  * simpl. apply eq_sym in H as H'. apply element_exist in H'. destruct H', H0. subst.
    simpl. rewrite substcomp_scons. rewrite IHn; auto.
Qed.

Theorem list_subst_lt : forall n vals ξ, n < length vals ->
  list_subst vals ξ n = inl (nth n vals (ELit 0)).
Proof.
  induction n; intros; destruct vals.
  * inversion H.
  * simpl. auto.
  * inversion H.
  * simpl in H. apply Lt.lt_S_n in H. eapply IHn in H. simpl. exact H.
Qed.

Theorem list_subst_ge : forall n vals ξ, n >= length vals ->
  list_subst vals ξ n = ξ (n - length vals).
Proof.
  induction n; intros; destruct vals.
  * simpl. auto.
  * inversion H.
  * cbn. auto.
  * simpl in H. apply le_S_n in H. eapply IHn in H. simpl. exact H.
Qed.

Corollary list_subst_get_possibilities : forall n vals ξ,
  list_subst vals ξ n = inl (nth n vals (ELit 0)) /\ n < length vals
\/
  list_subst vals ξ n = ξ (n - length vals) /\ n >= length vals.
Proof.
  intros. pose (Nat.lt_decidable n (length vals)). destruct d.
  * left. split. now apply list_subst_lt. auto.
  * right. split. apply list_subst_ge. lia. lia.
Qed.

Lemma substcomp_id_r :
  forall ξ, ξ >> idsubst = ξ.
Proof.
  unfold ">>". intros. extensionality x.
  break_match_goal; auto. rewrite idsubst_is_id. auto.
Qed.

Lemma substcomp_id_l :
  forall ξ, idsubst >> ξ = ξ.
Proof.
  unfold ">>", idsubst. intros. extensionality x. auto.
Qed.

Lemma subst_ren_scons : forall (ξ : Substitution) e,
  ξ 0 = inl e ->
  (e .: (fun n : nat => n + 1) >>> ξ) = ξ.
Proof.
  intros. extensionality x. unfold ">>>", scons. destruct x; auto.
  rewrite Nat.add_comm. reflexivity.
Qed.

Lemma ren_up_subst :
  forall ξ,
    ren (fun n => S n) >> up_subst ξ = ξ >> ren (fun n => S n).
Proof.
  intros. extensionality x; cbn.
  unfold shift. unfold ">>".
  break_match_goal; cbn.
  now rewrite <- renaming_is_subst.
  reflexivity.
Qed.

Lemma ren_scons :
  forall ξ f, forall x, ren (fun n => S (f n)) >> x .: ξ = ren (fun n => f n) >> ξ.
Proof.
  intros.
  extensionality k. cbn. auto.
Qed.

Lemma rename_upn_list_subst :
  forall m ξ vals, length vals = m ->
    ren (fun n => m + n) >> (upn m ξ >> list_subst vals idsubst) = ξ.
Proof.
  intros.
  rewrite (subst_list_extend m ξ vals H).
  generalize dependent vals. induction m; intros; cbn.
  - replace (ren (fun n => n)) with idsubst by auto. apply length_zero_iff_nil in H.
    subst. cbn. now rewrite substcomp_id_l.
  - assert (length vals = S m) by auto.
    apply eq_sym, element_exist in H as [x0 [xs H1]]. subst. inversion H0.
    replace (list_subst (x0 :: xs) ξ) with (x0 .: list_subst xs ξ) by auto.
    specialize (IHm xs H1).
    erewrite H1, ren_scons; eauto.
Qed.

Ltac fold_list_subst :=
match goal with
| |- context G [?x .: list_subst ?xs ?ξ] => replace (x .: list_subst xs ξ) with (list_subst (x :: xs) ξ) by auto
end.

Ltac fold_list_subst_hyp :=
match goal with
| [H: context G [?x .: list_subst ?xs ?ξ] |- _] => replace (x .: list_subst xs ξ) with (list_subst (x :: xs) ξ) in H by auto
end.

Lemma substcomp_assoc :
  forall ξ σ η, (ξ >> σ) >> η = ξ >> (σ >> η).
Proof.
  intros. extensionality x. unfold ">>".
  destruct (ξ x) eqn:D1; auto.
  rewrite subst_comp. reflexivity.
Qed.