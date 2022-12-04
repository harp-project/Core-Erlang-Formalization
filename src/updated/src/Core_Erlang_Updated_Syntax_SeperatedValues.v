From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Logic.FunctionalExtensionality.
From Coq Require Import FunctionalExtensionality PropExtensionality.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.
Require Export Coq.Structures.OrderedType.
Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat.
               
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
(*All Vals*)
| ENil
| ELit    (l : Literal)
| EFun    (vl : nat) (e : Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
| EMap    (l : list (Expression * Expression))
| EValues (el : list Expression)
| EVar    (n : nat)
| EFunId  (n : nat)
(** Initially: for built-in functions : *)
| ECall   (f : string)    (l : list Expression)
| EPrimOp (f : string)    (l : list Expression)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : nat) (e1 e2 : Expression)
(** For sequencing: do expressions (ESeq) *)
| ESeq    (e1 e2 : Expression)
(*| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression) *)
| ELetRec (l : list (nat * Expression)) (e : Expression)
| ETry    (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
.

Inductive Value : Set :=
| VNil
| VLit    (l : Literal)
| VVar    (n : nat)
| VFunId  (n : nat)
| VFun    (vl : nat) (e : Expression)
| VCons   (hd tl : Value)
| VTuple  (l : list Value)
| VMap    (l : list (Value * Value))
| VValues (el : list Value)
.

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
| scoped_enil (n : nat)                              : ExpScoped ENil n
| scoped_elit (l : Literal) (n : nat)                : ExpScoped (ELit l) n
| scoped_efunId (fi : nat) (n : nat)                 : n > fi -> ExpScoped (EFunId fi) n
| scoped_evar (v : nat) (n : nat)                    : n > v -> ExpScoped (EVar v) n
| scoped_etuple (l : list Expression) (n : nat)     : Forall (fun x => ExpScoped x n) l -> ExpScoped (ETuple l) (n)
| scoped_econs (hd tl : Expression) (n : nat)       : ExpScoped hd n -> ExpScoped tl n -> ExpScoped (ECons hd tl) (n)
| scoped_emap (l : list (Expression * Expression)) (n : nat) : 
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x n) (map (fun '(x,y) => y) l)
  -> ExpScoped (EMap l) n
| scoped_evalues (el : list Expression) (n : nat)   : Forall (fun x => ExpScoped x n) el -> ExpScoped (EValues el) (n)
| scoped_efun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (S(vl) + n) -> ExpScoped (EFun vl e) (n)
| scoped_call (f : string) (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> ExpScoped (ECall f l) (n)
| scoped_primOp (f : string) (l : list Expression) (n : nat) : Forall (fun x => ExpScoped x n) l -> ExpScoped (EPrimOp f l) (n)
| scoped_app (exp: Expression) (l : list Expression) (n : nat) : ExpScoped exp n -> Forall (fun x => ExpScoped x n) l -> ExpScoped (EApp exp l) (n)
| scoped_case (e : Expression) (l : list ((list Pattern) * Expression * Expression)) (m n : nat) : 
  ExpScoped e n -> 
  Forall (fun x => patternListScope x <= m) (map (fun '(x,y,z) => x) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => y) l) ->
  Forall (fun x => ExpScoped x (m+n))       (map (fun '(x,y,z) => z) l)
  -> ExpScoped (ECase e l) (n)
| scoped_let (l : nat) (e1 e2 : Expression) (n : nat) : 
  ExpScoped e1 n -> ExpScoped e2 (l+n)
  -> ExpScoped (ELet l e1 e2) n
| scoped_seq (e1 e2 : Expression) (n : nat) : ExpScoped e1 n -> ExpScoped e2 n -> ExpScoped (ESeq e1 e2) n
| scoped_letRec (l : list (nat * Expression)) (e : Expression) (m n : nat) :
  Forall (fun x => x <= m) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ExpScoped x (S(m) + n)) (map (fun '(x,y) => y) l) -> (*in m + n we may need +(length l) as well because of function definitions in letRec *)
  ExpScoped e (n + (length l))
  -> ExpScoped (ELetRec l e) n
| scoped_try (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression) (n : nat) : 
  ExpScoped e1 n -> 
  ExpScoped e2 (n + vl1) ->
  ExpScoped e3 (n + vl2)
  -> ExpScoped (ETry e1 vl1 e2 vl2 e3) n
.

Inductive ValScoped : Value -> nat -> Prop :=
(*Exp re a func nál hivatkozok*)
| scoped_vnil (n : nat)                              : ValScoped VNil n
| scoped_vlit (l : Literal) (n : nat)                : ValScoped (VLit l) n
| scoped_vfunId (fi : nat) (n : nat)                 : n > fi -> ValScoped (VFunId fi) n
| scoped_vvar (v : nat) (n : nat)                    : n > v -> ValScoped (VVar v) n
| scoped_vtuple (l : list Value) (n : nat)     : Forall (fun x => ValScoped x n) l -> ValScoped (VTuple l) (n)
| scoped_vcons (hd tl : Value) (n : nat)       : ValScoped hd n -> ValScoped tl n -> ValScoped (VCons hd tl) (n)
| scoped_vmap (l : list (Value * Value)) (n : nat) : 
  Forall (fun x => ValScoped x n) (map (fun '(x,y) => x) l) ->
  Forall (fun x => ValScoped x n) (map (fun '(x,y) => y) l)
  -> ValScoped (VMap l) n
| scoped_vvalues (el : list Value) (n : nat) : Forall (fun x => ValScoped x n) el -> ValScoped (VValues el) (n)
| scoped_vfun (vl : nat) (e : Expression) (n : nat)  : ExpScoped e (S(vl) + n) -> ValScoped (VFun vl e) (n)
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

(*rename Expressions*)

Fixpoint rename (ρ : Renaming) (ex : Expression) : Expression :=
match ex with
 | ENil         => ex
 | ELit l       => ex
 | EFun vl e    => EFun vl (rename (uprenn (S(vl)) ρ) e)
 | EVar n       => EVar (ρ n)
 | EFunId n     => EFunId (ρ n)
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

(*rename Values*)

Fixpoint renameValues (ρ : Renaming) (val : Value) : Value :=
match val with
 | VNil         => val
 | VLit l       => val
 | VFun vl e    => VFun vl (rename (uprenn (S(vl)) ρ) e)
 | VVar n       => VVar (ρ n)
 | VFunId n     => VFunId (ρ n)
 | VValues el       => VValues (map (fun x => renameValues ρ x) el)
 | VCons   hd tl    => VCons (renameValues ρ hd) (renameValues ρ tl)
 | VTuple  l        => VTuple (map (fun x => renameValues ρ x) l)
 | VMap    l        => VMap (map (fun '(x,y) => (renameValues ρ x, renameValues ρ y)) l)
end
.


Fixpoint valueToExpression (val : Value) : Expression :=
match val with
 | VNil => ENil
 | VLit l => ELit l
 | VVar n => EVar n
 | VFunId n => EFunId n
 | VFun vl e => EFun vl e
 | VCons hd tl => ECons (valueToExpression hd) (valueToExpression tl)
 | VTuple l => ETuple (map (fun x => valueToExpression x) l)
 | VMap l => EMap (map (fun '(x,y) => (valueToExpression x, valueToExpression y)) l)
 | VValues el => EValues (map (fun x => valueToExpression x) el)
end.


(*Substitution For Expressions*)

Definition Substitution := nat -> Value + nat. (** We need to have the names for the
                                                  identity elements explicitly, because 
                                                  of the shiftings (up, upn) *)
Definition idsubst : Substitution := fun x => inr x.

Definition shift (ξ : Substitution) : Substitution := 
fun s =>
  match ξ s with
  | inl exp => inl (renameValues (fun n => S n) exp)
  | inr num => inr (S num)
  end.

Definition up_subst (ξ : Substitution) : Substitution :=
  fun x =>
    match x with
    | 0 => inr 0
    | S x' => shift ξ x'
    end.

Notation upn := (iterate up_subst).


Fixpoint subst (ξ : Substitution) (ex : Expression) : Expression :=
match ex with
 | ENil         => ex
 | ELit l       => ex
 | EFun vl e    => EFun vl (subst (upn (S(vl)) ξ) e)
 | EVar n       => match ξ n with
                     | inl exp => valueToExpression exp
                     | inr num => EVar num
                     end
 | EFunId n     => match ξ n with
                     | inl exp => valueToExpression exp
                     | inr num => EFunId num
                     end
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

(*Substitution For Values*)

Fixpoint substForValue (ξ : Substitution) (val : Value) : Value :=
match val with
 | VNil         => val
 | VLit l       => val
 | VFun vl e    => VFun vl (subst (upn (S(vl)) ξ) e) (*Problem here*)
 | VVar n       => match ξ n with
                     | inl exp => exp
                     | inr num => VVar num
                     end
 | VFunId n     => match ξ n with
                     | inl exp => exp
                     | inr num => VFunId num
                     end
 | VValues el       => VValues (map (fun x => substForValue ξ x) el)
 | VCons   hd tl    => VCons (substForValue ξ hd) (substForValue ξ tl)
 | VTuple  l        => VTuple (map (fun x => substForValue ξ x) l)
 | VMap    l        => VMap (map (fun '(x,y) => (substForValue ξ x, substForValue ξ y)) l)
end
.

(*--------------------------------------------------------------------------*)

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



Section correct_expression_ind.

Variables
(* Expression *)
  (P : Expression -> Prop)
  (Q : list Expression -> Prop)
  (R : list (Expression * Expression) -> Prop)
  (W : list (list Pattern * Expression * Expression) -> Prop)
  (Z : list (nat * Expression) -> Prop).
(* SingleExpression *)
  (* (P2 : SingleExpression -> Prop)
  (Q2 : list SingleExpression -> Prop). *)

Hypotheses
  (H : forall (l : list Expression), Q l -> P (EValues l))
  (* (H0 : forall (e : SingleExpression), P2 e -> P1 (ESingle e)) *)
  (I : P ENil)
  (I0 : forall (l : Literal), P (ELit l))
  (I1 : forall (v : nat), P (EVar v))
  (I2 : forall (f : nat), P (EFunId f))
  (I3 : forall (e : Expression), P e -> forall (vl : nat), P (EFun vl e))
  (I4 : forall (hd : Expression), P hd -> forall (tl : Expression), P tl 
       -> P (ECons hd tl))
  (I5 : forall (l : list Expression), Q l -> P (ETuple l))
  (I6 : forall (l : list Expression), Q l -> forall (f : string), P (ECall f l))
  (I7 : forall (l : list Expression), Q l -> forall (f : string), P (EPrimOp f l))
  (I8 : forall (e : Expression), P e -> forall (l : list Expression), Q l
       -> P (EApp e l))
  (I9 : forall (e : Expression), P e ->
        forall (l : list (list Pattern * Expression * Expression)), W l
       -> P (ECase e l))
  (I10 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2
       -> forall (vl : nat), P (ELet vl e1 e2))
  (I11 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2
       -> P (ESeq e1 e2))
  (I12 : forall (l : list (nat * Expression) ), Z l
       -> forall (e : Expression), P e -> P (ELetRec l e))
  (I13 : forall (l : list (Expression * Expression)), R l -> P (EMap l))
  (I14 : forall (e1 : Expression), P e1 ->
         forall (e2 : Expression), P e2 ->
         forall (e3 : Expression), P e3 ->
         forall (vl1 vl2 : nat), P (ETry e1 vl1 e2 vl2 e3))
  (J : Q [])
  (J0 : R [])
  (J1 : W [])
  (J2 : Z [])
  (K : forall (e : Expression), P e -> forall (l : list Expression), Q l
      -> Q (e::l))
  (K0 : forall (e : Expression), P e -> forall (l : list Expression), Q l
      -> Q (e::l))
  (K1 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 ->
        forall (l : list (Expression * Expression)), R l
      -> R ((e1, e2)::l))
  (K2 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 ->
        forall (l : list (list Pattern * Expression * Expression)), W l
     -> forall (pl : list Pattern), W ((pl, e1, e2)::l))
  (K3 : forall (e : Expression), P e -> 
        forall (l : list (nat * Expression)), Z l
     -> forall (vl : nat), Z (((vl, e))::l)).

Fixpoint Expression_ind2 (e : Expression) : P e :=
match e as x return P x with
 | EValues el => H el ((fix l_ind (l':list Expression) : Q l' :=
                       match l' as x return Q x with
                       | [] => J
                       | v::xs => K v (Expression_ind2 v) xs (l_ind xs)
                       end) el)
 | ENil => I
 | ELit l => I0 l
 | EVar v => I1 v
 | EFunId f => I2 f
 | EFun vl e => I3 e (Expression_ind2 e) vl
 | ECons hd tl => I4 hd (Expression_ind2 hd) tl (Expression_ind2 tl)
 | ETuple l => I5 l ((fix l_ind (l':list Expression) : Q l' :=
                       match l' as x return Q x with
                       | [] => J
                       | v::xs => K0 v (Expression_ind2 v) xs (l_ind xs)
                       end) l)
 | ECall f l => I6 l ((fix l_ind (l':list Expression) : Q l' :=
                       match l' as x return Q x with
                       | [] => J
                       | v::xs => K0 v (Expression_ind2 v) xs (l_ind xs)
                       end) l) f
 | EPrimOp f l => I7 l ((fix l_ind (l':list Expression) : Q l' :=
                       match l' as x return Q x with
                       | [] => J
                       | v::xs => K0 v (Expression_ind2 v) xs (l_ind xs)
                       end) l) f
 | EApp exp l => I8 exp (Expression_ind2 exp) l ((fix l_ind (l':list Expression) : Q l' :=
                       match l' as x return Q x with
                       | [] => J
                       | v::xs => K0 v (Expression_ind2 v) xs (l_ind xs)
                       end) l)
 | ECase e l => I9 e (Expression_ind2 e) l
                ((fix l_ind (l':list (list Pattern * Expression * Expression)) : W l' :=
                       match l' as x return W x with
                       | [] => J1
                       | (pl, e1, e2)::xs => K2 e1 (Expression_ind2 e1) 
                                                e2 (Expression_ind2 e2)
                                                xs (l_ind xs) pl
                       end) l)
 | ELet l e1 e2 => I10 e1 (Expression_ind2 e1) e2 (Expression_ind2 e2) l
 | ESeq e1 e2 => I11 e1 (Expression_ind2 e1) e2 (Expression_ind2 e2)
 | ELetRec l e => I12 l 
        ((fix l_ind (l': list (nat * Expression)) : Z l' :=
                       match l' as x return Z x with
                       | [] => J2
                       | (vl, e)::xs => K3 e (Expression_ind2 e) xs (l_ind xs) vl
                       end) l) 
                     e (Expression_ind2 e)
 | EMap l => I13 l ((fix l_ind (l':list (Expression * Expression)) : R l' :=
                       match l' as x return R x with
                       | [] => J0
                       | (e1, e2)::xs => K1 e1 (Expression_ind2 e1)
                                            e2 (Expression_ind2 e2)
                                            xs (l_ind xs)
                       end) l)
 | ETry e1 vl1 e2 vl2 e0 => I14 e1 (Expression_ind2 e1)
                                e2 (Expression_ind2 e2)
                                e0 (Expression_ind2 e0)
                                vl1 vl2
end.

End correct_expression_ind.



Section correct_value_ind.

Variables
  (P  : Value -> Prop)
  (Q  : list Value -> Prop)
  (R  : list (Value * Value) -> Prop).

Hypotheses
 (H1 : P VNil)
 (H2 : forall (l : Literal), P (VLit l))
 (H3 : forall (n : nat), P (VVar n))
 (H4 : forall (n : nat), P (VFunId n))
 (H5 : forall (n : nat) (e : Expression), P (VFun n e))
 (H6 : forall (hd : Value), P hd -> forall (tl : Value), P tl -> P (VCons hd tl))
 (H7 : forall (l : list Value), Q l -> P (VTuple l))
 (H8 : forall (l : list (Value * Value)), R l -> P (VMap l))
 (H9 : forall (el : list Value), Q el -> P (VValues el))
  
 (HQ1: Q [])
 (HQ2: forall (v : Value), P v -> forall (vl : list Value), Q vl -> Q (v::vl))
 (HR1: R [])
 (HR2: forall (v1 : Value), P v1 -> forall (v2 : Value), P v2 ->
 forall (vl : list (Value * Value)), R vl -> R ((v1,v2)::vl))
 .


Fixpoint Value_ind2 (v : Value) : P v :=
  match v as x return P x with
  | VNil => H1
  | VLit l => H2 l
  | VVar n => H3 n
  | VFunId n => H4 n
  | VFun vl e => H5 vl e
  | VCons hd tl => H6 hd (Value_ind2 hd) tl (Value_ind2 tl)
  | VTuple l => H7 l (list_ind Q HQ1 (fun v ls => HQ2 v (Value_ind2 v) ls) l)
  | VMap l => H8 l (list_ind R HR1 (fun '(v1,v2) ls => HR2 v1 (Value_ind2 v1) v2 (Value_ind2 v2) ls) l)
  | VValues el => H9 el (list_ind Q HQ1 (fun v ls => HQ2 v (Value_ind2 v) ls) el)
  end.

End correct_value_ind.

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

Notation "s .[ σ ]ᵥ" := (substForValue σ s)
  (at level 2, σ at level 200, left associativity,
   format "s .[ σ ]ᵥ" ).
Notation "s .[ t /]ᵥ" := (substForValue (t .: idsubst) s)
  (at level 2, t at level 200, left associativity,
   format "s .[ t /]ᵥ").
Notation "s .[ t1 , t2 , .. , tn /]ᵥ" :=
  (substForValue (scons (inl t1) (scons (inl t2) .. (scons (inl tn) idsubst) .. )) s)
  (at level 2, left associativity).

Definition composition {A B C} (f : A -> B) (g : B -> C) : A -> C := fun x => g (f x).
Notation "f >>> g" := (composition f g)
  (at level 56, left associativity).

Definition list_subst (l : list Value) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.


Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match ξ x with
    | inl exp => inl (substForValue η exp)
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

Theorem renaming_is_subst : forall e ρ,
  rename ρ e = e.[ren ρ].
Proof.
  einduction e using Expression_ind2 with
  (Q := fun l => forall ρ, Forall (fun x : Expression => rename ρ x = x.[ren ρ]) l)
  (R := fun l => forall ρ, Forall
  (fun x : Expression * Expression =>
   (let '(x0, y) := x in (rename ρ x0, rename ρ y)) =
   (let '(x0, y) := x in (x0.[ren ρ], y.[ren ρ]))) l)
  (W := fun l => forall ρ, Forall
  (fun x : list Pattern * Expression * Expression =>
   (let
    '(p, x0, y) := x in
     (p, rename (uprenn (patternListScope p) ρ) x0, rename (uprenn (patternListScope p) ρ) y)) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (patternListScope p) (ren ρ)], y.[upn (patternListScope p) (ren ρ)]))) l)
  (Z := fun l => forall ρ, Forall
  (fun x : nat * Expression =>
   (let '(n, x0) := x in (n, rename (upren (uprenn n ρ)) x0)) =
   (let '(n, x0) := x in (n, x0.[up_subst (upn n (ren ρ))]))) l)
  ;
  intros.
  (* Expressions *)
  * simpl. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ren ρ])).
    - reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite IHe0. rewrite ren_up. rewrite renn_up. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ren ρ])).
    - reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ren ρ])).
    - reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ren ρ])).
    - reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ren ρ])).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (patternListScope p) (ren ρ)], y.[upn (patternListScope p) (ren ρ)]))).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite renn_up. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[up_subst (upn n (ren ρ))]))).
    - rewrite IHe1. rewrite renn_up. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ren ρ], y.[ren ρ]))).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite IHe0_3.
    rewrite renn_up. rewrite renn_up. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. rewrite renn_up. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite IHe0. rewrite ren_up. rewrite renn_up. reflexivity.
    - apply IHe1.
Qed.

(*For Valuer Begin*)

Theorem renaming_is_subst_forVal :
  forall e ρ, renameValues ρ e = e.[ren ρ]ᵥ.
Proof.
  einduction e using Value_ind2 with
  (Q := fun l => forall ρ, Forall (fun x : Value => renameValues ρ x = x.[ren ρ]ᵥ) l)
  (R := fun l => forall ρ, Forall
  (fun x : Value * Value =>
   (let '(x0, y) := x in (renameValues ρ x0, renameValues ρ y)) =
   (let '(x0, y) := x in (x0.[ren ρ]ᵥ, y.[ren ρ]ᵥ))) l)
  ;
  intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * pose proof renaming_is_subst as H.
    simpl. rewrite <- renn_up. rewrite <- ren_up. rewrite H. reflexivity.
  * simpl. rewrite IHv2. rewrite IHv1. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Value => x.[ren ρ]ᵥ)).
    - simpl. reflexivity.
    - apply IHv.
  * simpl. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ren ρ]ᵥ, y.[ren ρ]ᵥ))).
    - reflexivity.
    - apply IHv.
  * simpl. erewrite map_ext_Forall with (g := (fun x : Value => x.[ren ρ]ᵥ)).
    - reflexivity.
    - apply IHv.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv. reflexivity.
    - apply IHv0.
  * constructor.
  * constructor.
    - rewrite IHv1. rewrite IHv2. reflexivity.
    - apply IHv3.
Qed.
(*For Values End*)

Theorem idrenaming_up : upren id = id.
Proof.
  extensionality x. destruct x; auto.
Qed.

Corollary idrenaming_upn n : uprenn n id = id.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idrenaming_up. auto.
Qed.

Theorem idrenaming_is_id : forall e, rename id e = e.
Proof.
  einduction e using Expression_ind2 (*with
  (Q := fun l => forall ρ, Forall (fun x : Expression => rename id x = id x) l)*)
  ;intros.
  (* Expressions *)
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite idrenaming_upn. rewrite idrenaming_up. rewrite IHe0. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite IHe0. rewrite map_id. reflexivity.
    - apply IHe1.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite IHe0. rewrite map_id. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite idrenaming_upn. rewrite IHe0_2. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite idrenaming_upn. rewrite map_id. rewrite IHe1. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite idrenaming_upn. rewrite IHe0_2.
    rewrite idrenaming_upn. rewrite IHe0_3. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite idrenaming_upn. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite idrenaming_upn. rewrite idrenaming_up. rewrite IHe0. reflexivity.
    - apply IHe1.
Qed.

Theorem idsubst_up : up_subst idsubst = idsubst.
Proof.
  extensionality x. unfold up_subst. destruct x; auto.
Qed.

Corollary idsubst_upn n : upn n idsubst = idsubst.
Proof.
  induction n; auto.
  simpl. rewrite IHn, idsubst_up. auto.
Qed.

Theorem idsubst_is_id : forall e, e.[idsubst] = e.
Proof.
  einduction e using Expression_ind2
  ;intros.
  (* Expressions *)
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite idsubst_upn. rewrite idsubst_up. rewrite IHe0. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite IHe0. rewrite map_id. reflexivity.
    - apply IHe1.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite IHe0. rewrite map_id. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite idsubst_upn. rewrite IHe0_2. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite idsubst_upn. rewrite map_id. rewrite IHe1. reflexivity.
    - apply IHe0.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite idsubst_upn. rewrite IHe0_2.
    rewrite idsubst_upn. rewrite IHe0_3. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite idsubst_upn. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite idsubst_upn. rewrite idsubst_up. rewrite IHe0. reflexivity.
    - apply IHe1.
Qed.

Theorem idsubst_is_id_forVal :
  forall e, e.[idsubst]ᵥ = e.
Proof.
  einduction e using Value_ind2
  ;
  intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * pose proof idsubst_is_id as H.
    simpl. rewrite idsubst_upn. rewrite idsubst_up. rewrite H. reflexivity.
  * simpl. rewrite IHv2. rewrite IHv1. reflexivity.
  * simpl. erewrite map_ext_Forall with (g := id).
    - simpl. rewrite map_id. reflexivity.
    - apply IHv.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHv.
  * simpl. erewrite map_ext_Forall with (g := id).
    - rewrite map_id. reflexivity.
    - apply IHv.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv. reflexivity.
    - apply IHv0.
  * constructor.
  * constructor.
    - rewrite IHv1. rewrite IHv2. reflexivity.
    - apply IHv3.
Qed.

Lemma up_get_inl ξ x y:
  ξ x = inl y -> up_subst ξ (S x) = inl (renameValues (fun n => S n) y).
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

Lemma subst_ren :
  forall e (σ : Renaming) (ξ : Substitution), e.[ren σ].[ξ] = e.[σ >>> ξ].
Proof.
  einduction e using Expression_ind2 with
  (Q := fun l => forall σ ξ, Forall (fun x : Expression => x.[ren σ].[ξ] = x.[σ >>> ξ]) l)
  (R := fun l => forall σ ξ, Forall
  (fun x : Expression * Expression =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ren σ], y.[ren σ]) in (x0.[ξ], y.[ξ])) =
   (let '(x0, y) := x in (x0.[σ >>> ξ], y.[σ >>> ξ]))) l)
  (W := fun l => forall σ ξ, Forall
  (fun x : list Pattern * Expression * Expression =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, x0.[upn (patternListScope p) (ren σ)],
      y.[upn (patternListScope p) (ren σ)]) in
     (p, x0.[upn (patternListScope p) ξ], y.[upn (patternListScope p) ξ])) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (patternListScope p) (σ >>> ξ)],
     y.[upn (patternListScope p) (σ >>> ξ)]))) l)
  (Z := fun l => forall σ ξ, Forall
  (fun x : nat * Expression =>
   (let
    '(n, x0) := let '(n, x0) := x in (n, x0.[up_subst (upn n (ren σ))]) in
     (n, x0.[up_subst (upn n ξ)])) =
   (let '(n, x0) := x in (n, x0.[up_subst (upn n (σ >>> ξ))]))) l)
  ;intros.
  (* Expressions *)
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[σ >>> ξ])).
    - reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite <- renn_up. rewrite <- ren_up. rewrite <- uprenn_subst_upn. 
    rewrite <- upren_subst_up. rewrite IHe0. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[σ >>> ξ])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[σ >>> ξ])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[σ >>> ξ])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[σ >>> ξ])).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (patternListScope p) (σ >>> ξ)],
      y.[upn (patternListScope p) (σ >>> ξ)]))).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite <- renn_up. rewrite <- uprenn_subst_upn.
    rewrite IHe0_2. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[up_subst (upn n (σ >>> ξ))]))).
    - rewrite <- renn_up. rewrite IHe1. rewrite <- uprenn_subst_upn.
      rewrite map_length. reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[σ >>> ξ], y.[σ >>> ξ]))).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite IHe0_2.
    rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite IHe0_3. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite <- renn_up. rewrite <- uprenn_subst_upn. rewrite <- upren_subst_up.
      rewrite <- ren_up. rewrite IHe0. reflexivity.
    - apply IHe1.
Qed.

(*For Valuer Begin*)

Theorem subst_ren_forVal :
  forall e (σ : Renaming) (ξ : Substitution), e.[ren σ]ᵥ.[ξ]ᵥ = e.[σ >>> ξ]ᵥ.
Proof.
  einduction e using Value_ind2 with
  (Q := fun l => forall σ ξ, Forall (fun x : Value => x.[ren σ]ᵥ.[ξ]ᵥ = x.[σ >>> ξ]ᵥ) l)
  (R := fun l => forall σ ξ, Forall
  (fun x : Value * Value =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ren σ]ᵥ, y.[ren σ]ᵥ) in
     (x0.[ξ]ᵥ, y.[ξ]ᵥ)) = (let '(x0, y) := x in (x0.[σ >>> ξ]ᵥ, y.[σ >>> ξ]ᵥ))) l)
  ;
  intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * pose proof subst_ren as H.
    simpl. rewrite <- renn_up. rewrite <- ren_up. rewrite <- uprenn_subst_upn. 
    rewrite <- upren_subst_up. rewrite H. reflexivity.
  * simpl. rewrite IHv2. rewrite IHv1. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => x.[σ >>> ξ]ᵥ)).
    - simpl. reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[σ >>> ξ]ᵥ, y.[σ >>> ξ]ᵥ))).
    - reflexivity.
    - apply IHv.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Value => x.[σ >>> ξ]ᵥ)).
    - reflexivity.
    - apply IHv.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv. reflexivity.
    - apply IHv0.
  * constructor.
  * constructor.
    - rewrite IHv1. rewrite IHv2. reflexivity.
    - apply IHv3.
Qed.
(*For Values End*)

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

Theorem rename_up : forall e n σ ρ,
  rename (uprenn n σ) (rename (uprenn n ρ) e) = rename (uprenn n (ρ >>> σ)) e.
Proof.
  einduction e using Expression_ind2 with
  (Q := fun l => forall n σ ρ, Forall
  (fun x : Expression =>
   rename (uprenn n σ) (rename (uprenn n ρ) x) = rename (uprenn n (ρ >>> σ)) x) l)
  (R := fun l => forall n σ ρ, Forall
  (fun x : Expression * Expression =>
   (let
    '(x0, y) :=
     let '(x0, y) := x in (rename (uprenn n ρ) x0, rename (uprenn n ρ) y) in
     (rename (uprenn n σ) x0, rename (uprenn n σ) y)) =
   (let
    '(x0, y) := x in
     (rename (uprenn n (ρ >>> σ)) x0, rename (uprenn n (ρ >>> σ)) y))) l)
  (W := fun l => forall n σ ρ, Forall
  (fun x : list Pattern * Expression * Expression =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, rename (uprenn (patternListScope p) (uprenn n ρ)) x0,
      rename (uprenn (patternListScope p) (uprenn n ρ)) y) in
     (p, rename (uprenn (patternListScope p) (uprenn n σ)) x0,
     rename (uprenn (patternListScope p) (uprenn n σ)) y)) =
   (let
    '(p, x0, y) := x in
     (p, rename (uprenn (patternListScope p) (uprenn n (ρ >>> σ))) x0,
     rename (uprenn (patternListScope p) (uprenn n (ρ >>> σ))) y))) l)
  (Z := fun l => forall n σ ρ, Forall
  (fun x : nat * Expression =>
   (let
    '(n0, x0) :=
     let '(n0, x0) := x in (n0, rename (upren (uprenn n0 (uprenn n ρ))) x0) in
     (n0, rename (upren (uprenn n0 (uprenn n σ))) x0)) =
   (let '(n0, x0) := x in (n0, rename (upren (uprenn n0 (uprenn n (ρ >>> σ)))) x0)))
  l)
  ;intros.
  (* Expressions *)
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite <- uprenn_comp. reflexivity.
  * simpl. repeat fold_upn. rewrite <- uprenn_comp. rewrite <- uprenn_comp.
    rewrite IHe0. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite <- uprenn_comp. rewrite IHe0_1. rewrite <- uprenn_comp. rewrite IHe0_2. 
  rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (uprenn n (ρ >>> σ)) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (uprenn n (ρ >>> σ)) x)).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, rename (uprenn (patternListScope p) (uprenn n (ρ >>> σ))) x,
      rename (uprenn (patternListScope p) (uprenn n (ρ >>> σ))) y))).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(n0, x) => (n0, rename (upren (uprenn n0 (uprenn n (ρ >>> σ)))) x))).
    - rewrite map_length. rewrite IHe1. rewrite <- uprenn_comp. reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := fun '(x, y) =>
      (rename (uprenn n (ρ >>> σ)) x, rename (uprenn n (ρ >>> σ)) y)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite IHe0_3. rewrite <- uprenn_comp. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - repeat fold_upn. do 2 rewrite <- uprenn_comp. rewrite uprenn_comp. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - repeat fold_upn. do 2 rewrite <- uprenn_comp. rewrite uprenn_comp. rewrite IHe0. reflexivity.
    - apply IHe1.
Qed.


Theorem rename_comp :
  forall e σ ρ, rename σ (rename ρ e) = rename (ρ >>> σ) e.
Proof.
  einduction e using Expression_ind2 with
  (Q := fun l => forall σ ρ, Forall (fun x : Expression => rename σ (rename ρ x) = rename (ρ >>> σ) x) l)
  (R := fun l => forall σ ρ, Forall
  (fun x : Expression * Expression =>
   (let
    '(x0, y) := let '(x0, y) := x in (rename ρ x0, rename ρ y) in
     (rename σ x0, rename σ y)) =
   (let '(x0, y) := x in (rename (ρ >>> σ) x0, rename (ρ >>> σ) y))) l)
  (W := fun l => forall σ ρ, Forall
  (fun x : list Pattern * Expression * Expression =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, rename (uprenn (patternListScope p) ρ) x0,
      rename (uprenn (patternListScope p) ρ) y) in
     (p, rename (uprenn (patternListScope p) σ) x0,
     rename (uprenn (patternListScope p) σ) y)) =
   (let
    '(p, x0, y) := x in
     (p, rename (uprenn (patternListScope p) (ρ >>> σ)) x0,
     rename (uprenn (patternListScope p) (ρ >>> σ)) y))) l)
  (Z := fun l => forall σ ρ, Forall
  (fun x : nat * Expression =>
   (let
    '(n, x0) := let '(n, x0) := x in (n, rename (upren (uprenn n ρ)) x0) in
     (n, rename (upren (uprenn n σ)) x0)) =
   (let '(n, x0) := x in (n, rename (upren (uprenn n (ρ >>> σ))) x0))) l)
  ;intros.
  (* Expressions *)
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. auto.
  * simpl. auto.
  * simpl. do 3 fold_upn. rewrite <- uprenn_comp. rewrite IHe0. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (ρ >>> σ) x)).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => rename (ρ >>> σ) x)).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, rename (uprenn (patternListScope p) (ρ >>> σ)) x,
      rename (uprenn (patternListScope p) (ρ >>> σ)) y))).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite <- uprenn_comp. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(n, x) => (n, rename (upren (uprenn n (ρ >>> σ))) x))).
    - rewrite map_length. rewrite IHe1. rewrite <- uprenn_comp. reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(x, y) => (rename (ρ >>> σ) x, rename (ρ >>> σ) y))).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite IHe0_3. do 2 rewrite <- uprenn_comp. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. rewrite <- uprenn_comp. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite IHe0. rewrite <- uprenn_comp. do 2 fold_upn. rewrite <- upren_comp. reflexivity.
    - apply IHe1.
Qed.

(*For Valuer Begin*)
Theorem rename_comp_forVal :
  forall e σ ρ, renameValues σ (renameValues ρ e) = renameValues (ρ >>> σ) e.
Proof.
  einduction e using Value_ind2 with
  (Q := fun l => forall σ ρ, Forall
  (fun x : Value => renameValues σ (renameValues ρ x) = renameValues (ρ >>> σ) x) l)
  (R := fun l => forall σ ρ, Forall
  (fun x : Value * Value =>
   (let
    '(x0, y) := let '(x0, y) := x in (renameValues ρ x0, renameValues ρ y) in
     (renameValues σ x0, renameValues σ y)) =
   (let '(x0, y) := x in (renameValues (ρ >>> σ) x0, renameValues (ρ >>> σ) y))) l)
  ;intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * pose proof rename_comp as H.
    simpl. do 3 fold_upn. rewrite <- uprenn_comp. rewrite H. reflexivity.
  * simpl. rewrite IHv2. rewrite IHv1. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => renameValues (ρ >>> σ) x)).
    - reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (renameValues (ρ >>> σ) x, renameValues (ρ >>> σ) y))).
    - reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => renameValues (ρ >>> σ) x)).
    - reflexivity.
    - apply IHv.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv. reflexivity.
    - apply IHv0.
  * constructor.
  * constructor.
    - rewrite IHv1. rewrite IHv2. reflexivity.
    - apply IHv3.
Qed.
(*For Values End*)

Lemma subst_up_upren : forall σ ξ,
  up_subst ξ >> ren (upren σ) = up_subst (ξ >> ren σ).
Proof.
  intros. extensionality x. unfold upren, up_subst, ">>", shift.
  destruct x; auto. destruct (ξ x) eqn:P; auto.
  pose proof renaming_is_subst_forVal as H.
  rewrite <- H. rewrite <- H. f_equiv.
  replace (fun n : nat => match n with
                       | 0 => 0
                       | S n' => S (σ n')
                       end) with (upren σ) by auto.
  rewrite rename_comp_forVal, rename_comp_forVal. f_equiv.
Qed.

Lemma subst_upn_uprenn : forall n σ ξ,
  upn n ξ >> ren (uprenn n σ) = upn n (ξ >> ren σ).
Proof.
  induction n; intros; auto. simpl.
  rewrite subst_up_upren, IHn. auto.
Qed.

Lemma subst_in_val_or_exp :
  forall v σ, (valueToExpression v).[fun x : nat => inr (σ x)] =
  valueToExpression v.[fun x : nat => inr (σ x)]ᵥ.
Proof.
  einduction v using Value_ind2 with
  (Q := fun l => forall σ, Forall
  (fun x : Value =>
   (valueToExpression x).[fun x0 : nat => inr (σ x0)] =
   valueToExpression x.[fun x0 : nat => inr (σ x0)]ᵥ) l)
  (R := fun l => forall σ, Forall
  (fun x : Value * Value =>
   (let
    '(x0, y) := let '(x0, y) := x in (valueToExpression x0, valueToExpression y)
     in (x0.[fun x1 : nat => inr (σ x1)], y.[fun x1 : nat => inr (σ x1)])) =
   (let
    '(x0, y) :=
     let
     '(x0, y) := x in
      (x0.[fun x1 : nat => inr (σ x1)]ᵥ, y.[fun x1 : nat => inr (σ x1)]ᵥ) in
     (valueToExpression x0, valueToExpression y))) l)
  ;intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. rewrite IHv0_2. rewrite IHv0_1. reflexivity.
  * simpl. rewrite map_map. rewrite map_map.
    erewrite map_ext_Forall with (g := fun x : Value => valueToExpression x.[fun x0 : nat => inr (σ x0)]ᵥ).
    - reflexivity.
    - apply IHv0.
  * simpl. rewrite map_map. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value * Value =>
      let
      '(x0, y) :=
       let
       '(x0, y) := x in
        (x0.[fun x1 : nat => inr (σ x1)]ᵥ, y.[fun x1 : nat => inr (σ x1)]ᵥ) in
       (valueToExpression x0, valueToExpression y))).
    - reflexivity.
    - apply IHv0.
  * simpl. rewrite map_map. rewrite map_map.
  erewrite map_ext_Forall with (g := fun x : Value => valueToExpression x.[fun x0 : nat => inr (σ x0)]ᵥ).
    - reflexivity.
    - apply IHv0.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv0. reflexivity.
    - apply IHv1.
  * constructor.
  * constructor.
    - rewrite IHv0_1. rewrite IHv0_2. reflexivity.
    - apply IHv0_3.
Qed.

Lemma ren_subst :
  forall e ξ σ, e.[ξ].[ren σ] = e.[ξ >> ren σ].
Proof.
  einduction e using Expression_ind2 with
  (Q := fun l => forall ξ σ, Forall (fun x : Expression => x.[ξ].[ren σ] = x.[ξ >> ren σ]) l)
  (R := fun l => forall ξ σ, Forall
  (fun x : Expression * Expression =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ], y.[ξ]) in (x0.[ren σ], y.[ren σ])) =
   (let '(x0, y) := x in (x0.[ξ >> ren σ], y.[ξ >> ren σ]))) l)
  (W := fun l => forall ξ σ, Forall
  (fun x : list Pattern * Expression * Expression =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, x0.[upn (patternListScope p) ξ], y.[upn (patternListScope p) ξ]) in
     (p, x0.[upn (patternListScope p) (ren σ)],
     y.[upn (patternListScope p) (ren σ)])) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (patternListScope p) (ξ >> ren σ)],
     y.[upn (patternListScope p) (ξ >> ren σ)]))) l)
  (Z  := fun l => forall ξ σ, Forall
  (fun x : nat * Expression =>
   (let
    '(n, x0) := let '(n, x0) := x in (n, x0.[up_subst (upn n ξ)]) in
     (n, x0.[up_subst (upn n (ren σ))])) =
   (let '(n, x0) := x in (n, x0.[up_subst (upn n (ξ >> ren σ))]))) l)
  ;intros.
  (* Expressions *)
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> ren σ])).
    - reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. unfold ">>", ren. destruct (ξ v) eqn:P; auto. rewrite subst_in_val_or_exp. reflexivity.
  * simpl. unfold ">>", ren. destruct (ξ f) eqn:P; auto. rewrite subst_in_val_or_exp. reflexivity.
  * simpl. do 3 fold_upn. rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite IHe0. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> ren σ])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> ren σ])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> ren σ])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> ren σ])).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(p, x, y) =>
      (p, x.[upn (patternListScope p) (ξ >> ren σ)],
      y.[upn (patternListScope p) (ξ >> ren σ)]))).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite <- renn_up. rewrite <- subst_upn_uprenn.
    rewrite IHe0_2. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[up_subst (upn n (ξ >> ren σ))]))).
    - rewrite map_length. rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite IHe1. reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> ren σ], y.[ξ >> ren σ]))).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. do 2 rewrite <- renn_up. do 2 rewrite <- subst_upn_uprenn.
    rewrite IHe0_2. rewrite IHe0_3. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite <- renn_up. rewrite <- subst_upn_uprenn.  rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite <- renn_up. rewrite <- subst_upn_uprenn. rewrite <- ren_up. do 2 fold_upn.
      rewrite IHe0. rewrite <- subst_up_upren. reflexivity.
    - apply IHe1.
Qed.

(*For Valuer Begin*)

Theorem ren_subst_forVal :
  forall e ξ σ, e.[ξ]ᵥ.[ren σ]ᵥ = e.[ξ >> ren σ]ᵥ.
Proof.
  einduction e using Value_ind2 with
  (Q := fun l => forall ξ σ, Forall (fun x : Value => x.[ξ]ᵥ.[ren σ]ᵥ = x.[ξ >> ren σ]ᵥ) l)
  (R := fun l => forall ξ σ, Forall
  (fun x : Value * Value =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ) in
     (x0.[ren σ]ᵥ, y.[ren σ]ᵥ)) =
   (let '(x0, y) := x in (x0.[ξ >> ren σ]ᵥ, y.[ξ >> ren σ]ᵥ))) l)
  ;intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. do 3 fold_upn. rewrite <- renn_up. rewrite <- subst_upn_uprenn.
    rewrite ren_subst. reflexivity.
  * simpl. rewrite IHv2. rewrite IHv1. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Value => x.[ξ >> ren σ]ᵥ)).
    - reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> ren σ]ᵥ, y.[ξ >> ren σ]ᵥ))).
    - reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => x.[ξ >> ren σ]ᵥ)).
    - reflexivity.
    - apply IHv.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv. reflexivity.
    - apply IHv0.
  * constructor.
  * constructor.
    - rewrite IHv1. rewrite IHv2. reflexivity.
    - apply IHv3.
Qed.
(*For Values End*)

Lemma up_comp ξ η :
  up_subst ξ >> up_subst η = up_subst (ξ >> η).
Proof.
  extensionality x.
  unfold ">>". cbn. unfold up_subst, shift. destruct x; auto.
  destruct (ξ x) eqn:P; auto.
  do 2 rewrite renaming_is_subst_forVal. rewrite ren_subst_forVal, subst_ren_forVal.
  unfold ren. f_equiv. f_equiv. extensionality n.
  unfold ">>>", ">>", up_subst, shift. destruct (η n) eqn:P0; auto.
  rewrite renaming_is_subst_forVal. auto.
Qed.

Corollary upn_comp : forall n ξ η,
  upn n ξ >> upn n η = upn n (ξ >> η).
Proof.
  induction n; intros; auto. simpl. rewrite <- IHn, up_comp. auto.
Qed.

Lemma subst_in_val_or_exp_2 :
  forall v η, (valueToExpression v).[η] = valueToExpression v.[η]ᵥ.
Proof.
  einduction v using Value_ind2 with
  (Q := fun l => forall η, Forall (fun x : Value => (valueToExpression x).[η] = valueToExpression x.[η]ᵥ) l)
  (R := fun l => forall η, Forall
  (fun x : Value * Value =>
   (let
    '(x0, y) := let '(x0, y) := x in (valueToExpression x0, valueToExpression y)
     in (x0.[η], y.[η])) =
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[η]ᵥ, y.[η]ᵥ) in
     (valueToExpression x0, valueToExpression y))) l)
  ;intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. unfold ">>", ren. destruct (η n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct (η n) eqn:P; auto.
  * simpl. reflexivity.
  * simpl. rewrite IHv0_2. rewrite IHv0_1. reflexivity.
  * simpl. rewrite map_map. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => valueToExpression x.[η]ᵥ)).
    - simpl. reflexivity.
    - apply IHv0.
  * simpl. rewrite map_map. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value * Value => let
      '(x0, y) := let '(x0, y) := x in (x0.[η]ᵥ, y.[η]ᵥ) in
       (valueToExpression x0, valueToExpression y))).
    - reflexivity.
    - apply IHv0.
  * simpl. rewrite map_map. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => valueToExpression x.[η]ᵥ)).
    - reflexivity.
    - apply IHv0.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv0. reflexivity.
    - apply IHv1.
  * constructor.
  * constructor.
    - rewrite IHv0_1. rewrite IHv0_2. reflexivity.
    - apply IHv0_3.
Qed.

Lemma subst_comp :
  forall e ξ η, e.[ξ].[η] = e.[ξ >> η].
Proof.
  einduction e using Expression_ind2 with
  (Q  := fun l => forall ξ η, Forall (fun x : Expression => x.[ξ].[η] = x.[ξ >> η]) l)
  (R  := fun l => forall ξ η, Forall (fun x : Expression * Expression =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ], y.[ξ]) in (x0.[η], y.[η])) =
   (let '(x0, y) := x in (x0.[ξ >> η], y.[ξ >> η]))) l)
   (W  := fun l => forall ξ η, Forall (fun x : list Pattern * Expression * Expression =>
   (let
    '(p, x0, y) :=
     let
     '(p, x0, y) := x in
      (p, x0.[upn (patternListScope p) ξ],
      y.[upn (patternListScope p) ξ]) in
     (p, x0.[upn (patternListScope p) η],
     y.[upn (patternListScope p) η])) =
   (let
    '(p, x0, y) := x in
     (p, x0.[upn (patternListScope p) (ξ >> η)],
     y.[upn (patternListScope p) (ξ >> η)]))) l)
  (Z  := fun l => forall ξ η, Forall (fun x : nat * Expression =>
   (let
    '(n, x0) := let '(n, x0) := x in (n, x0.[up_subst (upn n ξ)]) in
     (n, x0.[up_subst (upn n η)])) =
   (let '(n, x0) := x in (n, x0.[up_subst (upn n (ξ >> η))]))) l)
  ;intros.
  (* Expressions *)
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> η])).
    - reflexivity.
    - apply IHe0.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. unfold ">>", ren. destruct (ξ v) eqn:P; auto. rewrite subst_in_val_or_exp_2. reflexivity.
  * simpl. unfold ">>", ren. destruct (ξ f) eqn:P; auto. rewrite subst_in_val_or_exp_2. reflexivity.
  * simpl. do 3 fold_upn. rewrite IHe0. rewrite upn_comp. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> η])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> η])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> η])).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Expression => x.[ξ >> η])).
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite map_map. erewrite map_ext_Forall.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite upn_comp. reflexivity.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. reflexivity.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(n, x) => (n, x.[up_subst (upn n (ξ >> η))]))).
    - rewrite IHe1. rewrite map_length. rewrite upn_comp. reflexivity.
    - apply IHe0.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> η], y.[ξ >> η]))).
    - reflexivity.
    - apply IHe0.
  * simpl. rewrite IHe0_1. rewrite IHe0_2. rewrite IHe0_3.
    rewrite upn_comp. rewrite upn_comp. reflexivity.
  (* Lists *)
  * constructor.
  * constructor.
  * constructor.
  * constructor.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0. reflexivity.
    - apply IHe1.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. reflexivity.
    - apply IHe0_3.
  * constructor.
    - rewrite IHe0_1. rewrite IHe0_2. rewrite upn_comp. reflexivity.
    - apply IHe0_3.
  * constructor.
    - do 3 fold_upn. rewrite IHe0. rewrite upn_comp. reflexivity.
    - apply IHe1.
Qed.

Lemma subst_comp_forVal :
  forall e ξ η, e.[ξ]ᵥ.[η]ᵥ = e.[ξ >> η]ᵥ.
Proof.
  einduction e using Value_ind2 with
  (Q := fun l => forall ξ η, Forall (fun x : Value => x.[ξ]ᵥ.[η]ᵥ = x.[ξ >> η]ᵥ) l)
  (R := fun l => forall ξ η, Forall (fun x : Value * Value =>
   (let
    '(x0, y) := let '(x0, y) := x in (x0.[ξ]ᵥ, y.[ξ]ᵥ) in
     (x0.[η]ᵥ, y.[η]ᵥ)) =
   (let '(x0, y) := x in (x0.[ξ >> η]ᵥ, y.[ξ >> η]ᵥ))) l)
  ;
  intros.
  (* Expressions *)
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * simpl. unfold ">>", ren. destruct (ξ n) eqn:P; auto.
  * pose proof subst_comp as H.
    simpl. do 3 fold_upn. rewrite H. rewrite upn_comp. reflexivity.
  * simpl. rewrite IHv2. rewrite IHv1. reflexivity.
  * simpl. rewrite map_map. erewrite map_ext_Forall with (g := (fun x : Value => x.[ξ >> η]ᵥ)).
    - simpl. reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun '(x, y) => (x.[ξ >> η]ᵥ, y.[ξ >> η]ᵥ))).
    - reflexivity.
    - apply IHv.
  * simpl. rewrite map_map.
    erewrite map_ext_Forall with (g := (fun x : Value => x.[ξ >> η]ᵥ)).
    - reflexivity.
    - apply IHv.
  (* Lists *)
  * constructor.
  * constructor.
    - rewrite IHv. reflexivity.
    - apply IHv0.
  * constructor.
  * constructor.
    - rewrite IHv1. rewrite IHv2. reflexivity.
    - apply IHv3.
Qed.

Theorem rename_subst_core : forall e v,
  (rename (fun n : nat => S n) e).[v .:: idsubst] = e.
Proof.
  intros.
  rewrite renaming_is_subst, subst_comp. cbn.
  unfold substcomp, ren. cbn. rewrite idsubst_is_id. reflexivity.
Qed.

Theorem rename_subst_core_forVal : forall e v,
  (renameValues (fun n : nat => S n) e).[v .:: idsubst]ᵥ = e.
Proof.
  intros.
  rewrite renaming_is_subst_forVal, subst_comp_forVal. cbn.
  unfold substcomp, ren. cbn. rewrite idsubst_is_id_forVal. reflexivity.
Qed.

Theorem rename_subst : forall e v,
  (rename (fun n : nat => S n) e).[v/] = e.
Proof.
  intros. apply rename_subst_core.
Qed.


Lemma scons_substcomp_core v ξ η :
  (v .:: ξ) >> η = match v with 
                   | inl exp => inl (exp.[η]ᵥ)
                   | inr n => η n
                   end .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp. now destruct x.
Qed.

Lemma scons_substcomp v ξ η :
  (v .: ξ) >> η = v.[η]ᵥ .: (ξ >> η).
Proof.
  apply scons_substcomp_core.
Qed.

Lemma scons_substcomp_list ξ η vals :
  (list_subst vals ξ) >> η = list_subst (map (substForValue η) vals) (ξ >> η).
Proof.
  induction vals; simpl. auto.
  rewrite scons_substcomp, IHvals. auto.
Qed.

Lemma substcomp_scons_core v ξ η :
  up_subst ξ >> v .:: η = v .:: (ξ >> η).
Proof.
  extensionality x. unfold scons, substcomp, up_subst. destruct x; auto.
  unfold shift. destruct (ξ x) eqn:P; auto.
  rewrite renaming_is_subst_forVal. rewrite subst_comp_forVal. f_equiv.
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

(*-- from Basic --*)
Ltac break_match_hyp :=
match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end.

Ltac break_match_goal :=
match goal with
| [ |- context [ match ?X with _=>_ end ] ] => 
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
end.
(*-- from Basic end--*)


Theorem subst_extend_core : forall ξ v,
  (up_subst ξ) >> (v .:: idsubst) = v .:: ξ.
Proof.
  intros. unfold substcomp. extensionality x. destruct x; auto.
  cbn. break_match_goal.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. rewrite rename_subst_core_forVal. auto.
  * unfold shift in Heqs. break_match_hyp; inversion Heqs. cbn. reflexivity.
Qed.

Theorem subst_extend : forall ξ v,
  (up_subst ξ) >> (v .: idsubst) = v .: ξ.
Proof.
  intros. apply subst_extend_core.
Qed.

(*-- from Basic --*)
Lemma element_exist {A : Type} : forall n (l : list A), S n = Datatypes.length l -> exists e l', l = e::l'.
Proof.
  intros. destruct l.
  * inversion H.
  * apply ex_intro with a. apply ex_intro with l. reflexivity.
Qed.
(*-- from Basic end --*)

Corollary subst_list_extend : forall n ξ vals, length vals = n ->
  (upn n ξ) >> (list_subst vals idsubst) = list_subst vals ξ.
Proof.
  induction n; intros.
  * apply length_zero_iff_nil in H. subst. cbn. unfold substcomp. extensionality x.
    break_match_goal; try rewrite idsubst_is_id_forVal; try reflexivity.
  * simpl. apply eq_sym in H as H'. apply element_exist in H'. destruct H', H0. subst.
    simpl. rewrite substcomp_scons. rewrite IHn; auto.
Qed.

Theorem list_subst_lt : forall n vals ξ, n < length vals ->
  list_subst vals ξ n = inl (nth n vals (VLit (Integer 0))).
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
  list_subst vals ξ n = inl (nth n vals (VLit (Integer 0))) /\ n < length vals
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
  break_match_goal; auto. rewrite idsubst_is_id_forVal. auto.
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
  now rewrite <- renaming_is_subst_forVal.
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
  rewrite subst_comp_forVal. reflexivity.
Qed.
