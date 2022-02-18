From Coq Require ZArith.BinInt.
From Coq Require Strings.String.

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

Definition composition {A B C} (f : A -> B) (g : B -> C) : A -> C := fun x => g (f x).
Notation "f >>> g" := (composition f g)
  (at level 56, left associativity).

Definition list_subst (l : list Value) (ξ : Substitution) : Substitution :=
  fold_right (fun v acc => v .: acc) ξ l.


Definition substcomp (ξ η : Substitution) : Substitution :=
  fun x => (* composition (substi ξ) η*)
    match ξ x with
    | inl exp => inl (subst η exp)
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
