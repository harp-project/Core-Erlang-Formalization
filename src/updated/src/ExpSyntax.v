From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Export FunctionalExtensionality PropExtensionality.

(*Require Import Utf8.*)

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.
Require Export Coq.Structures.OrderedType.
Require Export Coq.micromega.Lia
               Coq.Lists.List
               Coq.Arith.PeanoNat.

Require Export Basics.

Import ListNotations.


Inductive Literal : Set :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Set :=
| PVar
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
| VCons   (hd tl : ValueExpression)
| VTuple  (l : list ValueExpression)
| VMap    (l : list (ValueExpression * ValueExpression))
(* | VValues (el : list ValueExpression) *)
(* VValues will need to be seperate to avoid VValues in VValues. *)
| VVar    (n : nat)
| VFunId  (n : nat)
| VClos   (ext : list (nat * nat * Expression))
(* list( (id of the fn) * (length of the parameter list of the fn) * (fn body) )*)
          (id : nat) (* Inner function identifier *)
          (vc : nat) (* Variable count *)
          (e : Expression)
(* Scoping vl + length ext *)

with NonValueExpression : Set :=
| EFun    (vl : nat) (e : Expression) (* One step reduction *)
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
| ELetRec (l : list (nat * Expression)) (e : Expression) (* One step reduction *)
| ETry    (e1 : Expression) (vl1 : nat) (e2 : Expression) (vl2 : nat) (e3 : Expression)
.

Section correct_pattern_ind.

Variables
  (P : Pattern -> Prop)(Q : list Pattern -> Prop)(R : list (Pattern * Pattern) -> Prop).

Hypotheses
 (H : P PNil)
 (H0 : forall (l : Literal), P (PLit l))
 (*(H1 : forall (s : Var), P (PVar s)) *) (* Var Pattern changed *)
 (H1 :  P PVar)
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
  | PVar => H1
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
    (VV : list (nat * nat * Expression) -> Prop) (* New *)
    (W : list ((list Pattern) * Expression * Expression) -> Prop)
    (Z : list (nat * Expression) -> Prop).

  Hypotheses
   (HV : forall (e : ValueExpression), PV e -> P (Val e))
   (HE : forall (e : NonValueExpression), PE e -> P (Exp e))
   
   (HV1 : PV VNil)
   (HV2 : forall (l : Literal), PV (VLit l))
   (HV3 : forall (hd : ValueExpression), PV hd -> forall (tl : ValueExpression), PV tl ->  PV (VCons hd tl))
   (HV4 : forall (l : list ValueExpression), QV l -> PV (VTuple l))
   (HV5 : forall (l : list (ValueExpression * ValueExpression)), RV l -> PV (VMap l))
   (*(HV6 : forall (el : list ValueExpression), QV el -> PV (VValues el))*)
   (HV7 : forall (n : nat), PV(VVar n))
   (HV8 : forall (n : nat), PV(VFunId n))
   (HV9 : forall (id : nat) (vl : nat) (ext : list (nat * nat * Expression)), VV ext -> forall (e : Expression), P e -> PV(VClos ext id vl e))
   
   (HE1 : forall (n : nat) (e : Expression), P e -> PE (EFun n e))
   (HE2 : forall (el : list Expression), Q el -> PE (EValues el))
   (HE3 : forall (hd : Expression), P hd -> forall (tl : Expression), P tl -> PE (ECons hd tl))
   (HE4 : forall (l : list Expression), Q l -> PE (ETuple l))
   (HE5 : forall (l : list (Expression * Expression)), R l -> PE (EMap l))
   (HE6 : forall (f : string) (l : list Expression), Q l -> PE (ECall f l))
   (HE7 : forall (f : string) (l : list Expression), Q l -> PE (EPrimOp f l))
   (HE8 : forall (e: Expression), P e -> forall (l : list Expression), Q l -> PE (EApp e l))
   (HE9 : forall (e : Expression), P e -> forall (l : list ((list Pattern) * Expression * Expression)), W l -> PE (ECase e l) )
   (HE10 : forall (l : nat) (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 -> PE (ELet l e1 e2))
   (HE11: forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2 -> PE (ESeq e1 e2))
   (HE12: forall (e : Expression), P e -> forall (l : list (nat * Expression)), Z l -> PE (ELetRec l e))
   (HE13: forall (e1 : Expression), P e1 -> forall (vl1 : nat) (e2 : Expression), P e2 -> 
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
   (HVV1 : VV [])
   (HVV2 : forall (n : nat) (m : nat) (e : Expression), P e -> forall (el : list (nat * nat * Expression)), VV el -> VV ((n,m,e)::el))
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
  | EFun vl e => HE1 vl e (Expression_ind2 e)
  | EValues el => HE2 el (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) el)
  | ECons hd tl => HE3 hd (Expression_ind2 hd) tl (Expression_ind2 tl)
  | ETuple l => HE4 l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | EMap l => HE5 l (list_ind R HR1 (fun '(e1,e2) ls => HR2 e1 (Expression_ind2 e1) e2 (Expression_ind2 e2) ls) l)
  | ECall f l => HE6 f l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | EPrimOp f l => HE7 f l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | EApp exp l => HE8 exp (Expression_ind2 exp) l (list_ind Q HQ1 (fun e ls => HQ2 e (Expression_ind2 e) ls) l)
  | ECase e l => HE9 e (Expression_ind2 e) l 
  (list_ind W HW1 (fun '(lp, e1, e2) ls => (HW2 lp e1 (Expression_ind2 e1) e2 (Expression_ind2 e2) ls)) l)
  | ELet l e1 e2 => HE10 l e1 (Expression_ind2 e1) e2 (Expression_ind2 e2)
  | ESeq e1 e2 => HE11 e1 (Expression_ind2 e1) e2 (Expression_ind2 e2)
  | ELetRec l e => HE12 e (Expression_ind2 e) l (list_ind Z HZ1 (fun '(n,e) ls => HZ2 n e (Expression_ind2 e) ls) l)
  | ETry e1 vl1 e2 vl2 e3 => HE13 e1 (Expression_ind2 e1) vl1 e2 (Expression_ind2 e2) vl2 e3 (Expression_ind2 e3)
  end
  
  with ValueExpression_ind2 (ve : ValueExpression) : PV ve :=
  match ve as x return PV x with
  | VNil => HV1
  | VLit l => HV2 l
  | VCons hd tl => HV3 hd (ValueExpression_ind2 hd) tl (ValueExpression_ind2 tl)
  | VTuple l => HV4 l (list_ind QV HQV1 (fun e ls => HQV2 e (ValueExpression_ind2 e) ls) l)
  | VMap l => HV5 l (list_ind RV HRV1 (fun '(e1,e2) ls => HRV2 e1 (ValueExpression_ind2 e1) e2 (ValueExpression_ind2 e2) ls) l)
  (*| VValues el => HV6 el (list_ind QV HQV1 (fun e ls => HQV2 e (ValueExpression_ind2 e) ls) el) *)
  | VVar n => HV7 n
  | VFunId n => HV8 n
  | VClos ext id vl e => HV9 id vl ext (list_ind VV HVV1 (fun '(n,m,e) ls => HVV2 n m e (Expression_ind2 e) ls) ext) e (Expression_ind2 e)
  end
  .
  Combined Scheme Exp_ind from Expression_ind2, NonValueExpression_ind2, ValueExpression_ind2.

End correct_exp_ind.