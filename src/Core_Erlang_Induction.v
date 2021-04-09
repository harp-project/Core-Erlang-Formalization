Require Core_Erlang_Syntax.

(**
 Correct induction principles for the syntax of Core Erlang

*)

Module Induction.

Export Core_Erlang_Syntax.Syntax.
Import ListNotations.

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
  (Z : list (FunctionIdentifier * (list Var * Expression)) -> Prop).
(* SingleExpression *)
  (* (P2 : SingleExpression -> Prop)
  (Q2 : list SingleExpression -> Prop). *)

Hypotheses
  (H : forall (l : list Expression), Q l -> P (EValues l))
  (* (H0 : forall (e : SingleExpression), P2 e -> P1 (ESingle e)) *)
  (I : P ENil)
  (I0 : forall (l : Literal), P (ELit l))
  (I1 : forall (v : Var), P (EVar v))
  (I2 : forall (f : FunctionIdentifier), P (EFunId f))
  (I3 : forall (e : Expression), P e -> forall (vl : list Var), P (EFun vl e))
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
       -> forall (vl : list Var), P (ELet vl e1 e2))
  (I11 : forall (e1 : Expression), P e1 -> forall (e2 : Expression), P e2
       -> P (ESeq e1 e2))
  (I12 : forall (l : list (FunctionIdentifier * (list Var * Expression))), Z l
       -> forall (e : Expression), P e -> P (ELetRec l e))
  (I13 : forall (l : list (Expression * Expression)), R l -> P (EMap l))
  (I14 : forall (e1 : Expression), P e1 ->
         forall (e2 : Expression), P e2 ->
         forall (e3 : Expression), P e3 ->
         forall (vl1 vl2 : list Var), P (ETry e1 vl1 e2 vl2 e3))
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
        forall (l : list (FunctionIdentifier * (list Var * Expression))), Z l
     -> forall (f : FunctionIdentifier) (vl : list Var), Z ((f, (vl, e))::l)).

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
        ((fix l_ind (l':list (FunctionIdentifier * (list Var * Expression))) : Z l' :=
                       match l' as x return Z x with
                       | [] => J2
                       | (f, (vl, e))::xs => K3 e (Expression_ind2 e) xs (l_ind xs) f vl
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
  (P : Value -> Prop)(Q : list Value -> Prop) (R : list (Value * Value) -> Prop)
  (W : list ((Var + FunctionIdentifier) * Value) -> Prop).

Hypotheses
 (H : P VNil)
 (H0 : forall (l : Literal), P (VLit l))
 (H1 : forall (hd : Value), P hd -> forall (tl : Value), P tl -> P (VCons hd tl))
 (H2 : forall ref, W ref -> forall ext id params body, P (VClos ref ext id params body))
 (H3 : forall (l:list Value), Q l -> P (VTuple l))
 (H4 : forall (l:list (Value * Value)), R l -> P (VMap l))
 (H' : forall v : Value, P v -> forall l:list Value, Q l -> Q (v :: l))
 (H0' : forall (v1 v2 : Value), P v1 -> P v2 -> forall l:list (Value * Value), R l -> R ((v1, v2) :: l))
 (H1' : Q [])
 (H2' : R [])
 (H3' : W [])
 (H4' : forall (v: Value), P v -> 
        forall (l : list ((Var + FunctionIdentifier) * Value)), W l ->
        forall (id : Var + FunctionIdentifier),W ((id, v)::l)).


Fixpoint Value_ind2 (v : Value) : P v :=
  match v as x return P x with
  | VNil => H
  | VLit l => H0 l
  | VCons hd tl => H1 hd (Value_ind2 hd) tl (Value_ind2 tl)
  | VClos ref ext id params body => H2 ref
  ((fix l_ind (l':list ((Var + FunctionIdentifier) * Value)) : W l' :=
                       match l' as x return W x with
                       | [] => H3'
                       | (id, v)::xs => H4' v (Value_ind2 v) xs (l_ind xs) id
                       end) ref)
   ext id params body
  | VTuple l => H3 l ((fix l_ind (l':list Value) : Q l' :=
                       match l' as x return Q x with
                       | [] => H1'
                       | v::xs => H' v (Value_ind2 v) xs (l_ind xs)
                       end) l)
  | VMap l => H4 l ((fix l_ind (l' : list (Value * Value)) : R l' :=
                      match l' as x return R x with
                      | [] => H2'
                      | (v1, v2)::xs => H0' v1 v2 (Value_ind2 v1) (Value_ind2 v2) xs (l_ind xs)
                      end) l)
  end.

End correct_value_ind.


End Induction.