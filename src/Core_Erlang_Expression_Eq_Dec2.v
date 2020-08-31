From Coq Require ZArith.BinInt.
From Coq Require Strings.String.
From Coq Require Structures.OrderedTypeEx.

Module Syntax.

Export ZArith.BinInt.
Export Strings.String.
Export Lists.List.

Import ListNotations.

Require Omega.
From Coq Require Classes.EquivDec.

Module Equalities.


Import ListNotations.
Export Arith.PeanoNat.
Import Classes.EquivDec.
Export Omega.

Definition Var : Type := string.

Inductive Literal : Type :=
| Atom (s: string)
| Integer (x : Z)
(* | Float (q : R) *).


Inductive Pattern : Type :=
| PVar     (v : Var)
| PLit (l : Literal)
| PCons  (hd tl : Pattern)
| PTuple (l : list Pattern)
| PMap (l : list (Pattern * Pattern))
| PNil.

Definition FunctionIdentifier : Type := string * nat.


Inductive Expression : Type :=
| EValues (el : list SingleExpression)
| ESingle (e : SingleExpression)
with SingleExpression : Type :=
| ENil
| ELit    (l : Literal)
| EVar    (v : Var)
| EFunId  (f : FunctionIdentifier)
| EFun    (vl : list Var) (e : Expression)
| ECons   (hd tl : Expression)
| ETuple  (l : list Expression)
(** Initially: for built-in functions and primitive operations : *)
| ECall   (f: string)     (l : list Expression)
(** For function applications: *)
| EApp    (exp: Expression)     (l : list Expression)
| ECase   (e : Expression) (l : list ((list Pattern) * Expression * Expression))
| ELet    (l : list Var) (e1 e2 : Expression)
(** For sequencing: do expressions (ESeq) *)
| ESeq    (e1 e2 : Expression)
| ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) (e : Expression)
| EMap    (l : list (Expression * Expression))
| ETry    (e1 : Expression) (vl1 : list Var) (e2 : Expression) (vl2 : list Var) (e3 : Expression).


Section Basic_Eq_Dec.
(** Decidable equality for product and sum types *)
Variables A B : Type.

Hypothesis A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
Hypothesis B_eq_dec : forall b1 b2 : B, {b1 = b2} + {b1 <> b2}.

Proposition prod_eq_dec : forall p1 p2 : A * B, {p1 = p2} + {p1 <> p2}.
Proof.
  set (eq1 := A_eq_dec).
  set (eq2 := B_eq_dec).
  decide equality.
Defined.

Proposition sum_eq_dec : forall p1 p2 : A + B, {p1 = p2} + {p1 <> p2}.
Proof.
  set (eq1 := A_eq_dec).
  set (eq2 := B_eq_dec).
  decide equality.
Defined.

End Basic_Eq_Dec.

  (** Decidable and boolean equality for the syntax *)

  Scheme Equality for Literal.

  Fixpoint Pattern_eq_dec (p1 p2 : Pattern) : {p1 = p2} + {p1 <> p2}.
  Proof.
    set (Pattern_list_eq_dec := list_eq_dec Pattern_eq_dec).
    set (Pattern_var_eq_dec := string_dec).
    set (Pattern_literal_eq_dec := Literal_eq_dec).
    set (list_eq_dec (prod_eqdec Pattern_eq_dec Pattern_eq_dec)).
    decide equality.
  Qed.

From Coq Require Program.Equality.
From Coq Require Classes.EquivDec.


Module Expression_Eq_Dec.


Import Program.Equality.
Import Classes.EquivDec.

Import ListNotations.

Set Implicit Arguments.

Lemma alma: forall e e0 : SingleExpression, (forall e1 e2 : Expression, {e1 = e2} + {e1 <> e2}) -> {e = e0} + {e <> e0} .
Proof.
  intros.
  set (var_eq_dec := string_dec).
  set (literal_eq_dec := Literal_eq_dec).
  set (pattern_eq_dec := Pattern_eq_dec).
  set (explist_eq_dec := list_eq_dec X ).
  set (varlist_eq_dec := list_eq_dec string_dec).  (* for function signatures: *)
  set (funsig_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec).  set (patlist_eq_dec := list_eq_dec pattern_eq_dec).
  (* for letrec *)
  set (listvarexp_eq_dec := list_eq_dec (prod_eqdec (list_eq_dec string_dec) X)).
    (* for fnames *)
  set (listfunsig_eq_dec := list_eq_dec funsig_eq_dec).
  set (listlistvar_eq_dec := list_eq_dec (list_eq_dec string_dec)).
  set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pattern_eq_dec) X) X)).
  set (list_eq_dec (prod_eqdec string_dec X)).
  set (list_eq_dec (prod_eqdec funsig_eq_dec (prod_eqdec (list_eq_dec string_dec) X))).
  set (list_eq_dec (prod_eqdec X X)).
  set (list_eq_dec (prod_eqdec X string_dec)).
  decide equality.
Qed. 

Lemma alma2: forall l l1 : list SingleExpression, (forall e e0: SingleExpression, {e = e0} + {e <> e0}) -> {l = l1} + {l <> l1}.
Proof.
  intros.
  dependent induction l; destruct l1.
  * left. reflexivity.
  * right. congruence.
  * right. congruence.
  * assert({l = l1} + {l <> l1}).
    - eapply IHl. exact X.
    - assert({a = s} + {a <> s}).
      + eapply X.
      + destruct H, H0; try(left;now subst); try(right;congruence).
Qed.

Fixpoint Expression_eq_dec_helper (e e0 : SingleExpression) : (forall e1 e2 : Expression, {e1 = e2} + {e1 <> e2}) -> {e = e0} + {e <> e0}.
Proof.
 intros.
 set (var_eq_dec := string_dec).
  set (literal_eq_dec := Literal_eq_dec).
  set (pattern_eq_dec := Pattern_eq_dec).
  set (explist_eq_dec := list_eq_dec X ).
  set (varlist_eq_dec := list_eq_dec string_dec).  (* for function signatures: *)
  set (funsig_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec).  set (patlist_eq_dec := list_eq_dec pattern_eq_dec).
  (* for letrec *)
  set (listvarexp_eq_dec := list_eq_dec (prod_eqdec (list_eq_dec string_dec) X)).
    (* for fnames *)
  set (listfunsig_eq_dec := list_eq_dec funsig_eq_dec).
  set (listlistvar_eq_dec := list_eq_dec (list_eq_dec string_dec)).
  set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pattern_eq_dec) X) X)).
  set (list_eq_dec (prod_eqdec string_dec X)).
  set (list_eq_dec (prod_eqdec funsig_eq_dec (prod_eqdec (list_eq_dec string_dec) X))).
  set (list_eq_dec (prod_eqdec X X)).
  set (list_eq_dec (prod_eqdec X string_dec)).
  decide equality.
(*   * decide equality. decide equality.
  * decide equality. *)
Qed.

(* Fixpoint Expression_eq_dec_helper *)

Fixpoint Expression_eq_dec (e1 e2 : Expression) : {e1 = e2} + {e1 <> e2}.
Proof.
(*   destruct e1, e2.
  * assert({el = el0} + {el <> el0}). { eapply alma2. intros. eapply alma. exact Expression_eq_dec. } destruct H.
    - left. now subst.
    - right. congruence.
  * right. congruence.
  * right. congruence.
  * destruct (Expression_eq_dec_helper e e0 Expression_eq_dec).
    - left. now subst.
    - right. congruence.
Defined. *)

  set (var_eq_dec := string_dec).
  set (literal_eq_dec := Literal_eq_dec).
  set (pattern_eq_dec := Pattern_eq_dec).
  set (explist_eq_dec := list_eq_dec Expression_eq_dec).
  set (varlist_eq_dec := list_eq_dec string_dec).  (* for function signatures: *)
  set (funsig_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec).  set (patlist_eq_dec := list_eq_dec pattern_eq_dec).
  (* for letrec *)
  set (listvarexp_eq_dec := list_eq_dec (prod_eqdec (list_eq_dec string_dec) Expression_eq_dec)).
    (* for fnames *)
  set (listfunsig_eq_dec := list_eq_dec funsig_eq_dec).
  set (listlistvar_eq_dec := list_eq_dec (list_eq_dec string_dec)).
  set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pattern_eq_dec) Expression_eq_dec) Expression_eq_dec)).
  set (list_eq_dec (prod_eqdec string_dec Expression_eq_dec)).
  set (list_eq_dec (prod_eqdec funsig_eq_dec (prod_eqdec (list_eq_dec string_dec) Expression_eq_dec))).
  set (list_eq_dec (prod_eqdec Expression_eq_dec Expression_eq_dec)).
  set (list_eq_dec (prod_eqdec Expression_eq_dec string_dec)).
  decide equality.
  * decide equality. decide equality.
  * decide equality.
Defined.

Section exp_rect.
  Variable P : Expression -> Type.
  Variable P0 : SingleExpression -> Type.

  Variable P_list_expr : list Expression -> Type.
  Hypothesis P_list_expr_nil : P_list_expr [].
  Hypothesis P_list_expr_cons : forall e l, P e -> P_list_expr l -> P_list_expr (e :: l).
  
  Variable P_list_pat_expr_expr : list (list Pattern * Expression * Expression) -> Type.
  Hypothesis P_list_pat_expr_expr_nil : P_list_pat_expr_expr [].
  Hypothesis P_list_pat_expr_expr_cons : forall (p : list Pattern) e1 e2 l, P e1 -> P e2 -> P_list_pat_expr_expr l -> P_list_pat_expr_expr ((p, e1, e2) :: l).
  
  Variable P_list_funid_var_expr : list (FunctionIdentifier * ((list Var) * Expression)) -> Type.
  Hypothesis P_list_funid_var_expr_nil : P_list_funid_var_expr [].
  Hypothesis P_list_funid_var_expr_cons : forall f vl e l, P e -> P_list_funid_var_expr l -> P_list_funid_var_expr ((f,(vl,e)) :: l).
  
  Variable P_list_expr_expr : list (Expression * Expression) -> Type.
  Hypothesis P_list_expr_expr_nil : P_list_expr_expr [].
  Hypothesis P_list_expr_expr_cons : forall e1 e2 l, P e1 -> P e2 -> P_list_expr_expr l -> P_list_expr_expr ((e1, e2) :: l).
  
  Variables P_list_single_expr : list SingleExpression -> Type.
  Hypothesis P_list_single_expr_nil : P_list_single_expr [].
  Hypothesis P_list_single_expr_cons : forall e l, P0  e -> P_list_single_expr l -> P_list_single_expr (e::l).
  
  Hypothesis P_empty_list : P (ESingle ENil).
  Hypothesis P_literal : forall l, P (ESingle (ELit l)).
  Hypothesis P_var : forall v, P (ESingle (EVar v)).
  Hypothesis P_funid : forall f, P (ESingle (EFunId f)).
  Hypothesis P_fun : forall vl e, P e -> P (ESingle (EFun vl e)).
  Hypothesis P_list : forall e1 e2, P e1 -> P e2 -> P (ESingle (ECons e1 e2)).
  Hypothesis P_tuple: forall l, P_list_expr l -> P (ESingle (ETuple l)).
  Hypothesis P_call : forall f l, P_list_expr l -> P (ESingle (ECall f l)).
  Hypothesis P_apply : forall exp l, P exp -> P_list_expr l -> P (ESingle (EApp exp l)).
  Hypothesis P_case : forall e l, P e -> P_list_pat_expr_expr l -> P (ESingle (ECase e l)).
  Hypothesis P_let : forall vl e1 e2, P e1 -> P e2 -> P (ESingle (ELet vl e1 e2)).
  Hypothesis P_seq : forall e1 e2, P e1 -> P e2 -> P (ESingle( ESeq e1 e2)).
  Hypothesis P_letrec : forall l e, P e -> P_list_funid_var_expr l ->  P (ESingle (ELetRec l e)).
  Hypothesis P_map : forall l, P_list_expr_expr l -> P (ESingle (EMap l)).
  Hypothesis P_try: forall e1 vl1 e2 vl2 e3, P e1 -> P e2 -> P e3 -> P (ESingle (ETry e1 vl1 e2 vl2 e3)).
  Hypothesis P_values: forall v, P_list_single_expr v -> P (EValues v).
  
  Hypothesis P0_empty_list : P0 ENil.
  Hypothesis P0_literal : forall l, P0 (ELit l).
  Hypothesis P0_var : forall v, P0 (EVar v).
  Hypothesis P0_funid : forall f, P0 (EFunId f).
  Hypothesis P0_fun : forall vl e, P e -> P0 (EFun vl e).
  Hypothesis P0_list : forall e1 e2, P e1 -> P e2 -> P0 (ECons e1 e2).
  Hypothesis P0_tuple: forall l, P_list_expr l -> P0 (ETuple l).
  Hypothesis P0_call : forall f l, P_list_expr l -> P0 (ECall f l).
  Hypothesis P0_apply : forall exp l, P exp -> P_list_expr l -> P0 (EApp exp l).
  Hypothesis P0_case : forall e l, P e -> P_list_pat_expr_expr l -> P0 (ECase e l).
  Hypothesis P0_let : forall vl e1 e2, P e1 -> P e2 -> P0 (ELet vl e1 e2).
  Hypothesis P0_seq : forall e1 e2, P e1 -> P e2 -> P0 (ESeq e1 e2).
  Hypothesis P0_letrec : forall l e, P e -> P_list_funid_var_expr l ->  P0 (ELetRec l e).
  Hypothesis P0_map : forall l, P_list_expr_expr l -> P0 (EMap l).
  Hypothesis P0_try: forall e1 vl1 e2 vl2 e3, P e1 -> P e2 -> P e3 -> P0 (ETry e1 vl1 e2 vl2 e3).
  
  Check Expression_rect.
  Check SingleExpression_rect.
  Check SingleExpression_ind.
  
  Fixpoint expr_rect_1 (e : Expression) : P e :=
        let fix go_list_tuple (l : list Expression) : P_list_expr l :=
            match l with
            | [] => P_list_expr_nil
            | e :: l => P_list_expr_cons (expr_rect_1 e) (go_list_tuple l)
            end in
        let fix go_list_case (l : list (list Pattern * Expression * Expression)) : P_list_pat_expr_expr l :=
            match l with
            | [] => P_list_pat_expr_expr_nil
            | (p,e1,e2) :: l => P_list_pat_expr_expr_cons p (expr_rect_1 e1) (expr_rect_1 e2) (go_list_case l)
            end in
        let fix go_list_letrec ( l : list (FunctionIdentifier * ((list Var) * Expression))) : P_list_funid_var_expr l :=
            match l with
            | [] => P_list_funid_var_expr_nil
            | (f,(vl,e)) :: l => P_list_funid_var_expr_cons f vl (expr_rect_1 e) (go_list_letrec l)
            end in
        let fix go_list_map (l : list (Expression * Expression)) : P_list_expr_expr l :=
            match l with
            | [] => P_list_expr_expr_nil
            | (e,e0) :: l => P_list_expr_expr_cons (expr_rect_1 e) (expr_rect_1 e0) (go_list_map l)
            end in
        let fix go_list_values (l : list SingleExpression) : P_list_single_expr l :=
            match l with
            | [] => P_list_single_expr_nil
            | e :: l => P_list_single_expr_cons (expr_rect_2 e) (go_list_values l)
            end in
        match e with
        | ESingle e0 => match e0 with
          | ENil => P_empty_list
          | ELit l => P_literal l
          | EVar v => P_var v
          | EFunId f => P_funid f
          | EFun vl e => P_fun vl (expr_rect_1 e)
          | ECons e1 e2 => P_list (expr_rect_1 e1) (expr_rect_1 e2)
          | ETuple l => P_tuple (go_list_tuple l)
          | ECall f l => P_call f (go_list_tuple l)
          | EApp exp l => P_apply (expr_rect_1 exp) (go_list_tuple l)
          | ECase e l => P_case (expr_rect_1 e) (go_list_case l)
          | ELet vl e1 e2 => P_let vl (expr_rect_1 e1) (expr_rect_1 e2)
          | ESeq e1 e2 => P_seq (expr_rect_1 e1) (expr_rect_1 e2)
          | ELetRec l e => P_letrec (expr_rect_1 e) (go_list_letrec l) 
          | EMap l => P_map (go_list_map l)
          | ETry e1 vl1 e2 vl2 e3 => P_try vl1 vl2 (expr_rect_1 e1) (expr_rect_1 e2) (expr_rect_1 e3)
          end
        | EValues v => P_values (go_list_values v)
        end
        with expr_rect_2 (e : SingleExpression) : P0 e  :=
        let fix go_list_tuple (l : list Expression) : P_list_expr l :=
            match l with
            | [] => P_list_expr_nil
            | e :: l => P_list_expr_cons (expr_rect_1 e) (go_list_tuple l)
            end in
        let fix go_list_case (l : list (list Pattern * Expression * Expression)) : P_list_pat_expr_expr l :=
            match l with
            | [] => P_list_pat_expr_expr_nil
            | (p,e1,e2) :: l => P_list_pat_expr_expr_cons p (expr_rect_1 e1) (expr_rect_1 e2) (go_list_case l)
            end in
        let fix go_list_letrec ( l : list (FunctionIdentifier * ((list Var) * Expression))) : P_list_funid_var_expr l :=
            match l with
            | [] => P_list_funid_var_expr_nil
            | (f,(vl,e)) :: l => P_list_funid_var_expr_cons f vl (expr_rect_1 e) (go_list_letrec l)
            end in
        let fix go_list_map (l : list (Expression * Expression)) : P_list_expr_expr l :=
            match l with
            | [] => P_list_expr_expr_nil
            | (e,e0) :: l => P_list_expr_expr_cons (expr_rect_1 e) (expr_rect_1 e0) (go_list_map l)
            end in
            match e with
              | ENil => P0_empty_list
              | ELit l => P0_literal l
              | EVar v => P0_var v
              | EFunId f => P0_funid f
              | EFun vl e => P0_fun vl (expr_rect_1 e)
              | ECons e1 e2 => P0_list (expr_rect_1 e1) (expr_rect_1 e2)
              | ETuple l => P0_tuple (go_list_tuple l)
              | ECall f l => P0_call f (go_list_tuple l)
              | EApp exp l => P0_apply (expr_rect_1 exp) (go_list_tuple l)
              | ECase e l => P0_case (expr_rect_1 e) (go_list_case l)
              | ELet vl e1 e2 => P0_let vl (expr_rect_1 e1) (expr_rect_1 e2)
              | ESeq e1 e2 => P0_seq (expr_rect_1 e1) (expr_rect_1 e2)
              | ELetRec l e => P0_letrec (expr_rect_1 e) (go_list_letrec l) 
              | EMap l => P0_map (go_list_map l)
              | ETry e1 vl1 e2 vl2 e3 => P0_try vl1 vl2 (expr_rect_1 e1) (expr_rect_1 e2) (expr_rect_1 e3)
            end
        .
          Combined Scheme expr_rect from expr_rect_1, expr_rect_2.
End exp_rect.

Section expr_ind.
  Check Expression_ind.
  Check SingleExpression_ind.
  Scheme expr_ind := Induction for Expression Sort Prop 
    with single_expr_ind_ext := Induction for SingleExpression Sort Prop.
  Check expr_rect.
  Check expr_ind.
  Axiom expr_ind_ext:
  forall (P : Expression -> Prop) (P0 : SingleExpression -> Prop),
       (forall el : list SingleExpression, 
       (forall i, i < length el -> P0 (nth i el ENil)) -> P (EValues el)) ->
       
       (forall e : SingleExpression, P0 e -> P (ESingle e)) ->
       
       P0 ENil ->
       
       (forall l : Literal, P0 (ELit l)) ->
       
       (forall v : Var, P0 (EVar v)) ->
       
       (forall f4 : FunctionIdentifier, P0 (EFunId f4)) ->
       
       (forall (vl : list Var) (e : Expression), P e -> P0 (EFun vl e)) ->
       
       (forall hd : Expression,
        P hd -> forall tl : Expression, 
        P tl -> P0 (ECons hd tl)) ->
        
       (forall l : list Expression,
        (forall i, i < length l -> P (nth i l (ESingle ENil))) -> P0 (ETuple l)) ->
       
       (forall (f8 : string) (l : list Expression), 
        (forall i, i < length l -> P (nth i l (ESingle ENil))) -> P0 (ECall f8 l)) ->
       
       (forall exp : Expression,
        P exp -> forall l : list Expression, 
       (forall i, i < length l -> P (nth i l (ESingle ENil))) -> P0 (EApp exp l)) ->
        
       (forall e : Expression,
        P e ->
        forall l : list (list Pattern * Expression * Expression),
        P0 (ECase e l)) ->
        
       (forall (l : list Var) (e1 : Expression),
        P e1 -> forall e2 : Expression, P e2 -> P0 (ELet l e1 e2)) ->
        
       (forall e1 : Expression,
        P e1 -> forall e2 : Expression, P e2 -> P0 (ESeq e1 e2)) ->
        
       (forall (l : list (FunctionIdentifier * (list Var * Expression)))
          (e : Expression), P e -> P0 (ELetRec l e)) ->
          
       (forall l : list (Expression * Expression), P0 (EMap l)) ->
       
       (forall e1 : Expression,
        P e1 ->
        forall (vl1 : list Var) (e2 : Expression),
        P e2 ->
        forall (vl2 : list Var) (e3 : Expression),
        P e3 -> P0 (ETry e1 vl1 e2 vl2 e3)) ->
        
       forall e : Expression, P e
  .
 (*  
  Lemma Expression_eq_dec_with_axiom : forall e e' : Expression, e = e' \/ e <> e'.
  Proof.
  intros. dependent induction e; destruct e'.
  * assert (el = el0 \/ el <> el0). { admit. } destruct H. 
    + left. now subst. 
    + right. congruence.
  * right. congruence.
  * right. congruence.
  * induction e. assert (e = e0 \/ e <> e0). { admit. } destruct H.
    + left. now subst.
    + right. congruence.
  
  
  Axiom single_expr_ind_ext: 
    forall
         P : SingleExpression -> Prop,
       P ENil ->
       (forall l : Literal, P (ELit l)) ->
       (forall v : Var, P (EVar v)) ->
       (forall f2 : FunctionIdentifier,
        P (EFunId f2)) ->
       (forall (vl : list Var) (e : Expression),
        P e -> P (EFun vl e)) ->
       (forall hd : SingleExpression,
        P hd ->
        forall tl : SingleExpression,
        P tl -> P (ECons hd tl)) ->
       (forall 
          l : list Expression,
       (forall i, i < length l -> P (nth i l ENil)) -> P (ETuple l)) ->
       (forall (f : string)
          (l : list Expression),
       (forall i, i < length l -> P (nth i l ENil)) -> P (ECall f l)) ->
       (forall (exp : Expression) 
          (l : list Expression),
       (forall i, i < length l -> P (nth i l ENil)) -> P exp -> P (EApp exp l)) ->
       (forall el : list Expression,
        forall
          l : list (list Pattern * Expression * Expression),
          (forall i,  i < length el -> P (nth i el ENil)) ->
          (forall i, i < length l -> P (nth i (snd (split (fst (split l)))) ENil)) -> 
          
          (forall i, i < length l -> P (nth i (snd (split l)) ENil)) ->
        P (ECase el l)) ->
       (forall (l : list (Var * Expression))
          (e : Expression), (forall i, i < length l -> P (nth i (snd (split l)) ENil)) -> P e -> P (ELet l e)) ->
       (
        forall e1 : Expression,
        P e1 ->
        forall e2 : Expression,
        P e2 -> P (ESeq e1 e2)
       ) ->
       (forall
          (l : list
                 (FunctionIdentifier *
                  (list Var * Expression)))
          (e : Expression), (forall i, i < length l -> P (nth i (snd (split (snd (split l)))) ENil)) ->
        P e -> P (ELetRec l e)) ->
       (forall
          l : list
                (Expression *
                 Expression),
        (forall i, i < length l -> P (nth i (fst (split l)) ENil))  -> (forall i, i < length l -> P (nth i (snd (split l)) ENil)) -> P (EMap l)) ->
        (forall el : list (Expression * Var),
        (forall i, i < length el -> P (nth i (fst (split el)) ENil)) ->
        forall e1 : Expression,
        P e1 ->
        forall e2 : Expression,
        P e2 ->
        forall (vl : list Var) (vex1 vex2 vex3 : Var),
        P (ETry el e1 e2 vex1 vex2 vex3)) ->
       forall e : Expression,
       P e.
End expr_ind. *)

Definition funid_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec.
Definition list_var_eq_dec := list_eq_dec string_dec.

(* Lemma list_expr_expr_eq_dec: forall l l0 : list (Expression * Expression), 
  (forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (fst (split l)) (ESingle ENil) = e' \/
    nth i (fst (split l)) (ESingle ENil) <> e') ->
  (forall i : nat,
     i < Datatypes.length l ->
     forall e' : Expression,
     nth i (snd (split l)) (ESingle ENil) = e' \/
     nth i (snd (split l)) (ESingle ENil) <> e')
      -> l = l0 \/ l <> l0 .
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in H, H0. pose (H_0th := H 0 (Nat.lt_0_succ _)). pose (H0_0th := H0 0 (Nat.lt_0_succ _)). simpl in H_0th, H0_0th. destruct a, (split l). simpl in H_0th, H0_0th. destruct p. pose (H_0th' := H_0th e4). pose (H0_0th' := H0_0th e5). destruct H_0th', H0_0th'; try(right; congruence).
  assert(l = l0 \/ l <> l0). {eapply IHl; intros. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H (S i) H4 e'). simpl in P. simpl. assumption. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H0 (S i) H4 e'). simpl in P. simpl. assumption. } destruct H3.
  * left. now subst.
  * right. congruence.
Qed. *)

Lemma list_expr_eq_dec: forall l l0 : list Expression,
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i l (ESingle ENil) = e' \/ nth i l (ESingle ENil) <> e' ) ->
    l = l0 \/ l <> l0.
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  remember H as H'. simpl in H. pose (H_0th := H 0 (Nat.lt_0_succ _)). simpl in H_0th. pose (H_0th' := H_0th e). destruct H_0th'.
    * assert(l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < Datatypes.length (a :: l)). { simpl. omega. } pose (P := H' (S i) H2 e'). simpl in P. assumption. } destruct H1.
      - left. now subst.
      - right. congruence.
    * right. congruence.
Qed.

Lemma list_var_expr_eq_dec: forall l l0 : list (Var * Expression),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (snd (split l)) (ESingle ENil) = e' \/
    nth i (snd (split l)) (ESingle ENil) <> e')
     -> l = l0 \/ l <> l0.
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in *. pose (H_0th := H 0 (Nat.lt_0_succ _)). destruct a, (split l). simpl in H_0th. destruct p. pose (H_0th' := H_0th e0). destruct H_0th', (string_dec v v0); try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < S(Datatypes.length (l))). { omega. } pose (P := H (S i) H2 e'). simpl in P. assumption. } destruct H1.
    * left. now subst.
    * right. congruence.
Qed.

Lemma list_expr_var_eq_dec: forall l l0 : list (Expression * Var),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (fst (split l)) (ESingle ENil) = e' \/
    nth i (fst (split l)) (ESingle ENil) <> e')
     -> l = l0 \/ l <> l0.
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in *. pose (H_0th := H 0 (Nat.lt_0_succ _)). destruct a, (split l). simpl in H_0th. destruct p. pose (H_0th' := H_0th e0). destruct H_0th', (string_dec v v0); try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < S(Datatypes.length (l))). { omega. } pose (P := H (S i) H2 e'). simpl in P. assumption. } destruct H1.
    * left. now subst.
    * right. congruence.
Qed.

(* Lemma list_pat_expr_expr_eq_dec : forall l l0 : list (list Pattern * Expression * Expression),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (snd (split (fst (split l)))) (ESingle ENil) = e' \/
    nth i (snd (split (fst (split l)))) (ESingle ENil) <>
    e') -> 
(forall i : nat,
     i < Datatypes.length l ->
     forall e' : Expression,
     nth i (snd (split l)) (ESingle ENil) = e' \/
     nth i (snd (split l)) (ESingle ENil) <> e') 
-> l = l0 \/ l <> l0. 
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in H,H0. pose (H_0th := H 0 (Nat.lt_0_succ _)). pose (H0_0th := H0 0 (Nat.lt_0_succ _)). simpl in H_0th,H0_0th. destruct a, (split l). simpl in H_0th,H0_0th. destruct p. simpl in *. destruct p0, (split l1). simpl in H_0th,H0_0th. destruct p.  pose (H_0th' := H_0th e5). pose (H0_0th' := H0_0th e0). destruct H_0th', H0_0th'; try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl; intros. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H (S i) H4 e'). simpl in P. assumption. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H0 (S i) H4 e'). simpl in P. assumption. } destruct H3.
  * destruct (list_eq_dec (Pattern_eq_dec) l3 l6).
    - left. now subst.
    - right. congruence.
  * right. congruence.
Qed. *)

Lemma list_funid_listvar_expr_eq_dec : forall l l0 : list (FunctionIdentifier * ((list Var) * Expression)),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (snd (split (snd (split l))))
      (ESingle ENil) = e' \/
    nth i (snd (split (snd (split l))))
      (ESingle ENil) <> e')
-> l = l0 \/ l <> l0. 
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in H. pose (H_0th := H 0 (Nat.lt_0_succ _)). simpl in H_0th. destruct a, (split l). simpl in *. destruct p0, (split l2). simpl in H_0th. destruct p. destruct p. pose (H_0th' := H_0th e0). destruct H_0th', (funid_eq_dec f f0),(list_var_eq_dec l3 l6); try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H (S i) H2 e'). simpl in P. assumption. } destruct H1.
  * left. now subst.
  * right. congruence.
Qed.

Lemma Expression_eq_dec_with_axiom : forall e e' : Expression, e = e' \/ e <> e'.
Proof using.
  intros. 
  dependent induction e using expr_ind_ext; destruct e'; try(right; congruence).
  * left. reflexivity.
  * destruct (Literal_eq_dec l l0).
    - left. now subst.
    - right. congruence.
  * destruct (string_dec v v0).
    - left. now subst.
    - right. congruence.
  * destruct (funid_eq_dec f f2).
    - left. now subst.
    - right. congruence.
  * destruct (IHe e'), (list_var_eq_dec vl vl0); try(right;congruence).
    - left. now subst.
  * destruct (IHe1 e'1), (IHe2 e'2); try(right;congruence).
    - left. now subst.
  * destruct (list_expr_eq_dec l l0 H).
    - rewrite H0. auto.
    - right. congruence.
  * destruct (list_expr_eq_dec l l0 H).
    - rewrite H0. destruct (string_dec f f0).
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (list_expr_eq_dec l l0 H).
    - rewrite H0. destruct (IHe e').
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (list_expr_eq_dec el el0 H).
    - destruct (list_pat_expr_expr_eq_dec l l0 H0 H1).
      + subst. auto.
      + right. congruence.
    - right. congruence.
  * destruct (list_var_expr_eq_dec l l0 H).
    - rewrite H0. destruct (IHe e').
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (IHe1 e'1), (IHe2 e'2); try(right;congruence).
    - left. now subst.
  * destruct (list_funid_listvar_expr_eq_dec l l0 H).
    - destruct (IHe e').
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (list_expr_expr_eq_dec l l0 H H0).
    - rewrite H1. auto.
    - right. congruence.
  * destruct (IHe1 e'1), (IHe2 e'2), (string_dec vex1 vex0), (string_dec vex2 vex4), (string_dec vex3 vex5); try(right;congruence).
    subst. destruct (list_expr_var_eq_dec el el0).
    - intros. apply H. assumption.
    - subst. left. reflexivity.
    - right. congruence.
Qed.


End Expression_Eq_Dec.