(* Require Core_Erlang_Induction. *)

Require Export ExpSyntax.

Require Lia.
From Coq Require Classes.EquivDec.
Require Import List.
Require Import Coq.Structures.OrderedTypeEx.
Module Equalities.

(* Export Core_Erlang_Induction.Induction. *)

Import ListNotations.
Export Arith.PeanoNat.
Import Classes.EquivDec.
Export Lia.

Section Basic_Eq_Dec.
(** Decidable equality for product and sum types *)
  Context {A B : Type}.

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

  Definition prod_eqb {A B : Type} (eqx : A -> A -> bool) (eqy : B -> B -> bool) (p1 p2 : A * B) :=
  match p1, p2 with
  | (x, y), (x', y') => andb (eqx x x') (eqy y y')
  end.

  Theorem prod_eqb_refl eqx eqy p :
    (forall p1, eqx p1 p1 = true) ->
    (forall p2, eqy p2 p2 = true) ->
    @prod_eqb A B eqx eqy p p = true.
  Proof.
    intros. destruct p. simpl.
    rewrite (H a), (H0 b). auto.
  Qed.

  Theorem prod_eqb_eq :
    forall p1 p2 eqx eqy,
    (forall e1 e2, e1 = e2 <-> eqx e1 e2 = true) ->
    (forall e1 e2, e1 = e2 <-> eqy e1 e2 = true) ->
    p1 = p2
  <->
    @prod_eqb A B eqx eqy p1 p2 = true.
  Proof.
    split.
    * intros. subst. apply prod_eqb_refl.
      intros. apply H. auto. intros. apply H0. auto.
    * intros. destruct p1, p2. pose (H a a0). pose (H0 b b0).
      simpl in H1. apply andb_prop in H1. destruct H1.
      rewrite <- i in H1. rewrite <- i0 in H2. subst. auto.
  Qed.

End Basic_Eq_Dec.

Section list_eqb.

  Context {A : Type}.

  Fixpoint list_eqb (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x::xs, y::ys => eq x y && list_eqb eq xs ys
  | _, _ => false
  end.

  Proposition list_eqb_refl {f : A -> A -> bool} (l : list A) :
    (forall a, f a a = true)
  ->
    list_eqb f l l = true.
  Proof.
    induction l.
    * simpl. reflexivity.
    * simpl. intros. rewrite (H a), (IHl H). auto.
  Qed.

  Theorem list_eqb_eq :
    forall (l1 l2 : list A) eqf,
    (forall e1 e2, e1 = e2 <-> eqf e1 e2 = true) ->
    l1 = l2
  <->
    list_eqb eqf l1 l2 = true.
  Proof.
    split.
    * intros. subst. apply list_eqb_refl.
      intros. apply H. auto.
    * generalize dependent l2. induction l1; intros.
      - destruct l2; try inversion H0. auto.
      - destruct l2; try inversion H0.
        apply andb_prop in H2. destruct H2. apply H in H1.
        apply IHl1 in H2. subst. auto.
  Qed.

End list_eqb.

Section Equalities.
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

(** Boolean equalities: *)

  (* The equality of function signatures *)
  Definition funid_eqb (v1 v2 : FunctionIdentifier) : bool :=
  match v1, v2 with
  | (fid1, num1), (fid2, num2) => Nat.eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (*Used to be (Var + FunctionIdentifier) but now Var is just a Nat *)
  Definition Var : Set := nat. (*TODO: Rewritten like this for ease for now.*)
  (* Extended equality between functions and vars *)
  Definition var_funid_eqb (v1 v2 : Var + FunctionIdentifier) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => Nat.eqb s1 s2
  | inr f1, inr f2 => funid_eqb f1 f2
  | _, _ => false
  end.

  Definition Literal_eqb (l1 l2 : Literal) : bool :=
  match l1, l2 with
   | Atom s1, Atom s2 => eqb s1 s2
   | Integer x1, Integer x2 => Z.eqb x1 x2
   | _, _ => false
  end.


  (*TODO: PVar has no arguments. Is this ok?*)
  Fixpoint Pattern_eqb (p1 p2 : Pattern) {struct p1} : bool :=
  match p1, p2 with
   (*| PVar v1, PVar v2 => eqb v1 v2*)
   | PVar, PVar  => true
   | PLit l1, PLit l2 => Literal_eqb l1 l2
   | PCons hd tl, PCons hd' tl' => Pattern_eqb hd hd' && Pattern_eqb tl tl'
   | PTuple l, PTuple l' => (fix blist_eq l l' := match l, l' with
                                         | [], [] => true
                                         | x::xs, x'::xs' => andb (Pattern_eqb x x') (blist_eq xs xs')
                                         | _, _ => false
                                         end) l l'
   | PNil, PNil => true
   | PMap l, PMap l' => (fix blist_eq l l' := match l, l' with
                                         | [], [] => true
                                         | (x, y)::xs, (x', y')::xs' => 
                       andb (andb (Pattern_eqb x x') (Pattern_eqb y y')) (blist_eq xs xs')
                                         | _, _ => false
                                         end) l l'
   | _, _ => false
  end.


  Fixpoint Value_eqb (e1 e2 : ValueExpression) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Literal_eqb l l'
  | VCons hd tl, VCons hd' tl' => Value_eqb hd hd' && Value_eqb tl tl'
  | VTuple l, VTuple l' => (fix blist l l' := match l, l' with
                                             | [], [] => true
                                             | x::xs, x'::xs' => andb (Value_eqb x x') (blist xs xs')
                                             | _, _ => false
                                             end) l l'
  | VMap l, VMap l' => (fix blist l l' := match l, l' with
                                                   | [], [] => true
                                                   | (x,y)::xs, (x',y')::xs' => andb (Value_eqb x x') (andb (Value_eqb y y') (blist xs xs'))
                                                   | _, _ => false
                                                   end) l l'
  | VVar v, VVar v' => Nat.eqb v v'
  | VFunId v, VFunId v' => Nat.eqb v v'
  | VClos ext id vc e, VClos ext' id' vc' e' => Nat.eqb id id'
  | _, _ => false
  end.
  
  (* TODO: NEEDS BIG REDO*)
  Fixpoint Expression_eqb (e1 e2 : Expression) : bool :=
  match e1, e2 with
   | Val a, Val b => Value_eqb a b
   | Exp (EValues l), Exp (EValues l') => (fix blist l l' := match l, l' with
                                        | [], [] => true
                                        | x::xs, x'::xs' => andb (Expression_eqb x x') 
                                                                 (blist xs xs')
                                        | _, _ => false
                                        end) l l'
   | Exp (EFun vl e), Exp (EFun vl' e') => Nat.eqb vl vl' && Expression_eqb e e'
   | Exp (ECons hd tl), Exp (ECons hd' tl') => Expression_eqb hd hd' && Expression_eqb tl tl'
   | Exp (ETuple l), Exp (ETuple l') => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | Exp (ECall f l), Exp (ECall f' l') => eqb f f' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | Exp (EPrimOp f l), Exp (EPrimOp f' l') => eqb f f' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | Exp (EApp exp l), Exp (EApp exp' l') => Expression_eqb exp exp' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | Exp (ECase e l), Exp (ECase e' l') => Expression_eqb e e'
    && Nat.eqb (length l) (length l') &&
         (fix blist l l' := match l, l' with
             | [], [] => true
             | (pl,y,z)::xs, (pl',y',z')::xs' => andb (
               (fix blist l l' := match l, l' with
               | [], [] => true
               | x::xs, x'::xs' => andb (Pattern_eqb x x') (blist xs xs')
               | _, _ => false
               end) pl pl') 
               (andb (Expression_eqb y y') (andb (Expression_eqb z z') (blist xs xs')))
                                                 | _, _ => false
                                                 end) l l' 
   | Exp (ELet l e1 e2), Exp (ELet l' e1' e2') => Nat.eqb l l' && Expression_eqb e1 e1' && Expression_eqb e2 e2'
   | Exp (ESeq e1 e2), Exp (ESeq e1' e2') => andb (Expression_eqb e1 e1') (Expression_eqb e2 e2')
   | Exp (ELetRec l e), Exp (ELetRec l' e') => 
                                               (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,y)::xs, (x',y')::xs' => 
                                                 andb (Nat.eqb x x') (andb (Expression_eqb y y') (blist xs xs'))
                                                 | _, _ => false
                                                 end) l l' &&
                                               Expression_eqb e e'
   | Exp (EMap l), Exp (EMap l') => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,y)::xs, (x',y')::xs' => andb (Expression_eqb x x') (andb (Expression_eqb y y') (blist xs xs'))
                                                 | _, _ => false
                                                 end) l l'
   | Exp (ETry e1 vl1 e2 vl2 e3), Exp (ETry e1' vl1' e2' vl2' e3') => Nat.eqb vl1 vl1' && Nat.eqb vl2 vl2' &&
                                                          Expression_eqb e1 e1' && Expression_eqb e2 e2' &&
                                                          Expression_eqb e3 e3'
   | _, _ => false
  end.


  (*TODO: I only need cmp for string waht is needed? *)
  (*Require Import Coq.Structures.OrderedTypeEx.*)
  Import Structures.OrderedTypeEx.String_as_OT.
  
  Definition string_ltb (s1 s2 : string) : bool :=
  match cmp s1 s2 with
  | Lt => true
  | _ => false
  end.

  Definition literal_ltb (l1 l2 : Literal) : bool :=
  match l1, l2 with
  | Integer x, Integer x' => Z.ltb x x'
  | Atom s, Atom s' => string_ltb s s'
  | Integer x, Atom s => true
  | _, _ => false
  end.
  
  Section bool_list_ltb.
  Variable A : Type.
  Hypothesis less : A -> A -> bool.
  Hypothesis eq : A -> A -> bool.

  Fixpoint list_less (a b : list A) : bool :=
  match a, b with
  | [], [] => false
  | x::xs, [] => false
  | [], y::ys => true
  | x::xs, y::ys => if eq x y then list_less xs ys else less x y
  end.
  
  Fixpoint list_equal (a b : list A) : bool :=
  match a, b with
  | [], [] => true
  | x::xs, [] => false
  | [], y::ys => false
  | x::xs, y::ys => if eq x y then list_equal xs ys else false
  end.

  End bool_list_ltb.
  
  Check list_less.
(** TODO: investigate, but now, we dont compare value sequences, only single values *)
  Fixpoint Value_ltb (k v : ValueExpression) : bool :=
  match k, v with
  | VLit l, VLit l' => literal_ltb l l'
  | VLit _, _ => true
  | VClos _ id _ _, VClos _ id' _ _=> Nat.ltb id id'
  | VClos _ _ _ _, VTuple _ => true
  | VClos _ _ _ _, VMap _ => true
  | VClos _ _ _ _, VNil => true
  | VClos _ _ _ _, VCons _ _ => true
  | VTuple l, VTuple l' => orb (Nat.ltb (length l) (length l')) (andb (Nat.eqb (length l) (length l')) (list_less ValueExpression Value_eqb Value_ltb l l'))
  | VTuple _, VNil => true
  | VTuple _, VMap _ => true
  | VTuple l, VCons _ _ => true
  | VMap l, VMap l' => orb (Nat.ltb (length l) (length l')) (andb (Nat.eqb (length l) (length l'))
                       (orb ((fix list_less (l l' : list (ValueExpression * ValueExpression)) :=
                          match l, l' with
                          | [], [] => false
                          | (x,y)::xs, [] => false
                          | [], (x',y')::ys => true
                          | (x,y)::xs, (x',y')::ys => 
                                  if Value_eqb x x' then list_less xs ys else Value_ltb x x'
                          end) l l')
                          (andb 
                          (list_equal ValueExpression Value_eqb (map fst l) (map fst l'))
                          
                          ((fix list_less (l l' : list (ValueExpression * ValueExpression)) :=
                          match l, l' with
                          | [], [] => false
                          | (x,y)::xs, [] => false
                          | [], (x',y')::ys => true
                          | (x,y)::xs, (x',y')::ys => 
                                  if Value_eqb y y' then list_less xs ys else Value_ltb y y'
                          end) l l'))))
  | VMap _, VNil => true
  | VMap _, VCons _ _ => true
  | VNil, VCons _ _ => true
  | VCons hd tl, VCons hd' tl' => if Value_eqb hd hd' then Value_ltb tl tl' else Value_ltb hd hd'
  | _, _ => false
  end.

  (*TODO: Adapt the rest if needed!*)
End Equalities.
End Equalities.
