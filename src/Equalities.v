(* Require Core_Erlang_Induction. *)

From CoreErlang Require Export Syntax.

Require Export Lia.
From Coq Require Import Classes.EquivDec.
Require Import List.
Require Import Coq.Structures.OrderedTypeEx.


(* Export Core_Erlang_Induction.Induction. *)

Import ListNotations.
Export Arith.PeanoNat.

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

  Scheme Equality for Lit.

  Fixpoint Pat_eq_dec (p1 p2 : Pat) : {p1 = p2} + {p1 <> p2}.
  Proof.
    set (Pat_list_eq_dec := list_eq_dec Pat_eq_dec).
    set (Pat_var_eq_dec := string_dec).
    set (Pat_literal_eq_dec := Lit_eq_dec).
    set (list_eq_dec (prod_eqdec Pat_eq_dec Pat_eq_dec)).
    decide equality.
  Qed.

(** Boolean equalities: *)

  (* The equality of function signatures *)
  Definition funid_eqb (v1 v2 : FunId) : bool :=
  match v1, v2 with
  | (fid1, num1), (fid2, num2) => Nat.eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (* Extended equality between functions and vars *)
  Definition var_funid_eqb (v1 v2 : Var + FunId) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => Nat.eqb s1 s2
  | inr f1, inr f2 => funid_eqb f1 f2
  | _, _ => false
  end.

  (*TODO: PVar has no arguments. Is this ok?*)
  Fixpoint Pat_eqb (p1 p2 : Pat) {struct p1} : bool :=
  match p1, p2 with
   (*| PVar v1, PVar v2 => eqb v1 v2*)
   | PVar, PVar  => true
   | PLit l1, PLit l2 => Lit_beq l1 l2
   | PCons hd tl, PCons hd' tl' => Pat_eqb hd hd' && Pat_eqb tl tl'
   | PTuple l, PTuple l' => (fix blist_eq l l' :=
                            match l, l' with
                            | [], [] => true
                            | x::xs, x'::xs' => andb (Pat_eqb x x') (blist_eq xs xs')
                            | _, _ => false
                            end) l l'
   | PNil, PNil => true
   | PMap l, PMap l' => (fix blist_eq l l' :=
                            match l, l' with
                            | [], [] => true
                            | (x, y)::xs, (x', y')::xs' => 
          andb (andb (Pat_eqb x x') (Pat_eqb y y')) (blist_eq xs xs')
                            | _, _ => false
                            end) l l'
   | _, _ => false
  end.


  Proposition Exp_eq_dec (e1 e2 : Exp) :
    {e1 = e2} + {e1 <> e2}
  with Val_eq_dec (e1 e2 : Val):
    {e1 = e2} + {e1 <> e2}
  with NVal_eq_dec (e1 e2 : NonVal):
    {e1 = e2} + {e1 <> e2}.
  Proof.
    {
      decide equality.
    }
    {
      set (list_eq_dec Val_eq_dec).
      set (Nat.eq_dec).
      set (Lit_eq_dec).
      set (list_eq_dec (prod_eqdec Val_eq_dec Val_eq_dec)).
      decide equality.
      * decide equality.
      * set (list_eq_dec (prod_eqdec (prod_eqdec Nat.eq_dec Nat.eq_dec) Exp_eq_dec)).
        apply s3.
    }
    {
      set (list_eq_dec Exp_eq_dec).
      set (string_dec).
      set (Nat.eq_dec).
      set (Lit_eq_dec).
      set (list_eq_dec (prod_eqdec Exp_eq_dec Exp_eq_dec)).
      decide equality.
      * set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pat_eq_dec) Exp_eq_dec) Exp_eq_dec)).
        apply s4.
      * set (list_eq_dec (prod_eqdec Nat.eq_dec Exp_eq_dec)).
        apply s4.
    }
  Qed.
  

  Fixpoint Val_eqb (e1 e2 : Val) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  | VCons hd tl, VCons hd' tl' => Val_eqb hd hd' && Val_eqb tl tl'
  | VTuple l, VTuple l' => (fix blist l l' := match l, l' with
                                             | [], [] => true
                                             | x::xs, x'::xs' => andb (Val_eqb x x') (blist xs xs')
                                             | _, _ => false
                                             end) l l'
  | VMap l, VMap l' => (fix blist l l' := match l, l' with
                                                   | [], [] => true
                                                   | (x,y)::xs, (x',y')::xs' => andb (Val_eqb x x') (andb (Val_eqb y y') (blist xs xs'))
                                                   | _, _ => false
                                                   end) l l'
  | VVar v, VVar v' => Nat.eqb v v'
  | VFunId v, VFunId v' => funid_eqb v v'
  (* Note this line: closures are considered as equal, if their id is equal *)
  (* | VClos ext id vc e, VClos ext' id' vc' e' => Nat.eqb id id' *)
  | VClos ext id vc e, VClos ext' id' vc' e' => false (* NOTE: not safe! *)
  | _, _ => false
  end.

  Fixpoint Exp_eqb (e1 e2 : Exp) : bool :=
  match e1, e2 with
   | VVal a, VVal b => Val_eqb a b
   | EExp (EValues l), EExp (EValues l') => (fix blist l l' := match l, l' with
                                        | [], [] => true
                                        | x::xs, x'::xs' => andb (Exp_eqb x x') 
                                                                 (blist xs xs')
                                        | _, _ => false
                                        end) l l'
   | EExp (EFun vl e), EExp (EFun vl' e') => Nat.eqb vl vl' && Exp_eqb e e'
   | EExp (ECons hd tl), EExp (ECons hd' tl') => Exp_eqb hd hd' && Exp_eqb tl tl'
   | EExp (ETuple l), EExp (ETuple l') => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Exp_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | EExp (ECall f l), EExp (ECall f' l') => eqb f f' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Exp_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | EExp (EPrimOp f l), EExp (EPrimOp f' l') => eqb f f' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Exp_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | EExp (EApp exp l), EExp (EApp exp' l') => Exp_eqb exp exp' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Exp_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | EExp (ECase e l), EExp (ECase e' l') => Exp_eqb e e'
    && Nat.eqb (length l) (length l') &&
         (fix blist l l' := match l, l' with
             | [], [] => true
             | (pl,y,z)::xs, (pl',y',z')::xs' => andb (
               (fix blist l l' := match l, l' with
               | [], [] => true
               | x::xs, x'::xs' => andb (Pat_eqb x x') (blist xs xs')
               | _, _ => false
               end) pl pl') 
               (andb (Exp_eqb y y') (andb (Exp_eqb z z') (blist xs xs')))
                                                 | _, _ => false
                                                 end) l l' 
   | EExp (ELet l e1 e2), EExp (ELet l' e1' e2') => Nat.eqb l l' && Exp_eqb e1 e1' && Exp_eqb e2 e2'
   | EExp (ESeq e1 e2), EExp (ESeq e1' e2') => andb (Exp_eqb e1 e1') (Exp_eqb e2 e2')
   | EExp (ELetRec l e), EExp (ELetRec l' e') => 
                                               (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,y)::xs, (x',y')::xs' => 
                                                 andb (Nat.eqb x x') (andb (Exp_eqb y y') (blist xs xs'))
                                                 | _, _ => false
                                                 end) l l' &&
                                               Exp_eqb e e'
   | EExp (EMap l), EExp (EMap l') => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,y)::xs, (x',y')::xs' => andb (Exp_eqb x x') (andb (Exp_eqb y y') (blist xs xs'))
                                                 | _, _ => false
                                                 end) l l'
   | EExp (ETry e1 vl1 e2 vl2 e3), EExp (ETry e1' vl1' e2' vl2' e3') => Nat.eqb vl1 vl1' && Nat.eqb vl2 vl2' &&
                                                          Exp_eqb e1 e1' && Exp_eqb e2 e2' &&
                                                          Exp_eqb e3 e3'
   | _, _ => false
  end.

  Import Structures.OrderedTypeEx.String_as_OT.
  
  Definition string_ltb (s1 s2 : string) : bool :=
  match cmp s1 s2 with
  | Lt => true
  | _ => false
  end.

  Definition Lit_ltb (l1 l2 : Lit) : bool :=
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

    Fixpoint Val_ltb (k v : Val) : bool :=
    match k, v with
    | VLit l, VLit l' => Lit_ltb l l'
    | VLit _, _ => true
    (* | VClos _ id _ _, VClos _ id' _ _=> Nat.ltb id id' *)
    | VClos _ id _ _, VClos _ id' _ _=> false (* NOT: not safe comparison! *)
    | VClos _ _ _ _, VTuple _ => true
    | VClos _ _ _ _, VMap _ => true
    | VClos _ _ _ _, VNil => true
    | VClos _ _ _ _, VCons _ _ => true
    | VTuple l, VTuple l' => orb (Nat.ltb (length l) (length l')) 
                                (andb (Nat.eqb (length l) (length l')) (list_less Val Val_ltb Val_eqb l l'))
    | VTuple _, VNil => true
    | VTuple _, VMap _ => true
    | VTuple l, VCons _ _ => true
    | VMap l, VMap l' => orb (Nat.ltb (length l) (length l')) (andb (Nat.eqb (length l) (length l'))
                        (orb ((fix list_less (l l' : list (Val * Val)) :=
                            match l, l' with
                            | [], [] => false
                            | (x,y)::xs, [] => false
                            | [], (x',y')::ys => true
                            | (x,y)::xs, (x',y')::ys => 
                                    if Val_eqb x x' then list_less xs ys else Val_ltb x x'
                            end) l l')
                            (andb 
                            (list_equal Val Val_eqb (map fst l) (map fst l'))
                            
                            ((fix list_less (l l' : list (Val * Val)) :=
                            match l, l' with
                            | [], [] => false
                            | (x,y)::xs, [] => false
                            | [], (x',y')::ys => true
                            | (x,y)::xs, (x',y')::ys => 
                                    if Val_eqb y y' then list_less xs ys else Val_ltb y y'
                            end) l l'))))
    | VMap _, VNil => true
    | VMap _, VCons _ _ => true
    | VNil, VCons _ _ => true
    | VCons hd tl, VCons hd' tl' => if Val_eqb hd hd' then Val_ltb tl tl' else Val_ltb hd hd'
    | _, _ => false
    end.

  (*TODO: Adapt the rest if needed!*)

End Equalities.

Lemma Lit_eqb_eq : forall l1 l2, Lit_beq l1 l2 = true <-> l1 = l2.
Proof.
  split; intros.
  * now apply internal_Lit_dec_bl.
  * now apply internal_Lit_dec_lb. 
Qed.

Lemma Lit_eqb_refl : forall l, Lit_beq l l = true.
Proof.
  intro. rewrite Lit_eqb_eq. reflexivity.
Qed.
