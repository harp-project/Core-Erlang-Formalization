(* Require Core_Erlang_Induction. *)

From CoreErlang Require Export Induction.

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

  (* NOTE: do not use this (too hard to use in proofs): *)
  (* Scheme Equality for Lit. *)

  Definition Lit_beq (l1 l2 : Lit) : bool :=
    match l1, l2 with
    | Integer i1, Integer i2 => Z.eqb i1 i2
    | Atom a1, Atom a2 =>
      match string_dec a1 a2 with
      | left _ => true
      | right _ => false
      end
    | _, _ => false
    end.

  Lemma Lit_eqb_refl :
    forall l, Lit_beq l l = true.
  Proof.
    destruct l; simpl.
    * destruct string_dec; auto.
    * lia.
  Qed.

  Lemma Lit_eqb_eq :
    forall l1 l2, Lit_beq l1 l2 = true <-> l1 = l2.
  Proof.
    destruct l1, l2; split; intros; inv H.
    2,4: apply Lit_eqb_refl.
    break_match_hyp; subst; auto. congruence.
    apply Z.eqb_eq in H1. now subst.
  Qed.

  Lemma Lit_eqb_sym :
    forall l1 l2, Lit_beq l1 l2 = Lit_beq l2 l1.
  Proof.
    destruct l1, l2; simpl; auto.
    * do 2 destruct string_dec; auto. subst. congruence.
    * now rewrite Z.eqb_sym.
  Qed.

  Theorem Lit_eq_dec (l1 l2 : Lit) : {l1 = l2} + {l1 <> l2}.
  Proof.
    set string_dec.
    set Z.eq_dec.
    decide equality.
  Qed.
    

  Fixpoint Pat_eq_dec (p1 p2 : Pat) : {p1 = p2} + {p1 <> p2}.
  Proof.
    set (Pat_list_eq_dec := list_eq_dec Pat_eq_dec).
    set (Pat_var_eq_dec := string_dec).
    set (Pat_literal_eq_dec := Lit_eq_dec).
    set (list_eq_dec (prod_eqdec Pat_eq_dec Pat_eq_dec)).
    repeat decide equality.
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
(*       * set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pat_eq_dec) Exp_eq_dec) Exp_eq_dec)).
        apply s4. *)
    }
  Qed.

  Fixpoint Val_eqb (e1 e2 : Val) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  | VPid p, VPid p' => true
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
  | VClos ext id vc e, VClos ext' id' vc' e' => Nat.eqb id id'
  (* | VClos ext id vc e, VClos ext' id' vc' e' => false  (*<- NOTE: not safe!*) *)
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
   | EExp (ECall m f l), EExp (ECall m' f' l') => Exp_eqb f f' && Exp_eqb m m' && (fix blist l l' := match l, l' with
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
  (*  | EReceive l, EReceive l' => ... *)
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
    (* Note: comparison of closures should be based on something, otherwise
             the equivalence definitions would not work as intended for maps:
      if `clos1 <> clos2` (while their `id`-s are not equal), then
      `map_insert clos1 (map_insert clos2 []) <> map_insert clos2 (map_insert clos1 [])`
      However, this has to hold for the compatibility property of maps *)
    | VClos _ id _ _, VClos _ id' _ _=> Nat.ltb id id'
    (*| VClos _ id _ _, VClos _ id' _ _=> false (* NOT: not safe comparison! *)*)
    | VClos _ _ _ _, VTuple _ => true
    | VClos _ _ _ _, VPid _ => true
    | VClos _ _ _ _, VMap _ => true
    | VClos _ _ _ _, VNil => true
    | VClos _ _ _ _, VCons _ _ => true
    | VPid p, VPid p' => false
    | VPid _, VTuple _ => true
    | VPid _, VMap _ => true
    | VPid _, VNil => true
    | VPid _, VCons _ _ => true
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

End Equalities.

Notation "e1 =ₑ e2" := (Exp_eqb e1 e2) (at level 69, no associativity).
Notation "v1 =ᵥ v2" := (Val_eqb v1 v2) (at level 69, no associativity).
Notation "v1 <ᵥ v2" := (Val_ltb v1 v2) (at level 69, no associativity).

#[global]
Hint Unfold PBoth : core.


(** The following theorems are for basic properties of value
    equality and ordering. Note, that because these relations
    do not correspond to their syntactical counterpart, thus
    the proofs are complex, because all of the steps Coq could
    handle in Prop, needs to be taken care of in bool. *)
Lemma Val_eqb_refl :
  forall v, v =ᵥ v = true.
Proof.
  induction v using Val_ind_weakened with
    (Q := Forall (fun v => v =ᵥ v = true))
    (R := Forall (PBoth (fun v => v =ᵥ v = true))); simpl; auto.
  * now rewrite Lit_eqb_refl.
  (* * now rewrite Nat.eqb_refl. *)
  * now rewrite IHv1, IHv2.
  * induction IHv; auto. now rewrite H, IHIHv. 
  * induction IHv; auto. destruct x, H. simpl in *.
    now rewrite H, H0, IHIHv.
  * now rewrite Nat.eqb_refl.
  * destruct n; simpl; now do 2 rewrite Nat.eqb_refl.
  * now rewrite Nat.eqb_refl.
Qed.

Lemma Val_eqb_sym :
  forall v1 v2, v1 =ᵥ v2 = v2 =ᵥ v1.
Proof.
  valinduction; try destruct v2; simpl; auto.
  * now rewrite Lit_eqb_sym.
  (* * now rewrite Nat.eqb_sym. *)
  * now rewrite IHv1_1, IHv1_2.
  * revert l0. induction IHv1; intros; destruct l0; simpl in *; try congruence.
  * revert l0. induction IHv1; intros; destruct l0; simpl in *; try congruence.
    - destruct p; congruence.
    - destruct x. auto.
    - destruct p, x, H; rewrite H, H0, IHIHv1; simpl in *; auto.
  * intros. now rewrite Nat.eqb_sym.
  * intros; destruct n, n0; simpl in *.
    rewrite (Nat.eqb_sym n0). now rewrite (Nat.eqb_sym n2).
  * intros. now rewrite Nat.eqb_sym.
Qed.

Lemma Val_eqb_trans :
  forall v1 v2 v3,
  v1 =ᵥ v2 = true -> v2 =ᵥ v3 = true ->
  v1 =ᵥ v3 = true.
Proof.
  remember (fun v1 => forall v2 v3, v1 =ᵥ v2 = true -> v2 =ᵥ v3 = true ->
  v1 =ᵥ v3 = true) as FProp.
  induction v1 using Val_ind_weakened with
    (Q := Forall FProp)
    (R := Forall (PBoth FProp)); subst FProp; intros; simpl; auto.
  all: try destruct v3, v2; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq. apply Lit_eqb_eq in H, H0. now subst.
  (* * apply Nat.eqb_eq in H, H0. subst. now rewrite Nat.eqb_refl. *)
  * apply Bool.andb_true_iff in H as [H_1 H_2], H0 as [H0_1 H0_2].
    now rewrite (IHv1_1 _ _ H_1 H0_1), (IHv1_2 _ _ H_2 H0_2).
  * generalize dependent l1. revert l0. induction IHv1; simpl; intros;
    destruct l0, l1; simpl in *; auto; try congruence.
    apply Bool.andb_true_iff in H1 as [H1_1 H1_2].
    apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
    erewrite (H _ _ H0_1 H1_1), IHIHv1; auto.
    all: eassumption.
  * generalize dependent l1. revert l0. induction IHv1; simpl; intros;
    destruct l0, l1; simpl in *; auto; try congruence.
    - destruct x, p. congruence.
    - destruct p0, x, p.
      apply Bool.andb_true_iff in H1 as [H1_1 H1_2].
      apply Bool.andb_true_iff in H1_2 as [H1_2 H1_3].
      apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.andb_true_iff in H0_2 as [H0_2 H0_3].
      destruct H; simpl in *.
      erewrite (H _ _ H0_1 H1_1), (H0 _ _ H0_2 H1_2), IHIHv1; auto.
      all: eassumption.
  * apply Nat.eqb_eq in H, H0. subst. apply Nat.eqb_refl.
  * destruct n, n0, n1; simpl in *.
    apply Bool.andb_true_iff in H as [H_1 H_2].
    apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
    apply Nat.eqb_eq in H_1, H0_1, H_2, H0_2. subst.
    now do 2 rewrite Nat.eqb_refl.
  * apply Nat.eqb_eq in H, H0. subst. apply Nat.eqb_refl.
Qed.

Lemma Val_eqb_neqb :
  forall v1 v2 v3,
    v1 =ᵥ v2 = false -> v2 =ᵥ v3 = true ->
    v1 =ᵥ v3 = false.
Proof.
  valinduction; intros; try destruct v2, v3; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq in H0. now subst.
  (* * apply Nat.eqb_eq in H0. now subst. *)
  * apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
    apply Bool.andb_false_iff in H as [H | H].
    - erewrite IHv1_1. 2-3: eassumption. reflexivity.
    - erewrite IHv1_2. 2-3: eassumption. apply Bool.andb_false_r.
  * generalize dependent l1. generalize dependent l0.
    induction IHv1; simpl; auto; intros; destruct l0, l1; 
    simpl in *; try congruence.
    apply Bool.andb_true_iff in H1 as [H1_1 H1_2].
    apply Bool.andb_false_iff in H0 as [H0 | H0].
    - eapply H in H0. 2: eassumption. now rewrite H0.
    - erewrite IHIHv1. apply Bool.andb_false_r.
      1-2: eassumption.
  * generalize dependent l1. generalize dependent l0.
    induction IHv1; simpl; auto; intros; destruct l0, l1; 
    simpl in *; try destruct p; try congruence.
    destruct x, p0. destruct H. simpl in *.
    apply Bool.andb_true_iff in H1 as [H1_1 H1_2].
    apply Bool.andb_true_iff in H1_2 as [H1_2 H1_3].
    apply Bool.andb_false_iff in H0 as [H0 | H0].
    2: apply Bool.andb_false_iff in H0 as [H0 | H0].
    - eapply H in H0. 2: eassumption. now rewrite H0.
    - eapply H2 in H0. 2: eassumption. rewrite H0.
      now apply Bool.andb_false_r.
    - erewrite IHIHv1. apply Bool.andb_false_intro2, Bool.andb_false_r.
      1-2: eassumption.
  * apply Nat.eqb_eq in H0. now subst.
  * destruct n, n0, n1. simpl in *.
    apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
    apply Nat.eqb_eq in H0_1, H0_2. now subst.
  * apply Nat.eqb_eq in H0. now subst.
Qed.

Lemma Lit_ltb_irrefl :
  forall l, Lit_ltb l l = false.
Proof.
  destruct l; simpl.
  * unfold string_ltb.
    break_match_goal; auto.
    apply String_as_OT.cmp_lt in Heqc.
    apply String_as_OT.lt_not_eq in Heqc.
    unfold String_as_OT.eq in Heqc. congruence.
  * lia.
Qed.

Lemma Val_ltb_irrefl :
  forall v, v <ᵥ v = false.
Proof.
  valinduction; auto; simpl.
  * now apply Lit_ltb_irrefl.
  (* * now apply Nat.ltb_irrefl. *)
  * now rewrite Val_eqb_refl.
  * rewrite Nat.eqb_refl, Nat.ltb_irrefl. simpl.
    induction l; simpl; auto.
    rewrite Val_eqb_refl. apply IHl. now inv IHv.
  * rewrite Nat.eqb_refl, Nat.ltb_irrefl. simpl.
    apply Bool.orb_false_iff. split.
    {
      induction IHv; auto.
      destruct x. now rewrite Val_eqb_refl, IHIHv.
    }
    {
      apply Bool.andb_false_iff. right.
      induction IHv; auto.
      destruct x. now rewrite Val_eqb_refl, IHIHv.
    }
  * now rewrite Nat.ltb_irrefl.
Qed.

Lemma Val_eqb_ltb_trans :
  forall v1 v2 v3,
    v1 =ᵥ v2 = true -> v2 <ᵥ v3 = true -> v1 <ᵥ v3 = true.
Proof.
  valinduction; intros; try destruct v2, v3; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq in H. now subst.
  (* * apply Nat.eqb_eq in H. now subst. *)
  * apply Bool.andb_true_iff in H as [H_1 H_2].
    break_match_hyp.
    - eapply Val_eqb_trans in Heqb. 2: eassumption.
      rewrite Heqb. eapply IHv1_2; eassumption.
    - rewrite Val_eqb_sym in Heqb.
      eapply Val_eqb_neqb in Heqb as Heqb'. 2: rewrite Val_eqb_sym; eassumption.
      rewrite Val_eqb_sym, Heqb'. eapply IHv1_1; eassumption.
  * assert (length l = length l0). {
      clear -H. generalize dependent l0. induction l; intros; destruct l0; auto; try congruence. simpl.
      apply Bool.andb_true_iff in H as [_ H]. erewrite IHl. reflexivity.
      assumption.
    }
    rewrite <- H1 in *. clear H1.
    apply Bool.orb_true_iff in H0 as [H0 | H0].
    - apply Bool.orb_true_iff. now left.
    - apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.orb_true_iff. right.
      apply Bool.andb_true_iff. split; auto.
      clear H0_1. generalize dependent l0. revert l1.
      induction IHv1; intros; destruct l0, l1; simpl in *; try congruence.
      apply Bool.andb_true_iff in H0 as [H0_1 H0_3].
      break_match_hyp.
      + eapply Val_eqb_trans in Heqb. 2: eassumption. rewrite Heqb.
        eapply IHIHv1; eassumption.
      + rewrite Val_eqb_sym in Heqb, H0_1.
        eapply Val_eqb_neqb in H0_1 as H0_1'. 2: eassumption.
        rewrite Val_eqb_sym, H0_1'. eapply H. 2: eassumption.
        now rewrite Val_eqb_sym.
  * assert (length l = length l0). {
      clear -H. generalize dependent l0. induction l; intros; destruct l0; auto; try congruence. simpl.
      destruct a. congruence.
      destruct a, p.
      do 2 apply Bool.andb_true_iff in H as [_ H].
      simpl. erewrite IHl. reflexivity.
      assumption.
    }
    rewrite <- H1 in *. clear H1.
    apply Bool.orb_true_iff in H0 as [H0 | H0].
    - apply Bool.orb_true_iff. now left.
    - apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.orb_true_iff. right.
      apply Bool.andb_true_iff. split; auto.
      clear H0_1. apply Bool.orb_true_iff in H0_2 as [H0_2 | H0_2].
      {
        apply Bool.orb_true_iff. left. generalize dependent l0. revert l1.
        induction l; intros; destruct l0, l1;
        try destruct a, p; simpl in *; try congruence.
        destruct p0. inv IHv1. destruct H2. simpl in *.
        apply Bool.andb_true_iff in H as [H_1 H_2].
        apply Bool.andb_true_iff in H_2 as [H_2 H_3].
        break_match_hyp.
        * eapply (Val_eqb_trans _ _ _ H_1) in Heqb.
          rewrite Heqb. eapply IHl; eassumption.
        * rewrite Val_eqb_sym in H_1.
          eapply Val_eqb_neqb in H_1 as H_1'. 2: rewrite Val_eqb_sym; eassumption.
          rewrite Val_eqb_sym, H_1'. eapply H0. 2: eassumption.
          now rewrite Val_eqb_sym.
      }
      {
        apply Bool.orb_true_iff. right.
        apply Bool.andb_true_iff in H0_2 as [H0_21 H0_22].
        apply Bool.andb_true_iff. split.
        {
          clear H0_22 IHv1. generalize dependent l0. revert l1.
          induction l; intros; destruct l0, l1;
          try destruct a; try destruct p; simpl in *; try congruence.
          destruct p0; simpl in *.
          apply Bool.andb_true_iff in H as [H_1 H_2].
          apply Bool.andb_true_iff in H_2 as [H_2 H_3].
          destruct Val_eqb eqn:Eq1 in H0_21; try congruence.
          eapply Val_eqb_trans in Eq1. 2: eassumption.
          rewrite Eq1. eapply IHl; eassumption.
        }
        {
          clear H0_21.
          generalize dependent l0. revert l1.
          induction l; intros; destruct l0, l1;
          try destruct a, p; simpl in *; try congruence.
          destruct p0. inv IHv1. destruct H2. simpl in *.
          apply Bool.andb_true_iff in H as [H_1 H_2].
          apply Bool.andb_true_iff in H_2 as [H_2 H_3].
          break_match_hyp.
          * eapply Val_eqb_trans in Heqb. 2: eassumption.
            rewrite Heqb. eapply IHl; eassumption.
          * rewrite Val_eqb_sym in H_2.
            eapply Val_eqb_neqb in H_2 as H_2'. 2: rewrite Val_eqb_sym; eassumption.
            rewrite Val_eqb_sym in H_2'. rewrite H_2'.
            eapply H1. 2: eassumption.
            now rewrite Val_eqb_sym.
        }
      }
  * apply Nat.eqb_eq in H. now subst.
Qed.

Lemma Val_ltb_eqb_trans :
  forall v1 v2 v3,
    v1 <ᵥ v2 = true -> v2 =ᵥ v3 = true -> v1 <ᵥ v3 = true.
Proof.
  valinduction; try intros v2 v3 H0 H; intros; try destruct v2, v3; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq in H. now subst.
  (* * apply Nat.eqb_eq in H. now subst. *)
  * apply Bool.andb_true_iff in H as [H_1 H_2].
    break_match_hyp.
    - eapply Val_eqb_trans in H_1. 2: eassumption.
      rewrite H_1. eapply IHv1_2; eassumption.
    - rewrite Val_eqb_sym in H_1.
      eapply Val_eqb_neqb in Heqb as Heqb'. 2: rewrite Val_eqb_sym; eassumption.
      rewrite Heqb'. eapply IHv1_1; try eassumption.
      now rewrite Val_eqb_sym.
  * assert (length l0 = length l1). {
      clear -H. generalize dependent l0. induction l1; intros; destruct l0; auto; try congruence. simpl.
      apply Bool.andb_true_iff in H as [_ H]. erewrite IHl1. reflexivity.
      assumption.
    }
    rewrite <- H1 in *. clear H1.
    apply Bool.orb_true_iff in H0 as [H0 | H0].
    - apply Bool.orb_true_iff. now left.
    - apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.orb_true_iff. right.
      apply Bool.andb_true_iff. split; auto.
      clear H0_1. generalize dependent l0. revert l1.
      induction IHv1; intros; destruct l0, l1; simpl in *; try congruence.
      apply Bool.andb_true_iff in H0 as [H0_1 H0_3].
      break_match_hyp.
      + eapply Val_eqb_trans in H0_1. 2: eassumption. rewrite H0_1.
        eapply IHIHv1; eassumption.
      + eapply Val_eqb_neqb in H0_1 as H0_1'. 2: eassumption.
        rewrite H0_1'. eapply H; eassumption.
  * assert (length l0 = length l1). {
      clear -H. generalize dependent l0. induction l1; intros; destruct l0; auto; try congruence. simpl.
      destruct p. congruence.
      destruct a, p.
      do 2 apply Bool.andb_true_iff in H as [_ H].
      simpl. erewrite IHl1. reflexivity.
      assumption.
    }
    rewrite <- H1 in *. clear H1.
    apply Bool.orb_true_iff in H0 as [H0 | H0].
    - apply Bool.orb_true_iff. now left.
    - apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.orb_true_iff. right.
      apply Bool.andb_true_iff. split; auto.
      clear H0_1. apply Bool.orb_true_iff in H0_2 as [H0_2 | H0_2].
      {
        apply Bool.orb_true_iff. left. generalize dependent l0. revert l1.
        induction l; intros; destruct l0, l1;
        try destruct p; try destruct p0; simpl in *; try congruence.
        destruct a. inv IHv1. destruct H2. simpl in *.
        apply Bool.andb_true_iff in H as [H_1 H_2].
        apply Bool.andb_true_iff in H_2 as [H_2 H_3].
        break_match_hyp.
        * eapply (Val_eqb_trans _ _ _ Heqb) in H_1.
          rewrite H_1. eapply IHl; eassumption.
        * eapply Val_eqb_neqb in H_1 as H_1'. 2: eassumption.
          rewrite H_1'. eapply H0; eassumption.
      }
      {
        apply Bool.orb_true_iff. right.
        apply Bool.andb_true_iff in H0_2 as [H0_21 H0_22].
        apply Bool.andb_true_iff. split.
        {
          clear H0_22 IHv1. generalize dependent l0. revert l1.
          induction l; intros; destruct l0, l1;
          try destruct a; try destruct p; simpl in *; try congruence.
          destruct p0; simpl in *.
          apply Bool.andb_true_iff in H as [H_1 H_2].
          apply Bool.andb_true_iff in H_2 as [H_2 H_3].
          destruct Val_eqb eqn:Eq1 in H0_21; try congruence.
          eapply Val_eqb_trans in H_1. 2: eassumption.
          rewrite H_1. eapply IHl; eassumption.
        }
        {
          clear H0_21.
          generalize dependent l0. revert l1.
          induction l; intros; destruct l0, l1;
          try destruct a; try destruct p; try destruct p0; simpl in *; try congruence.
          inv IHv1. destruct H2. simpl in *.
          apply Bool.andb_true_iff in H as [H_1 H_2].
          apply Bool.andb_true_iff in H_2 as [H_2 H_3].
          break_match_hyp.
          * eapply Val_eqb_trans in H_2. 2: eassumption.
            rewrite H_2. eapply IHl; eassumption.
          * eapply Val_eqb_neqb in H_2 as H_2'. 2: eassumption.
            rewrite H_2'. eapply H1; eassumption.
        }
      }
  * apply Nat.eqb_eq in H. now subst.
Qed.

Lemma Val_ltb_both :
  forall v1 v2, v1 <ᵥ v2 = true -> v2 <ᵥ v1 = true -> False.
Proof.
  valinduction; try intros v2 v3 H0 H; intros; try destruct v2; try destruct v3; simpl in *; try congruence; auto.
  * destruct l, l0; simpl in *.
    3-4: lia.
    unfold string_ltb in H, H0.
    rewrite String_as_OT.cmp_antisym in H.
    destruct String_as_OT.cmp; simpl in *; congruence.
    congruence.
  (* * apply Nat.ltb_lt in H, H0. lia. *)
  * break_match_hyp.
    - rewrite Val_eqb_sym, Heqb in H. now apply IHv1_2 in H.
    - rewrite Val_eqb_sym, Heqb in H. now apply IHv1_1 in H.
  * apply Bool.orb_true_iff in H, H0; destruct H, H0.
    - apply Nat.ltb_lt in H, H0. lia.
    - apply Bool.andb_true_iff in H0 as [H0 _].
      apply Nat.ltb_lt in H. apply Nat.eqb_eq in H0. lia.
    - apply Bool.andb_true_iff in H as [H _].
      apply Nat.ltb_lt in H0. apply Nat.eqb_eq in H. lia.
    - apply Bool.andb_true_iff in H as [_ H].
      apply Bool.andb_true_iff in H0 as [_ H0].
      generalize dependent l0. induction IHv1; intros; destruct l0; simpl in *; try congruence.
      break_match_hyp.
      + rewrite Val_eqb_sym, Heqb in H0. eapply IHIHv1; eassumption.
      + rewrite Val_eqb_sym, Heqb in H0. eapply H; eassumption.
  * apply Bool.orb_true_iff in H, H0; destruct H, H0.
    - apply Nat.ltb_lt in H, H0. lia.
    - apply Bool.andb_true_iff in H0 as [H0 _].
      apply Nat.ltb_lt in H. apply Nat.eqb_eq in H0. lia.
    - apply Bool.andb_true_iff in H as [H _].
      apply Nat.ltb_lt in H0. apply Nat.eqb_eq in H. lia.
    - apply Bool.andb_true_iff in H as [_ H].
      apply Bool.andb_true_iff in H0 as [_ H0].
      apply Bool.orb_true_iff in H, H0. destruct H, H0.
      {
        generalize dependent l0. induction IHv1; intros; destruct l0; try destruct p; try destruct x; simpl in *; try congruence.
        break_match_hyp.
        + rewrite Val_eqb_sym, Heqb in H0. eapply IHIHv1; eassumption.
        + rewrite Val_eqb_sym, Heqb in H0.
          destruct H. eapply H; eassumption.
      }
      {
        apply Bool.andb_true_iff in H0 as [H0 _].
        generalize dependent l0. induction IHv1; intros; destruct l0; try destruct p; try destruct x; simpl in *; try congruence.
        break_match_hyp.
        - rewrite Val_eqb_sym, Heqb in H0. eapply IHIHv1; eassumption.
        - congruence.
      }
      {
        apply Bool.andb_true_iff in H as [H _].
        generalize dependent l0. induction IHv1; intros; destruct l0; try destruct p; try destruct x; simpl in *; try congruence.
        break_match_hyp.
        - rewrite Val_eqb_sym, Heqb in H0. eapply IHIHv1; eassumption.
        - rewrite Val_eqb_sym, Heqb in H0. congruence.
      }
      {
        apply Bool.andb_true_iff in H as [_ H].
        apply Bool.andb_true_iff in H0 as [_ H0].
        generalize dependent l0. induction IHv1; intros; destruct l0; try destruct p; try destruct x; simpl in *; try congruence.
        break_match_hyp.
        - rewrite Val_eqb_sym, Heqb in H0. eapply IHIHv1; eassumption.
        - rewrite Val_eqb_sym, Heqb in H0. destruct H.
          eapply H2; eassumption.
      }
  * apply Nat.ltb_lt in H, H0. lia.
Qed.

Corollary Val_eqb_ltb :
  forall v1 v2, v1 =ᵥ v2 = true -> v1 <ᵥ v2 = false.
Proof.
  intros. apply Bool.not_true_is_false. intro.
  rewrite Val_eqb_sym in H.
  eapply Val_eqb_ltb_trans in H. 2: eassumption.
  rewrite Val_ltb_irrefl in H. congruence.
Qed.

Corollary Val_ltb_eqb :
  forall v1 v2, v1 <ᵥ v2 = true -> v1 =ᵥ v2 = false.
Proof.
  intros. apply Bool.not_true_is_false. intro.
  eapply Val_eqb_ltb_trans in H. 2: rewrite Val_eqb_sym; eassumption.
  rewrite Val_ltb_irrefl in H. congruence.
Qed.

Lemma Val_ltb_trans :
  forall v1 v2 v3,
  v1 <ᵥ v2 = true -> v2 <ᵥ v3 = true ->
  v1 <ᵥ v3 = true.
Proof.
  valinduction; intros; simpl; try destruct v3; auto.
  all: try now (destruct v2; simpl in *; congruence).
  * destruct v2; simpl in *; try congruence.
    destruct l, l1, l0; simpl in *; try congruence.
    - unfold string_ltb in *. do 2 break_match_hyp; try congruence.
      apply OrderedTypeEx.String_as_OT.compare_helper_lt in Heqc.
      apply OrderedTypeEx.String_as_OT.compare_helper_lt in Heqc0.
      pose proof (OrderedTypeEx.String_as_OT.lt_trans _ _ _ Heqc0 Heqc).
      apply OrderedTypeEx.String_as_OT.cmp_lt in H1. now rewrite H1.
    - lia.
  (* * destruct v2; simpl in *; try congruence.
    apply Nat.ltb_lt in H, H0. apply Nat.ltb_lt. lia. *)
  * simpl in *. destruct v2; simpl in *; try congruence.
    do 2 break_match_hyp.
    - rewrite (Val_eqb_trans _ _ _ Heqb0 Heqb).
      eapply IHv1_2; eassumption.
    - break_match_goal.
      + rewrite Val_eqb_sym in Heqb.
        eapply Val_eqb_trans in Heqb. 2: exact Heqb1.
        congruence.
      + eapply Val_ltb_eqb_trans in Heqb. 2: eassumption. assumption.
    - break_match_goal.
      + rewrite Val_eqb_sym in Heqb1.
        eapply Val_ltb_eqb_trans in Heqb1. 2: eassumption.
        apply Val_ltb_eqb in Heqb1. rewrite Val_eqb_sym in Heqb0.
        congruence.
      + eapply Val_eqb_ltb_trans in Heqb0. 2: exact H0. assumption.
    - break_match_goal.
      + eapply Val_ltb_eqb_trans in H0. 2: rewrite Val_eqb_sym; exact Heqb1.
        exfalso. eapply Val_ltb_both; eassumption.
      + eapply IHv1_1; eassumption.
  * destruct v2; simpl in *; try congruence.
    apply Bool.orb_true_iff in H as [H | H];
    apply Bool.orb_true_iff in H0 as [H0 | H0].
    - apply Nat.ltb_lt in H, H0.
      apply Bool.orb_true_iff. left. apply Nat.ltb_lt. lia.
    - apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Nat.eqb_eq in H0_1.
      apply Nat.ltb_lt in H.
      apply Bool.orb_true_iff. left. apply Nat.ltb_lt. lia.
    - apply Bool.andb_true_iff in H as [H_1 H_2].
      apply Nat.eqb_eq in H_1.
      apply Nat.ltb_lt in H0.
      apply Bool.orb_true_iff. left. apply Nat.ltb_lt. lia.
    - apply Bool.orb_true_iff. right.
      apply Bool.andb_true_iff.
      apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.andb_true_iff in H as [H_1 H_2].
      apply Nat.eqb_eq in H_1, H0_1. rewrite <- H_1 in H0_1.
      split.
      apply Nat.eqb_eq. lia.
      generalize dependent l1. generalize dependent l0.
      induction IHv1; simpl; auto; intros; destruct l0, l1; 
        simpl in *; try congruence.
      do 2 break_match_hyp.
      + eapply Val_eqb_trans in Heqb. 2: exact Heqb0. rewrite Heqb.
        eapply IHIHv1; try eassumption; lia.
      + break_match_goal.
        ** rewrite Val_eqb_sym in Heqb1. eapply Val_eqb_trans in Heqb1. 2: eassumption.
           rewrite Val_eqb_sym in Heqb1. congruence.
        ** eapply Val_ltb_eqb_trans; eassumption.
      + break_match_goal.
        ** rewrite Val_eqb_sym in Heqb1. eapply Val_ltb_eqb_trans in Heqb1. 2: eassumption.
           rewrite Val_eqb_sym in Heqb0. apply Val_eqb_ltb in Heqb0. congruence.
        ** eapply Val_eqb_ltb_trans; eassumption.
      + break_match_goal.
        ** rewrite Val_eqb_sym in Heqb1. eapply Val_ltb_eqb_trans in Heqb1. 2: eassumption.
           exfalso. eapply Val_ltb_both; eassumption.
        ** eapply H; eassumption.
  * destruct v2; simpl in *; try congruence.
    apply Bool.orb_true_iff in H as [H | H];
    apply Bool.orb_true_iff in H0 as [H0 | H0].
    - apply Nat.ltb_lt in H, H0.
      apply Bool.orb_true_iff. left. apply Nat.ltb_lt. lia.
    - apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Nat.eqb_eq in H0_1.
      apply Nat.ltb_lt in H.
      apply Bool.orb_true_iff. left. apply Nat.ltb_lt. lia.
    - apply Bool.andb_true_iff in H as [H_1 H_2].
      apply Nat.eqb_eq in H_1.
      apply Nat.ltb_lt in H0.
      apply Bool.orb_true_iff. left. apply Nat.ltb_lt. lia.
    - apply Bool.orb_true_iff. right.
      apply Bool.andb_true_iff.
      apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
      apply Bool.andb_true_iff in H as [H_1 H_2].
      apply Nat.eqb_eq in H_1, H0_1. rewrite <- H_1 in H0_1.
      split.
      apply Nat.eqb_eq. lia.
      (* map comparison is based first on keys, then on values, 
         thus a different stategy is needed to compare them: *)
      apply Bool.orb_true_iff in H_2 as [H_2 | H_2];
      apply Bool.orb_true_iff in H0_2 as [H0_2 | H0_2];
      try apply Bool.andb_true_iff in H0_2 as [H0_21 H0_22].
      {
        apply Bool.orb_true_iff. left.
        generalize dependent l1. generalize dependent l0.
        induction l; destruct l0, l1; simpl; intros; try congruence;
        destruct a, p; try congruence.
        destruct p0. inv IHv1. destruct H1 as [H1_1 H1_2].
        simpl in *. do 2 break_match_hyp.
        * eapply Val_eqb_trans in Heqb. 2: eassumption.
          erewrite Heqb, IHl. 5: exact H_2. 5: exact H0_2.
          all: auto; lia.
        * eapply Val_eqb_neqb in Heqb as Heqb'. 2: eassumption.
          rewrite Heqb'. eapply Val_ltb_eqb_trans; eassumption.
        * rewrite Val_eqb_sym in Heqb. eapply Val_eqb_neqb in Heqb as Heqb'.
          2: rewrite Val_eqb_sym; eassumption.
          rewrite Val_eqb_sym, Heqb'.
          eapply Val_eqb_ltb_trans; eassumption.
        * eapply H1_1 in H0_2. 2: eassumption.
          apply Val_ltb_eqb in H0_2 as H0_2'. rewrite H0_2'. assumption.
      }
      {
        apply Bool.orb_true_iff. left. clear H0_22.
        generalize dependent l1. generalize dependent l0.
        induction l; destruct l0, l1; simpl; intros; try congruence.
        destruct p0, p; simpl in *. destruct a.
        inv IHv1. destruct H1. simpl in *.
        destruct Val_eqb eqn:H0_23 in H0_21; try congruence.
        break_match_hyp.
        * eapply Val_eqb_trans in H0_23. 2: eassumption. rewrite H0_23.
          erewrite IHl. 5: eassumption.
          all: auto;lia.
        * eapply Val_eqb_neqb in Heqb as Heqb'. 2: eassumption.
          rewrite Heqb'. eapply Val_ltb_eqb_trans; eassumption.
      }
      {
        apply Bool.andb_true_iff in H_2 as [H_21 H_22].
        clear H_22.
        apply Bool.orb_true_iff. left.
        generalize dependent l1. generalize dependent l0.
        induction l; destruct l0, l1; simpl; intros; try congruence.
        destruct p; auto; congruence.
        destruct a, p, p0.
        inv IHv1. destruct H1. simpl in *.
        destruct Val_eqb eqn:H_23 in H_21; try congruence.
        break_match_hyp.
        * eapply Val_eqb_trans in Heqb. 2: eassumption. rewrite Heqb.
          erewrite IHl. 5: eassumption.
          all: auto;lia.
        * rewrite Val_eqb_sym in Heqb, H_23.
          eapply Val_eqb_neqb in H_23 as H_23'. 2: eassumption.
          rewrite Val_eqb_sym, H_23'. rewrite Val_eqb_sym in H_23.
          eapply Val_eqb_ltb_trans; eassumption.
      }
      {
        apply Bool.orb_true_iff. right.
        apply Bool.andb_true_iff in H_2 as [H_21 H_22].
        apply Bool.andb_true_iff. split.
        {
          clear H_22 H0_22 H_1 H0_1 IHv1.
          generalize dependent l1. generalize dependent l0.
          induction l; destruct l0, l1; simpl; intros;
          try destruct p; try destruct a; try congruence.
          destruct p0; simpl in *.
          do 2 break_match_hyp; try congruence.
          eapply Val_eqb_trans in Heqb. 2: eassumption.
          erewrite Heqb, IHl; auto; eassumption.
        }
        {
          clear H_21 H0_21 H0_1 H_1.
          generalize dependent l1. generalize dependent l0.
          induction l; destruct l0, l1; simpl; intros;
          try destruct p; try destruct a; try congruence.
          destruct p0. inv IHv1. destruct H1. simpl in *.
          do 2 break_match_hyp.
          * eapply Val_eqb_trans in Heqb. 2: eassumption. erewrite Heqb, IHl.
            3-4: eassumption. all: auto.
          * eapply Val_eqb_neqb in Heqb0 as Heqb0'. 2: eassumption.
            rewrite Heqb0'. eapply Val_ltb_eqb_trans; eassumption.
          * rewrite Val_eqb_sym in Heqb, Heqb0.
            eapply Val_eqb_neqb in Heqb as Heqb'. 2: eassumption.
            rewrite Val_eqb_sym, Heqb'.
            rewrite Val_eqb_sym in Heqb0.
            eapply Val_eqb_ltb_trans; eassumption.
          * eapply H0 in H0_22. 2: eassumption.
            apply Val_ltb_eqb in H0_22 as H0_22'. rewrite H0_22'.
            assumption.
        }        
      }
  * destruct v2; simpl in *; try congruence.
    apply Nat.ltb_lt in H, H0. apply Nat.ltb_lt. lia.
Qed.

Lemma Val_geb_eqb_trans :
  forall v1 v2 v3,
    v1 =ᵥ v2 = true -> v2 <ᵥ v3 = false ->
    v1 <ᵥ v3 = false.
Proof.
  valinduction; intros; simpl; try destruct v3; auto.
  all: try now (destruct v2; simpl in *; congruence).
  * destruct v2; simpl in *; try congruence.
    destruct l, l1, l0; simpl in *; try congruence.
    - destruct string_dec; subst; try congruence.
    - lia.
  (* * destruct v2; simpl in *; try congruence.
    apply Nat.eqb_eq in H. now subst. *)
  * destruct v2; simpl in *; try congruence.
    apply Bool.andb_true_iff in H as [H_1 H_2].
    break_match_hyp.
    - eapply Val_eqb_trans in Heqb. 2: exact H_1. rewrite Heqb.
      eapply IHv1_2; eassumption.
    - rewrite Val_eqb_sym in H_1. eapply Val_eqb_neqb in H_1 as H_1'.
      2: rewrite Val_eqb_sym; eassumption.
      rewrite Val_eqb_sym, H_1'. eapply IHv1_1; try eassumption.
      now rewrite Val_eqb_sym.
  * destruct v2; simpl in *; try congruence.
    assert (length l = length l1). {
      clear -H. generalize dependent l. induction l1; intros; destruct l; auto; try congruence. simpl.
      apply Bool.andb_true_iff in H as [_ H]. erewrite IHl1. reflexivity.
      assumption.
    }
    apply Bool.orb_false_iff in H0 as [H0_1 H0_2].
    apply Bool.orb_false_iff; split. now rewrite H1.
    apply Bool.andb_false_iff in H0_2 as [H0_2 | H0_2].
    1: apply Bool.andb_false_iff; left; now rewrite H1.
    apply Bool.andb_false_iff; right. clear H0_1 H1.
    generalize dependent l1. revert l0.
    induction IHv1; intros; destruct l0, l1; simpl in *; try congruence.
    apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
    break_match_hyp.
    - eapply Val_eqb_trans in Heqb. 2: eassumption. rewrite Heqb.
      eapply IHIHv1; eassumption.
    - rewrite Val_eqb_sym in H0_11. eapply Val_eqb_neqb in H0_11 as H0_11'.
      2: rewrite Val_eqb_sym; eassumption. rewrite Val_eqb_sym, H0_11'.
      eapply H. rewrite Val_eqb_sym. all: eassumption.
  * destruct v2; simpl in *; try congruence.
    assert (length l = length l1). {
      clear -H. generalize dependent l. induction l1; intros; destruct l; auto; 
      try destruct p; try congruence. simpl.
      destruct a.
      apply Bool.andb_true_iff in H as [_ H].
      apply Bool.andb_true_iff in H as [_ H]. erewrite IHl1. reflexivity.
      assumption.
    }
    apply Bool.orb_false_iff in H0 as [H0_1 H0_2].
    apply Bool.orb_false_iff; split. now rewrite H1.
    apply Bool.andb_false_iff in H0_2 as [H0_2 | H0_2].
    1: apply Bool.andb_false_iff; left; now rewrite H1.
    apply Bool.andb_false_iff; right. clear H0_1 H1.
    apply Bool.orb_false_iff in H0_2 as [H0_21 H0_22].
    apply Bool.orb_false_iff. split.
    {
      clear H0_22. generalize dependent l1. revert l0.
      induction IHv1; intros; destruct l0, l1; 
      try destruct x; try destruct p; try destruct p0; simpl in *; try congruence.
      apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
      apply Bool.andb_true_iff in H0_12 as [H0_12 H0_13].
      break_match_hyp.
      - eapply Val_eqb_trans in Heqb. 2: eassumption. rewrite Heqb.
        eapply IHIHv1; eassumption.
      - rewrite Val_eqb_sym in H0_11. eapply Val_eqb_neqb in H0_11 as H0_11'.
        2: rewrite Val_eqb_sym; eassumption. rewrite Val_eqb_sym, H0_11'.
        eapply H. rewrite Val_eqb_sym. all: eassumption.
    }
    {
      clear H0_21. apply Bool.andb_false_iff in H0_22 as [H0_22 | H0_22].
      * apply Bool.andb_false_iff. left. generalize dependent l1. revert l0.
        induction IHv1; intros; destruct l0, l1; 
        try destruct x; try destruct p; try destruct p0; simpl in *; try congruence.
        apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
        apply Bool.andb_true_iff in H0_12 as [H0_12 H0_13].
        break_match_hyp.
        - eapply Val_eqb_trans in Heqb. 2: eassumption. rewrite Heqb.
          eapply IHIHv1; eassumption.
        - rewrite Val_eqb_sym in H0_11. eapply Val_eqb_neqb in H0_11 as H0_11'.
          2: rewrite Val_eqb_sym; eassumption. rewrite Val_eqb_sym, H0_11'.
          reflexivity.
      * apply Bool.andb_false_iff. right. generalize dependent l1. revert l0.
        induction IHv1; intros; destruct l0, l1; 
        try destruct x; try destruct p; try destruct p0; simpl in *; try congruence.
        apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
        apply Bool.andb_true_iff in H0_12 as [H0_12 H0_13].
        break_match_hyp.
        - eapply Val_eqb_trans in Heqb. 2: eassumption. rewrite Heqb.
          eapply IHIHv1; eassumption.
        - rewrite Val_eqb_sym in H0_12. eapply Val_eqb_neqb in H0_12 as H0_12'.
          2: rewrite Val_eqb_sym; eassumption. rewrite Val_eqb_sym, H0_12'.
          eapply H. rewrite Val_eqb_sym. all: eassumption.
    }
  * destruct v2; simpl in *; try congruence.
    apply Nat.eqb_eq in H. now subst.
Qed.

Lemma Val_eqb_geb_trans :
  forall v1 v2 v3,
    v1 <ᵥ v2 = false -> v2 =ᵥ v3 = true ->
    v1 <ᵥ v3 = false.
Proof.
  valinduction; intros; simpl; try destruct v3; auto.
  all: try now (destruct v2; simpl in *; congruence).
  * destruct v2; simpl in *; try congruence.
    destruct l, l1, l0; simpl in *; try congruence.
    - destruct string_dec; subst; try congruence.
    - lia.
  (* * destruct v2; simpl in *; try congruence.
    apply Nat.eqb_eq in H0. now subst. *)
  * destruct v2; simpl in *; try congruence.
    apply Bool.andb_true_iff in H0 as [H0_1 H0_2].
    break_match_hyp.
    - eapply Val_eqb_trans in H0_1. 2: exact Heqb. rewrite H0_1.
      eapply IHv1_2; eassumption.
    - eapply Val_eqb_neqb in H0_1 as H0_1'.
      2: eassumption.
      rewrite H0_1'. eapply IHv1_1; try eassumption.
  * destruct v2; simpl in *; try congruence.
    assert (length l1 = length l0). {
      clear -H0. generalize dependent l0. induction l1; intros; destruct l0; auto; try congruence. simpl.
      apply Bool.andb_true_iff in H0 as [_ H0]. erewrite IHl1. reflexivity.
      assumption.
    }
    apply Bool.orb_false_iff in H as [H_1 H_2].
    apply Bool.orb_false_iff; split. now rewrite <- H1.
    apply Bool.andb_false_iff in H_2 as [H_2 | H_2].
    1: apply Bool.andb_false_iff; left; now rewrite <- H1.
    apply Bool.andb_false_iff; right. clear H_1 H1.
    generalize dependent l1. revert l0.
    induction IHv1; intros; destruct l0, l1; simpl in *; try congruence.
    apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
    break_match_hyp.
    - eapply Val_eqb_trans in H0_11. 2: eassumption. rewrite H0_11.
      eapply IHIHv1; eassumption.
    - eapply Val_eqb_neqb in H0_11 as H0_11'.
      2: eassumption. rewrite H0_11'.
      eapply H. all: eassumption.
  * destruct v2; simpl in *; try congruence.
    assert (length l1 = length l0). {
      clear -H0. generalize dependent l0. induction l1; intros; destruct l0; auto; 
      try destruct a; try destruct p; try congruence. simpl.
      apply Bool.andb_true_iff in H0 as [_ H0].
      apply Bool.andb_true_iff in H0 as [_ H0]. erewrite IHl1. reflexivity.
      assumption.
    }
    apply Bool.orb_false_iff in H as [H_1 H_2].
    apply Bool.orb_false_iff; split. now rewrite <- H1.
    apply Bool.andb_false_iff in H_2 as [H_2 | H_2].
    1: apply Bool.andb_false_iff; left; now rewrite <- H1.
    apply Bool.andb_false_iff; right. clear H_1 H1.
    apply Bool.orb_false_iff in H_2 as [H_21 H_22].
    apply Bool.orb_false_iff. split.
    {
      clear H_22. generalize dependent l1. revert l0.
      induction IHv1; intros; destruct l0, l1; 
      try destruct x; try destruct p; try destruct p0; simpl in *; try congruence.
      apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
      apply Bool.andb_true_iff in H0_12 as [H0_12 H0_13].
      break_match_hyp.
      - eapply Val_eqb_trans in H0_11. 2: eassumption. rewrite H0_11.
        eapply IHIHv1; eassumption.
      - eapply Val_eqb_neqb in H0_11 as H0_11'.
        2: eassumption. rewrite H0_11'.
        eapply H. all: eassumption.
    }
    {
      clear H_21. apply Bool.andb_false_iff in H_22 as [H_22 | H_22].
      * apply Bool.andb_false_iff. left. generalize dependent l1. revert l0.
        induction IHv1; intros; destruct l0, l1; 
        try destruct x; try destruct p; try destruct p0; simpl in *; try congruence.
        apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
        apply Bool.andb_true_iff in H0_12 as [H0_12 H0_13].
        break_match_hyp.
        - eapply Val_eqb_trans in H0_11. 2: eassumption. rewrite H0_11.
          eapply IHIHv1; eassumption.
        - eapply Val_eqb_neqb in H0_11 as H0_11'.
          2: eassumption. rewrite H0_11'.
          reflexivity.
      * apply Bool.andb_false_iff. right. generalize dependent l1. revert l0.
        induction IHv1; intros; destruct l0, l1; 
        try destruct x; try destruct p; try destruct p0; simpl in *; try congruence.
        apply Bool.andb_true_iff in H0 as [H0_11 H0_12].
        apply Bool.andb_true_iff in H0_12 as [H0_12 H0_13].
        break_match_hyp.
        - eapply Val_eqb_trans in H0_12. 2: eassumption. rewrite H0_12.
          eapply IHIHv1; eassumption.
        - eapply Val_eqb_neqb in H0_12 as H0_12'.
          2: eassumption. rewrite H0_12'.
          eapply H. all: eassumption.
    }
  * destruct v2; simpl in *; try congruence.
    apply Nat.eqb_eq in H0. now subst.
Qed.
