(**
  This file contains decidable and boolean equality definitions for the syntax
  of Core Erlang, together with the boolean less-than ordering of values (which
  simulates Erlang's term order). It also proves several theorems about these
  and their connection to definitional equality.
*)

From CoreErlang Require Export Induction Bitstrings.

From Stdlib Require Import Structures.OrderedTypeEx.
Import Structures.OrderedTypeEx.String_as_OT.

Import ListNotations.

(** Boolean equality for BinType, BinSign, BinEnd, and their basic properties. *)
Scheme Equality for BinType.
Scheme Equality for BinSign.
Scheme Equality for BinEnd.

Lemma BinType_eqb_refl :
  forall l, BinType_beq l l = true.
Proof.
  destruct l; now simpl.
Qed.

Lemma BinSign_eqb_refl :
  forall l, BinSign_beq l l = true.
Proof.
  destruct l; now simpl.
Qed.

Lemma BinEnd_eqb_refl :
  forall l, BinEnd_beq l l = true.
Proof.
  destruct l; now simpl.
Qed.

Lemma BinType_eqb_eq :
  forall l1 l2, BinType_beq l1 l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2; split; intros; inv H; reflexivity.
Qed.

Lemma BinSign_eqb_eq :
  forall l1 l2, BinSign_beq l1 l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2; split; intros; inv H; reflexivity.
Qed.

Lemma BinEnd_eqb_eq :
  forall l1 l2, BinEnd_beq l1 l2 = true <-> l1 = l2.
Proof.
  destruct l1, l2; split; intros; inv H; reflexivity.
Qed.

Lemma BinType_eqb_sym :
  forall l1 l2, BinType_beq l1 l2 = BinType_beq l2 l1.
Proof.
  destruct l1, l2; simpl; auto.
Qed.

Lemma BinSign_eqb_sym :
  forall l1 l2, BinSign_beq l1 l2 = BinSign_beq l2 l1.
Proof.
  destruct l1, l2; simpl; auto.
Qed.

Lemma BinEnd_eqb_sym :
  forall l1 l2, BinEnd_beq l1 l2 = BinEnd_beq l2 l1.
Proof.
  destruct l1, l2; simpl; auto.
Qed.


(** Decidable and boolean equality for products and Segments, and
    corresponding theorems. For the decidable equality of products, stdpp's
    `prod_eq_dec` is used. *)
Section Basic_Eq_Dec.
  Context {A B : Type}.

  Hypothesis A_eq_dec : forall a1 a2 : A, {a1 = a2} + {a1 <> a2}.
  Hypothesis B_eq_dec : forall b1 b2 : B, {b1 = b2} + {b1 <> b2}.

  (** Boolean equality of pairs, based on the boolean equalities of the
      components. *)
  Definition prod_eqb (eqx : A -> A -> bool) (eqy : B -> B -> bool) (p1 p2 : A * B) :=
  match p1, p2 with
  | (x, y), (x', y') => andb (eqx x x') (eqy y y')
  end.

  Theorem prod_eqb_refl eqx eqy p :
    (forall p1, eqx p1 p1 = true) ->
    (forall p2, eqy p2 p2 = true) ->
    prod_eqb eqx eqy p p = true.
  Proof.
    intros. destruct p. simpl.
    rewrite (H a), (H0 b). auto.
  Qed.

  Theorem prod_eqb_eq :
    forall p1 p2 eqx eqy,
    (forall e1 e2, eqx e1 e2 = true <-> e1 = e2) ->
    (forall e1 e2, eqy e1 e2 = true <-> e1 = e2) ->
    prod_eqb eqx eqy p1 p2 = true
  <->
    p1 = p2.
  Proof.
    split.
    * intros. destruct p1, p2.
      simpl in H1. apply andb_prop in H1 as [H1 H2].
      apply H in H1. apply H0 in H2. by subst.
    * intros. subst. apply prod_eqb_refl.
      - intros. by apply H.
      - intros. by apply H0.
  Qed.

  (** Boolean equality of segments, based on the boolean equalities of the
      value and size components. *)
  Definition Segment_eqb (eqA : A -> A -> bool) (eqB : B -> B -> bool)
    (segs1 segs2 : Segment A B) : bool :=
  match segs1, segs2 with
  | Build_Segment val1 size1 unit1 type1 sign1 endian1,
    Build_Segment val2 size2 unit2 type2 sign2 endian2 =>
    eqA val1 val2 && eqB size1 size2 && Nat.eqb unit1 unit2 &&
    BinType_beq type1 type2 && BinSign_beq sign1 sign2 && BinEnd_beq endian1 endian2
  end.

  Proposition Segment_eq_dec : forall s1 s2 : Segment A B, {s1 = s2} + {s1 <> s2}.
  Proof.
    repeat decide equality.
  Defined.

  Theorem Segment_eqb_refl s eqx eqy:
    (forall p1, eqx p1 p1 = true) ->
    (forall p2, eqy p2 p2 = true) ->
    Segment_eqb eqx eqy s s = true.
  Proof.
    intros. destruct s; simpl; rewrite H, H0.
    rewrite Nat.eqb_refl, BinSign_eqb_refl, BinType_eqb_refl, BinEnd_eqb_refl.
    reflexivity.
  Qed.

  Theorem Segment_eqb_eq :
    forall (s1 s2 : Segment A B) eqx eqy,
    (forall e1 e2, eqx e1 e2 = true <-> e1 = e2) ->
    (forall e1 e2, eqy e1 e2 = true <-> e1 = e2) ->
    Segment_eqb eqx eqy s1 s2 = true
  <->
    s1 = s2.
  Proof.
    split.
    * intros. destruct s1 as [v1 sz1 u1 t1 sg1 en1], s2 as [v2 sz2 u2 t2 sg2 en2]. simpl in *.
      repeat (rewrite andb_true_iff in H1; destruct H1 as [H1 ?]).
      rewrite (proj1 (H v1 v2)). 2: assumption.
      rewrite (proj1 (H0 sz1 sz2)). 2: assumption.
      apply BinType_eqb_eq in H4.
      apply BinSign_eqb_eq in H3.
      apply BinEnd_eqb_eq in H2.
      apply Nat.eqb_eq in H5.
      by subst.
    * intros. subst. apply Segment_eqb_refl.
      - intros. by apply H.
      - intros. by apply H0.
  Qed.

End Basic_Eq_Dec.

(** Boolean equality for lists, and corresponding theorems *)
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
    (forall e1 e2, eqf e1 e2 = true <-> e1 = e2) ->
    list_eqb eqf l1 l2 = true
  <->
    l1 = l2.
  Proof.
    split.
    * generalize dependent l2. induction l1; intros.
      - destruct l2; try inversion H0. auto.
      - destruct l2; try inversion H0.
        apply andb_prop in H2. destruct H2. apply H in H1.
        apply IHl1 in H2. subst. auto.
    * intros. subst. apply list_eqb_refl.
      intros. by apply H.
  Qed.

End list_eqb.

(** Decidable and boolean equality for the syntax of Core Erlang. *)
Section Equalities.

  (* NOTE: do not use this (too hard to use in proofs): *)
  (* Scheme Equality for Lit. *)

  (** Boolean equality for literals, and its basic properties. *)
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

  (** Decidable literal equality *)
  Theorem Lit_eq_dec (l1 l2 : Lit) : {l1 = l2} + {l1 <> l2}.
  Proof.
    set string_dec.
    set Z.eq_dec.
    decide equality.
    apply r.
  Defined.


  (** The equality of function signatures *)
  Definition funid_eqb (v1 v2 : FunId) : bool :=
  match v1, v2 with
  | (fid1, num1), (fid2, num2) => Nat.eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (** Extended equality between functions or variables *)
  Definition var_funid_eqb (v1 v2 : Var + FunId) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => Nat.eqb s1 s2
  | inr f1, inr f2 => funid_eqb f1 f2
  | _, _ => false
  end.


  (** Decidability of the expression/value/non-value/pattern equality *)
  Proposition Exp_eq_dec (e1 e2 : Exp) :
    {e1 = e2} + {e1 <> e2}
  with Val_eq_dec (e1 e2 : Val):
    {e1 = e2} + {e1 <> e2}
  with NVal_eq_dec (e1 e2 : NonVal):
    {e1 = e2} + {e1 <> e2}
  with Pat_eq_dec (p1 p2 : Pat) :
    {p1 = p2} + {p1 <> p2}.
  Proof.
    {
      decide equality.
    }
    {
      set (list_eq_dec Val_eq_dec).
      set (Nat.eq_dec).
      set (Lit_eq_dec).
      set (list_eq_dec (@prod_eq_dec _ Val_eq_dec _ Val_eq_dec)).
      decide equality.
      * decide equality.
      * apply (list_eq_dec (@prod_eq_dec _ (@prod_eq_dec _ Nat.eq_dec _ Nat.eq_dec) _ Exp_eq_dec)).
      * apply bvn_eq_dec.
    }
    {
      set (list_eq_dec Exp_eq_dec).
      set (string_dec).
      set (Nat.eq_dec).
      set (Lit_eq_dec).
      set (list_eq_dec (@prod_eq_dec _ Exp_eq_dec _ Exp_eq_dec)).
      decide equality.
      * apply (list_eq_dec (@prod_eq_dec _ (@prod_eq_dec _ (list_eq_dec Pat_eq_dec) _ Exp_eq_dec) _ Exp_eq_dec)).
      * apply (list_eq_dec (@prod_eq_dec _ Nat.eq_dec _ Exp_eq_dec)).
      * repeat decide equality.
    }
    {
      set (Lit_eq_dec).
      set (list_eq_dec Pat_eq_dec).
      set (list_eq_dec (@prod_eq_dec _ Pat_eq_dec _ Pat_eq_dec)).
      decide equality.
      apply (list_eq_dec (Segment_eq_dec Pat_eq_dec Val_eq_dec)).
    }
  Defined.

  (** Boolean equality for values. Note that this equality is weakened!
      All PIDs are considered equal, and closures are compared based on
      their reference number. *)
  Fixpoint Val_eqb (e1 e2 : Val) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  (* NOTE: This is deliberate: value equality (and the ordering `Val_ltb`)
     does not depend on the concrete PIDs, so it is invariant under PID
     renaming (see `Concurrent/PIDRenaming.v`). As a consequence, unlike in
     Erlang, `=:=` and `==` hold for any two PIDs, and map keys that differ
     only in PIDs are merged. *)
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
  | VBitstring b1, VBitstring b2 => bvn_eqb b1 b2
  | _, _ => false
  end.

  (** Less-than for strings (lexicographic, based on `String_as_OT.cmp`). *)
  Definition string_ltb (s1 s2 : string) : bool :=
  match cmp s1 s2 with
  | Lt => true
  | _ => false
  end.

  (** Less-than for literals: integers are ordered numerically, atoms
      lexicographically, and every integer is less than every atom. *)
  Definition Lit_ltb (l1 l2 : Lit) : bool :=
  match l1, l2 with
  | Integer x, Integer x' => Z.ltb x x'
  | Atom s, Atom s' => string_ltb s s'
  | Integer x, Atom s => true
  | _, _ => false
  end.

  (** Lexicographic less-than of lists, based on a less-than (`less`) and an
      equality (`eq`) function on the elements. *)
  Section bool_list_ltb.
    Variable A : Type.
    Hypothesis less : A -> A -> bool.
    Hypothesis eq : A -> A -> bool.

    (** Lexicographic less-than: a proper prefix is less than the list. *)
    Fixpoint list_less (a b : list A) : bool :=
    match a, b with
    | [], [] => false
    | x::xs, [] => false
    | [], y::ys => true
    | x::xs, y::ys => if eq x y then list_less xs ys else less x y
    end.

  End bool_list_ltb.

    (** Less-than for values. In Erlang, all values can be compared; this
        function simulates Erlang's term order:
        number < atom < fun < pid < tuple < map < nil < list < bitstring
        (references and ports are not modelled). Similarly to `Val_eqb`,
        closures are compared based on their reference number, and PIDs are
        not ordered. *)
    Fixpoint Val_ltb (k v : Val) : bool :=
    match k, v with
    | VLit l, VLit l' => Lit_ltb l l'
    | VLit _, _ => true
    (* Note: comparison of closures should be based on something, otherwise
             the equivalence definitions would not work as intended for maps:
      if `clos1 = clos2` (while their `id`-s are not equal), then
      `map_insert clos1 (map_insert clos2 []) <> map_insert clos2 (map_insert clos1 [])`
      However, this has to hold for the compatibility property of maps *)
    | VClos _ id _ _, VClos _ id' _ _=> Nat.ltb id id'
    (*| VClos _ id _ _, VClos _ id' _ _=> false (* NOT: not safe comparison! *)*)
    | VClos _ _ _ _, VTuple _ => true
    | VClos _ _ _ _, VPid _ => true
    | VClos _ _ _ _, VMap _ => true
    | VClos _ _ _ _, VNil => true
    | VClos _ _ _ _, VCons _ _ => true
    | VClos _ _ _ _, VBitstring _ => true
    (* NOTE: PIDs are not ordered, see the note in `Val_eqb`. *)
    | VPid p, VPid p' => false
    | VPid _, VTuple _ => true
    | VPid _, VMap _ => true
    | VPid _, VNil => true
    | VPid _, VCons _ _ => true
    | VPid _, VBitstring _ => true
    | VTuple l, VTuple l' => orb (Nat.ltb (length l) (length l')) 
                                (andb (Nat.eqb (length l) (length l')) (list_less Val Val_ltb Val_eqb l l'))
    | VTuple _, VNil => true
    | VTuple _, VMap _ => true
    | VTuple l, VCons _ _ => true
    | VTuple _, VBitstring _ => true
    (** For maps, the comparison is a bit complicated. First, the keys are
        compared, only then the values (if all keys were equal). *)
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
                            (list_eqb Val_eqb (map fst l) (map fst l'))

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
    | VMap _, VBitstring _ => true
    | VNil, VCons _ _ => true
    | VNil, VBitstring _ => true
    | VCons hd tl, VCons hd' tl' => if Val_eqb hd hd' then Val_ltb tl tl' else Val_ltb hd hd'
    | VCons _ _, VBitstring _ => true
    (** Lexicographic comparison, see [bvn_ltb] - using MSB first *)
    | VBitstring b1, VBitstring b2 => bvn_ltb b1 b2
    | _, _ => false
    end.

End Equalities.

(** Notations for the boolean equality and less-than of values. *)
Notation "v1 =ᵥ v2" := (Val_eqb v1 v2) (at level 69, no associativity).
Notation "v1 <ᵥ v2" := (Val_ltb v1 v2) (at level 69, no associativity).

#[global]
Hint Unfold PBoth : core.


(** The following theorems are about the basic properties of value
    equality and ordering. Since these relations do not correspond to
    their syntactical counterparts, the proofs are complex: all of the
    steps that Rocq could handle in Prop need to be done for bool. *)
(** Reflexivity of value equality. *)
Lemma Val_eqb_refl :
  forall v, v =ᵥ v = true.
Proof.
  induction v using Val_ind_weakened with
    (Q := Forall (fun v => v =ᵥ v = true))
    (R := Forall (PBoth (fun v => v =ᵥ v = true))); simpl; auto.
  * now rewrite Lit_eqb_refl.
  * now rewrite IHv1, IHv2.
  * induction IHv; auto. now rewrite H, IHIHv. 
  * induction IHv; auto. destruct x, H. simpl in *.
    now rewrite H, H0, IHIHv.
  * now rewrite Nat.eqb_refl.
  * destruct n; simpl; now do 2 rewrite Nat.eqb_refl.
  * now rewrite Nat.eqb_refl.
  * apply bvn_eqb_refl.
Qed.

(** Symmetry of value equality. *)
Lemma Val_eqb_sym :
  forall v1 v2, v1 =ᵥ v2 = v2 =ᵥ v1.
Proof.
  valinduction; try destruct v2; simpl; auto.
  * now rewrite Lit_eqb_sym.
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
  * apply bvn_eqb_sym.
Qed.

(** Transitivity of value equality. *)
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
  * apply bvn_eqb_eq in H, H0. subst. apply bvn_eqb_refl.
Qed.

(** Non-equality and equality combined results in non-equality. *)
Lemma Val_eqb_neqb :
  forall v1 v2 v3,
    v1 =ᵥ v2 = false -> v2 =ᵥ v3 = true ->
    v1 =ᵥ v3 = false.
Proof.
  valinduction; intros; try destruct v2, v3; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq in H0. now subst.
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
  * apply bvn_eqb_eq in H0. now subst.
Qed.

(** Less-than is irreflexive for literals *)
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

(** Less-than is irreflexive for values *)
Lemma Val_ltb_irrefl :
  forall v, v <ᵥ v = false.
Proof.
  valinduction; auto; simpl.
  * now apply Lit_ltb_irrefl.
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
  * apply bvn_ltb_irrefl.
Qed.

(** Transitivity of equality and less-than for values *)
Lemma Val_eqb_ltb_trans :
  forall v1 v2 v3,
    v1 =ᵥ v2 = true -> v2 <ᵥ v3 = true -> v1 <ᵥ v3 = true.
Proof.
  valinduction; intros; try destruct v2, v3; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq in H. now subst.
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
          destruct Val_eqb eqn:Eq1 in H0_21; simpl in H0_21; try congruence.
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
  * repeat match goal with
           | H : bvn_eqb _ _ = true |- _ => apply bvn_eqb_eq in H; subst
           end. assumption.
Qed.


(** Transitivity of less-than and equality for values *)
Lemma Val_ltb_eqb_trans :
  forall v1 v2 v3,
    v1 <ᵥ v2 = true -> v2 =ᵥ v3 = true -> v1 <ᵥ v3 = true.
Proof.
  valinduction; try intros v2 v3 H0 H; intros; try destruct v2, v3; simpl in *; try congruence; auto.
  * apply Lit_eqb_eq in H. now subst.
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
          destruct Val_eqb eqn:Eq1 in H0_21; simpl in H0_21; try congruence.
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
  * repeat match goal with
           | H : bvn_eqb _ _ = true |- _ => apply bvn_eqb_eq in H; subst
           end. assumption.
Qed.

(** Less-than is asymmetric. *)
Lemma Val_ltb_asym :
  forall v1 v2, v1 <ᵥ v2 = true -> v2 <ᵥ v1 = true -> False.
Proof.
  valinduction; try intros v2 v3 H0 H; intros; try destruct v2; try destruct v3; simpl in *; try congruence; auto.
  * destruct l, l0; simpl in *.
    3-4: lia.
    unfold string_ltb in H, H0.
    rewrite String_as_OT.cmp_antisym in H.
    destruct String_as_OT.cmp; simpl in *; congruence.
    congruence.
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
        - rewrite Val_eqb_sym, Heqb in H1. simpl in H1. eapply IHIHv1; eassumption.
        - rewrite Val_eqb_sym, Heqb in H1. simpl in H1. congruence.
      }
      {
        apply Bool.andb_true_iff in H as [H _].
        generalize dependent l0. induction IHv1; intros; destruct l0; try destruct p; try destruct x; simpl in *; try congruence.
        break_match_hyp.
        - rewrite Val_eqb_sym, Heqb in H0. simpl in H0. eapply IHIHv1; eassumption.
        - rewrite Val_eqb_sym, Heqb in H0. simpl in H0. congruence.
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
  * apply bvn_ltb_asym in H. congruence.
Qed.

(** Value equality means that less-than cannot be satisfied. *)
Corollary Val_eqb_ltb :
  forall v1 v2, v1 =ᵥ v2 = true -> v1 <ᵥ v2 = false.
Proof.
  intros. apply Bool.not_true_is_false. intro.
  rewrite Val_eqb_sym in H.
  eapply Val_eqb_ltb_trans in H. 2: eassumption.
  rewrite Val_ltb_irrefl in H. congruence.
Qed.

(** If one value is less than another, they are not equal. *)
Corollary Val_ltb_eqb :
  forall v1 v2, v1 <ᵥ v2 = true -> v1 =ᵥ v2 = false.
Proof.
  intros. apply Bool.not_true_is_false. intro.
  eapply Val_eqb_ltb_trans in H. 2: rewrite Val_eqb_sym; eassumption.
  rewrite Val_ltb_irrefl in H. congruence.
Qed.

(** Transitivity for less-than for values. *)
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
        exfalso. eapply Val_ltb_asym; eassumption.
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
           exfalso. eapply Val_ltb_asym; eassumption.
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
         thus a different strategy is needed to compare them: *)
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
        destruct Val_eqb eqn:H0_23 in H0_21; simpl in H0_21; try congruence.
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
        destruct Val_eqb eqn:H_23 in H_21; simpl in H_21; try congruence.
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
          apply andb_prop in H_21 as [Hk1 Hl1]. apply andb_prop in H0_21 as [Hk2 Hl2].
          erewrite Val_eqb_trans, IHl; eauto.
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
  * destruct v2; simpl in *; try congruence.
    eapply bvn_ltb_trans; eassumption.
Qed.

(** If two values are equal, and the second is greater than or equal to a
    third, then the first is also greater than or equal to the third. *)
Lemma Val_eqb_geb_trans :
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
        apply Bool.andb_false_iff in H0_22 as [Hk | Hl]; apply Bool.andb_false_iff.
        - left. rewrite Val_eqb_sym in Hk, H0_11 |- *. eapply Val_eqb_neqb; eassumption.
        - right. eapply IHIHv1; eassumption.
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
  * destruct v2; simpl in *; try congruence.
    repeat match goal with
           | H : bvn_eqb _ _ = true |- _ => apply bvn_eqb_eq in H; subst
           end. assumption.
Qed.

(** If a value is greater than or equal to a second one, which is equal to a
    third, then the first is also greater than or equal to the third. *)
Lemma Val_geb_eqb_trans :
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
        apply Bool.andb_false_iff in H_22 as [Hk | Hl]; apply Bool.andb_false_iff.
        - left. eapply Val_eqb_neqb; eassumption.
        - right. eapply IHIHv1; eassumption.
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
  * destruct v2; simpl in *; try congruence.
    repeat match goal with
           | H : bvn_eqb _ _ = true |- _ => apply bvn_eqb_eq in H; subst
           end. assumption.
Qed.

(** For literals, value equality coincides with syntactic equality. *)
Lemma VLit_val_eq: forall v l, v =ᵥ VLit l = true -> v = VLit l.
Proof.
  intros. destruct v; simpl in H; try congruence.
  apply Lit_eqb_eq in H. rewrite H. reflexivity.
Qed.

(** If a value is not equal to a literal, it is syntactically different. *)
Lemma VLit_val_neq: forall v l, v =ᵥ VLit l = false -> v <> VLit l.
Proof.
  intros. intro.
  rewrite H0 in H. rewrite Val_eqb_refl in H. discriminate.
Qed.

(** Value equality is compatible with itself: replacing both arguments with
    equal values does not change the result. *)
Lemma Val_eqb_congr x x' y y' :
  x =ᵥ x' = true -> y =ᵥ y' = true ->
  x =ᵥ y = (x' =ᵥ y').
Proof.
  intros H1 H2. destruct (x =ᵥ y) eqn:E.
  * assert (x' =ᵥ x = true) as A by (rewrite Val_eqb_sym; exact H1).
    pose proof (Val_eqb_trans _ _ _ A E) as A2.
    pose proof (Val_eqb_trans _ _ _ A2 H2) as A3. symmetry. exact A3.
  * destruct (x' =ᵥ y') eqn:E'; auto.
    assert (y' =ᵥ y = true) as B by (rewrite Val_eqb_sym; exact H2).
    pose proof (Val_eqb_trans _ _ _ E' B) as B2.
    pose proof (Val_eqb_trans _ _ _ H1 B2). congruence.
Qed.
