Require Core_Erlang_Induction.
Require Lia.
From Coq Require Classes.EquivDec.

Module Equalities.

Export Core_Erlang_Induction.Induction.

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
  | (fid1, num1), (fid2, num2) => eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (* Extended equality between functions and vars *)
  Definition var_funid_eqb (v1 v2 : Var + FunctionIdentifier) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => eqb s1 s2
  | inr f1, inr f2 => funid_eqb f1 f2
  | _, _ => false
  end.

  Definition Literal_eqb (l1 l2 : Literal) : bool :=
  match l1, l2 with
   | Atom s1, Atom s2 => eqb s1 s2
   | Integer x1, Integer x2 => Z.eqb x1 x2
   | _, _ => false
  end.


  Fixpoint Pattern_eqb (p1 p2 : Pattern) {struct p1} : bool :=
  match p1, p2 with
   | PVar v1, PVar v2 => eqb v1 v2
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

  Fixpoint Expression_eqb (e1 e2 : Expression) : bool :=
  match e1, e2 with
   | EValues l, EValues l' => (fix blist l l' := match l, l' with
                                        | [], [] => true
                                        | x::xs, x'::xs' => andb (Expression_eqb x x') 
                                                                 (blist xs xs')
                                        | _, _ => false
                                        end) l l'
 (*   | ESingle e, ESingle e' => SingleExpression_eqb e e'
   | _, _ => false
  end
  with SingleExpression_eqb (e1 e2 : SingleExpression) : bool :=
  match e1, e2 with *)
   | ENil, ENil => true
   | ELit l, ELit l' => Literal_eqb l l'
   | EVar v, EVar v' => eqb v v'
   | EFunId f, EFunId f' => funid_eqb f f'
   | EFun vl e, EFun vl' e' => list_eqb eqb vl vl' && Expression_eqb e e'
   | ECons hd tl, ECons hd' tl' => Expression_eqb hd hd' && Expression_eqb tl tl'
   | ETuple l, ETuple l' => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | ECall m f l, ECall m' f' l' => Expression_eqb f f' && Expression_eqb m m' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | EPrimOp m f l, EPrimOp m' f' l' => eqb f f' && eqb m m' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | EApp exp l, EApp exp' l' => Expression_eqb exp exp' && (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | ECase e l, ECase e' l' => Expression_eqb e e'
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
   | ELet l e1 e2, ELet l' e1' e2' => list_eqb eqb l l' && Expression_eqb e1 e1' && Expression_eqb e2 e2'
   | ESeq e1 e2, ESeq e1' e2' => andb (Expression_eqb e1 e1') (Expression_eqb e2 e2')
   | ELetRec l e, ELetRec l' e' => 
                                               (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,(y,z))::xs, (x',(y',z'))::xs' => andb (funid_eqb x x') (andb (
                                                     list_eqb eqb
                                                 y y') (andb (Expression_eqb z z') (blist xs xs')))
                                                 | _, _ => false
                                                 end) l l' &&
                                               Expression_eqb e e'
   | EMap l, EMap l' => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,y)::xs, (x',y')::xs' => andb (Expression_eqb x x') (andb (Expression_eqb y y') (blist xs xs'))
                                                 | _, _ => false
                                                 end) l l'
   | ETry e1 vl1 e2 vl2 e3, ETry e1' vl1' e2' vl2' e3' => list_eqb eqb vl1 vl1' && list_eqb eqb vl2 vl2' &&
                                                          Expression_eqb e1 e1' && Expression_eqb e2 e2' &&
                                                          Expression_eqb e3 e3'
   | _, _ => false
  end.


  Fixpoint Value_eqb (e1 e2 : Value) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Literal_eqb l l'
  | VClos env ext id p b, VClos env' ext' id' p' b' => Nat.eqb id id'
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
  | _, _ => false
  end.

(** Properties of var_funid_eqb *)
  Proposition var_funid_eqb_eq (v0 v : Var + FunctionIdentifier):
    var_funid_eqb v0 v = true <-> v0 = v.
  Proof.
    intros. split; intros.
    { destruct v0, v.
      * inversion H. apply eqb_eq in H1. subst. reflexivity.
      * inversion H.
      * inversion H.
      * inversion H. destruct f, f0. inversion H1. apply Bool.andb_true_iff in H2. inversion H2.
        apply eqb_eq in H0. apply Nat.eqb_eq in H3. subst. reflexivity.
    }
    { destruct v, v0.
      * inversion H. subst. simpl. apply eqb_refl.
      * inversion H.
      * inversion H.
      * inversion H. simpl. destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
    }
  Qed.

  Proposition var_funid_eqb_neq (v0 v : Var + FunctionIdentifier):
    var_funid_eqb v0 v = false <-> v0 <> v.
  Proof.
    split; intros.
    { destruct v0, v.
      * simpl in *. apply eqb_neq in H. unfold not in *. intros. apply H. inversion H0. reflexivity.
      * unfold not. intro. inversion H0.
      * unfold not. intro. inversion H0.
      * destruct f, f0. simpl in H. apply Bool.andb_false_iff in H. inversion H.
        - apply eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
        - apply Nat.eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
    }
    { destruct v0, v.
      * simpl in *. apply eqb_neq. unfold not in *. intro. apply H. subst. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. destruct f, f0. simpl. apply Bool.andb_false_iff.
        unfold not in H. case_eq ((s =? s0)%string); intros.
        - right. apply eqb_eq in H0. apply Nat.eqb_neq. unfold not. intro. apply H. subst. reflexivity.
        - left. reflexivity.
    }
  Qed.

  Proposition var_funid_eqb_refl (var : Var + FunctionIdentifier) :
  var_funid_eqb var var = true.
  Proof.
    destruct var.
    * simpl. apply eqb_refl.
    * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  Qed.

  Proposition var_funid_eqb_sym (v1 v2 : Var + FunctionIdentifier) :
    var_funid_eqb v1 v2 = var_funid_eqb v2 v1.
  Proof.
    destruct v1, v2.
    * simpl. rewrite eqb_sym. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. destruct f, f0. simpl. rewrite eqb_sym, Nat.eqb_sym. reflexivity.
  Qed.

  Fixpoint Expression_eq_dec (e1 e2 : Expression) : {e1 = e2} + {e1 <> e2}
  (* with SingleExpression_eq_dec (e1 e2 : SingleExpression) : {e1 = e2} + {e1 <> e2} *).
  Proof.
   (*  * set (list_eq_dec SingleExpression_eq_dec).
      decide equality. *)

    * set (Literal_eq_dec).
      set (string_dec).
      set (OrderedTypeEx.Z_as_OT.eq_dec).
      set (prod_eqdec string_dec Nat.eq_dec).
      set (list_eq_dec string_dec).
      set (list_eq_dec Expression_eq_dec).
      set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pattern_eq_dec) Expression_eq_dec) Expression_eq_dec)).
      decide equality. 
      - decide equality. decide equality.
      - repeat (decide equality).
      - repeat decide equality.
  Defined.

  Fixpoint Value_eq_dec (v1 v2 : Value) : {v1 = v2} + {v1 <> v2}.
  Proof.
    intros. decide equality.
    * apply Literal_eq_dec.
    * apply Expression_eq_dec.
    * apply list_eq_dec. apply string_dec.
    * apply Nat.eq_dec.
    * apply list_eq_dec. intros.
      apply prod_eq_dec.
      - apply prod_eq_dec.
        + apply Nat.eq_dec.
        + apply prod_eq_dec.
          ** apply string_dec.
          ** apply Nat.eq_dec.
      - apply prod_eq_dec.
        + apply list_eq_dec. apply string_dec.
        + apply Expression_eq_dec.
    * apply list_eq_dec.
      apply prod_eq_dec.
      - apply sum_eq_dec.
        + apply string_dec.
        + apply prod_eq_dec.
          ** apply string_dec.
          ** apply Nat.eq_dec.
      - apply Value_eq_dec.
    * apply list_eq_dec. apply Value_eq_dec.
    * apply list_eq_dec. apply prod_eq_dec; apply Value_eq_dec.
  Defined.

  Theorem Value_eqb_refl v :
    Value_eqb v v = true.
  Proof.
    einduction v using Value_ind2.
    * simpl. auto.
    * simpl. auto. destruct l; simpl. apply eqb_refl. apply Z.eqb_refl.
    * simpl. rewrite IHv0_1, IHv0_2. auto.
    * simpl.
    (* workaround *)
    assert (True). { apply IHv0. }
    (***)
    apply Nat.eqb_refl.
    * simpl. apply IHv0.
    * simpl. apply IHv0.
    * simpl. rewrite IHv0, IHv1. auto.
    * simpl. rewrite IHv0_1, IHv0_2, IHv0_3. auto.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
  Qed.

  Definition extension_eqb (ext ext' : list (nat * FunctionIdentifier * FunctionExpression)) : bool :=
  list_eqb (prod_eqb (prod_eqb Nat.eqb funid_eqb) (prod_eqb (list_eqb eqb) Expression_eqb)) ext ext'.

  Fixpoint Value_full_eqb (e1 e2 : Value) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Literal_eqb l l'
  | VClos env ext id p b, VClos env' ext' id' p' b' => 
      (((Nat.eqb id id' && Expression_eqb b b') && list_eqb (eqb) p p') &&
      (fix blist l l' := match l, l' with
                         | [], [] => true
                         | (x, v)::xs, (x', v')::xs' => andb (andb (Value_full_eqb v v') 
                                                                   (var_funid_eqb x x')) 
                                                             (blist xs xs')
                         | _, _ => false
                         end) env env') &&
      extension_eqb ext ext'
  | VCons hd tl, VCons hd' tl' => Value_full_eqb hd hd' && Value_full_eqb tl tl'
  | VTuple l, VTuple l' => (fix blist l l' := match l, l' with
                                             | [], [] => true
                                             | x::xs, x'::xs' => andb (Value_full_eqb x x') (blist xs xs')
                                             | _, _ => false
                                             end) l l'
  | VMap l, VMap l' => (fix blist l l' := match l, l' with
                                                   | [], [] => true
                                                   | (x,y)::xs, (x',y')::xs' => andb (Value_full_eqb x x') (andb (Value_full_eqb y y') (blist xs xs'))
                                                   | _, _ => false
                                                   end) l l'
  | _, _ => false
  end.

  Theorem funid_eqb_refl :
    forall f,
    funid_eqb f f = true.
  Proof.
    intros. destruct f.
    simpl. rewrite eqb_refl, Nat.eqb_refl. auto.
  Qed.

  Theorem funid_eqb_eq :
    forall f1 f2,
    f1 = f2
    <->
    funid_eqb f1 f2 = true.
  Proof.
    intros. destruct f1, f2.
    simpl. split; intros.
    * inversion H. subst. rewrite eqb_refl, Nat.eqb_refl. auto.
    * apply andb_prop in H. destruct H. apply Nat.eqb_eq in H0. apply eqb_eq in H.
      subst. auto.
  Qed.

  Lemma Pattern_eqb_refl p :
    Pattern_eqb p p = true.
  Proof.
    einduction p using Pattern_ind2; simpl; auto.
    * destruct l; simpl. apply eqb_refl. apply Z.eqb_refl.
    * apply eqb_refl.
    * rewrite IHp0_1, IHp0_2. auto.
    * apply IHp0.
    * apply IHp0.
    * simpl. rewrite IHp0. simpl. auto.
    * simpl. rewrite IHp0_1, IHp0_2. auto.
    * simpl. auto.
    * simpl. auto. 
  Qed.

  Lemma Pattern_list_eqb_refl pl :
  (fix blist (l0 l' : list Pattern) {struct l0} : bool :=
    match l0 with
    | [] => match l' with
            | [] => true
            | _ :: _ => false
            end
    | x :: xs =>
        match l' with
        | [] => false
        | x' :: xs' => andb (Pattern_eqb x x') (blist xs xs')
        end
    end) pl pl = true.
  Proof.
    induction pl.
    * auto.
    * simpl. rewrite Pattern_eqb_refl, IHpl. auto.
  Qed.

  Theorem Expression_eqb_refl e :
    Expression_eqb e e = true.
  Proof.
    einduction e using Expression_ind2.
    * apply IHe0.
    * simpl. auto.
    * simpl. destruct l; simpl. apply eqb_refl. apply Z.eqb_refl.
    * simpl. apply eqb_refl.
    * simpl. apply funid_eqb_refl.
    * simpl. rewrite IHe0. rewrite list_eqb_refl. auto. intros. apply eqb_refl.
    * simpl. rewrite IHe0_1, IHe0_2. auto.
    * apply IHe0.
    * simpl in IHe0_3.  simpl. rewrite IHe0_1. rewrite IHe0_2. simpl. auto.
    * simpl in IHe0. simpl. rewrite eqb_refl. rewrite eqb_refl. simpl. auto.
    * simpl in *. rewrite IHe0, IHe1. auto.
    * simpl. rewrite IHe0, Nat.eqb_refl. simpl. apply IHe1.
    * simpl. rewrite IHe0_1, IHe0_2. rewrite list_eqb_refl. auto. apply eqb_refl.
    * simpl. rewrite IHe0_1, IHe0_2. auto.
    * simpl. rewrite IHe1. simpl. apply IHe0.
    * simpl. apply IHe0.
    * simpl. rewrite IHe0_1, IHe0_2, IHe0_3. rewrite list_eqb_refl, list_eqb_refl. auto.
      apply eqb_refl. apply eqb_refl.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
    * simpl. rewrite IHe0. simpl in *. auto.
    * simpl in *. rewrite IHe0, IHe1. auto.
    * simpl in *. rewrite IHe0_1, IHe0_2, IHe0_3. auto.
    * simpl in *. rewrite IHe0_1, IHe0_2, IHe0_3. rewrite Pattern_list_eqb_refl. auto.
    * simpl in *. rewrite IHe0. simpl. rewrite Bool.andb_true_r in *.
      rewrite funid_eqb_refl, IHe1. simpl. rewrite Bool.andb_true_r.
      rewrite list_eqb_refl. auto. apply eqb_refl.
  Qed.

  Theorem extension_eqb_refl ext :
    extension_eqb ext ext = true.
  Proof.
    apply list_eqb_refl. intros.
    apply prod_eqb_refl.
    * intros. apply prod_eqb_refl.
      - apply Nat.eqb_refl.
      - intros. apply prod_eqb_refl. apply eqb_refl. apply Nat.eqb_refl.
    * intros. apply prod_eqb_refl.
      - intros. apply list_eqb_refl. apply eqb_refl.
      - intros. apply Expression_eqb_refl.
  Qed.

  Theorem Value_full_eqb_refl v :
    Value_full_eqb v v = true.
  Proof.
    einduction v using Value_ind2.
    * simpl. auto.
    * simpl. auto. destruct l; simpl. apply eqb_refl. apply Z.eqb_refl.
    * simpl. rewrite IHv0_1, IHv0_2. auto.
    * simpl. pose (P := Nat.eq_refl id). rewrite <- Nat.eqb_eq in P. rewrite P. simpl.
      rewrite Expression_eqb_refl. simpl.
      rewrite list_eqb_refl. simpl. 2: intros; rewrite eqb_eq; apply eq_refl.
      rewrite extension_eqb_refl. simpl.
      apply IHv0.
    * simpl. apply IHv0.
    * simpl. apply IHv0.
    * simpl. rewrite IHv0, IHv1. auto.
    * simpl. rewrite IHv0_1, IHv0_2, IHv0_3. auto.
    * simpl. auto.
    * simpl. auto.
    * simpl. auto.
    * simpl. rewrite IHv0. simpl.
      rewrite var_funid_eqb_refl. simpl. auto.
  Qed.

  Theorem Pattern_eqb_eq p1 p2:
    p1 = p2
  <->
    Pattern_eqb p1 p2 = true.
  Proof.
    split.
    * intros. subst. apply Pattern_eqb_refl.
    * generalize dependent p2. einduction p1 using Pattern_ind2 with
       (Q := fun l => forall l0, (fix blist_eq (l l' : list Pattern) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | x :: xs =>
            match l' with
            | [] => false
            | x' :: xs' => (Pattern_eqb x x' && blist_eq xs xs')%bool
            end
        end) l l0 = true -> l = l0)
       (R := fun l => forall l0, (fix blist_eq (l l' : list (Pattern * Pattern)) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | (x, y) :: xs =>
            match l' with
            | [] => false
            | (x', y') :: xs' =>
                (Pattern_eqb x x' && Pattern_eqb y y' && blist_eq xs xs')%bool
            end
        end) l l0 = true -> l = l0).
      - intros. destruct p2; inversion H. auto.
      - intros. destruct p2; inversion H. destruct l, l0; inversion H1.
        apply eqb_eq in H2. subst. auto.
        apply Z.eqb_eq in H2. subst. auto.
      - intros. destruct p2; inversion H. apply eqb_eq in H1. subst. auto.
      - intros. destruct p0; inversion H. apply andb_prop in H1. destruct H1.
        rewrite (IHp1 _ H0), (IHp2 _ H1). auto.
      - intros. destruct p2; inversion H. apply IHp in H1. subst. auto.
      - intros. destruct p2; inversion H. apply IHp in H1. subst. auto.
      - intros. destruct l0. inversion H.
        apply andb_prop in H. destruct H. apply IHp in H. apply IHp0 in H0.
        subst. auto.
      - intros. destruct l0. inversion H. destruct p.
        apply andb_prop in H. destruct H.
        apply andb_prop in H. destruct H. apply IHp1 in H. apply IHp2 in H1.
        apply IHp3 in H0. subst. auto.
      - intros. simpl. destruct l0; inversion H. auto.
      - intros. simpl. destruct l0; inversion H. auto.
  Qed.

  Lemma Pattern_list_eqb_eq pl l1:
     pl = l1
   <->
    (fix blist0 (l0 l'0 : list Pattern) {struct l0} : bool :=
        match l0 with
        | [] => match l'0 with
                | [] => true
                | _ :: _ => false
                end
        | x :: xs0 =>
            match l'0 with
            | [] => false
            | x' :: xs'0 => (Pattern_eqb x x' && blist0 xs0 xs'0)%bool
            end
        end) pl l1 = true.
   Proof.
     split.
     * intros. subst. apply Pattern_list_eqb_refl.
     * simpl. generalize dependent l1. induction pl.
       - intros. destruct l1; inversion H. auto.
       - intros. destruct l1. inversion H.
         apply andb_prop in H. destruct H. apply Pattern_eqb_eq in H.
         apply IHpl in H0. subst. auto.
  Qed.

  Theorem Expression_eqb_eq :
    forall e1 e2,
    e1 = e2
  <->
    Expression_eqb e1 e2 = true.
  Proof.
    split.
    * intros. subst. apply Expression_eqb_refl.
    * generalize dependent e2. einduction e1 using Expression_ind2 with
       (Q := fun l => forall l0, (fix blist (l l' : list Expression) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | x :: xs =>
            match l' with
            | [] => false
            | x' :: xs' => (Expression_eqb x x' && blist xs xs')%bool
            end
        end) l l0 = true -> l = l0)
       (W := fun l => forall l0, (fix blist (l l' : list (list Pattern * Expression * Expression)) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | (pl, y, z) :: xs =>
            match l' with
            | [] => false
            | (pl', y', z') :: xs' =>
                ((fix blist0 (l0 l'0 : list Pattern) {struct l0} : bool :=
                    match l0 with
                    | [] => match l'0 with
                            | [] => true
                            | _ :: _ => false
                            end
                    | x :: xs0 =>
                        match l'0 with
                        | [] => false
                        | x' :: xs'0 => Pattern_eqb x x' && blist0 xs0 xs'0
                        end
                    end) pl pl' &&
                 (Expression_eqb y y' && (Expression_eqb z z' && blist xs xs')))%bool
            end
        end) l l0 = true -> l = l0)
       (Z := fun l => forall l0, (fix blist (l l' : list (FunctionIdentifier * (list string * Expression))) {struct l} :
          bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | (x, (y, z)) :: xs =>
            match l' with
            | [] => false
            | (x', (y', z')) :: xs' =>
                (funid_eqb x x' &&
                 (list_eqb eqb y y' && (Expression_eqb z z' && blist xs xs')))%bool
            end
        end) l l0 = true -> l = l0)
       (R := fun l => forall l0, (fix blist (l l' : list (Expression * Expression)) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | (x, y) :: xs =>
            match l' with
            | [] => false
            | (x', y') :: xs' =>
                (Expression_eqb x x' && (Expression_eqb y y' && blist xs xs'))%bool
            end
        end) l l0 = true -> l = l0)
        .
      - simpl. intros. destruct e2; try destruct e; try inversion H.
        apply IHe in H. subst. auto.
      - simpl. intros. destruct e2; try destruct e; try inversion H. auto.
      - simpl. intros. destruct e2; try destruct e; try inversion H. auto.
        destruct l, l0; try inversion H. rewrite eqb_eq in H2. subst. auto.
        rewrite Z.eqb_eq in H2. subst. auto.
      - simpl. intros. destruct e2; try destruct e; try inversion H. auto.
        rewrite eqb_eq in H. subst. auto.
      - simpl. intros. destruct e2; try destruct e; try inversion H. auto.
        rewrite <- funid_eqb_eq in H. subst. auto.
      - simpl. intros. destruct e2; try destruct e0; try inversion H.
        apply andb_prop in H. destruct H. apply list_eqb_eq in H.
        apply IHe in H0. subst. auto. intros; split; apply eqb_eq.
      - simpl. intros. destruct e0; try destruct e; try inversion H.
        apply andb_prop in H. destruct H.
        pose (IHe1 _ H). pose (IHe2 _ H0). rewrite e, e0. auto.
      - simpl. intros. destruct e2; try destruct e; inversion H.
        apply IHe in H1. subst. auto.
      - simpl. intros. destruct e0; try destruct e; inversion H.
      apply andb_prop in H1. destruct H1. apply IHe3 in H1. 
      apply andb_prop in H0. destruct H0.
      apply IHe2 in H0. apply IHe1 in H2. subst. auto.
      
      (*simpl. intros. destruct e2; try destruct e; inversion H.
        apply andb_prop in H1.  destruct H1. apply andb_prop in H0. destruct H0.
        apply eqb_eq in H0. apply eqb_eq in H2.
        apply IHe in H1. subst. auto.*)
      - simpl. intros. destruct e2; try destruct e; inversion H.
        apply andb_prop in H1.  destruct H1. apply andb_prop in H0. destruct H0.
        apply eqb_eq in H0. apply eqb_eq in H2.
        apply IHe in H1. subst. auto.
      - simpl. intros. destruct e2; try destruct e0; inversion H.
        apply andb_prop in H1. destruct H1. apply IHe0 in H1. apply IHe in H0. subst. auto.
      - simpl. intros. destruct e2; try destruct e0; inversion H.
        apply andb_prop in H. destruct H.
        apply andb_prop in H. destruct H.
        apply IHe in H. apply IHe0 in H0. subst. auto.
      - simpl. intros. destruct e0; try destruct e; inversion H.
        apply andb_prop in H. destruct H.
        apply andb_prop in H. destruct H. apply IHe1 in H2. apply IHe2 in H0.
        apply list_eqb_eq in H. subst. auto. intros; split; apply eqb_eq.
      - simpl. intros. destruct e0; try destruct e; inversion H.
        apply andb_prop in H. destruct H.
        apply IHe1 in H. apply IHe2 in H0.
        subst. auto.
      - simpl. intros. destruct e2; try destruct e0; inversion H.
        apply andb_prop in H1. destruct H1. apply IHe0 in H1. apply IHe in H0. subst. auto.
      - simpl. intros. destruct e2; try destruct e; inversion H.
        apply IHe in H1. subst. auto.
      - simpl. intros. destruct e0; try destruct e; inversion H.
        apply andb_prop in H1. destruct H1.
        apply andb_prop in H0. destruct H0.
        apply andb_prop in H0. destruct H0.
        apply andb_prop in H0. destruct H0.
        apply IHe1 in H3. apply IHe2 in H2. apply IHe3 in H1.
        apply list_eqb_eq in H0. apply list_eqb_eq in H4. subst. auto.
        all: intros; split; apply eqb_eq.
      - intros. destruct l0; inversion H. auto.
      - intros. destruct l0; inversion H. auto.
      - intros. destruct l0; inversion H. auto.
      - intros. destruct l0; inversion H. auto.
      (* - intros. destruct el; inversion H. auto. *)
     (*  - intros. destruct l0; inversion H. apply andb_prop in H1.
        destruct H1. simpl in IHe. pose (IHe (ESingle s) H0). inversion e0.
        apply IHe0 in H1. subst. auto. *)
      - intros. destruct l0; inversion H. apply andb_prop in H1.
        destruct H1. apply IHe in H0. apply IHe0 in H1. subst. auto.
      - intros. destruct l0; inversion H. apply andb_prop in H1.
        destruct H1. apply IHe in H0. apply IHe0 in H1. subst. auto.
      - intros. destruct l0; inversion H. destruct p. apply andb_prop in H1.
        destruct H1.
        apply andb_prop in H1.
        destruct H1. apply IHe1 in H0. apply IHe2 in H1. apply IHe3 in H2. subst. auto.
      - intros. destruct l0; inversion H. destruct p, p.
        apply andb_prop in H1. destruct H1.
        apply andb_prop in H1. destruct H1.
        apply andb_prop in H2. destruct H2.
        apply IHe1 in H1. apply IHe2 in H2. apply IHe3 in H3.
        apply Pattern_list_eqb_eq in H0. subst. auto.
      - intros. destruct l0. inversion H. destruct p, p.
        apply andb_prop in H. destruct H.
        apply andb_prop in H0. destruct H0.
        apply andb_prop in H1. destruct H1.
        apply funid_eqb_eq in H. apply list_eqb_eq in H0. 2: intros; split; apply eqb_eq.
        apply IHe in H1. apply IHe0 in H2.
        subst. auto.
  Qed.

  Theorem extension_eqb_eq :
    forall e1 e2,
    e1 = e2
  <->
    extension_eqb e1 e2 = true.
  Proof.
    split.
    * intros. subst. apply extension_eqb_refl.
    * generalize dependent e2. induction e1; intros.
      - destruct e2; try inversion H. clear H. auto.
      - destruct e2; try inversion H. clear H.
        apply list_eqb_eq in H1. auto.
        intros. split; intros.
        + subst. apply prod_eqb_refl.
          ** intros. apply prod_eqb_refl; intros. apply Nat.eqb_refl. apply funid_eqb_refl.
          ** intros. apply prod_eqb_refl; intros.
             apply list_eqb_refl. intros. apply eqb_refl.
             apply Expression_eqb_refl.
        + apply prod_eqb_eq in H0.
          ** auto.
          ** intros. split; intros.
             -- subst. apply prod_eqb_refl; intros. apply Nat.eqb_refl. apply funid_eqb_refl.
             -- apply prod_eqb_eq in H3. auto. intros. split; apply Nat.eqb_eq.
                split; apply funid_eqb_eq.
          ** intros. split; intros.
             -- subst. apply prod_eqb_refl; intros.
                apply list_eqb_refl. intros. apply eqb_refl.
                apply Expression_eqb_refl.
             -- apply prod_eqb_eq in H3. auto.
                intros. split; intros. subst. apply list_eqb_refl. apply eqb_refl.
                apply list_eqb_eq in H5. auto.
                split; apply eqb_eq.
                split; apply Expression_eqb_eq.
  Qed.

  Theorem Value_full_eqb_eq :
    forall v1 v2,
    v1 = v2
  <->
    Value_full_eqb v1 v2 = true.
  Proof.
    split.
    * intros. rewrite H. apply Value_full_eqb_refl.
    * generalize dependent v2. induction v1 using Value_ind2 with (W := 
        fun ref => forall env, (fix blist (l l' : list ((Var + FunctionIdentifier) * Value)) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | (x, v) :: xs =>
            match l' with
            | [] => false
            | (x', v') :: xs' =>
                (Value_full_eqb v v' && var_funid_eqb x x' && blist xs xs')%bool
            end
        end) ref env = true -> ref = env)
        (Q := fun l => forall vl, (fix blist (l l' : list Value) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | x :: xs =>
            match l' with
            | [] => false
            | x' :: xs' => (Value_full_eqb x x' && blist xs xs')%bool
            end
        end) l vl = true -> l = vl)
        (R := fun l => forall l0, (fix blist (l l' : list (Value * Value)) {struct l} : bool :=
        match l with
        | [] => match l' with
                | [] => true
                | _ :: _ => false
                end
        | (x, y) :: xs =>
            match l' with
            | [] => false
            | (x', y') :: xs' =>
                (Value_full_eqb x x' && (Value_full_eqb y y' && blist xs xs'))%bool
            end
        end) l l0 = true -> l = l0); intros.
      - destruct v2; try inversion H. auto.
      - destruct v2; try inversion H. destruct l, l0; try inversion H1.
        + rewrite eqb_eq in H2. subst. auto.
        + rewrite Z.eqb_eq in H2. subst. auto.
      - destruct v2; try inversion H.
        apply andb_prop in H1. destruct H1.
        apply IHv1_1 in H0. apply IHv1_2 in H1. subst. auto.
      - destruct v2; try inversion H. clear H.
        apply andb_prop in H1. destruct H1.
        apply andb_prop in H. destruct H.
        apply andb_prop in H. destruct H.
        apply andb_prop in H. destruct H.
        apply extension_eqb_eq in H0.
        apply Expression_eqb_eq in H3.
        apply Nat.eqb_eq in H.
        apply list_eqb_eq in H2.
        2: { intros. split; intros. subst. apply eqb_refl. apply eqb_eq. auto. }
        apply IHv1 in H1. subst. auto.
      - destruct v2; try inversion H. clear H.
        apply IHv1 in H1. subst. auto.
      - destruct v2; try inversion H. clear H.
        apply IHv1 in H1. subst. auto.
      - destruct vl; try inversion H. clear H.
        apply andb_prop in H1. destruct H1.
        apply IHv1 in H. subst. pose (IHv0 vl H0). rewrite e. auto.
      - destruct l0; try inversion H. clear H. destruct p.
        apply andb_prop in H1. destruct H1.
        apply andb_prop in H0. destruct H0.
        apply IHv1_1 in H.
        apply IHv1_2 in H0.
        pose (IHv1_3 _ H1). rewrite H, H0, e. auto.
      - destruct vl; try inversion H. auto.
      - destruct l0; try inversion H. auto.
      - destruct env; try inversion H. auto.
      - destruct env; try inversion H. clear H. destruct p.
        apply andb_prop in H1. destruct H1.
        apply andb_prop in H. destruct H.
        apply IHv1 in H. apply var_funid_eqb_eq in H1.
        pose (IHv0 _ H0). rewrite H, H1, e. auto.
  Qed.

  Proposition value_full_list_eqb_eq :
    forall l1 l2,
    l1 = l2
  <->
    list_eqb Value_full_eqb l1 l2 = true.
  Proof.
    split.
    * intros. subst. apply list_eqb_refl. apply Value_full_eqb_refl.
    * generalize dependent l2. induction l1; intros.
      - simpl in H. destruct l2; auto. congruence.
      - simpl in H. destruct l2. congruence. apply andb_prop in H. destruct H.
        pose (IHl1 l2 H0). rewrite e. apply Value_full_eqb_eq in H. rewrite H. auto.
  Qed.

End Equalities.

Section Comparisons.
  (** Ordering on values *)
  Import Structures.OrderedTypeEx.String_as_OT.

  Inductive lt_Literal : Literal -> Literal -> Prop :=
  | lt_atom_int z a : lt_Literal (Integer z) (Atom a)
  | lt_atom_atom (a:string) (a':string) : lt a a' -> lt_Literal (Atom a) (Atom a')
  | lt_int_int (z : Z) (z' : Z) : Z.lt z z' -> lt_Literal (Integer z) (Integer z')
  .

  Lemma lt_5 : lt_Literal (Integer 5) (Integer 7).
  Proof.
    apply lt_int_int. lia.
  Qed.

  Lemma lt_str : lt_Literal (Atom "aaaa") (Atom "aaaa2").
  Proof.
    apply lt_atom_atom. apply lts_tail. apply lts_tail. apply lts_tail. apply lts_tail. apply lts_empty.
  Qed.

(* TODO: Major adjustment needed here ****

  Inductive lt_Value : Value -> Value -> Prop :=
  | lt_lit_lit l l' : lt_Literal l l' -> lt_Value (VLit l) (VLit l')
  | lt_lit_other l v : (forall l' : Literal, v <> VLit l') -> lt_Value (VLit l) (v)

  | lt_closure_closure ref params body ref' ext ext' params' body' n n' : 
     Nat.lt n n' ->
     lt_Value (VClos ref ext n params body) (VClos ref' ext' n' params' body')
  | lt_closure_other v ref ext id body params: (forall ref' ext' id' params' body', v <> VClos ref' ext' id' params' body') -> (forall l : Literal, v <> VLit l) -> lt_Value (VClos ref ext id params body) (v)
  | lt_tuple_tuple_nil exps' : exps' <> [] -> lt_Value (VTuple [])  (VTuple exps')
  | lt_tuple_length exps exps' : length exps < length exps' -> lt_Value (VTuple exps) (VTuple exps')
  | lt_tuple_tuple_hd exps exps' hd hd' : length exps = length exps' -> lt_Value hd hd' -> lt_Value (VTuple (hd::exps)) (VTuple (hd'::exps'))
  | lt_tuple_tuple_tl exps exps' hd hd' : length exps = length exps' -> hd = hd' -> lt_Value (VTuple exps) (VTuple exps') -> lt_Value (VTuple (hd::exps)) (VTuple (hd'::exps'))
  | lt_tuple_map (l : list Value) (ml : list (Value * Value)): lt_Value (VTuple l) (VMap ml)
  | lt_tuple_list l hd tl: lt_Value (VTuple l) (VCons hd tl)
  | lt_tuple_emptylist l: lt_Value (VTuple l) (VNil)
  | lt_map_map_nil l' : l' <> [] -> lt_Value (VMap []) (VMap l')
  | lt_map_length l l' : length l < length l' -> lt_Value (VMap l) (VMap l')
  | lt_map_map_hd (l l' : list (Value*Value)) hd hd' hdv hdv':
    length l = length l' -> lt_Value hd hd' -> lt_Value (VMap ((hd, hdv)::l)) (VMap ((hd', hdv')::l'))
  | lt_map_map_vl (l l' : list (Value*Value)) hd hd' hdv hdv':
    length l = length l' -> lt_Value (VMap l) (VMap l') -> lt_Value (VMap ((hd, hdv)::l)) (VMap ((hd', hdv')::l'))
 (* TODO: extension needed for values, if all keys are equal *)
  | lt_map_emptylist l : lt_Value (VMap l) VNil
  | lt_map_list l hd tl : lt_Value (VMap l) (VCons hd tl)
  | lt_emptylist_list hd tl : lt_Value VNil (VCons hd tl)
  | lt_list_list_head hd hd' tl tl': lt_Value hd hd' -> lt_Value (VCons hd tl) (VCons hd' tl')
  | lt_lis_list_tail hd hd' tl tl': hd = hd' -> lt_Value tl tl' -> lt_Value (VCons hd tl) (VCons hd' tl')
  . *)

(*   Example e1 : lt_Value (VTuple []) (VNil).
  Proof.
    apply lt_tuple_emptylist.
  Qed.

  Example e2 : lt_Value (VTuple []) (VTuple [VNil]).
  Proof.
    apply lt_tuple_tuple_nil. congruence.
  Qed.

  Example e3 : lt_Value (VMap [(VLit (Integer 5), VNil)]) (VMap [(VNil, VNil)]).
  Proof.
    apply lt_map_map_hd; auto. apply lt_lit_other. intros. congruence.
  Qed. *)

  (** Boolean comparison: *)

  Import Coq.Strings.Ascii.

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

  (** TODO: investigate, but now, we dont compare value sequences, only single values *)
  Fixpoint Value_ltb (k v : Value) : bool :=
  match k, v with
  | VLit l, VLit l' => literal_ltb l l'
  | VLit _, _ => true
  | VClos _ _ id _ _, VClos _ _ id' _ _ => Nat.ltb id id'
  | VClos _ _ _ _ _, VTuple _ => true
  | VClos _ _ _ _ _, VMap _ => true
  | VClos _ _ _ _ _, VNil => true
  | VClos _ _ _ _ _, VCons _ _ => true
  | VTuple l, VTuple l' => orb (Nat.ltb (length l) (length l')) (andb (Nat.eqb (length l) (length l')) (list_less Value Value_eqb Value_ltb l l'))
  | VTuple _, VNil => true
  | VTuple _, VMap _ => true
  | VTuple l, VCons _ _ => true
  | VMap l, VMap l' => orb (Nat.ltb (length l) (length l')) (andb (Nat.eqb (length l) (length l'))
                       (orb ((fix list_less (l l' : list (Value * Value)) :=
                          match l, l' with
                          | [], [] => false
                          | (x,y)::xs, [] => false
                          | [], (x',y')::ys => true
                          | (x,y)::xs, (x',y')::ys => 
                                  if Value_eqb x x' then list_less xs ys else Value_ltb x x'
                          end) l l')
                          (andb 
                          (list_equal Value Value_eqb (map fst l) (map fst l'))
                          
                          ((fix list_less (l l' : list (Value * Value)) :=
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

End Comparisons.

Import Core_Erlang_Syntax.Value_Notations.

Goal Value_ltb (VMap [(ErrorValue, ErrorValue); (VLit (Integer 8), VLit (Integer 7))])
                   (VMap [(ErrorValue, ErrorValue); (VLit (Integer 7), VLit (Integer 6))]) = false. Proof. reflexivity. Qed.
Goal Value_ltb (VMap [(ErrorValue, ErrorValue); (ErrorValue, VLit (Integer 7))])
                   (VMap [(ErrorValue, ErrorValue); (ErrorValue, VLit (Integer 8))]) = true. Proof. reflexivity. Qed.

End Equalities.
