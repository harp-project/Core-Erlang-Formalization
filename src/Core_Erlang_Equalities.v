Require Core_Erlang_Syntax.
Require Lia.
From Coq Require Classes.EquivDec.

Module Equalities.

Export Core_Erlang_Syntax.Syntax.

Import ListNotations.
Export Arith.PeanoNat.
Import Classes.EquivDec.
Export Lia.

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
   | _, _ => false
  end.

  Fixpoint varlist_eqb (l l' : list Var) : bool :=
  match l, l' with
  | [], [] => true
  | x::xs, x'::xs' => andb (eqb x x') (varlist_eqb xs xs')
  | _, _ => false
  end.

  Fixpoint Expression_eqb (e1 e2 : Expression) : bool :=
  match e1, e2 with
   | EValues l, EValues l' => (fix blist l l' := match l, l' with
                                        | [], [] => true
                                        | x::xs, x'::xs' => andb (SingleExpression_eqb x x') 
                                                                 (blist xs xs')
                                        | _, _ => false
                                        end) l l'
   | ESingle e, ESingle e' => SingleExpression_eqb e e'
   | _, _ => false
  end
  with SingleExpression_eqb (e1 e2 : SingleExpression) : bool :=
  match e1, e2 with
   | ENil, ENil => true
   | ELit l, ELit l' => Literal_eqb l l'
   | EVar v, EVar v' => eqb v v'
   | EFunId f, EFunId f' => funid_eqb f f'
   | EFun vl e, EFun vl' e' => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) vl vl' && Expression_eqb e e'
   | ECons hd tl, ECons hd' tl' => Expression_eqb hd hd' && Expression_eqb tl tl'
   | ETuple l, ETuple l' => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | x::xs, x'::xs' => andb (Expression_eqb x x') (blist xs xs')
                                                 | _, _ => false
                                                 end) l l'
   | ECall f l, ECall f' l' => eqb f f' && (fix blist l l' := match l, l' with
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
   | ELet l e1 e2, ELet l' e1' e2' => varlist_eqb l l' && Expression_eqb e1 e1' && Expression_eqb e2 e2'
   | ESeq e1 e2, ESeq e1' e2' => andb (Expression_eqb e1 e1') (Expression_eqb e2 e2')
   | ELetRec l e, ELetRec l' e' => 
                                               (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,(y,z))::xs, (x',(y',z'))::xs' => andb (funid_eqb x x') (andb (
                                                     (fix blist l l' := match l, l' with
                                                     | [], [] => true
                                                     | x::xs, x'::xs' => andb (eqb x x') (blist xs xs')
                                                     | _, _ => false
                                                 end)
                                                 y y') (andb (Expression_eqb z z') (blist xs xs')))
                                                 | _, _ => false
                                                 end) l l' &&
                                               Expression_eqb e e'
   | EMap l, EMap l' => (fix blist l l' := match l, l' with
                                                 | [], [] => true
                                                 | (x,y)::xs, (x',y')::xs' => andb (Expression_eqb x x') (andb (Expression_eqb y y') (blist xs xs'))
                                                 | _, _ => false
                                                 end) l l'
   | ETry e1 vl1 e2 vl2 e3, ETry e1' vl1' e2' vl2' e3' => varlist_eqb vl1 vl1' && varlist_eqb vl2 vl2' &&
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
      * destruct f, f0. simpl in H. Search andb. apply Bool.andb_false_iff in H. inversion H.
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

  Theorem Expression_eq_dec (e1 e2 : Expression) : {e1 = e2} + {e1 <> e2}
  with SingleExpression_eq_dec (e1 e2 : SingleExpression) : {e1 = e2} + {e1 <> e2}.
  Proof.
    * set (list_eq_dec SingleExpression_eq_dec).
      decide equality.

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
    einduction v using value_ind2.
    * simpl. auto.
    * simpl. auto. destruct l; simpl. apply eqb_refl. apply Z.eqb_refl.
    * simpl. rewrite IHv0_1, IHv0_2. auto.
    * simpl. apply Nat.eqb_refl.
    * simpl. apply IHv0.
    * simpl. apply IHv0.
    * simpl. rewrite IHv0, IHv1. auto.
    * simpl. rewrite IHv0_1, IHv0_2, IHv0_3. auto.
    * simpl. auto.
    * simpl. auto.
  Qed.

  Fixpoint list_eqb {A : Type} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
  match l1, l2 with
  | [], [] => true
  | x::xs, y::ys => eq x y && list_eqb eq xs ys
  | _, _ => false
  end.

  Proposition list_eqb_refl {A : Type} {f : A -> A -> bool} (l : list A) :
    (forall a, f a a = true)
  ->
    list_eqb f l l = true.
  Proof.
    induction l.
    * simpl. reflexivity.
    * simpl. intros. rewrite (H a), (IHl H). auto.
  Qed.

  Definition prod_eqb {A B : Type} (eqx : A -> A -> bool) (eqy : B -> B -> bool) (p1 p2 : A * B) :=
  match p1, p2 with
  | (x, y), (x', y') => andb (eqx x x') (eqy y y')
  end.

  Fixpoint Value_full_eqb (e1 e2 : Value) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Literal_eqb l l'
  | VClos env ext id p b, VClos env' ext' id' p' b' => 
      Nat.eqb id id' && Expression_eqb b b' && list_eqb (eqb) p p' &&
      (fix blist l l' := match l, l' with
                         | [], [] => true
                         | (x, v)::xs, (x', v')::xs' => andb (andb (Value_full_eqb v v') 
                                                                   (var_funid_eqb x x')) 
                                                             (blist xs xs')
                         | _, _ => false
                         end) env env' &&
      (fix blist l l' := match l, l' with
                         | [], [] => true
                         | (id, fid, fexp)::xs, (id', fid', fexp')::xs' => 
                            andb (andb (Nat.eqb id id') (funid_eqb fid fid'))
                                 (prod_eqb (list_eqb eqb) Expression_eqb fexp fexp')
                         | _, _ => false
                         end) ext ext'
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

  Theorem Value_eqb_eq :
    forall v1 v2,
    v1 = v2
  <->
    true = Value_eqb v1 v2.
  Proof.
   
  Admitted.

  Proposition value_list_eqb_eq :
    forall l1 l2,
    l1 = l2
  <->
    true = list_eqb Value_eqb l1 l2.
  Proof.
    split.
    * intros. subst. apply eq_sym, list_eqb_refl. apply Value_eqb_refl.
    * generalize dependent l2. induction l1; intros.
      - simpl in H. destruct l2; auto. congruence.
      - simpl in H. destruct l2. congruence. apply Bool.andb_true_eq in H. destruct H.
        pose (IHl1 l2 H0). rewrite e. apply Value_eqb_eq in H. rewrite H. auto.
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

Compute Value_ltb (VMap [(ErrorValue, ErrorValue); (VLit (Integer 8), VLit (Integer 7))])
                   (VMap [(ErrorValue, ErrorValue); (VLit (Integer 7), VLit (Integer 6))]) = false.
Compute Value_ltb (VMap [(ErrorValue, ErrorValue); (ErrorValue, VLit (Integer 7))])
                   (VMap [(ErrorValue, ErrorValue); (ErrorValue, VLit (Integer 8))]) = true.

End Equalities.
