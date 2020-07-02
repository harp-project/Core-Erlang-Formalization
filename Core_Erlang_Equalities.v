Load Core_Erlang_Syntax.

Module Core_Erlang_Equalities.

Import Core_Erlang_Syntax.

Import ZArith.BinInt.
Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Arith.PeanoNat.

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
Qed.

Proposition sum_eq_dec : forall p1 p2 : A + B, {p1 = p2} + {p1 <> p2}.
Proof.
  set (eq1 := A_eq_dec).
  set (eq2 := B_eq_dec).
  decide equality.
Qed.

End Basic_Eq_Dec.

Section Equalities.
  (** Decidable and boolean equality for the syntax *)

  Scheme Equality for Literal.

  Fixpoint Pattern_eq_dec (p1 p2 : Pattern) : {p1 = p2} + {p1 <> p2}.
  Proof.
    set (Pattern_list_eq_dec := list_eq_dec Pattern_eq_dec).
    set (Pattern_var_eq_dec := string_dec).
    set (Pattern_literal_eq_dec := Literal_eq_dec).
    decide equality.
  Qed.

  Fixpoint Expression_eq_dec (e1 e2 : Expression) {struct e1} : {e1 = e2} + {e1 <> e2}.
  Proof.
    set (var_eq_dec := string_dec).
    set (literal_eq_dec := Literal_eq_dec).
    set (pattern_eq_dec := Pattern_eq_dec).
    set (explist_eq_dec := list_eq_dec Expression_eq_dec).
    set (varlist_eq_dec := list_eq_dec string_dec).
    
    (* for function identifiers: *)
    set (funid_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec).
    
    set (patlist_eq_dec := list_eq_dec pattern_eq_dec).
    (* for letrec *)
    set (listvarexp_eq_dec := list_eq_dec (prod_eq_dec (list Var) Expression
                                    (list_eq_dec string_dec) Expression_eq_dec)).
    (* for fids *)
    set (listfunid_eq_dec := list_eq_dec funid_eq_dec).
    set (listlistvar_eq_dec := list_eq_dec (list_eq_dec string_dec)).
    decide equality.
  Qed.

(** Boolean equalities: *)

  (* The equality of function signatures *)
  Definition equal (v1 v2 : FunctionIdentifier) : bool :=
  match v1, v2 with
  | (fid1, num1), (fid2, num2) => eqb fid1 fid2 && Nat.eqb num1 num2
  end.

  (* Extended equality between functions and vars *)
  Fixpoint uequal (v1 v2 : Var + FunctionIdentifier) : bool :=
  match v1, v2 with
  | inl s1, inl s2 => eqb s1 s2
  | inr f1, inr f2 => equal f1 f2
  | _, _ => false
  end.

  Fixpoint bLiteral_eq_dec (l1 l2 : Literal) : bool :=
  match l1, l2 with
   | Atom s1, Atom s2 => eqb s1 s2
   | Integer x1, Integer x2 => Z.eqb x1 x2
   | _, _ => false
  end.


  Fixpoint bPattern_eq_dec (p1 p2 : Pattern) {struct p1} : bool :=
  match p1, p2 with
   | PVar v1, PVar v2 => eqb v1 v2
   | PLit l1, PLit l2 => bLiteral_eq_dec l1 l2
   | PCons hd tl, PCons hd' tl' => bPattern_eq_dec hd hd' && bPattern_eq_dec tl tl'
   | PTuple l, PTuple l' => (fix blist_eq l l' := match l, l' with
                                         | [], [] => true
                                         | x::xs, x'::xs' => andb (bPattern_eq_dec x x') 
                                                                  (blist_eq xs xs')
                                         | _, _ => false
                                         end) l l'
   | PNil, PNil => true
   | _, _ => false
  end.

  Fixpoint bExpression_eq_dec (e1 e2 : Expression) : bool :=
  match e1, e2 with
   | ENil, ENil => true
   | ELit l, ELit l' => bLiteral_eq_dec l l'
   | EVar v, EVar v' => eqb v v'
   | EFunId f, EFunId f' => equal f f'
   | EFun vl e, EFun vl' e' => 
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (eqb x x') (blist xs xs')
                        | _, _ => false
                        end) vl vl' && bExpression_eq_dec e e'
   | ECons hd tl, ECons hd' tl' => bExpression_eq_dec hd hd' && bExpression_eq_dec tl tl'
   | ETuple l, ETuple l' => 
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                        | _, _ => false
                        end) l l'
   | ECall f l, ECall f' l' => 
     eqb f f' && (fix blist l l' := match l, l' with
                                    | [], [] => true
                                    | x::xs, x'::xs' => andb (bExpression_eq_dec x x')
                                                             (blist xs xs')
                                    | _, _ => false
                                    end) l l'
   | EApp exp l, EApp exp' l' => 
     bExpression_eq_dec exp exp' && 
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                        | _, _ => false
                        end) l l'
   | ECase e pl gl bl, ECase e' pl' gl' bl' => 
     bExpression_eq_dec e e' &&
    (fix blist l l' := match l, l' with
                       | [], [] => true
                       | x::xs, x'::xs' => andb (bPattern_eq_dec x x') (blist xs xs')
                       | _, _ => false
                       end) pl pl' &&
    (fix blist l l' := match l, l' with
                       | [], [] => true
                       | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                       | _, _ => false
                       end) gl gl' &&
    (fix blist l l' := match l, l' with
                       | [], [] => true
                       | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                       | _, _ => false
                       end) bl bl'
   | ELet s el e, ELet s' el' e' => 
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (eqb x x') (blist xs xs')
                        | _, _ => false
                        end) s s' &&
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                        | _, _ => false
                        end) el el' &&
     bExpression_eq_dec e e'
   | ELetRec fids varlists bodylists e, ELetRec fids' varlists' bodylists' e' => 
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (equal x x') (blist xs xs')
                        | _, _ => false
                        end) fids fids' &&
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (
                          (fix blist l l' := 
                             match l, l' with
                             | [], [] => true
                             | x::xs, x'::xs' => andb (eqb x x') (blist xs xs')
                             | _, _ => false
                             end)
                       x x') (blist xs xs')
                       | _, _ => false
       end) varlists varlists' &&
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                        | _, _ => false
                        end) bodylists bodylists' &&
     bExpression_eq_dec e e'
   | EMap kl vl, EMap kl' vl' => 
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                        | _, _ => false
                       end) kl kl' &&
     (fix blist l l' := match l, l' with
                        | [], [] => true
                        | x::xs, x'::xs' => andb (bExpression_eq_dec x x') (blist xs xs')
                        | _, _ => false
                        end) vl vl'
   | ETry e e1 e2 v1 vex1 vex2 vex3, ETry e' e1' e2' v1' vex1' vex2' vex3' =>
     bExpression_eq_dec e e' && 
     bExpression_eq_dec e1 e1' && 
     bExpression_eq_dec e2 e2' && 
     eqb v1 v1' && eqb vex1 vex1' && eqb vex2 vex2' && eqb vex3 vex3'
   | _, _ => false
  end.


  Fixpoint bValue_eq_dec (e1 e2 : Value) : bool :=
  match e1, e2 with
  | VNil, VNil => true
  | VLit l, VLit l' => bLiteral_eq_dec l l'
  (** Closures in Core Erlang are never equal *)
  | VClos env ext n p b, VClos env' ext' n' p' b' => Nat.eqb n n'
  | VCons hd tl, VCons hd' tl' => bValue_eq_dec hd hd' && bValue_eq_dec tl tl'
  | VTuple l, VTuple l' => 
    (fix blist l l' := match l, l' with
                       | [], [] => true
                       | x::xs, x'::xs' => andb (bValue_eq_dec x x') (blist xs xs')
                       | _, _ => false
                       end) l l'
  | VMap kl vl, VMap kl' vl' => 
    (fix blist l l' := match l, l' with
                       | [], [] => true
                       | x::xs, x'::xs' => andb (bValue_eq_dec x x') (blist xs xs')
                       | _, _ => false
                       end) kl kl' &&
    (fix blist l l' := match l, l' with
                       | [], [] => true
                       | x::xs, x'::xs' => andb (bValue_eq_dec x x') (blist xs xs')
                       | _, _ => false
                       end) vl vl'
  | _, _ => false
  end.

(** Properties of uequal *)
  Proposition uequal_eq (v0 v : Var + FunctionIdentifier):
    uequal v0 v = true <-> v0 = v.
  Proof.
    intros. split; intros.
    { destruct v0, v.
      * inversion H. apply eqb_eq in H1. subst. reflexivity.
      * inversion H.
      * inversion H.
      * inversion H. destruct f, f0. inversion H1. apply Bool.andb_true_iff in H2. 
        inversion H2.
        apply eqb_eq in H0. apply Nat.eqb_eq in H3. subst. reflexivity.
    }
    { destruct v, v0.
      * inversion H. subst. simpl. apply eqb_refl.
      * inversion H.
      * inversion H.
      * inversion H. simpl. destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl.
        reflexivity.
    }
  Qed.

  Proposition uequal_neq (v0 v : Var + FunctionIdentifier):
    uequal v0 v = false <-> v0 <> v.
  Proof.
    split; intros.
    { destruct v0, v.
      * simpl in *. apply eqb_neq in H. unfold not in *. intros. apply H. inversion H0. 
        reflexivity.
      * unfold not. intro. inversion H0.
      * unfold not. intro. inversion H0.
      * destruct f, f0. simpl in H. apply Bool.andb_false_iff in H. inversion H.
        - apply eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
        - apply Nat.eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1.
          reflexivity.
    }
    { destruct v0, v.
      * simpl in *. apply eqb_neq. unfold not in *. intro. apply H. subst. reflexivity.
      * simpl. reflexivity.
      * simpl. reflexivity.
      * simpl. destruct f, f0. simpl. apply Bool.andb_false_iff.
        unfold not in H. case_eq ((s =? s0)%string); intros.
        - right. apply eqb_eq in H0. apply Nat.eqb_neq. unfold not. intro. apply H. subst.
          reflexivity.
        - left. reflexivity.
    }
  Qed.

  Proposition uequal_refl (var : Var + FunctionIdentifier) :
  uequal var var = true.
  Proof.
    destruct var.
    * simpl. apply eqb_refl.
    * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  Qed.

  Proposition uequal_sym (v1 v2 : Var + FunctionIdentifier) :
    uequal v1 v2 = uequal v2 v1.
  Proof.
    destruct v1, v2.
    * simpl. rewrite eqb_sym. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. destruct f, f0. simpl. rewrite eqb_sym, Nat.eqb_sym. reflexivity.
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
    apply lt_int_int. omega.
  Qed.

  Lemma lt_str : lt_Literal (Atom "aaaa") (Atom "aaaa2").
  Proof.
    apply lt_atom_atom. apply lts_tail. apply lts_tail. apply lts_tail. apply lts_tail.
    apply lts_empty.
  Qed.

  Inductive lt_Value : Value -> Value -> Prop :=
  | lt_lit_lit l l' : lt_Literal l l' -> lt_Value (VLit l) (VLit l')
  | lt_lit_other l v : (forall l' : Literal, v <> VLit l') -> lt_Value (VLit l) (v)

  | lt_closure_closure ref params body ref' ext ext' params' body' n n' : 
     Nat.lt n n' ->
     lt_Value (VClos ref ext n params body) (VClos ref' ext' n' params' body')
  | lt_closure_other v ref ext body params n: 
    (forall ref' ext' n' params' body', v <> VClos ref' ext' n' params' body') -> 
    (forall l : Literal, v <> VLit l) 
  ->
    lt_Value (VClos ref ext n params body) (v)
  | lt_tuple_tuple_nil exps' : exps' <> [] -> lt_Value (VTuple [])  (VTuple exps')
  | lt_tuple_length exps exps' : length exps < length exps' -> 
      lt_Value (VTuple exps) (VTuple exps')
  | lt_tuple_tuple_hd exps exps' hd hd' : 
     length exps = length exps' ->
     lt_Value hd hd' 
   ->
     lt_Value (VTuple (hd::exps)) (VTuple (hd'::exps'))
  | lt_tuple_tuple_tl exps exps' hd hd' : 
    length exps = length exps' -> 
    hd = hd' -> 
    lt_Value (VTuple exps) (VTuple exps') 
  ->
    lt_Value (VTuple (hd::exps)) (VTuple (hd'::exps'))
  | lt_tuple_map (l kl vl : list Value): lt_Value (VTuple l) (VMap kl vl)
  | lt_tuple_list l hd tl: lt_Value (VTuple l) (VCons hd tl)
  | lt_tuple_emptylist l: lt_Value (VTuple l) (VNil)
  | lt_map_map_nil kl' vl': length kl' = length vl' -> lt_Value (VMap [] []) (VMap kl' vl')
  | lt_map_length kl kl' vl vl' : length kl < length kl' ->
      lt_Value (VMap kl vl) (VMap kl' vl')
  | lt_map_map_hd (kl kl' vl vl' : list Value) hd hd' hdv hdv':
    length kl = length kl' -> 
    lt_Value hd hd' 
  ->
    lt_Value (VMap (hd::kl) (hdv::vl)) (VMap (hd'::kl') (hdv'::vl'))
  | lt_map_map_vl (kl kl' vl vl' : list Value) hd hd' hdv hdv':
    length kl = length kl' -> 
    lt_Value (VMap kl vl) (VMap kl' vl')
  -> 
    lt_Value (VMap (hd::kl) (hdv::vl)) (VMap (hd'::kl') (hdv'::vl'))
  | lt_map_emptylist kl vl : lt_Value (VMap kl vl) VNil
  | lt_map_list kl vl hd tl : lt_Value (VMap kl vl) (VCons hd tl)
  | lt_emptylist_list hd tl : lt_Value VNil (VCons hd tl)
  | lt_list_list_head hd hd' tl tl': lt_Value hd hd' -> lt_Value (VCons hd tl) (VCons hd' tl')
  | lt_lis_list_tail hd hd' tl tl': 
    hd = hd' -> 
    lt_Value tl tl'
  ->
    lt_Value (VCons hd tl) (VCons hd' tl')
  .

  Example e1 : lt_Value (VTuple []) (VNil).
  Proof.
    apply lt_tuple_emptylist.
  Qed.

  Example e2 : lt_Value (VTuple []) (VTuple [VNil]).
  Proof.
    apply lt_tuple_tuple_nil. congruence.
  Qed.

  Example e3 : lt_Value (VMap [VLit (Integer 5)] [VNil])
                        (VMap [VNil] [VNil]).
  Proof.
    apply lt_map_map_hd; auto. apply lt_lit_other. intros. congruence.
  Qed.

  (** Boolean comparison: *)

  Import Coq.Strings.Ascii.

  Fixpoint string_less (s1 s2 : string) : bool :=
  match s1, s2 with
  | EmptyString, String a s => true
  | String a s, String a' s' => (nat_of_ascii a <? nat_of_ascii a') || string_less s s'
  | _, _ => false
  end.

  Fixpoint literal_less (l1 l2 : Literal) : bool :=
  match l1, l2 with
  | Integer x, Integer x' => Z.ltb x x'
  | Atom s, Atom s' => string_less s s'
  | Integer x, Atom s => true
  | _, _ => false
  end.

  Section bool_less_list.
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

  End bool_less_list.


  Fixpoint value_less (k v : Value) : bool :=
  match k, v with
  | VLit l, VLit l' => literal_less l l'
  | VLit _, _ => true

  | VClos _ _ n _ _, VClos _ _ n' _ _ => Nat.ltb n n'
  | VClos _ _ _ _ _, VTuple _ => true
  | VClos _ _ _ _ _, VMap _ _ => true
  | VClos _ _ _ _ _, VNil => true
  | VClos _ _ _ _ _, VCons _ _ => true
  | VTuple l, VTuple l' => orb (Nat.ltb (length l) (length l'))
                               (andb (Nat.eqb (length l) (length l')) 
                                     (list_less Value value_less bValue_eq_dec l l'))
  | VTuple _, VNil => true
  | VTuple _, VMap _ _ => true
  | VTuple l, VCons _ _ => true
  | VMap kl vl, VMap kl' vl' => orb (Nat.ltb (length kl) (length kl')) 
                                    (andb (Nat.eqb (length kl) (length kl'))
                                       (orb (list_less Value value_less bValue_eq_dec kl kl')
                                          (andb (list_equal Value bValue_eq_dec kl kl')
                                            (list_less Value value_less bValue_eq_dec vl vl')) ))
  | VMap _ _, VNil => true
  | VMap _ _, VCons _ _ => true
  | VNil, VCons _ _ => true
  | VCons hd tl, VCons hd' tl' => if bValue_eq_dec hd hd' then value_less tl tl' 
                                                          else value_less hd hd'
  | _, _ => false
  end.

End Comparisons.

Compute value_less (VMap [ErrorValue; ErrorValue] [ErrorValue; VLit (Integer 7)])
                   (VMap [ErrorValue; ErrorValue] [ErrorValue; VLit (Integer 8)]).

End Core_Erlang_Equalities.
