From CoreErlang.BigStep Require Export SideEffects.
Require Export Coq.Sorting.Permutation.

Import ListNotations.

(**
  Built-in function simulation

  BIFCode: we need it in order to enable better pattern-matching on strings
 *)
(* Inductive PrimopCode :=
| PMatchFail
| PNothing
. *)


Inductive BIFCode :=
| BPlus | BMinus | BMult | BDivide | BRem | BDiv | BSl | BSr | BAbs
| BFwrite | BFread 
| BAnd | BOr | BNot
| BEq | BTypeEq | BNeq | BTypeNeq
| BApp | BMinusMinus
| BTupleToList | BListToTuple
| BLt | BLe | BGt | BGe
| BLength | BTupleSize
| BTl | BHd
| BElement | BSetElement
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean
| BError
| PMatchFail
| BNothing
.

Definition convert_primop_to_code (s : string) : BIFCode :=
match s with
  (** primops *)
  | ("match_fail"%string) => PMatchFail
  | _ => BNothing
end.


Definition convert_string_to_code (s : string * string) : BIFCode :=
match s with
| ("erlang"%string, "+"%string) => BPlus
| ("erlang"%string, "-"%string) => BMinus
| ("erlang"%string, "*"%string) => BMult
| ("erlang"%string, "/"%string) => BDivide
| ("erlang"%string, "bsl"%string) => BSl
| ("erlang"%string, "bsr"%string) => BSr
| ("erlang"%string, "rem"%string) => BRem
| ("erlang"%string, "div"%string) => BDiv
| ("erlang"%string, "abs"%string) => BAbs
| ("io"%string, "fwrite"%string) => BFwrite
| ("io"%string, "fread"%string) => BFread
| ("erlang"%string, "and"%string) => BAnd
| ("erlang"%string, "or"%string) => BOr
| ("erlang"%string, "not"%string) => BNot
| ("erlang"%string, "=="%string) => BEq
| ("erlang"%string, "=:="%string) => BTypeEq
| ("erlang"%string, "/="%string) => BNeq
| ("erlang"%string, "=/="%string) => BTypeNeq
| ("erlang"%string, "++"%string) => BApp
| ("erlang"%string, "--"%string) => BMinusMinus
| ("erlang"%string, "tuple_to_list"%string) => BTupleToList
| ("erlang"%string, "list_to_tuple"%string) => BListToTuple
| ("erlang"%string, "<"%string) => BLt
| ("erlang"%string, ">"%string) => BGt
| ("erlang"%string, "=<"%string) => BLe
| ("erlang"%string, ">="%string) => BGe
| ("erlang"%string, "length"%string) => BLength
| ("erlang"%string, "tuple_size"%string) => BTupleSize
| ("erlang"%string, "hd"%string) => BHd
| ("erlang"%string, "tl"%string) => BTl
| ("erlang"%string, "element"%string) => BElement
| ("erlang"%string, "setelement"%string) => BSetElement
| ("erlang"%string, "is_number"%string) => BIsNumber
| ("erlang"%string, "is_integer"%string) => BIsInteger
| ("erlang"%string, "is_atom"%string) => BIsAtom
| ("erlang"%string, "is_boolean"%string) => BIsBoolean
| ("erlang"%string, "error"%string) => BError
(** anything else *)
| _ => BNothing
end.

(** For biuilt-in arithmetic calls *)
Definition eval_arith (mname : string) (fname : string) (params : list Value) :  ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
(** addition *)
| BPlus, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a + b))]
| BPlus, [a; b]                               => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** subtraction *)
| BMinus, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a - b))]
| BMinus, [a; b]                               => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** unary minus *)
| BMinus, [VLit (Integer a)]                   => inl [VLit (Integer (0 - a))]
| BMinus, [a]                                  => inr (badarith (VTuple [VLit (Atom fname); a]))
(** unary plus *)
| BPlus, [VLit (Integer a)]                   => inl [VLit (Integer a)]
| BPlus, [a]                                  => inr (badarith (VTuple [VLit (Atom fname); a]))
(** multiplication *)
| BMult, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a * b))]
| BMult, [a; b]                               => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** division *)
| BDivide, [VLit (Integer a); VLit (Integer 0)] => inr (badarith (VTuple [VLit (Atom fname); VLit (Integer a); VLit (Integer 0)]))
| BDivide, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a / b))]
| BDivide, [a; b]                               => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** rem *)
| BRem, [VLit (Integer a); VLit (Integer 0)] => inr (badarith (VTuple [VLit (Atom fname); VLit (Integer a); VLit (Integer 0)]))
| BRem, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (Z.rem a b))]
| BRem, [a; b]                               => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** div *)
| BDiv, [VLit (Integer a); VLit (Integer 0)] => inr (badarith (VTuple [VLit (Atom fname); VLit (Integer a); VLit (Integer 0)]))
| BDiv, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (Z.quot a b))]
| BDiv, [a; b]                               => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** bsl *)
| BSl, [VLit (Integer a); VLit (Integer b)]  => inl [VLit (Integer (Z.shiftl a b))]
| BSl, [a; b]                                => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** bsr *)
| BSr, [VLit (Integer a); VLit (Integer b)]  => inl [VLit (Integer (Z.shiftr a b))]
| BSr, [a; b]                                => inr (badarith (VTuple [VLit (Atom fname); a; b]))
(** abs *)
| BAbs, [VLit (Integer a)]                   => inl [VLit (Integer (Z.abs a))]
| BAbs, [a]                                  => inr (badarg (VTuple [VLit (Atom fname); a]))
(** anything else *)
| _         , _                              => inr (undef (VLit (Atom fname)))
end.

(** For IO maniputaion: *)
Definition eval_io (mname : string) (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((ValueSequence + Exception) * SideEffectList) :=
match convert_string_to_code (mname, fname), length params, params with
(** writing *)
| BFwrite, 1, _ => (inl [ok]                                  , eff ++ [(Output, params)])
(** reading *)
| BFread, 2, e => (inl [VTuple [ok; nth 1 params ErrorValue]], eff ++ [(Input, params)])
(** anything else *)
| _              , _, _ => (inr (undef (VLit (Atom fname)))           , eff)
end.

Definition eval_logical  (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
(** logical and *)
| BAnd, [a; b] => 
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => inl [ffalse]
   | VLit (Atom "true") , VLit (Atom "false")   => inl [ffalse]
   | VLit (Atom "false"), VLit (Atom "false")   => inl [ffalse]
   | _                         , _              => inr (badarg (VTuple [VLit (Atom fname); a; b]))
   end
(** logical or *)
| BOr, [a; b] =>
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "true") , VLit (Atom "false")   => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "false")   => inl [ffalse]
   | _                         , _              => inr (badarg (VTuple [VLit (Atom fname); a; b]))
   end
(** logical not *)
| BNot, [a] =>
   match a with
   | VLit (Atom "true")  => inl [ffalse]
   | VLit (Atom "false") => inl [ttrue]
   | _                   => inr (badarg (VTuple [VLit (Atom fname); a]))
   end
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_equality (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
| BEq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeEq, [v1; v2] => if Value_eqb v1 v2 then inl [ttrue] else inl [ffalse]
| BNeq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeNeq, [v1; v2] => if Value_eqb v1 v2 then inl [ffalse] else inl [ttrue]
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint is_shallow_proper_list (v : Value) : bool :=
match v with
| VNil => true
| VCons x y => is_shallow_proper_list y
| _ => false
end.

Fixpoint eval_append (v1 v2 : Value) : ValueSequence + Exception :=
match v1, v2 with
| VNil, x => inl [x]
| VCons x y, x' => match eval_append y x' with
                   | inr ex    => inr (badarg (VTuple [VLit (Atom "++"); v1; v2]))
                   | inl [res] => inl [VCons x res]
                   | _ => inr (badarg (VTuple [VLit (Atom "++"); v1; v2]))
                   end
| _, _ => inr (badarg (VTuple [VLit (Atom "++"); v1; v2]))
end.

Fixpoint subtract_elem (v1 v2 : Value) : Value :=
match v1 with
| VNil => VNil
| VCons x y =>
  match y with
  | VNil => if Value_eqb x v2 then VNil else VCons x y
  | VCons z w => if Value_eqb x v2 then y else VCons x (subtract_elem y v2)
  | z => if Value_eqb x v2 then VCons z VNil else if Value_eqb z v2 then VCons x VNil else VCons x y
  end
| _ => ErrorValue
end.

Fixpoint eval_subtract (v1 v2 : Value) : ValueSequence + Exception :=
if andb (is_shallow_proper_list v1) (is_shallow_proper_list v2) then
  match v1, v2 with
  | VNil, VNil => inl [VNil]
  | VNil, VCons x y => inl [VNil]
  | VCons x y, VNil => inl [VCons x y]
  | VCons x y, VCons x' y' => 
     match y' with
     | VNil => inl [subtract_elem (VCons x y) x']
     | VCons z w => eval_subtract (subtract_elem (VCons x y) x') y'
     | z => inl [subtract_elem (subtract_elem (VCons x y) x') z]
     end
  | _        , _         => inr (badarg (VTuple [VLit (Atom "--"); v1; v2]))
  end
else
  inr (badarg (VTuple [VLit (Atom "--"); v1; v2])).

Definition eval_transform_list (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
| BApp, [v1; v2]        => eval_append v1 v2
| BMinusMinus, [v1; v2] => eval_subtract v1 v2
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition transform_tuple (v : Value) : ValueSequence + Exception :=
match v with
| VTuple l => inl [((fix unfold_list l :=
                   match l with
                   | [] => VNil
                   | x::xs => VCons x (unfold_list xs)
                   end) l)]
| _        => inr (badarg (VTuple [VLit (Atom "tuple_to_list"); v]))
end.

Fixpoint transform_list (v : Value) : list Value + Exception :=
match v with
| VNil      => inl []
| VCons x y => match y with
               | VNil => inl [x]
               | VCons z w => match (transform_list y) with
                              | inr ex => inr ex
                              | inl res => inl (x::res)
                              end
               | _ => inr (badarg (VTuple [VLit (Atom "list_to_tuple"); v]))
               end
| _         => inr (badarg (VTuple [VLit (Atom "list_to_tuple"); v]))
end.

Definition eval_list_tuple (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
| BTupleToList, [v] => transform_tuple v
| BListToTuple, [v] => match (transform_list v) with
                                 | inr ex => inr ex
                                 | inl l => inl [VTuple l]
                                 end
| _                     , _   => inr (undef (VLit (Atom fname)))
end.

Definition eval_cmp (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
| BLt,  [v1; v2] => if Value_ltb v1 v2 then inl [ttrue] else inl [ffalse]
| BLe, [v1; v2] => if orb (Value_ltb v1 v2) (Value_eqb v1 v2) 
                           then inl [ttrue] else inl [ffalse]
| BGt,  [v1; v2] => if Value_ltb v2 v1 then inl [ttrue] else inl [ffalse]
| BGe, [v1; v2] => if orb (Value_ltb v2 v1) (Value_eqb v1 v2) 
                           then inl [ttrue] else inl [ffalse]
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_length (params : list Value) : ValueSequence + Exception :=
match params with
| [v] => let res :=
          (fix len val := match val with
                         | VNil => inl Z.zero
                         | VCons x y => let res := len y in
                                          match res with
                                          | inl n => inl (Z.add 1 n)
                                          | inr _ => res
                                          end
                         | _ => inr (badarg (VTuple [VLit (Atom "length"); v]))
                         end) v in
        match res with
        | inl n => inl [VLit (Integer n)]
        | inr ex => inr ex
        end
| _ => inr (undef (VLit (Atom "length")))
end.

Definition eval_tuple_size (params : list Value) : ValueSequence + Exception :=
match params with
| [VTuple l] => inl [VLit (Integer (Z.of_nat (length l)))]
| [v] => inr (badarg (VTuple [VLit (Atom "tuple_size"); v]))
| _ => inr (undef (VLit (Atom "tuple_size")))
end.

Definition eval_hd_tl (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
| BHd, [VCons x y] => inl [x]
| BHd, [v] => inr (badarg (VTuple [VLit (Atom fname); v]))
| BTl, [VCons x y] => inl [y]
| BTl, [v] => inr (badarg (VTuple [VLit (Atom fname); v]))
| _, _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint replace_nth_error {A : Type} (l : list A) (i : nat) (e : A) : option (list A) :=
match i, l with
| 0, x::xs => Some (e::xs)
| _, [] => None
| S n, x::xs => match (replace_nth_error xs n e) with
               | None => None
               | Some l' => Some (x::l')
               end
end.

Definition eval_elem_tuple (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code (mname, fname), params with
| BElement, [VLit (Integer i); VTuple l] =>
    match i with
    | Z.pos p => match nth_error l (pred (Pos.to_nat p)) with
                 | None   => inr (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
                 | Some v => inl [v]
                 end
    | _       => inr (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
    end
| BElement, [v1; v2] => inr (badarg (VTuple [VLit (Atom fname); v1; v2]))
| BSetElement, [VLit (Integer i); VTuple l; val] =>
    match i with
    | Z.pos p => match replace_nth_error l (pred (Pos.to_nat p)) val with
                 | None    => inr (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l; val]))
                 | Some l' => inl [VTuple l']
                 end
    | _       => inr (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
    end
| BSetElement, [v1; v2; v3] => inr (badarg (VTuple [VLit (Atom fname); v1; v2; v3]))
| _, _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_check (mname : string) (fname : string) (params : list Value) : ValueSequence + Exception := 
match convert_string_to_code (mname, fname), params with
| BIsNumber, [VLit (Integer i)]     => inl [ttrue]
| BIsNumber, [_]                    => inl [ffalse]
| BIsInteger, [VLit (Integer i)]    => inl [ttrue]
| BIsInteger, [_]                   => inl [ffalse] 
| BIsAtom, [VLit (Atom a)]          => inl [ttrue]
| BIsAtom, [_]                      => inl [ffalse]
| BIsBoolean, [VLit (Atom "true")]
| BIsBoolean, [VLit (Atom "false")] => inl [ttrue]
| BIsBoolean, [_]                   => inl [ffalse]
| _, _              => inr (undef (VLit (Atom fname)))
end.

Definition eval_error (mname : string) (fname : string) (params : list Value) : Exception :=
match params with
| [VTuple [val]] => (Error, val, VNil)
| [VTuple [val; reas]] => (Error, val, reas)
| [val]        => (Error, val, VNil)
| [val1; val2] => (Error, val1, val2)
| _            => undef (VLit (Atom fname))
end.

Definition eval_primop_error (fname : string) (params : list Value) : Exception :=
match params with
| [VTuple [val]] => (Error, val, VNil)
| [VTuple [val; reas]] => (Error, val, reas)
| [val]        => (Error, val, VNil)
| [val1; val2] => (Error, val1, val2)
| _            => undef (VLit (Atom fname))
end.

(* Eval for primary operations *)
Definition primop_eval (fname : string) (params : list Value) (eff : SideEffectList) : ((ValueSequence + Exception) * SideEffectList) :=
match convert_primop_to_code ( fname) with
  | PMatchFail  =>  (inr (eval_primop_error fname params), eff)
  | _ => (inr (undef (VLit (Atom fname))), eff)
end.


(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (mname : string) (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((ValueSequence + Exception) * SideEffectList) :=
match convert_string_to_code (mname, fname) with
| BPlus | BMinus | BMult | BDivide | BRem | BDiv
| BSl   | BSr    | BAbs                           => (eval_arith mname fname params, eff)
| BFwrite | BFread                                => eval_io mname fname params eff
| BAnd | BOr | BNot                               => (eval_logical mname fname params, eff)
| BEq | BTypeEq | BNeq | BTypeNeq                 => (eval_equality mname fname params, eff)
| BApp | BMinusMinus                              => (eval_transform_list mname fname params, eff)
| BTupleToList | BListToTuple                     => (eval_list_tuple mname fname params, eff)
| BLt | BGt | BLe | BGe                           => (eval_cmp mname fname params, eff)
| BLength                                         => (eval_length params, eff)
| BTupleSize                                      => (eval_tuple_size params, eff)
| BHd | BTl                                       => (eval_hd_tl mname fname params, eff)
| BElement | BSetElement                          => (eval_elem_tuple mname fname params, eff)
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean   => (eval_check mname fname params, eff)
| BError                                          => (inr (eval_error mname fname params), eff)
(** anything else *)
| BNothing  | PMatchFail                                       => (inr (undef (VLit (Atom fname))), eff)
end.


Theorem primop_eval_effect_extension fname vals eff1 res eff2 :
  primop_eval fname vals eff1 = (res, eff2)
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros. unfold primop_eval in H.
  
  destruct (convert_primop_to_code fname) eqn:Hfname; simpl in H.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check, eval_error in H; rewrite Hfname in H; destruct vals;
    [ inversion H; exists []; rewrite app_nil_r; auto |
      destruct v; try (destruct vals; inversion H; exists []; rewrite app_nil_r; auto) ]).
  1-39 : inversion H; exists []; rewrite app_nil_r; auto.
Qed.

Theorem eval_effect_extension mname fname vals eff1 res eff2 :
  eval mname fname vals eff1 = (res, eff2)
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros. unfold eval in H.
  destruct (convert_string_to_code (mname,fname)) eqn:Hfname; simpl in H.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check, eval_error in H; rewrite Hfname in H; destruct vals;
    [ inversion H; exists []; rewrite app_nil_r; auto |
      destruct v; try (destruct vals; inversion H; exists []; rewrite app_nil_r; auto) ]).
  * unfold eval_io in H; rewrite Hfname in H; destruct (length vals) eqn:Hl; inversion H.
    - exists []; rewrite app_nil_r. auto.
    - destruct n.
      + inversion H. exists [(Output, vals)]. auto.
      + inversion H. exists []; rewrite app_nil_r. auto.
  * unfold eval_io in H; rewrite Hfname in H; destruct (length vals) eqn:Hl; inversion H.
    - exists []; rewrite app_nil_r. auto.
    - destruct n.
      + inversion H. exists []; rewrite app_nil_r. auto.
      + destruct n.
        ** inversion H.  exists [(Input, vals)]. auto.
        ** inversion H. exists []; rewrite app_nil_r. auto.
  * unfold eval_length in H.
    destruct vals; inversion H; exists []; rewrite app_nil_r; auto.
  * unfold eval_tuple_size in H.
    destruct vals; inversion H; exists []; rewrite app_nil_r; auto.
  * inversion H. exists []; rewrite app_nil_r; auto.
  * inversion H. exists []; rewrite app_nil_r; auto.
  * inversion H. exists []; rewrite app_nil_r; auto.
  Qed.

Theorem primop_eval_effect_exists_snd {mname fname vals eff} :
  exists eff', snd (eval mname fname vals eff) = eff'.
Proof.
  unfold eval. destruct (convert_string_to_code (mname, fname)) eqn:Hfname.
  all: try ( unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check, eval_error; rewrite Hfname; destruct vals; 
             [ exists eff | simpl; auto ]).
  all: simpl; auto.
  1-9, 12-39: exists eff; auto.
  * unfold eval_io. rewrite Hfname. destruct (length vals).
    - exists eff. auto.
    - destruct n. eexists. simpl. reflexivity.
      eexists. reflexivity.
  * unfold eval_io. rewrite Hfname. destruct (length vals).
    - exists eff. auto.
    - destruct n. eexists. simpl. reflexivity.
      eexists. reflexivity.
Qed.

Theorem eval_effect_irrelevant_snd {mname fname vals eff eff'}:
  snd (eval mname fname vals eff) = eff ++ eff'
->
  forall eff0, snd (eval mname fname vals eff0) = eff0 ++ eff'.
Proof.
  intros.
  unfold eval in *. destruct (convert_string_to_code (mname, fname)) eqn:Hfname.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check in *; rewrite Hfname in *; destruct vals;
    simpl in *; rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity).
  * unfold eval_io in *. rewrite Hfname in *. destruct (length vals).
    - simpl in *; rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
    - destruct n; simpl in *.
      + apply app_inv_head in H. rewrite H. reflexivity.
      + rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
  * unfold eval_io in *. rewrite Hfname in *. destruct (length vals).
    - simpl in *; rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
    - destruct n; simpl in *.
      + simpl in *; rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
      + destruct n.
        ** apply app_inv_head in H. rewrite H. reflexivity.
        ** rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
  * unfold eval_length. simpl in *.
    rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
  * unfold eval_tuple_size in *.
    rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
  * rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
  * rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
 * rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
             rewrite app_nil_r; reflexivity.
Qed.

Theorem primop_eval_effect_irrelevant_snd {fname vals eff eff'}:
  snd (primop_eval fname vals eff) = eff ++ eff'
->
  forall eff0, snd (primop_eval fname vals eff0) = eff0 ++ eff'.
Proof.
  intros.
  unfold primop_eval in *. destruct (convert_primop_to_code fname) eqn:Hfname.
  all: rewrite <- app_nil_r in H at 1; apply app_inv_head in H; subst;
  rewrite app_nil_r; reflexivity.
Qed.


Theorem eval_effect_irrelevant_fst {mname fname vals eff eff0}:
  fst (eval mname fname vals eff) = fst (eval mname fname vals eff0).
Proof.
  unfold eval. destruct (convert_string_to_code (mname, fname)) eqn:Hfname.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check; rewrite Hfname; destruct vals;
    [ reflexivity |
      destruct v; try (destruct vals; auto) ]).
  * unfold eval_io. rewrite Hfname. destruct (length vals).
    - reflexivity.
    - destruct n; reflexivity.
  * unfold eval_io. rewrite Hfname. destruct (length vals).
    - reflexivity.
    - destruct n. reflexivity.
      + destruct n; reflexivity.
  * unfold eval_length. reflexivity.
  * reflexivity.
  * reflexivity.
  * reflexivity.
  * reflexivity.
Qed.

Theorem primop_eval_effect_irrelevant_fst {fname vals eff eff0}:
  fst (primop_eval fname vals eff) = fst (primop_eval fname vals eff0).
Proof.
  unfold primop_eval. destruct (convert_primop_to_code  fname) eqn:Hfname.
  all: reflexivity.
Qed.

Theorem eval_effect_extension_snd mname fname vals eff1 eff2 :
  snd (eval mname fname vals eff1) = eff2
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros.
  pose (eval_effect_extension mname fname vals eff1 (fst (eval mname fname vals eff1)) eff2).
  assert (eval mname fname vals eff1 = (fst (eval mname fname vals eff1), eff2)).
  {
    rewrite surjective_pairing at 1.
    rewrite H. auto.
  }
  apply e. assumption.
Qed.

Theorem primop_eval_effect_extension_snd fname vals eff1 eff2 :
  snd (primop_eval  fname vals eff1) = eff2
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros.
  pose (primop_eval_effect_extension fname vals eff1 (fst (primop_eval fname vals eff1)) eff2).
  assert (primop_eval fname vals eff1 = (fst (primop_eval fname vals eff1), eff2)).
  {
    rewrite surjective_pairing at 1.
    rewrite H. auto.
  }
  apply e. assumption.
Qed.

Theorem eval_effect_permutation m f vals eff eff' :
  Permutation eff eff'
->
  Permutation (snd (eval m f vals eff)) (snd (eval m f vals eff')).
Proof.
  intros.
  unfold eval. destruct (convert_string_to_code (m,f)) eqn:Hfname.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check; rewrite Hfname; destruct vals; auto).
  * unfold eval_io. rewrite Hfname. destruct (length vals).
    - simpl. auto.
    - destruct n.
      + simpl. apply Permutation_app_tail. auto.
      + auto.
  * unfold eval_io. rewrite Hfname. destruct (length vals).
    - auto.
    - destruct n. auto.
      destruct n.
      + simpl. apply Permutation_app_tail. auto.
      + auto.
  * unfold eval_length. auto.
  * auto.
  * auto.
  * auto.
  * auto.
Qed.

Proposition plus_comm_basic {e1 e2 t : Value} {eff : SideEffectList} : 
eval "erlang"%string "+"%string [e1 ; e2] eff = (inl [t], eff)
->
eval "erlang"%string "+"%string [e2; e1] eff = (inl [t], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_value {e1 e2 v : Value} (eff eff2 : SideEffectList) : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = (inl [v], eff)
->
  eval "erlang"%string "+"%string [e2; e1] eff2 = (inl [v], eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_extended {e1 e2 : Value} (v : ValueSequence + Exception) (eff eff2 : SideEffectList) : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = (v, eff)
->
  exists v', eval "erlang"%string "+"%string [e2; e1] eff2 = (v', eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-7, 9-36: eexists; try(inversion H1; reflexivity).
  * eexists. reflexivity.
Qed.

Proposition plus_effect_unmodified {e1 e2 : Value} (v' : ValueSequence + Exception) (eff eff2 : SideEffectList) :
  eval "erlang"%string "+"%string [e1 ; e2] eff = (v', eff2)
->
  eff = eff2.
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inversion H1; reflexivity).
  all: try(destruct l); try(inversion H1; reflexivity).
  all: destruct l0.
Qed.

Proposition plus_effect_changeable {v1 v2 : Value} (v' : ValueSequence + Exception) (eff eff2 : SideEffectList) :
  eval "erlang"%string "+"%string [v1; v2] eff = (v', eff)
->
  eval "erlang"%string "+"%string [v1; v2] eff2 = (v', eff2).
Proof.
  intros. simpl in *. case_eq v1; case_eq v2; intros; subst.
  all: try(inversion H; reflexivity).
  all: try(destruct l); try(inversion H; reflexivity).
  all: destruct l0; inversion H; auto.
Qed.

Section Tests.

(** Tests *)

Goal (eval "erlang" "+" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl [VLit (Integer (-1))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VTuple [VLit (Atom "-"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Atom "foo")]) [] 
    = (inr (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Atom "foo")]) [] 
    = (inr (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo")])), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal (eval "erlang" "bsl" [VLit (Integer 10); VLit (Integer 20)]) [] = (inl [VLit (Integer 10485760)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Integer 10); VLit (Integer 20)]) [] = (inl [VLit (Integer 0)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VTuple [VLit (Atom "bsl"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VTuple [VLit (Atom "bsl"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VTuple [VLit (Atom "bsr"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VTuple [VLit (Atom "bsr"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Atom "foo")]) [] 
    = (inr (undef (VLit (Atom "bsl"))), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Atom "foo")]) [] 
    = (inr (undef (VLit (Atom "bsr"))), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal (eval "erlang" "not" [ttrue]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [ffalse]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [VLit (Integer 5)]) [] = (inr (badarg (VTuple [VLit (Atom "not"); VLit (Integer 5)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [VLit (Integer 5); VEmptyTuple]) [] = (inr (undef (VLit (Atom "not"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "and" [ttrue; ttrue]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue; ffalse]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ffalse; ttrue]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ffalse; ffalse]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue; VEmptyTuple]) [] = (inr (badarg (VTuple [VLit (Atom "and"); ttrue; VTuple []])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue]) [] = (inr (undef (VLit (Atom "and"))), []). Proof. reflexivity. Qed.

Goal (eval "erlang" "or" [ttrue; ttrue]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue; ffalse]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ffalse; ttrue]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ffalse; ffalse]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue; VEmptyTuple]) [] = (inr (badarg (VTuple [VLit (Atom "or"); ttrue; VTuple []])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue]) [] = (inr (undef (VLit (Atom "or"))), []).
Proof. reflexivity. Qed.

Goal (eval "io" "fwrite" [ttrue]) [] = (inl [ok], [(Output, [ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fwrite" [VMap [(ttrue, ttrue)]]) [] = (inl [ok], [(Output, [VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fwrite" []) [] = (inr (undef (VLit (Atom "fwrite"))), []).
Proof. reflexivity. Qed.

Goal (eval "io" "fread" [VLit (Atom "foo.txt"); ttrue]) [] = 
   (inl [VTuple [ok; ttrue]], [(Input, [VLit (Atom "foo.txt"); ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]]) [] = 
   (inl [VTuple [ok; VMap [(ttrue, ttrue)]]], [(Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fread" []) [] = (inr (undef (VLit (Atom "fread"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "==" [ttrue; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [ttrue; ffalse]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "/=" [ttrue; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [ttrue; ffalse]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [ttrue]) [] = (inr (undef (VLit (Atom "/="))), []).
Proof. reflexivity. Qed.

Definition l1 : Value := VCons ttrue VNil.
Definition l2 : Value := VCons ttrue ttrue.
Definition l3 : Value := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Value := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Value := VCons ttrue (VCons ttrue ttrue).

Goal (eval "erlang" "++" [ttrue; ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "++"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l1]) [] = (inl [VCons ttrue (VCons ttrue VNil)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l2]) [] = 
  (inl [VCons ttrue (VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l3]) [] = 
  (inl [VCons ttrue (VCons (VCons ttrue ttrue) ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l3; l3]) [] = 
  (inr (badarg (VTuple [VLit (Atom "++"); VCons (VCons ttrue ttrue) ttrue; VCons (VCons ttrue ttrue) ttrue])), []).
Proof.  unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; ErrorValue]) [] = (inl [VCons ttrue ErrorValue], []).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.

Goal (eval "erlang" "--" [ttrue; ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "--"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l1]) [] = (inl [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l2]) [] = 
  (inr (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons ttrue ttrue])), []).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l3]) [] = 
  (inr (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l3; l3]) [] = 
  (inr (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue;
                        VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l3; l1]) [] =
  (inr (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue; VCons ttrue VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l4; l4]) [] = (inl [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [VCons (VLit (Integer 0)) (VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) (VCons VNil VNil))));
  VCons VNil (VCons (VLit (Integer 0)) VNil)
] [])
=
  (inl [(VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) VNil)))], []).
Proof. unfold eval, eval_transform_list, eval_subtract. simpl. reflexivity. Qed.

Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] []) =
  (inl [VCons ttrue (VCons ttrue (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] []) =
  (inl [VCons ttrue (VCons ttrue (VCons (VCons ttrue (VCons ttrue ttrue)) 
                                 (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] []) =
  (inl [VCons ttrue (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] []) =
  (inl [VCons ttrue (VCons ttrue (VCons (VCons ttrue ttrue) (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [ttrue] []) = 
  (inr (badarg (VTuple [VLit (Atom "tuple_to_list"); ttrue])), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "list_to_tuple" [l1] []) = (inl [VTuple [VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l2] []) =
  (inr (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l3] []) =
  (inr (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l4] []) =
  (inl [VTuple [VLit (Atom "true"); VLit (Atom "true"); VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l5] []) =
  (inr (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "<" [ttrue; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [ttrue; ffalse]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "=<" [ttrue; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [ttrue; ffalse]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" ">" [ttrue; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [ffalse; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" ">=" [ttrue; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [ffalse; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "length" [l1]) [] = (inl [VLit (Integer 1)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l2]) [] = (inr (badarg (VTuple [VLit (Atom "length");l2])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l3]) [] = (inr (badarg (VTuple [VLit (Atom "length");l3])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l4]) [] = (inl [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l5]) [] = (inr (badarg (VTuple [VLit (Atom "length");l5])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "length");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l5;l3]) [] = (inr (undef (VLit (Atom "length"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "tuple_size" [l3]) [] = (inr (badarg (VTuple [VLit (Atom "tuple_size");l3])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple []]) [] = (inl [VLit (Integer 0)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]]) [] = (inl [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]; ErrorValue]) [] = (inr (undef (VLit (Atom "tuple_size"))), []).
Proof. reflexivity. Qed.


Goal (eval "erlang" "hd" [l1]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [VNil]) [] = (inr (badarg (VTuple [VLit (Atom "hd");VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l2]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l3]) [] = (inl [(VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l4]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l5]) [] = (inl [ttrue], []).
Proof. unfold l5. reflexivity. Qed.
Goal (eval "erlang" "hd" [ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "hd");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l5;l3]) [] = (inr (undef (VLit (Atom "hd"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "tl" [l1]) [] = (inl [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [VNil]) [] = (inr (badarg (VTuple [VLit (Atom "tl");VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l2]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l3]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l4]) [] = (inl [(VCons ttrue (VCons ttrue VNil))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l5]) [] = (inl [VCons ttrue ttrue], []).
Proof. unfold l5. reflexivity. Qed.
Goal (eval "erlang" "tl" [ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "tl");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l5;l3]) [] = (inr (undef (VLit (Atom "tl"))), []).
Proof. reflexivity. Qed.


Goal (eval "erlang" "element" [VLit (Integer 2); VTuple [ttrue]]) [] = (inr (badarg (VTuple [VLit (Atom "element"); VLit (Integer 2); VTuple [ttrue]])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "element" [VLit (Integer 1); VTuple [ttrue]]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "element" [ttrue; ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "element"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "element" [ttrue]) [] = (inr (undef (VLit (Atom "element"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "setelement" [VLit (Integer 2); VTuple [ttrue]; ffalse]) [] = (inr (badarg (VTuple [VLit (Atom "setelement"); VLit (Integer 2); VTuple [ttrue]; ffalse])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "setelement" [VLit (Integer 1); VTuple [ttrue]; ffalse]) [] = (inl [VTuple [ffalse]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "setelement" [ttrue; ttrue; ttrue]) [] = (inr (badarg (VTuple [VLit (Atom "setelement"); ttrue; ttrue; ttrue])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "setelement" [ttrue]) [] = (inr (undef (VLit (Atom "setelement"))), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_number" [VLit (Integer 2)] [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse] [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse; ffalse] [] = (inr (undef (VLit (Atom "is_number"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [VLit (Integer 2)] [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse] [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse; ffalse] [] = (inr (undef (VLit (Atom "is_integer"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Integer 2)] [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Atom "foo")] [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [ffalse; ffalse] [] = (inr (undef (VLit (Atom "is_atom"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [VLit (Integer 2)] [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ttrue] [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse] [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse; ffalse] [] = (inr (undef (VLit (Atom "is_boolean"))), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "error" [ffalse; ffalse] [] = (inr (Error, ffalse, ffalse), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [ffalse] [] = (inr (Error, ffalse, VNil), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [] [] = (inr (undef ErrorValue), []).
Proof. reflexivity. Qed.


End Tests.