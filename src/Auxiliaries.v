From CoreErlang Require Export SideEffects Scoping Equalities.
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

(** For built-in arithmetic calls *)
Definition eval_arith (mname : string) (fname : string) (params : list Val) :  Redex :=
match convert_string_to_code (mname, fname), params with
(** addition *)
| BPlus, [VLit (Integer a); VLit (Integer b)] => RValSeq [VLit (Integer (a + b))]
| BPlus, [a; b]                               => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** subtraction *)
| BMinus, [VLit (Integer a); VLit (Integer b)] => RValSeq [VLit (Integer (a - b))]
| BMinus, [a; b]                               => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** unary minus *)
| BMinus, [VLit (Integer a)]                   => RValSeq [VLit (Integer (0 - a))]
| BMinus, [a]                                  => RExc (badarith (VTuple [VLit (Atom fname); a]))
(** unary plus *)
| BPlus, [VLit (Integer a)]                   => RValSeq [VLit (Integer a)]
| BPlus, [a]                                  => RExc (badarith (VTuple [VLit (Atom fname); a]))
(** multiplication *)
| BMult, [VLit (Integer a); VLit (Integer b)] => RValSeq [VLit (Integer (a * b))]
| BMult, [a; b]                               => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** division *)
| BDivide, [VLit (Integer a); VLit (Integer 0)] => RExc (badarith (VTuple [VLit (Atom fname); VLit (Integer a); VLit (Integer 0)]))
| BDivide, [VLit (Integer a); VLit (Integer b)] => RValSeq [VLit (Integer (a / b))]
| BDivide, [a; b]                               => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** rem *)
| BRem, [VLit (Integer a); VLit (Integer 0)] => RExc (badarith (VTuple [VLit (Atom fname); VLit (Integer a); VLit (Integer 0)]))
| BRem, [VLit (Integer a); VLit (Integer b)] => RValSeq [VLit (Integer (Z.rem a b))]
| BRem, [a; b]                               => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** div *)
| BDiv, [VLit (Integer a); VLit (Integer 0)] => RExc (badarith (VTuple [VLit (Atom fname); VLit (Integer a); VLit (Integer 0)]))
| BDiv, [VLit (Integer a); VLit (Integer b)] => RValSeq [VLit (Integer (Z.quot a b))]
| BDiv, [a; b]                               => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** bsl *)
| BSl, [VLit (Integer a); VLit (Integer b)]  => RValSeq [VLit (Integer (Z.shiftl a b))]
| BSl, [a; b]                                => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** bsr *)
| BSr, [VLit (Integer a); VLit (Integer b)]  => RValSeq [VLit (Integer (Z.shiftr a b))]
| BSr, [a; b]                                => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** abs *)
| BAbs, [VLit (Integer a)]                   => RValSeq [VLit (Integer (Z.abs a))]
| BAbs, [a]                                  => RExc (badarg (VTuple [VLit (Atom fname); a]))
(** anything else *)
| _         , _                              => RExc (undef (VLit (Atom fname)))
end.

(** For IO maniputaion: *)
Definition eval_io (mname : string) (fname : string) (params : list Val) (eff : SideEffectList) 
   : ((Redex) * SideEffectList) :=
match convert_string_to_code (mname, fname), length params, params with
(** writing *)
| BFwrite, 1, _ => (RValSeq [ok]                                  , eff ++ [(Output, params)])
(** reading *)
| BFread, 2, e => (RValSeq [VTuple [ok; nth 1 params ErrorVal]], eff ++ [(Input, params)])
(** anything else *)
| _              , _, _ => (RExc (undef (VLit (Atom fname)))           , eff)
end.

Definition eval_logical (mname fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
(** logical and *)
| BAnd, [a; b] => 
   (*match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => RValSeq [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => RValSeq [ffalse]
   | VLit (Atom "true") , VLit (Atom "false")   => RValSeq [ffalse]
   | VLit (Atom "false"), VLit (Atom "false")   => RValSeq [ffalse]
   | _                         , _              => RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   end*)
   if Val_eqb a ttrue
   then
    if Val_eqb b ttrue
    then RValSeq [ttrue]
    else
      if Val_eqb b ffalse
      then RValSeq [ffalse]
      else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   else
    if Val_eqb a ffalse
    then
      if Val_eqb b ttrue
      then RValSeq [ffalse]
      else
        if Val_eqb b ffalse
        then RValSeq [ffalse]
        else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
    else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   
(** logical or *)
| BOr, [a; b] =>
   (*match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => RValSeq [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => RValSeq [ttrue]
   | VLit (Atom "true") , VLit (Atom "false")   => RValSeq [ttrue]
   | VLit (Atom "false"), VLit (Atom "false")   => RValSeq [ffalse]
   | _                         , _              => RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   end *)
   if Val_eqb a ttrue
   then
    if Val_eqb b ttrue
    then RValSeq [ttrue]
    else
      if Val_eqb b ffalse
      then RValSeq [ttrue]
      else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   else
    if Val_eqb a ffalse
    then
      if Val_eqb b ttrue
      then RValSeq [ttrue]
      else
        if Val_eqb b ffalse
        then RValSeq [ffalse]
        else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
    else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
(** logical not *)
| BNot, [a] =>
   (* match a with
   | VLit (Atom "true")  => RValSeq [ffalse]
   | VLit (Atom "false") => RValSeq [ttrue]
   | _                   => RExc (badarg (VTuple [VLit (Atom fname); a]))
   end *)
   if Val_eqb a ttrue
   then RValSeq [ffalse]
   else
    if Val_eqb a ffalse
    then RValSeq [ttrue]
    else RExc (badarg (VTuple [VLit (Atom fname); a]))
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_equality (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BEq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeEq, [v1; v2] => if Val_eqb v1 v2 then RValSeq [ttrue] else RValSeq [ffalse]
| BNeq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeNeq, [v1; v2] => if Val_eqb v1 v2 then RValSeq [ffalse] else RValSeq [ttrue]
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Fixpoint is_shallow_proper_list (v : Val) : bool :=
match v with
| VNil => true
| VCons x y => is_shallow_proper_list y
| _ => false
end.

Fixpoint eval_append (v1 v2 : Val) : Redex :=
match v1, v2 with
| VNil, x => RValSeq [x]
| VCons x y, x' => match eval_append y x' with
                   | RExc ex    => RExc (badarg (VTuple [VLit (Atom "++"); v1; v2]))
                   | RValSeq [res] => RValSeq [VCons x res]
                   | _ => RExc (badarg (VTuple [VLit (Atom "++"); v1; v2]))
                   end
| _, _ => RExc (badarg (VTuple [VLit (Atom "++"); v1; v2]))
end.

Fixpoint subtract_elem (v1 v2 : Val) : Val :=
match v1 with
| VNil => VNil
| VCons x y =>
  match y with
  | VNil => if Val_eqb x v2 then VNil else VCons x y
  | VCons z w => if Val_eqb x v2 then y else VCons x (subtract_elem y v2)
  | z => if Val_eqb x v2 then VCons z VNil else if Val_eqb z v2 then VCons x VNil else VCons x y
  end
| _ => ErrorVal
end.

Fixpoint eval_subtract (v1 v2 : Val) : Redex :=
if andb (is_shallow_proper_list v1) (is_shallow_proper_list v2) then
  match v1, v2 with
  | VNil, VNil => RValSeq [VNil]
  | VNil, VCons x y => RValSeq [VNil]
  | VCons x y, VNil => RValSeq [VCons x y]
  | VCons x y, VCons x' y' => 
     match y' with
     | VNil => RValSeq [subtract_elem (VCons x y) x']
     | VCons z w => eval_subtract (subtract_elem (VCons x y) x') y'
     | z => RValSeq [subtract_elem (subtract_elem (VCons x y) x') z]
     end
  | _        , _         => RExc (badarg (VTuple [VLit (Atom "--"); v1; v2]))
  end
else
  RExc (badarg (VTuple [VLit (Atom "--"); v1; v2])).

Definition eval_transform_list (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BApp, [v1; v2]        => eval_append v1 v2
| BMinusMinus, [v1; v2] => eval_subtract v1 v2
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition transform_tuple (v : Val) : Redex :=
match v with
| VTuple l => RValSeq [((fix unfold_list l :=
                   match l with
                   | [] => VNil
                   | x::xs => VCons x (unfold_list xs)
                   end) l)]
| _        => RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); v]))
end.

Fixpoint transform_list (v : Val) : list Val + Exception :=
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

Definition eval_list_tuple (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BTupleToList, [v] => transform_tuple v
| BListToTuple, [v] => match (transform_list v) with
                                 | inr ex => RExc ex
                                 | inl l => RValSeq [VTuple l]
                                 end
| _                     , _   => RExc (undef (VLit (Atom fname)))
end.

Definition eval_cmp (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BLt,  [v1; v2] => if Val_ltb v1 v2 then RValSeq [ttrue] else RValSeq [ffalse]
| BLe, [v1; v2] => if orb (Val_ltb v1 v2) (Val_eqb v1 v2) 
                           then RValSeq [ttrue] else RValSeq [ffalse]
| BGt,  [v1; v2] => if Val_ltb v2 v1 then RValSeq [ttrue] else RValSeq [ffalse]
| BGe, [v1; v2] => if orb (Val_ltb v2 v1) (Val_eqb v1 v2) 
                           then RValSeq [ttrue] else RValSeq [ffalse]
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_length (params : list Val) : Redex :=
match params with
| [v] => let res :=
          (fix len val := match val with
                         | VNil => Some Z.zero
                         | VCons x y => let res := len y in
                                          match res with
                                          | Some n => Some (Z.add 1 n)
                                          | None => None
                                          end
                         | _ => None
                         end) v in
        match res with
        | Some n => RValSeq [VLit (Integer n)]
        | None => RExc (badarg (VTuple [VLit (Atom "length"); v]))
        end
| _ => RExc (undef (VLit (Atom "length")))
end.

Definition eval_tuple_size (params : list Val) : Redex :=
match params with
| [VTuple l] => RValSeq [VLit (Integer (Z.of_nat (length l)))]
| [v] => RExc (badarg (VTuple [VLit (Atom "tuple_size"); v]))
| _ => RExc (undef (VLit (Atom "tuple_size")))
end.

Definition eval_hd_tl (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BHd, [VCons x y] => RValSeq [x]
| BHd, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| BTl, [VCons x y] => RValSeq [y]
| BTl, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| _, _ => RExc (undef (VLit (Atom fname)))
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

Definition eval_elem_tuple (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BElement, [VLit (Integer i); VTuple l] =>
    match i with
    | Z.pos p => match nth_error l (pred (Pos.to_nat p)) with
                 | None   => RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
                 | Some v => RValSeq [v]
                 end
    | _       => RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
    end
| BElement, [v1; v2] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2]))
| BSetElement, [VLit (Integer i); VTuple l; val] =>
    match i with
    | Z.pos p => match replace_nth_error l (pred (Pos.to_nat p)) val with
                 | None    => RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l; val]))
                 | Some l' => RValSeq [VTuple l']
                 end
    | _       => RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
    end
| BSetElement, [v1; v2; v3] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2; v3]))
| _, _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_check (mname fname : string) (params : list Val) : Redex := 
match convert_string_to_code (mname, fname), params with
| BIsNumber, [VLit (Integer i)]     => RValSeq [ttrue]
| BIsNumber, [_]                    => RValSeq [ffalse]
| BIsInteger, [VLit (Integer i)]    => RValSeq [ttrue]
| BIsInteger, [_]                   => RValSeq [ffalse] 
| BIsAtom, [VLit (Atom a)]          => RValSeq [ttrue]
| BIsAtom, [_]                      => RValSeq [ffalse]
(*| BIsBoolean, [VLit (Atom "true")]
| BIsBoolean, [VLit (Atom "false")] => RValSeq [ttrue] *)
| BIsBoolean, [v] => if orb (Val_eqb v ttrue) (Val_eqb v ffalse)
                     then RValSeq [ttrue]
                     else RValSeq [ffalse]
| _, _              => RExc (undef (VLit (Atom fname)))
end.

Definition eval_error (mname : string) (fname : string) (params : list Val) : Exception :=
match params with
| [VTuple [val]] => (Error, val, VNil)
| [VTuple [val; reas]] => (Error, val, reas)
| [val]        => (Error, val, VNil)
| [val1; val2] => (Error, val1, val2)
| _            => undef (VLit (Atom fname))
end.

Definition eval_primop_error (fname : string) (params : list Val) : Exception :=
match params with
| [VTuple [val]] => (Error, val, VNil)
| [VTuple [val; reas]] => (Error, val, reas)
| [val]        => (Error, val, VNil)
| [val1; val2] => (Error, val1, val2)
| _            => undef (VLit (Atom fname))
end.

(* Eval for primary operations *)
Definition primop_eval (fname : string) (params : list Val) (eff : SideEffectList) : ((Redex) * SideEffectList) :=
match convert_primop_to_code ( fname) with
  | PMatchFail  =>  (RExc (eval_primop_error fname params), eff)
  | _ => (RExc (undef (VLit (Atom fname))), eff)
end.


(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (mname : string) (fname : string) (params : list Val) (eff : SideEffectList) 
   : ((Redex) * SideEffectList) :=
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
| BError                                          => (RExc (eval_error mname fname params), eff)
(** anything else *)
| BNothing  | PMatchFail                                       => (RExc (undef (VLit (Atom fname))), eff)
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

Proposition plus_comm_basic {e1 e2 t : Val} {eff : SideEffectList} : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = (RValSeq [t], eff)
->
  eval "erlang"%string "+"%string [e2; e1] eff = (RValSeq [t], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_Val {e1 e2 v : Val} (eff eff2 : SideEffectList) : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = (RValSeq [v], eff)
->
  eval "erlang"%string "+"%string [e2; e1] eff2 = (RValSeq [v], eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_extended {e1 e2 : Val} (v : Redex) (eff eff2 : SideEffectList) : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = (v, eff)
->
  exists v', eval "erlang"%string "+"%string [e2; e1] eff2 = (v', eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inversion H1; eexists; reflexivity).
Qed.

Proposition plus_effect_unmodified {e1 e2 : Val} (v' : Redex) (eff eff2 : SideEffectList) :
  eval "erlang"%string "+"%string [e1 ; e2] eff = (v', eff2)
->
  eff = eff2.
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inversion H1; reflexivity).
  all: try(destruct l); try(inversion H1; reflexivity).
  all: destruct l0.
Qed.

Proposition plus_effect_changeable {v1 v2 : Val} (v' : Redex) (eff eff2 : SideEffectList) :
  eval "erlang"%string "+"%string [v1; v2] eff = (v', eff)
->
  eval "erlang"%string "+"%string [v1; v2] eff2 = (v', eff2).
Proof.
  intros. simpl in *. case_eq v1; case_eq v2; intros; subst.
  all: try(inversion H; reflexivity).
  all: try(destruct l); try(inversion H; reflexivity).
  all: destruct l0; inversion H; auto.
Qed.

Lemma subtract_elem_closed Γ:
  forall v1 v2, VAL Γ ⊢ v1 -> VAL Γ ⊢ v2 ->
  VAL Γ ⊢ (subtract_elem v1 v2).
Proof.
  induction v1; intros; cbn; try constructor.
  repeat break_match_goal; destruct_redex_scopes; auto.
Qed.

Lemma primop_eval_is_result :
  forall f vl eff,
  Forall (fun v => VALCLOSED v) vl ->
  is_result (fst (primop_eval f vl eff)).
Proof.
  intros. unfold primop_eval.
  break_match_goal; simpl; unfold undef; try constructor; auto.
  unfold eval_primop_error.
  destruct vl; unfold undef; auto.
  destruct v; destruct vl; unfold undef; auto; try destruct vl; unfold undef; auto.
  all: try constructor; repeat destruct_foralls; auto.
  all: destruct l; try destruct l; try destruct l; constructor; auto.
  all: destruct_redex_scope; destruct_foralls.
  apply (H1 0). slia.
  apply (H1 0). slia.
  apply (H1 1). slia.
Qed.

Lemma is_result_closed :
  forall r, is_result r -> REDCLOSED r.
Proof.
  destruct r; intros; inv H; auto.
Qed.

Lemma eval_is_result :
  forall f m vl eff,
  Forall (fun v => VALCLOSED v) vl ->
  is_result (fst (eval m f vl eff)).
Proof.
  intros. unfold eval.
  break_match_goal; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error; try rewrite Heqb.
  all: try destruct vl; try destruct vl.
  all: simpl; try (now (constructor; constructor)).
  all: repeat break_match_goal.
  all: try (constructor; constructor); auto.
  all: try now constructor; auto.
  all: destruct_foralls; destruct_redex_scopes; auto.
  all: try (apply indexed_to_forall; repeat constructor; auto).
  * constructor. apply indexed_to_forall. repeat constructor. auto.
  * clear Heqb eff m f. induction v; cbn.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    - now do 2 constructor.
    - destruct_redex_scopes. apply IHv1 in H4 as H4'. break_match_goal.
      2: break_match_goal. 3: break_match_goal.
      all: try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
      do 3 constructor; subst; auto.
      apply IHv2 in H5. destruct_redex_scopes. apply is_result_closed in H5. 
      inv H5. now inv H0.
  * clear Heqb eff m f. generalize dependent v. induction v0; intros; cbn; break_match_goal; try destruct v.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    1-3: destruct_redex_scopes; do 3 constructor; auto.
    destruct_redex_scopes. destruct v0_2; cbn in *.
    3: {
      apply IHv0_2; auto.
      repeat break_match_goal; auto.
      constructor; auto.
      now apply subtract_elem_closed.
    }
    all: repeat break_match_goal; auto.
    all: constructor; constructor; auto.
    all: try apply subtract_elem_closed; auto.
    all: constructor; auto; now apply subtract_elem_closed.
  * clear Heqb eff m f. induction v; cbn.
    all: destruct_redex_scopes; try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
    do 2 constructor; auto. induction l; constructor.
    - apply (H1 0). simpl. lia.
    - apply IHl. intros. apply (H1 (S i)). simpl. lia.
  * clear Heqb eff m f. generalize dependent v. induction l; cbn; intros.
    - constructor. simpl. lia.
    - destruct v; cbn in Heqs; try congruence.
      destruct_redex_scopes. 
      repeat break_match_hyp; inversion Heqs; subst.
      constructor. apply indexed_to_forall. constructor; auto.
      apply IHl in Heqs0; auto.
      constructor. apply indexed_to_forall. constructor; auto.
      inversion Heqs0. now rewrite <- indexed_to_forall in H1.
  * clear Heqb eff m f. generalize dependent e. induction v; cbn; intros.
    all: try congruence.
    all: try inversion Heqs; subst; clear Heqs.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    destruct (transform_list v2) eqn:Eq.
    - destruct v2; try congruence; inversion H0; subst.
      all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    - destruct v2; try congruence; inversion H0; subst.
      all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
      apply IHv2; auto. destruct_redex_scopes. auto.
  * epose proof (proj1 (nth_error_Some l0 (Init.Nat.pred (Pos.to_nat p))) _).
    Unshelve. 2: { intro. rewrite H in Heqo. congruence. }
    eapply nth_error_nth with (d := VNil) in Heqo. subst. now apply H2.
  * remember (Init.Nat.pred (Pos.to_nat p)) as k. clear Heqk Heqb m f p eff.
    generalize dependent l2. revert k. induction l0; intros; simpl in *.
    - destruct k; congruence.
    - destruct k.
      + inversion Heqo. subst. constructor.
        intros. destruct i; simpl in *.
        auto.
        apply (H2 (S i)). lia.
      + break_match_hyp. 2: congruence.
        inversion Heqo; subst; clear Heqo. constructor. simpl.
        intros. destruct i.
        apply (H2 0). lia.
        apply IHl0 in Heqo0. inversion Heqo0. apply (H4 i). lia.
        intros. apply (H2 (S i0)). lia.
  * apply indexed_to_forall in H1. destruct_foralls. now constructor.
  * apply indexed_to_forall in H1. destruct_foralls. now constructor. 
Qed.

Corollary closed_primop_eval : forall f vl eff,
  Forall (fun v => VALCLOSED v) vl ->
  REDCLOSED (fst (primop_eval f vl eff)).
Proof.
  intros.
  apply is_result_closed. now apply primop_eval_is_result.
Qed.

Corollary closed_eval : forall m f vl eff,
  Forall (fun v => VALCLOSED v) vl ->
  REDCLOSED (fst (eval m f vl eff)).
Proof.
  intros.
  apply is_result_closed. now apply eval_is_result.
Qed.

Proposition eval_length_number :
  forall vs vs', eval_length vs = RValSeq vs' ->
  (exists (n : Z), vs' = [VLit n]) /\ (vs = [VNil] \/ exists v1 v2, vs = [VCons v1 v2]).
Proof.
  intros. destruct vs; inv H. destruct vs; inv H1.
  revert vs' H0 ; induction v; intros; auto; inv H0.
  * intuition. eexists. reflexivity.
  * break_match_hyp; inv H1. split.
    - eexists. reflexivity.
    - break_match_hyp; try congruence. inv Heqo.
      specialize (IHv2 _ eq_refl) as [_ H]. destruct H.
      + right. do 2 eexists. reflexivity.
      + right. do 2 eexists. reflexivity.
Qed.

Proposition eval_length_positive :
  forall v1 v2 (x : Z), eval_length [VCons v1 v2] = RValSeq [VLit x] ->
  (x > 0)%Z.
Proof.
  induction v2; intros; simpl in *; inv H; try lia.
  break_match_hyp; try congruence. inv H1.
  break_match_hyp; try congruence. destruct z; inv Heqo; try lia.
  specialize (IHv2_2 _ eq_refl). lia.
Qed.


Section Tests.

(** Tests *)

Goal (eval "erlang" "+" [VLit (Integer 1); VLit (Integer 2)]) [] = (RValSeq [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Integer 1); VLit (Integer 2)]) [] = (RValSeq [VLit (Integer (-1))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Atom "foo")]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Atom "foo")]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo")])), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal (eval "erlang" "bsl" [VLit (Integer 10); VLit (Integer 20)]) [] = (RValSeq [VLit (Integer 10485760)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Integer 10); VLit (Integer 20)]) [] = (RValSeq [VLit (Integer 0)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Atom "foo")]) [] 
    = (RExc (undef (VLit (Atom "bsl"))), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Atom "foo")]) [] 
    = (RExc (undef (VLit (Atom "bsr"))), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal (eval "erlang" "not" [ttrue]) [] = (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [ffalse]) [] = (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [VLit (Integer 5)]) [] = (RExc (badarg (VTuple [VLit (Atom "not"); VLit (Integer 5)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [VLit (Integer 5); VEmptyTuple]) [] = (RExc (undef (VLit (Atom "not"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "and" [ttrue; ttrue]) [] = (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue; ffalse]) [] = (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ffalse; ttrue]) [] = (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ffalse; ffalse]) [] = (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue; VEmptyTuple]) [] = (RExc (badarg (VTuple [VLit (Atom "and"); ttrue; VTuple []])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue]) [] = (RExc (undef (VLit (Atom "and"))), []). Proof. reflexivity. Qed.

Goal (eval "erlang" "or" [ttrue; ttrue]) [] = (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue; ffalse]) [] = (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ffalse; ttrue]) [] = (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ffalse; ffalse]) [] = (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue; VEmptyTuple]) [] = (RExc (badarg (VTuple [VLit (Atom "or"); ttrue; VTuple []])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue]) [] = (RExc (undef (VLit (Atom "or"))), []).
Proof. reflexivity. Qed.

Goal (eval "io" "fwrite" [ttrue]) [] = (RValSeq [ok], [(Output, [ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fwrite" [VMap [(ttrue, ttrue)]]) [] = (RValSeq [ok], [(Output, [VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fwrite" []) [] = (RExc (undef (VLit (Atom "fwrite"))), []).
Proof. reflexivity. Qed.

Goal (eval "io" "fread" [VLit (Atom "foo.txt"); ttrue]) [] = 
   (RValSeq [VTuple [ok; ttrue]], [(Input, [VLit (Atom "foo.txt"); ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]]) [] = 
   (RValSeq [VTuple [ok; VMap [(ttrue, ttrue)]]], [(Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fread" []) [] = (RExc (undef (VLit (Atom "fread"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "==" [ttrue; ttrue]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [ttrue; ffalse]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] 1 0 EEmptyMap; ttrue]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "/=" [ttrue; ttrue]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [ttrue; ffalse]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; ttrue]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed. 
Goal (eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [ttrue]) [] = (RExc (undef (VLit (Atom "/="))), []).
Proof. reflexivity. Qed.

Definition l1 : Val := VCons ttrue VNil.
Definition l2 : Val := VCons ttrue ttrue.
Definition l3 : Val := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Val := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Val := VCons ttrue (VCons ttrue ttrue).

Goal (eval "erlang" "++" [ttrue; ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "++"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l1]) [] = (RValSeq [VCons ttrue (VCons ttrue VNil)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l2]) [] = 
  (RValSeq [VCons ttrue (VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l3]) [] = 
  (RValSeq [VCons ttrue (VCons (VCons ttrue ttrue) ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l3; l3]) [] = 
  (RExc (badarg (VTuple [VLit (Atom "++"); VCons (VCons ttrue ttrue) ttrue; VCons (VCons ttrue ttrue) ttrue])), []).
Proof.  unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; ErrorVal]) [] = (RValSeq [VCons ttrue ErrorVal], []).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.

Goal (eval "erlang" "--" [ttrue; ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "--"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l1]) [] = (RValSeq [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l2]) [] = 
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons ttrue ttrue])), []).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l3]) [] = 
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l3; l3]) [] = 
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue;
                        VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l3; l1]) [] =
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue; VCons ttrue VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l4; l4]) [] = (RValSeq [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [VCons (VLit (Integer 0)) (VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) (VCons VNil VNil))));
  VCons VNil (VCons (VLit (Integer 0)) VNil)
] [])
=
  (RValSeq [(VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) VNil)))], []).
Proof. unfold eval, eval_transform_list, eval_subtract. simpl. reflexivity. Qed.

Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] []) =
  (RValSeq [VCons ttrue (VCons ttrue (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] []) =
  (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue (VCons ttrue ttrue)) 
                                 (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] []) =
  (RValSeq [VCons ttrue (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] []) =
  (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue ttrue) (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [ttrue] []) = 
  (RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); ttrue])), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "list_to_tuple" [l1] []) = (RValSeq [VTuple [VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l2] []) =
  (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l3] []) =
  (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l4] []) =
  (RValSeq [VTuple [VLit (Atom "true"); VLit (Atom "true"); VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l5] []) =
  (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "<" [ttrue; ttrue]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [ttrue; ffalse]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "=<" [ttrue; ttrue]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [ttrue; ffalse]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" ">" [ttrue; ttrue]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [ffalse; ttrue]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" ">=" [ttrue; ttrue]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [ffalse; ttrue]) [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "length" [l1]) [] = (RValSeq [VLit (Integer 1)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l2]) [] = (RExc (badarg (VTuple [VLit (Atom "length");l2])), []).
Proof. cbn. reflexivity. Qed.
Goal (eval "erlang" "length" [l3]) [] = (RExc (badarg (VTuple [VLit (Atom "length");l3])), []).
Proof. cbn. reflexivity. Qed.
Goal (eval "erlang" "length" [l4]) [] = (RValSeq [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l5]) [] = (RExc (badarg (VTuple [VLit (Atom "length");l5])), []).
Proof. cbn. reflexivity. Qed.
Goal (eval "erlang" "length" [ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "length");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l5;l3]) [] = (RExc (undef (VLit (Atom "length"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "tuple_size" [l3]) [] = (RExc (badarg (VTuple [VLit (Atom "tuple_size");l3])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple []]) [] = (RValSeq [VLit (Integer 0)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]]) [] = (RValSeq [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]; ErrorVal]) [] = (RExc (undef (VLit (Atom "tuple_size"))), []).
Proof. reflexivity. Qed.


Goal (eval "erlang" "hd" [l1]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [VNil]) [] = (RExc (badarg (VTuple [VLit (Atom "hd");VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l2]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l3]) [] = (RValSeq [(VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l4]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l5]) [] = (RValSeq [ttrue], []).
Proof. unfold l5. reflexivity. Qed.
Goal (eval "erlang" "hd" [ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "hd");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l5;l3]) [] = (RExc (undef (VLit (Atom "hd"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "tl" [l1]) [] = (RValSeq [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [VNil]) [] = (RExc (badarg (VTuple [VLit (Atom "tl");VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l2]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l3]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l4]) [] = (RValSeq [(VCons ttrue (VCons ttrue VNil))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l5]) [] = (RValSeq [VCons ttrue ttrue], []).
Proof. unfold l5. reflexivity. Qed.
Goal (eval "erlang" "tl" [ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "tl");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l5;l3]) [] = (RExc (undef (VLit (Atom "tl"))), []).
Proof. reflexivity. Qed.


Goal (eval "erlang" "element" [VLit (Integer 2); VTuple [ttrue]]) [] = (RExc (badarg (VTuple [VLit (Atom "element"); VLit (Integer 2); VTuple [ttrue]])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "element" [VLit (Integer 1); VTuple [ttrue]]) [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "element" [ttrue; ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "element"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "element" [ttrue]) [] = (RExc (undef (VLit (Atom "element"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "setelement" [VLit (Integer 2); VTuple [ttrue]; ffalse]) [] = (RExc (badarg (VTuple [VLit (Atom "setelement"); VLit (Integer 2); VTuple [ttrue]; ffalse])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "setelement" [VLit (Integer 1); VTuple [ttrue]; ffalse]) [] = (RValSeq [VTuple [ffalse]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "setelement" [ttrue; ttrue; ttrue]) [] = (RExc (badarg (VTuple [VLit (Atom "setelement"); ttrue; ttrue; ttrue])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "setelement" [ttrue]) [] = (RExc (undef (VLit (Atom "setelement"))), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_number" [VLit (Integer 2)] [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse] [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse; ffalse] [] = (RExc (undef (VLit (Atom "is_number"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [VLit (Integer 2)] [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse] [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse; ffalse] [] = (RExc (undef (VLit (Atom "is_integer"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Integer 2)] [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Atom "foo")] [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [ffalse; ffalse] [] = (RExc (undef (VLit (Atom "is_atom"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [VLit (Integer 2)] [] = (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ttrue] [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse] [] = (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse; ffalse] [] = (RExc (undef (VLit (Atom "is_boolean"))), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "error" [ffalse; ffalse] [] = (RExc (Error, ffalse, ffalse), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [ffalse] [] = (RExc (Error, ffalse, VNil), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [] [] = (RExc (undef ErrorVal), []).
Proof. reflexivity. Qed.

End Tests.
