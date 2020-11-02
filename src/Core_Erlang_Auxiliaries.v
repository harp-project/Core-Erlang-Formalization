Require Core_Erlang_Side_Effects.

Module Auxiliaries.

Export Core_Erlang_Side_Effects.Side_Effects.

Import ListNotations.

(**
  Built-in function simulation

  BIFCode: we need it in order to enable better pattern-matching on strings
 *)

Inductive BIFCode :=
| BPlus | BMinus | BMult | BDivide | BRem | BDiv 
| BFwrite | BFread 
| BAnd | BOr | BNot
| BEq | BTypeEq | BNeq | BTypeNeq
| BApp | BMinusMinus
| BTupleToList | BListToTuple
| BLt | BLe | BGt | BGe
| BLength | BTupleSize
| BTl | BHd
| BElement | BSetElement
| BNothing
.

Definition convert_string_to_code (s : string) : BIFCode :=
match s with
| "+"%string => BPlus
| "-"%string => BMinus
| "*"%string => BMult
| "/"%string => BDivide
| "rem"%string => BRem
| "div"%string => BDiv
| "fwrite"%string => BFwrite
| "fread"%string => BFread
| "and"%string => BAnd
| "or"%string => BOr
| "not"%string => BNot
| "=="%string => BEq
| "=:="%string => BTypeEq
| "/="%string => BNeq
| "=/="%string => BTypeNeq
| "++"%string => BApp
| "--"%string => BMinusMinus
| "tuple_to_list"%string => BTupleToList
| "list_to_tuple"%string => BListToTuple
| "<"%string => BLt
| ">"%string => BGt
| "=<"%string => BLe
| ">="%string => BGe
| "length"%string => BLength
| "tuple_size"%string => BTupleSize
| "hd"%string => BHd
| "tl"%string => BTl
| "element"%string => BElement
| "setelement"%string => BSetElement
(** anything else *)
| _ => BNothing
end.

(** For biuilt-in arithmetic calls *)
Definition eval_arith (fname : string) (params : list Value) :  ValueSequence + Exception :=
match convert_string_to_code fname, params with
(** addition *)
| BPlus, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a + b))]
| BPlus, [a; b]                               => inr (badarith (VCons a b))
(** subtraction *)
| BMinus, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a - b))]
| BMinus, [a; b]                               => inr (badarith (VCons a b))
(** unary minus *)
| BMinus, [VLit (Integer a)]                   => inl [VLit (Integer (0 - a))]
| BMinus, [a]                                  => inr (badarith a)
(** multiplication *)
| BMult, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a * b))]
| BMult, [a; b]                               => inr (badarith (VCons a b))
(** division *)
| BDivide, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a / b))]
| BDivide, [a; b]                               => inr (badarith (VCons a b))
(** rem *)
| BRem, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (Z.rem a b))]
| BRem, [a; b]                               => inr (badarith (VCons a b))
(** div *)
| BDiv, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (Z.div a b))]
| BDiv, [a; b]                               => inr (badarith (VCons a b))
(** anything else *)
| _         , _                                    => inr (undef (VLit (Atom fname)))
end.

(** For IO maniputaion: *)
Definition eval_io (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((ValueSequence + Exception) * SideEffectList) :=
match convert_string_to_code fname, length params, params with
(** writing *)
| BFwrite, 1, _ => (inl [ok]                                  , eff ++ [(Output, params)])
(** reading *)
| BFread, 2, e => (inl [VTuple [ok; nth 1 params ErrorValue]], eff ++ [(Input, params)])
(** anything else *)
| _              , _, _ => (inr (undef (VLit (Atom fname)))           , eff)
end.

Definition eval_logical (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
(** logical and *)
| BAnd, [a; b] => 
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => inl [ffalse]
   | VLit (Atom "true") , VLit (Atom "false")   => inl [ffalse]
   | VLit (Atom "false"), VLit (Atom "false")   => inl [ffalse]
   | _                         , _              => inr (badarg (VCons a b))
   end
(** logical or *)
| BOr, [a; b] =>
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "true") , VLit (Atom "false")   => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "false")   => inl [ffalse]
   | _                         , _              => inr (badarg (VCons a b))
   end
(** logical not *)
| BNot, [a] =>
   match a with
   | VLit (Atom "true")  => inl [ffalse]
   | VLit (Atom "false") => inl [ttrue]
   | _                   => inr (badarg a)
   end
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_equality (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
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
| VNil, VNil => inl [VNil]
| VNil, VCons x y => inl [VCons x y]
| VCons x y, VNil => inl [VCons x y]
| VCons x y, VCons x' y' =>
  match y with
  | VCons z w => match eval_append y (VCons x' y') with
                 | inr ex => inr ex
                 | inl [res] => inl [VCons x res]
                 | _ => inr (badarg (VCons v1 v2))
                 end
  | VNil      => inl [VCons x (VCons x' y')]
  | z         => inr (badarg (VCons v1 v2))
  end
| _, _ => inr (badarg (VCons v1 v2))
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
  | _        , _         => inr (badarg (VCons v1 v2))
  end
else
  inr (badarg (VCons v1 v2)).

Definition eval_transform_list (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
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
| _        => inr (badarg v)
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
               | z => inr (badarg v)
               end
| _         => inr (badarg v)
end.

Definition eval_list_tuple (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
| BTupleToList, [v] => transform_tuple v
| BListToTuple, [v] => match (transform_list v) with
                                 | inr ex => inr ex
                                 | inl l => inl [VTuple l]
                                 end
| _                     , _   => inr (undef (VLit (Atom fname)))
end.

Definition eval_cmp (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
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
                         | _ => inr (badarg v)
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
| [v] => inr (badarg v)
| _ => inr (undef (VLit (Atom "tuple_size")))
end.

Definition eval_hd_tl (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
| BHd, [VCons x y] => inl [x]
| BHd, [v] => inr (badarg v)
| BTl, [VCons x y] => inl [y]
| BTl, [v] => inr (badarg v)
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

Definition eval_elem_tuple (fname : string) (params : list Value) : ValueSequence + Exception :=
match convert_string_to_code fname, params with
| BElement, [VLit (Integer i); VTuple l] =>
    match i with
    | Z.pos p => match nth_error l (pred (Pos.to_nat p)) with
                 | None   => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
                 | Some v => inl [v]
                 end
    | _       => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
    end
| BElement, [v1; v2] => inr (badarg (VCons v1 v2))
| BSetElement, [VLit (Integer i); VTuple l; val] =>
    match i with
    | Z.pos p => match replace_nth_error l (pred (Pos.to_nat p)) val with
                 | None    => inr (badarg (VCons (VLit (Integer i)) (VCons (VTuple l) val)))
                 | Some l' => inl [VTuple l']
                 end
    | _       => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
    end
| BSetElement, [v1; v2; v3] => inr (badarg (VCons v1 (VCons v2 v3)))
| _, _ => inr (undef (VLit (Atom fname)))
end.

(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((ValueSequence + Exception) * SideEffectList) :=
match convert_string_to_code fname with
| BPlus      | BMinus
| BMult      | BDivide
| BRem       | BDiv                => (eval_arith fname params, eff)
| BFwrite    | BFread              => eval_io fname params eff
| BAnd   | BOr
| BNot                => (eval_logical fname params, eff)
| BEq   | BTypeEq
| BNeq     | BTypeNeq   => (eval_equality fname params, eff)
| BApp     | BMinusMinus    => (eval_transform_list fname params, eff)
| BTupleToList
| BListToTuple           => (eval_list_tuple fname params, eff)
| BLt      | BGt 
| BLe     | BGe    => (eval_cmp fname params, eff)
| BLength                  => (eval_length params, eff)
| BTupleSize              => (eval_tuple_size params, eff)
| BHd     | BTl    => (eval_hd_tl fname params, eff)
| BElement
| BSetElement              => (eval_elem_tuple fname params, eff)
(** anything else *)
| BNothing                         => (inr (undef (VLit (Atom fname))), eff)
end.


Theorem eval_effect_extension fname vals eff1 res eff2 :
  eval fname vals eff1 = (res, eff2)
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros. unfold eval in H.
  destruct (convert_string_to_code fname) eqn:Hfname; simpl in H.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple in H; rewrite Hfname in H; destruct vals;
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
Qed.

Proposition plus_comm_basic {e1 e2 t : Value} {eff : SideEffectList} : 
eval "+"%string [e1 ; e2] eff = (inl [t], eff)
->
eval "+"%string [e2; e1] eff = (inl [t], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_value {e1 e2 v : Value} (eff eff2 : SideEffectList) : 
  eval "+"%string [e1 ; e2] eff = (inl [v], eff)
->
  eval "+"%string [e2; e1] eff2 = (inl [v], eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inversion H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inversion H1).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_extended {e1 e2 : Value} (v : ValueSequence + Exception) (eff eff2 : SideEffectList) : 
  eval "+"%string [e1 ; e2] eff = (v, eff)
->
  exists v', eval "+"%string [e2; e1] eff2 = (v', eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-7, 9-36: eexists; try(inversion H1; reflexivity).
  * eexists. reflexivity.
Qed.

Proposition plus_effect_unmodified {e1 e2 : Value} (v' : ValueSequence + Exception) (eff eff2 : SideEffectList) :
  eval "+"%string [e1 ; e2] eff = (v', eff2)
->
  eff = eff2.
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inversion H1; reflexivity).
  all: try(destruct l); try(inversion H1; reflexivity).
  all: destruct l0.
Qed.

Proposition plus_effect_changeable {v1 v2 : Value} (v' : ValueSequence + Exception) (eff eff2 : SideEffectList) :
  eval "+"%string [v1; v2] eff = (v', eff)
->
  eval "+"%string [v1; v2] eff2 = (v', eff2).
Proof.
  intros. simpl in *. case_eq v1; case_eq v2; intros; subst.
  all: try(inversion H; reflexivity).
  all: try(destruct l); try(inversion H; reflexivity).
  all: destruct l0; inversion H; auto.
Qed.


End Auxiliaries.

Section Tests.

Import Auxiliaries.
Import ListNotations.

(** Tests *)

Goal (eval "+" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "-" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl [VLit (Integer (-1))], []).
Proof. reflexivity. Qed.
Goal (eval "+" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VCons (VLit (Atom "foo")) (VLit (Integer 2)))), []).
Proof. reflexivity. Qed.
Goal (eval "+" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VCons (VLit (Integer 1)) (VLit (Atom "foo")))), []).
Proof. reflexivity. Qed.
Goal (eval "-" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VCons (VLit (Atom "foo")) (VLit (Integer 2)))), []).
Proof. reflexivity. Qed.
Goal (eval "-" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VCons (VLit (Integer 1)) (VLit (Atom "foo")))), []).
Proof. reflexivity. Qed.
Goal (eval "-" [VLit (Atom "foo")]) [] 
    = (inr (badarith (VLit (Atom "foo"))), []).
Proof. reflexivity. Qed.
Goal (eval "+" [VLit (Atom "foo")]) [] 
    = (inr (undef (VLit (Atom "+"))), []).
Proof. reflexivity. Qed.

Goal (eval "not" [ttrue]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "not" [ffalse]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "not" [VLit (Integer 5)]) [] = (inr (badarg (VLit (Integer 5))), []).
Proof. reflexivity. Qed.
Goal (eval "not" [VLit (Integer 5); VEmptyTuple]) [] = (inr (undef (VLit (Atom "not"))), []).
Proof. reflexivity. Qed.

Goal (eval "and" [ttrue; ttrue]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "and" [ttrue; ffalse]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "and" [ffalse; ttrue]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "and" [ffalse; ffalse]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "and" [ttrue; VEmptyTuple]) [] = (inr (badarg (VCons ttrue (VTuple []))), []).
Proof. reflexivity. Qed.
Goal (eval "and" [ttrue]) [] = (inr (undef (VLit (Atom "and"))), []). Proof. reflexivity. Qed.

Goal (eval "or" [ttrue; ttrue]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "or" [ttrue; ffalse]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "or" [ffalse; ttrue]) [] = (inl [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "or" [ffalse; ffalse]) [] = (inl [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "or" [ttrue; VEmptyTuple]) [] = (inr (badarg (VCons ttrue (VTuple []))), []).
Proof. reflexivity. Qed.
Goal (eval "or" [ttrue]) [] = (inr (undef (VLit (Atom "or"))), []).
Proof. reflexivity. Qed.

Goal (eval "fwrite" [ttrue]) [] = (inl [ok], [(Output, [ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "fwrite" [VMap [(ttrue, ttrue)]]) [] = (inl [ok], [(Output, [VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "fwrite" []) [] = (inr (undef (VLit (Atom "fwrite"))), []).
Proof. reflexivity. Qed.

Goal (eval "fread" [VLit (Atom "foo.txt"); ttrue]) [] = 
   (inl [VTuple [ok; ttrue]], [(Input, [VLit (Atom "foo.txt"); ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]]) [] = 
   (inl [VTuple [ok; VMap [(ttrue, ttrue)]]], [(Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "fread" []) [] = (inr (undef (VLit (Atom "fread"))), []).
Proof. reflexivity. Qed.

Goal (eval "==" [ttrue; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "==" [ttrue; ffalse]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "==" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "/=" [ttrue; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "/=" [ttrue; ffalse]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "/=" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "/=" [ttrue]) [] = (inr (undef (VLit (Atom "/="))), []).
Proof. reflexivity. Qed.

Definition l1 : Value := VCons ttrue VNil.
Definition l2 : Value := VCons ttrue ttrue.
Definition l3 : Value := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Value := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Value := VCons ttrue (VCons ttrue ttrue).

Goal (eval "++" [ttrue; ttrue]) [] = (inr (badarg (VCons ttrue ttrue)), []).
Proof. reflexivity. Qed.
Goal (eval "++" [l1; l1]) [] = (inl [VCons ttrue (VCons ttrue VNil)], []).
Proof. reflexivity. Qed.
Goal (eval "++" [l1; l2]) [] = 
  (inl [VCons ttrue (VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "++" [l1; l3]) [] = 
  (inl [VCons ttrue (VCons (VCons ttrue ttrue) ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "++" [l3; l3]) [] = 
  (inr (badarg (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons (VCons ttrue ttrue) ttrue))), []).
Proof. reflexivity. Qed.

Goal (eval "--" [ttrue; ttrue]) [] = (inr (badarg (VCons ttrue ttrue)), []).
Proof. reflexivity. Qed.
Goal (eval "--" [l1; l1]) [] = (inl [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "--" [l1; l2]) [] = 
  (inr (badarg (VCons (VCons ttrue VNil) (VCons ttrue ttrue))), []).
Proof. reflexivity. Qed.
Goal (eval "--" [l1; l3]) [] = 
  (inr (badarg (VCons (VCons ttrue VNil) (VCons (VCons ttrue ttrue) ttrue))), []).
Proof. reflexivity. Qed.
Goal (eval "--" [l3; l3]) [] = 
  (inr (badarg (VCons (VCons (VCons ttrue ttrue) ttrue)
                      (VCons (VCons ttrue ttrue) ttrue))), []).
Proof. reflexivity. Qed.
Goal (eval "--" [l3; l1]) [] =
  (inr (badarg (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue VNil))), []).
Proof. reflexivity. Qed.
Goal (eval "--" [l4; l4]) [] = (inl [VNil], []).
Proof. reflexivity. Qed.

Goal (eval "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] []) =
  (inl [VCons ttrue (VCons ttrue (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] []) =
  (inl [VCons ttrue (VCons ttrue (VCons (VCons ttrue (VCons ttrue ttrue)) 
                                 (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] []) =
  (inl [VCons ttrue (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] []) =
  (inl [VCons ttrue (VCons ttrue (VCons (VCons ttrue ttrue) (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "tuple_to_list" [ttrue] []) = 
  (inr (badarg ttrue), []).
Proof. reflexivity. Qed.

Goal (eval "list_to_tuple" [l1] []) = (inl [VTuple [VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "list_to_tuple" [l2] []) =
  (inr (Error, VLit (Atom "badarg"), VCons ttrue ttrue), []).
Proof. reflexivity. Qed.
Goal (eval "list_to_tuple" [l3] []) =
  (inr (badarg (VCons (VCons ttrue ttrue) ttrue)), []).
Proof. reflexivity. Qed.
Goal (eval "list_to_tuple" [l4] []) =
  (inl [VTuple [VLit (Atom "true"); VLit (Atom "true"); VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "list_to_tuple" [l5] []) =
  (inr (Error, VLit (Atom "badarg"), VCons ttrue ttrue), []).
Proof. reflexivity. Qed.

Goal (eval "<" [ttrue; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "<" [ttrue; ffalse]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "=<" [ttrue; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "=<" [ttrue; ffalse]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "=<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "=<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "=<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval ">" [ttrue; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval ">" [ffalse; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval ">" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval ">" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval ">" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval ">=" [ttrue; ttrue]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval ">=" [ffalse; ttrue]) [] = (inl [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval ">=" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval ">=" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval ">=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Proof. reflexivity. Qed.

End Tests.