From CoreErlang Require Export SideEffects Scoping Equalities.
Require Export Coq.Sorting.Permutation.

Import ListNotations.

(**
  Built-in function simulation

  BIFCode: we need it in order to enable better pattern-matching on strings
 *)
Inductive PrimopCode :=
| PMatchFail | PRaise | PNothing
| PRecvNext | PPeekMsg | PRemoveMsg | PRecvWaitTimeout
.


Inductive BIFCode :=
| BPlus | BMinus | BMult | BDivide | BRem | BDiv | BSl | BSr | BAbs
| BFwrite | BFread 
| BAnd | BOr | BNot
| BEq | BTypeEq | BNeq | BTypeNeq
| BApp | BMinusMinus | BSplit
| BTupleToList | BListToTuple
| BLt | BLe | BGt | BGe
| BLength | BTupleSize
| BTl | BHd
| BElement | BSetElement
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean
| BError | BExit | BThrow
(* !, spawn, process_flag, self, link, unlink, exit/2 <-
   these are handled on the process-local level, they behave as
   undefined  *)
| BSend | BSpawn | BSpawnLink | BProcessFlag | BSelf | BLink | BUnLink
| BNothing
| BFunInfo
.

Definition convert_primop_to_code (s : string) : PrimopCode :=
match s with
  (** primops *)
  | "match_fail"%string => PMatchFail
  | "raise"%string => PRaise
  | "recv_next"%string => PRecvNext
  | "recv_peek_message"%string => PPeekMsg
  | "remove_message"%string => PRemoveMsg
  | "recv_wait_timeout"%string => PRecvWaitTimeout
  | _ => PNothing
end.

Opaque convert_primop_to_code.

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
| ("erlang"%string, "fun_info"%string) => BFunInfo
| ("erlang"%string, "error"%string) => BError
| ("erlang"%string, "exit"%string) => BExit
| ("erlang"%string, "throw"%string) => BThrow
(* concurrency *)
| ("erlang"%string, "!"%string) => BSend
| ("erlang"%string, "spawn"%string) => BSpawn
| ("erlang"%string, "spawn_link"%string) => BSpawnLink
| ("erlang"%string, "process_flag"%string) => BProcessFlag
| ("erlang"%string, "self"%string) => BSelf
| ("erlang"%string, "link"%string) => BLink
| ("erlang"%string, "unlink"%string) => BUnLink
(** lists *)
| ("lists"%string, "split"%string) => BSplit
(** anything else *)
| _ => BNothing
end.

Opaque convert_string_to_code.

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
(** Note: we intentionally avoid pattern matching on strings here *)
(** logical and *)
| BAnd, [a; b] =>
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
| VCons x y => if Val_eqb x v2 then y else VCons x (subtract_elem y v2)
| _ => ErrorVal
end.

Fixpoint eval_subtract (v1 v2 : Val) : Redex :=
if andb (is_shallow_proper_list v1) (is_shallow_proper_list v2) then
  match v2 with
  | VNil        => RValSeq [v1]
  | VCons hd tl => eval_subtract (subtract_elem v1 hd) tl
  | _           => RExc (badarg (VTuple [VLit (Atom "--"); v1; v2]))
  end
else RExc (badarg (VTuple [VLit (Atom "--"); v1; v2])).

Fixpoint split_cons (n : nat) (v : Val) : option (Val * Val) :=
match n, v with
| 0, _ => Some (VNil, v)
| (S n'), VCons hd tl =>
  match split_cons n' tl with
  | Some (v1, v2) => Some (VCons hd v1, v2)
  | None => None
  end
| _, _ => None
end.

(* TODO: this is a module function
   We use this function to define concurrent map. *)
Definition eval_split (v1 v2 : Val) : Redex :=
match v1 with
| VLit (Integer i) => if Z.ltb i 0
                      then RExc (badarg (VTuple [VLit (Atom "split"); v1; v2]))
                      else 
                        match split_cons (Z.to_nat i) v2 with
                        | Some (v1, v2) => RValSeq [VTuple [v1;v2]]
                        | None => RExc (badarg (VTuple [VLit (Atom "split"); v1; v2]))
                        end
| _ => RExc (badarg (VTuple [VLit (Atom "split"); v1; v2]))
end.

Definition eval_transform_list (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BApp, [v1; v2]        => eval_append v1 v2
| BMinusMinus, [v1; v2] => eval_subtract v1 v2
| BSplit, [v1; v2] => eval_split v1 v2
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Fixpoint meta_to_cons l :=
 match l with
 | [] => VNil
 | x::xs => VCons x (meta_to_cons xs)
 end.

Definition transform_tuple (v : Val) : Redex :=
match v with
| VTuple l => RValSeq [meta_to_cons l]
| _        => RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); v]))
end.

Fixpoint mk_list (l : Val) : option (list Val) :=
match l with
| VNil => Some []
| VCons v1 v2 => match mk_list v2 with
                 | Some l => Some (v1 :: l)
                 | _ => None
                 end
| _ => None
end.

Definition eval_list_tuple (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BTupleToList, [v] => transform_tuple v
| BListToTuple, [v] => match mk_list v with
                                 | None => RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); v]))
                                 | Some l => RValSeq [VTuple l]
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

Fixpoint len (l : Val) : option nat :=
match l with
| VNil => Some 0
| VCons v1 v2 => match len v2 with
                 | Some n2 => Some (S n2)
                 | _ => None
                 end
| _ => None
end.


Definition eval_length (params : list Val) : Redex :=
match params with
| [v] => match len v with
         | Some n => RValSeq [VLit (Integer (Z.of_nat n))]
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
(** Note: we intentionally avoid pattern matching on strings here *)
| BIsBoolean, [v] => if orb (Val_eqb v ttrue) (Val_eqb v ffalse)
                     then RValSeq [ttrue]
                     else RValSeq [ffalse]
| _, _              => RExc (undef (VLit (Atom fname)))
end.

Definition eval_error (mname : string) (fname : string) (params : list Val) : option Exception :=
match convert_string_to_code (mname, fname), params with
| BError, [reason]              => Some (Error, reason, VNil) (* TODO stacktrace! *)
| BError, [reason;args]         => Some (Error, reason, args) (* TODO stacktrace! *)
| BError, [reason;args;options] => Some (Error, reason, args) (* TODO options, stacktrace! *)
| BThrow, [reason]              => Some (Throw, reason, VNil) (* TODO stacktrace! *)
| BExit, [reason]               => Some (Exit, reason, VNil) (* TODO stacktrace! *)
| BExit, [_;_]                  => None (* THIS IS CONCURRENT EXIT! *)
| _, _                          => Some (undef (VLit (Atom fname)))
end.

Definition eval_primop_error (fname : string) (params : list Val) : option Exception :=
match convert_primop_to_code fname with
| PMatchFail =>
  match params with
  | [val]        => Some (Error, val, VNil) (* TODO: in the future VNil should be the stacktrace *)
  | _            => None (* This is a compilation error *)
  end
| PRaise => match params with
  | [stacktrace; reas] => Some (Error, reas, stacktrace)
  | _ => None (* This is a compilation error *)
  end
| _ => Some (undef (VLit (Atom fname)))
end.

(* Eval for primary operations *)
Definition primop_eval (fname : string) (params : list Val) (eff : SideEffectList) : option (Redex * SideEffectList) :=
match convert_primop_to_code fname with
  | PMatchFail | PRaise =>
    match (eval_primop_error fname params) with
    | Some exc => Some (RExc exc, eff)
    | None => None (* this is a compile-time error *)
    end
  | PRecvNext | PRemoveMsg | PPeekMsg
  | PRecvWaitTimeout => None (* These are concurrent Primops *)
  | _ => Some (RExc (undef (VLit (Atom fname))), eff)
end.

Definition eval_funinfo (params : list Val) : Redex :=
match params with
| [VClos ext id params e;v] =>
  if v =ᵥ VLit "arity"%string
  then RValSeq [VLit (Z.of_nat params)]
  else RExc (badarg (VTuple [VLit "fun_info"%string;VClos ext id params e;v]))
| [v1;v2] => RExc (badarg (VTuple [VLit "fun_info"%string;v1;v2]))
| _ => RExc (undef (VLit "fun_info"%string))
end.

(* This function returns None, for the correct parametherisation of the concurrent BIFs *)
Definition eval_concurrent (mname : string) (fname : string) (params : list Val) : option Exception :=
match convert_string_to_code (mname, fname) with
| BSend                          => match params with
                                    | _ :: _ :: _ => None
                                    | _           => Some (undef (VLit (Atom fname)))
                                    end
| BSpawn | BSpawnLink            => match params with (* TODO: 1, 3 parameter spawn versions *)
                                    | _ :: _ :: _ => None
                                    | _           => Some (undef (VLit (Atom fname)))
                                    end
| BSelf                          => match params with
                                    | [] => None
                                    | _  => Some (undef (VLit (Atom fname)))
                                    end
| BLink | BUnLink | BProcessFlag => match params with
                                    | _ :: _ => None
                                    | _      => Some (undef (VLit (Atom fname)))
                                    end
| _                              => Some (undef (VLit (Atom fname)))
end.

(* Note: Always can be extended, this function simulates inter-module calls *)
Definition eval (mname : string) (fname : string) (params : list Val) (eff : SideEffectList) 
   : option (Redex * SideEffectList) :=
match convert_string_to_code (mname, fname) with
| BPlus | BMinus | BMult | BDivide | BRem | BDiv
| BSl   | BSr    | BAbs                           => Some (eval_arith mname fname params, eff)
| BFwrite | BFread                                => Some (eval_io mname fname params eff)
| BAnd | BOr | BNot                               => Some (eval_logical mname fname params, eff)
| BEq | BTypeEq | BNeq | BTypeNeq                 => Some (eval_equality mname fname params, eff)
| BApp | BMinusMinus | BSplit                     => Some (eval_transform_list mname fname params, eff)
| BTupleToList | BListToTuple                     => Some (eval_list_tuple mname fname params, eff)
| BLt | BGt | BLe | BGe                           => Some (eval_cmp mname fname params, eff)
| BLength                                         => Some (eval_length params, eff)
| BTupleSize                                      => Some (eval_tuple_size params, eff)
| BHd | BTl                                       => Some (eval_hd_tl mname fname params, eff)
| BElement | BSetElement                          => Some (eval_elem_tuple mname fname params, eff)
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean   => Some (eval_check mname fname params, eff)
| BError | BExit | BThrow                         => match (eval_error mname fname params) with
                                                      | Some exc => Some (RExc exc, eff)
                                                      | None => None
                                                     end
| BFunInfo                                        => Some (eval_funinfo params, eff)
(** undefined functions *)
| BNothing                                        => Some (RExc (undef (VLit (Atom fname))), eff)
(* concurrent BIFs *)
| BSend | BSpawn | BSpawnLink | BSelf | BProcessFlag
| BLink | BUnLink                                 => match eval_concurrent mname fname params with
                                                     | Some exc => Some (RExc exc, eff)
                                                     | None => None
                                                     end
end.


Theorem primop_eval_effect_extension fname vals eff1 res eff2 :
  primop_eval fname vals eff1 = Some (res, eff2)
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros. unfold primop_eval in H.
  destruct (convert_primop_to_code fname) eqn:Hfname; simpl in H.
  all: try (unfold eval_primop_error in H; rewrite Hfname in H;
    repeat break_match_hyp; inv H; try congruence).
  * inv Heqo. exists []. now rewrite app_nil_r.
  * inv Heqo. exists []. now rewrite app_nil_r.
  * inv H. exists []. now rewrite app_nil_r.
  * inv H.
  * inv H.
  * inv H.
  * inv H.
Qed.

Theorem eval_effect_extension mname fname vals eff1 res eff2 :
  eval mname fname vals eff1 = Some (res, eff2)
->
  exists l', eff2 = eff1 ++ l'.
Proof.
  intros. unfold eval in H.
  destruct (convert_string_to_code (mname,fname)) eqn:Hfname; simpl in H; repeat invSome.
  all: try (unfold eval_error, eval_concurrent in H; rewrite Hfname in H; repeat break_match_hyp; repeat invSome).
  all: try now (exists []; rewrite app_nil_r).
  * unfold eval_io in H1; rewrite Hfname in H1; destruct (length vals) eqn:Hl; inv H1.
    - exists []; now rewrite app_nil_r.
    - destruct n.
      + inv H0. now exists [(Output, vals)].
      + inv H0. exists []; now rewrite app_nil_r.
  * unfold eval_io in H1; rewrite Hfname in H1; destruct (length vals) eqn:Hl; inv H1.
    - exists []; now rewrite app_nil_r.
    - destruct n.
      + inv H0. exists []; now rewrite app_nil_r.
      + destruct n.
        ** inv H0. now exists [(Input, vals)].
        ** inv H0. exists []; now rewrite app_nil_r.
Qed.

Theorem eval_effect_irrelevant {mname fname vals eff eff' r}:
  eval mname fname vals eff = Some (r, eff ++ eff')
->
  forall eff0, (eval mname fname vals eff0) = Some (r, eff0 ++ eff').
Proof.
  intros.
  unfold eval in *. destruct (convert_string_to_code (mname, fname)) eqn:Hfname; repeat invSome.
  all: try now (rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst; rewrite app_nil_r).
  3-5: unfold eval_error in *; rewrite Hfname in *; repeat break_match_hyp; repeat invSome.
  14-20: unfold eval_concurrent in *; rewrite Hfname in *; repeat break_match_hyp; repeat invSome.
  all: try now (rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst; rewrite app_nil_r).
  * unfold eval_io in *. rewrite Hfname in *. destruct (length vals); try invSome.
    - simpl in *; rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst;
             rewrite app_nil_r; reflexivity.
    - destruct n; simpl in *; invSome.
      + apply app_inv_head in H2. rewrite H2. reflexivity.
      + rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst;
             rewrite app_nil_r; reflexivity.
  * unfold eval_io in *. rewrite Hfname in *. destruct (length vals); try invSome.
    - simpl in *; rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst;
             rewrite app_nil_r; reflexivity.
    - destruct n; simpl in *; try invSome.
      + simpl in *; rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst;
             rewrite app_nil_r; reflexivity.
      + destruct n; invSome.
        ** apply app_inv_head in H2. rewrite H2. reflexivity.
        ** rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst;
             rewrite app_nil_r; reflexivity.
Qed.

Theorem primop_eval_effect_irrelevant {fname vals eff eff' r}:
  primop_eval fname vals eff = Some (r, eff ++ eff')
->
  forall eff0, primop_eval fname vals eff0 = Some (r, eff0 ++ eff').
Proof.
  intros.
  unfold primop_eval in *. destruct (convert_primop_to_code fname) eqn:Hfname;
    try unfold eval_primop_error in *; try rewrite Hfname in *; try invSome.
  all: repeat break_match_hyp; repeat invSome;
       rewrite <- app_nil_r in H2 at 1; apply app_inv_head in H2; subst;
  rewrite app_nil_r; reflexivity.
Qed.

Theorem eval_effect_permutation m f vals eff eff' r1 r2 eff1 eff2 :
  eval m f vals eff = Some (r1, eff1) ->
  eval m f vals eff' = Some (r2, eff2) ->
  Permutation eff eff'
->
  Permutation eff1 eff2.
Proof.
  intros. apply eval_effect_extension in H as H'.
  apply eval_effect_extension in H0 as H0'. destruct_hyps. subst.
  eapply eval_effect_irrelevant in H. rewrite H in H0. inv H0.
  apply app_inv_head in H4. subst.
  now apply Permutation_app_tail.
Qed.

Proposition plus_comm_basic {e1 e2 t : Val} {eff : SideEffectList} : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = Some (RValSeq [t], eff)
->
  eval "erlang"%string "+"%string [e2; e1] eff = Some (RValSeq [t], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inv H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inv H3).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_Val {e1 e2 v : Val} (eff eff2 : SideEffectList) : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = Some (RValSeq [v], eff)
->
  eval "erlang"%string "+"%string [e2; e1] eff2 = Some (RValSeq [v], eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inv H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inv H3).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_extended {e1 e2 : Val} (v : Redex) (eff eff2 : SideEffectList) : 
  eval "erlang"%string "+"%string [e1 ; e2] eff = Some (v, eff)
->
  exists v', eval "erlang"%string "+"%string [e2; e1] eff2 = Some (v', eff2).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(inv H1; eexists; reflexivity).
Qed.

Proposition plus_effect_unmodified {e1 e2 : Val} (v' : Redex) (eff eff2 : SideEffectList) :
  eval "erlang"%string "+"%string [e1 ; e2] eff = Some (v', eff2)
->
  eff = eff2.
Proof.
  simpl. intros. now inv H.
Qed.

Proposition plus_effect_changeable {v1 v2 : Val} (v' : Redex) (eff eff2 : SideEffectList) :
  eval "erlang"%string "+"%string [v1; v2] eff = Some (v', eff)
->
  eval "erlang"%string "+"%string [v1; v2] eff2 = Some (v', eff2).
Proof.
  intros. case_eq v1; case_eq v2; intros; subst.
  all: try(inv H; reflexivity).
Qed.

Lemma subtract_elem_closed Γ:
  forall v1 v2, VAL Γ ⊢ v1 -> VAL Γ ⊢ v2 ->
  VAL Γ ⊢ (subtract_elem v1 v2).
Proof.
  induction v1; intros; cbn; try constructor.
  repeat break_match_goal; destruct_redex_scopes; auto.
Qed.

Lemma eval_subtract_nil :
  forall v, is_shallow_proper_list v = true ->
    eval_subtract VNil v = RValSeq [VNil].
Proof.
  induction v; intros Hprop; inv Hprop; auto.
  simpl. rewrite H0. auto.
Qed.

Lemma primop_eval_is_result :
  forall f vl eff r eff',
  Forall (fun v => VALCLOSED v) vl ->
  primop_eval f vl eff = Some (r, eff') ->
  is_result r.
Proof.
  intros. unfold primop_eval in *.
  repeat break_match_hyp; invSome; unfold undef in *; auto.
  all: unfold eval_primop_error in *; repeat break_match_hyp; invSome; destruct_foralls; try now constructor.
Qed.

Lemma is_result_closed :
  forall r, is_result r -> REDCLOSED r.
Proof.
  destruct r; intros; inv H; auto.
Qed.

Lemma eval_is_result :
  forall f m vl eff r eff',
  Forall (fun v => VALCLOSED v) vl ->
  eval m f vl eff = Some (r, eff') ->
  is_result r.
Proof.
  intros. unfold eval in *.
  break_match_hyp; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_concurrent in *; try rewrite Heqb in *; try invSome.
  all: repeat break_match_goal; try invSome; subst.
  all: try now constructor; auto.
  all: destruct_foralls; destruct_redex_scopes; auto.
  all: try constructor; try constructor; try (apply indexed_to_forall; repeat constructor; auto).
  all: auto.
  1-2: repeat break_match_hyp; invSome; unfold undef; auto.
  * do 3 constructor. apply indexed_to_forall. repeat constructor.
    rewrite indexed_to_forall in H. apply H. lia.
  * clear Heqb m f eff'. induction v; cbn.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    - now do 2 constructor.
    - destruct_redex_scopes. apply IHv1 in H4 as H4'. break_match_goal.
      2: break_match_goal. 3: break_match_goal.
      all: try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
      do 3 constructor; subst; auto.
      apply IHv2 in H5. destruct_redex_scopes. apply is_result_closed in H5. 
      inv H5. now inv H0.
  * clear Heqb eff' m f. generalize dependent v. induction v0; intros; cbn; break_match_goal; try destruct v.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    all: try now do 2 constructor.
    all: cbn in Heqb; try congruence.
    - inv H1. now apply IHv0_2.
    - inv H1. apply IHv0_2; auto. now apply subtract_elem_closed.
  * destruct v; simpl.
    2: destruct l. 3: break_match_goal. 4: break_match_goal.
    all: try constructor; auto.
    all: try (constructor; apply indexed_to_forall).
    all: try constructor; auto.
    clear -Heqo H1. destruct p. constructor. constructor; auto.
    constructor. apply indexed_to_forall.
    remember (Z.to_nat _) as n. clear Heqn x.
    revert v v1 v0 Heqo H1. induction n; intros; simpl in *.
    - inv Heqo. constructor; auto.
    - destruct v0; try invSome. break_match_hyp. 2: invSome.
      destruct p. invSome. destruct_redex_scopes.
      apply IHn in Heqo0; auto. destruct_foralls.
      auto.
  * clear Heqb eff' m f. induction v; cbn.
    all: destruct_redex_scopes; try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
    do 2 constructor; auto. induction l; constructor.
    - apply (H1 0). simpl. lia.
    - apply IHl. intros. apply (H1 (S i)). simpl. lia.
  * clear Heqb eff' m f. generalize dependent v. induction l0; cbn; intros.
    - constructor. simpl. lia.
    - destruct v; cbn in Heqo; try congruence.
      destruct_redex_scopes. 
      repeat break_match_hyp; inversion Heqo; subst.
      constructor. apply indexed_to_forall. constructor; auto.
      apply IHl0 in Heqo0; auto.
      inversion Heqo0. now rewrite <- indexed_to_forall in H1.
  * clear Heqb eff' f m. induction H; simpl; unfold undef; auto.
    repeat break_match_goal; auto.
    do 2 constructor. apply indexed_to_forall. now repeat constructor.
  * clear Heqb eff' f m. induction H; simpl; unfold undef; auto. destruct x, l; unfold badarg; auto.
    all: inv H; do 2 constructor; apply indexed_to_forall; repeat constructor; auto.
  * epose proof (proj1 (nth_error_Some l2 (Init.Nat.pred (Pos.to_nat p))) _).
    Unshelve. 2: { intro. rewrite H in Heqo. congruence. }
    eapply nth_error_nth with (d := VNil) in Heqo. subst. now apply H2.
  * remember (Init.Nat.pred (Pos.to_nat p)) as k. clear Heqk Heqb m f p eff'.
    generalize dependent l4. revert k. induction l2; intros; simpl in *.
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
        apply IHl2 in Heqo0. inversion Heqo0. apply (H4 i). lia.
        intros. apply (H2 (S i0)). lia.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
    all: destruct_foralls; constructor; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
    all: destruct_foralls; constructor; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
    all: destruct_foralls; constructor; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * repeat break_match_hyp; repeat invSome; unfold undef; auto.
  * unfold eval_funinfo. repeat break_match_goal; unfold undef; auto.
    all: do 2 constructor; apply indexed_to_forall; subst; destruct_foralls; auto.
Qed.

Corollary closed_primop_eval : forall f vl eff r eff',
  Forall (fun v => VALCLOSED v) vl ->
  (primop_eval f vl eff) = Some (r, eff') ->
  REDCLOSED r.
Proof.
  intros.
  apply is_result_closed. eapply primop_eval_is_result; eassumption.
Qed.

Corollary closed_eval : forall m f vl eff r eff',
  Forall (fun v => VALCLOSED v) vl ->
  eval m f vl eff = Some (r, eff') ->
  REDCLOSED r.
Proof.
  intros.
  apply is_result_closed. eapply eval_is_result; eassumption.
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
  break_match_hyp; try congruence. inv Heqo; try lia.
Qed.

Transparent convert_string_to_code.
Transparent convert_primop_to_code.

Section Tests.

(** Tests *)

Goal (eval "erlang" "+" [VLit (Integer 1); VLit (Integer 2)]) [] = Some (RValSeq [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Integer 1); VLit (Integer 2)]) [] = Some (RValSeq [VLit (Integer (-1))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "-" [VLit (Atom "foo")]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "+" [VLit (Atom "foo")]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo")])), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal (eval "erlang" "bsl" [VLit (Integer 10); VLit (Integer 20)]) [] = Some (RValSeq [VLit (Integer 10485760)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Integer 10); VLit (Integer 20)]) [] = Some (RValSeq [VLit (Integer 0)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Atom "foo"); VLit (Integer 2)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = Some (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Integer 1); VLit (Atom "foo")])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "bsl" [VLit (Atom "foo")]) [] 
    = Some (RExc (undef (VLit (Atom "bsl"))), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.
Goal (eval "erlang" "bsr" [VLit (Atom "foo")]) [] 
    = Some (RExc (undef (VLit (Atom "bsr"))), []).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal (eval "erlang" "not" [ttrue]) [] = Some (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [ffalse]) [] = Some (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [VLit (Integer 5)]) [] = Some (RExc (badarg (VTuple [VLit (Atom "not"); VLit (Integer 5)])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "not" [VLit (Integer 5); VEmptyTuple]) [] = Some (RExc (undef (VLit (Atom "not"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "and" [ttrue; ttrue]) [] = Some (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue; ffalse]) [] = Some (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ffalse; ttrue]) [] = Some (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ffalse; ffalse]) [] = Some (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue; VEmptyTuple]) [] = Some (RExc (badarg (VTuple [VLit (Atom "and"); ttrue; VTuple []])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue]) [] = Some (RExc (undef (VLit (Atom "and"))), []). Proof. reflexivity. Qed.

Goal (eval "erlang" "or" [ttrue; ttrue]) [] = Some (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue; ffalse]) [] = Some (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ffalse; ttrue]) [] = Some (RValSeq [ttrue], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ffalse; ffalse]) [] = Some (RValSeq [ffalse], []). Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue; VEmptyTuple]) [] = Some (RExc (badarg (VTuple [VLit (Atom "or"); ttrue; VTuple []])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "or" [ttrue]) [] = Some (RExc (undef (VLit (Atom "or"))), []).
Proof. reflexivity. Qed.

Goal (eval "io" "fwrite" [ttrue]) [] = Some (RValSeq [ok], [(Output, [ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fwrite" [VMap [(ttrue, ttrue)]]) [] = Some (RValSeq [ok], [(Output, [VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fwrite" []) [] = Some (RExc (undef (VLit (Atom "fwrite"))), []).
Proof. reflexivity. Qed.

Goal (eval "io" "fread" [VLit (Atom "foo.txt"); ttrue]) [] = Some 
   (RValSeq [VTuple [ok; ttrue]], [(Input, [VLit (Atom "foo.txt"); ttrue])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]]) [] = Some 
   (RValSeq [VTuple [ok; VMap [(ttrue, ttrue)]]], [(Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])]).
Proof. reflexivity. Qed.
Goal (eval "io" "fread" []) [] = Some (RExc (undef (VLit (Atom "fread"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "==" [ttrue; ttrue]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [ttrue; ffalse]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] 1 0 EEmptyMap; ttrue]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "/=" [ttrue; ttrue]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [ttrue; ffalse]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; ttrue]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed. 
Goal (eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "/=" [ttrue]) [] = Some (RExc (undef (VLit (Atom "/="))), []).
Proof. reflexivity. Qed.

Definition l1 : Val := VCons ttrue VNil.
Definition l2 : Val := VCons ttrue ttrue.
Definition l3 : Val := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Val := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Val := VCons ttrue (VCons ttrue ttrue).

Goal (eval "erlang" "++" [ttrue; ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "++"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l1]) [] = Some (RValSeq [VCons ttrue (VCons ttrue VNil)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l2]) [] = Some
  (RValSeq [VCons ttrue (VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; l3]) [] = Some
  (RValSeq [VCons ttrue (VCons (VCons ttrue ttrue) ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "++" [l3; l3]) [] = Some
  (RExc (badarg (VTuple [VLit (Atom "++"); VCons (VCons ttrue ttrue) ttrue; VCons (VCons ttrue ttrue) ttrue])), []).
Proof.  unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal (eval "erlang" "++" [l1; ErrorVal]) [] = Some (RValSeq [VCons ttrue ErrorVal], []).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.

Goal (eval "lists" "split" [VLit (Integer 0); VNil]) [] = Some (RValSeq [VTuple [VNil; VNil]], []).
Proof. reflexivity. Qed.
Goal (eval "lists" "split" [VLit (Integer 0); VCons ttrue (VCons ttrue VNil)]) [] = Some (RValSeq [VTuple [VNil; VCons ttrue (VCons ttrue VNil)]], []).
Proof. cbn. reflexivity. Qed.
Goal exists x, (eval "lists" "split" [VLit (Integer 4); VCons ttrue (VCons ttrue VNil)]) [] = Some (RExc (badarg x), []).
Proof. eexists. reflexivity. Qed.
Goal (eval "lists" "split" [VLit (Integer 4); VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue VNil)))))]) [] = Some (RValSeq [VTuple [VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue VNil))); VCons ttrue (VCons ttrue VNil)]], []).
Proof. reflexivity. Qed.



Goal (eval "erlang" "--" [ttrue; ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "--"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l1]) [] = Some (RValSeq [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l2]) [] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons ttrue ttrue])), []).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal (eval "erlang" "--" [l1; l3]) [] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l3; l3]) [] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue;
                        VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l3; l1]) [] =
  Some (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue; VCons ttrue VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [l4; l4]) [] = Some (RValSeq [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "--" [VCons (VLit (Integer 0)) (VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) (VCons VNil VNil))));
  VCons VNil (VCons (VLit (Integer 0)) VNil)
] [])
=
  Some (RValSeq [(VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) VNil)))], []).
Proof. unfold eval, eval_transform_list, eval_subtract. simpl. reflexivity. Qed.

Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] []) =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] []) =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue (VCons ttrue ttrue)) 
                                 (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] []) =
  Some (RValSeq [VCons ttrue (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] []) =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue ttrue) (VCons (VCons ttrue VNil) VNil)))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_to_list" [ttrue] []) = Some
  (RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); ttrue])), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "list_to_tuple" [l1] []) = Some (RValSeq [VTuple [VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l2] []) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l3] []) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons (VCons ttrue ttrue) ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l4] []) =
  Some (RValSeq [VTuple [VLit (Atom "true"); VLit (Atom "true"); VLit (Atom "true")]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_tuple" [l5] []) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); l5])), []).
Proof. cbn. reflexivity. Qed.

Goal (eval "erlang" "<" [ttrue; ttrue]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [ttrue; ffalse]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "=<" [ttrue; ttrue]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [ttrue; ffalse]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" ">" [ttrue; ttrue]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [ffalse; ttrue]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" ">=" [ttrue; ttrue]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [ffalse; ttrue]) [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" ">=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "length" [l1]) [] = Some (RValSeq [VLit (Integer 1)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l2]) [] = Some (RExc (badarg (VTuple [VLit (Atom "length");l2])), []).
Proof. cbn. reflexivity. Qed.
Goal (eval "erlang" "length" [l3]) [] = Some (RExc (badarg (VTuple [VLit (Atom "length");l3])), []).
Proof. cbn. reflexivity. Qed.
Goal (eval "erlang" "length" [l4]) [] = Some (RValSeq [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l5]) [] = Some (RExc (badarg (VTuple [VLit (Atom "length");l5])), []).
Proof. cbn. reflexivity. Qed.
Goal (eval "erlang" "length" [ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "length");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "length" [l5;l3]) [] = Some (RExc (undef (VLit (Atom "length"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "tuple_size" [l3]) [] = Some (RExc (badarg (VTuple [VLit (Atom "tuple_size");l3])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple []]) [] = Some (RValSeq [VLit (Integer 0)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]]) [] = Some (RValSeq [VLit (Integer 3)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]; ErrorVal]) [] = Some (RExc (undef (VLit (Atom "tuple_size"))), []).
Proof. reflexivity. Qed.


Goal (eval "erlang" "hd" [l1]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [VNil]) [] = Some (RExc (badarg (VTuple [VLit (Atom "hd");VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l2]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l3]) [] = Some (RValSeq [(VCons ttrue ttrue)], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l4]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l5]) [] = Some (RValSeq [ttrue], []).
Proof. unfold l5. reflexivity. Qed.
Goal (eval "erlang" "hd" [ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "hd");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "hd" [l5;l3]) [] = Some (RExc (undef (VLit (Atom "hd"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "tl" [l1]) [] = Some (RValSeq [VNil], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [VNil]) [] = Some (RExc (badarg (VTuple [VLit (Atom "tl");VNil])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l2]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l3]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l4]) [] = Some (RValSeq [(VCons ttrue (VCons ttrue VNil))], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l5]) [] = Some (RValSeq [VCons ttrue ttrue], []).
Proof. unfold l5. reflexivity. Qed.
Goal (eval "erlang" "tl" [ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "tl");ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "tl" [l5;l3]) [] = Some (RExc (undef (VLit (Atom "tl"))), []).
Proof. reflexivity. Qed.


Goal (eval "erlang" "element" [VLit (Integer 2); VTuple [ttrue]]) [] = Some (RExc (badarg (VTuple [VLit (Atom "element"); VLit (Integer 2); VTuple [ttrue]])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "element" [VLit (Integer 1); VTuple [ttrue]]) [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "element" [ttrue; ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "element"); ttrue; ttrue])), []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "element" [ttrue]) [] = Some (RExc (undef (VLit (Atom "element"))), []).
Proof. reflexivity. Qed.

Goal (eval "erlang" "setelement" [VLit (Integer 2); VTuple [ttrue]; ffalse]) [] = Some (RExc (badarg (VTuple [VLit (Atom "setelement"); VLit (Integer 2); VTuple [ttrue]; ffalse])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "setelement" [VLit (Integer 1); VTuple [ttrue]; ffalse]) [] = Some (RValSeq [VTuple [ffalse]], []).
Proof. reflexivity. Qed.
Goal (eval "erlang" "setelement" [ttrue; ttrue; ttrue]) [] = Some (RExc (badarg (VTuple [VLit (Atom "setelement"); ttrue; ttrue; ttrue])), []).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal (eval "erlang" "setelement" [ttrue]) [] = Some (RExc (undef (VLit (Atom "setelement"))), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_number" [VLit (Integer 2)] [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse] [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse; ffalse] [] = Some (RExc (undef (VLit (Atom "is_number"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [VLit (Integer 2)] [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse] [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse; ffalse] [] = Some (RExc (undef (VLit (Atom "is_integer"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Integer 2)] [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Atom "foo")] [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [ffalse; ffalse] [] = Some (RExc (undef (VLit (Atom "is_atom"))), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [VLit (Integer 2)] [] = Some (RValSeq [ffalse], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ttrue] [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse] [] = Some (RValSeq [ttrue], []).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse; ffalse] [] = Some (RExc (undef (VLit (Atom "is_boolean"))), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "error" [ffalse; ffalse] [] = Some (RExc (Error, ffalse, ffalse), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [ffalse] [] = Some (RExc (Error, ffalse, VNil), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [] [] = Some (RExc (undef ErrorVal), []).
Proof. reflexivity. Qed.

Goal eval "erlang" "fun_info" [ffalse; ffalse] [] = Some (RExc (badarg (VTuple [VLit "fun_info"%string; ffalse; ffalse])), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "fun_info" [ffalse] [] = Some (RExc (undef (VLit "fun_info"%string)), []).
Proof. reflexivity. Qed.
Goal eval "erlang" "fun_info" [VClos [] 0 2 (˝VNil); VLit "arity"%string] [] = Some (RValSeq [VLit 2%Z], []).
Proof. reflexivity. Qed.

End Tests.
