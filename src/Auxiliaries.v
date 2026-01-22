(**
  This file contains function definitions that simulate the behaviour of
  built-in and standard functions (and primitive operations) of Core Erlang.
  In also includes a number of theorems about their properties and many unit
  tests.
*)

(**
  WARNING!

  Changes made to the eval definition can potentially break some proofs in the
  following files:
  - FrameStack/Compatibility.v
  - Concurrent/PIDRenaming.v
  - Concurrent/NodeSemanticsLemmas.v
*)

From CoreErlang Require Export SideEffects ScopingLemmas Equalities.
Require Export Stdlib.Sorting.Permutation.
From Stdlib Require Export Ascii.
From Stdlib Require Export Numbers.DecimalString Decimal.

Import ListNotations.

(**
  Built-in function simulation

  PrimopCode and BIFCode is used to enable better pattern-matching on strings
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
| BListToAtom | BIntegerToList
| BLt | BLe | BGt | BGe
| BLength | BTupleSize
| BTl | BHd
| BElement | BSetElement
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean
| BError | BExit | BThrow
(** !, spawn, process_flag, self, link, unlink, exit/2:
   these BIF and primops are handled on the process-local level, they behave
   here as undefined  *)
| BSend | BSpawn | BSpawnLink | BProcessFlag | BSelf | BLink | BUnLink
| BNothing
| BFunInfo
.

(**
  Conversion from strings to codes
*)
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
| ("erlang"%string, "list_to_atom"%string) => BListToAtom
| ("erlang"%string, "integer_to_list"%string) => BIntegerToList
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
Definition eval_io (mname : string) (fname : string) (params : list Val)
   : (Redex * option SideEffect) :=
match convert_string_to_code (mname, fname), length params, params with
(** writing *)
| BFwrite, 1, _ => (RValSeq [ok], Some (Output, params))
(** reading *)
| BFread, 2, e => (RValSeq [VTuple [ok; nth 1 params ErrorVal]], Some (Input, params))
(** anything else *)
| _              , _, _ => (RExc (undef (VLit (Atom fname))), None)
end.

(** For boolean operations *)
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

(** For equality *)
Definition eval_equality (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BEq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeEq, [v1; v2] => if Val_eqb v1 v2 then RValSeq [ttrue] else RValSeq [ffalse]
| BNeq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeNeq, [v1; v2] => if Val_eqb v1 v2 then RValSeq [ffalse] else RValSeq [ttrue]
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

(** In Erlang, there are not proper lists, e.g., [1|2] => VCons (VLit 1) (VLit 2)
*)
Fixpoint is_shallow_proper_list (v : Val) : bool :=
match v with
| VNil => true
| VCons x y => is_shallow_proper_list y
| _ => false
end.

(** Append for VCons *)
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

(** List subtraction *)
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

(** List splitting *)
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

(** NOTE: this is a module function - after formalising the module system for
          the frame stack semantics, it should be handled in the 'lists'
          module, and not as a simulated function.
    We use this function to define concurrent map in `MapPmap.v`. *)
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

(** List transformation functions *)
Definition eval_transform_list (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BApp, [v1; v2]        => eval_append v1 v2
| BMinusMinus, [v1; v2] => eval_subtract v1 v2
| BSplit, [v1; v2] => eval_split v1 v2
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

(** Meta level lists are converted to Core Erlang lists with this function. *)
Fixpoint meta_to_cons l :=
 match l with
 | [] => VNil
 | x::xs => VCons x (meta_to_cons xs)
 end.

(** Tuple transforming functions *)
Definition transform_tuple (v : Val) : Redex :=
match v with
| VTuple l => RValSeq [meta_to_cons l]
| _        => RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); v]))
end.

(** Core Erlang lists are transformed to meta level lists, if possible (for proper
    lists). *)
Fixpoint mk_list (l : Val) : option (list Val) :=
match l with
| VNil => Some []
| VCons v1 v2 => match mk_list v2 with
                 | Some l => Some (v1 :: l)
                 | _ => None
                 end
| _ => None
end.

(** Turning lists into tuples and vice versa *)
Definition eval_list_tuple (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BTupleToList, [v] => transform_tuple v
| BListToTuple, [v] => match mk_list v with
                                 | None => RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); v]))
                                 | Some l => RValSeq [VTuple l]
                                 end
| _                     , _   => RExc (undef (VLit (Atom fname)))
end.

(** TODO: Revise the definition as the badarg exceptions (not a proper list / not a char list)
    are not distinguished from each other *)
Fixpoint mk_ascii_list (l : Val) : option (list ascii) :=
match l with
| VNil => Some []
| VCons (VLit (Integer v1)) v2 =>
  match mk_ascii_list v2 with
    | Some s => Some ((Ascii.ascii_of_nat (Z.to_nat(v1))) :: s)
    | _ => None
    end
| _ => None
end.

Fixpoint string_to_vcons (s : string) : Val :=
match s with
 | EmptyString => VNil
 | String x xs => VCons (VLit (Z.of_nat (nat_of_ascii x))) (string_to_vcons xs)
end.

(** Turning lists into atoms *)
Definition eval_convert (mname : string) (fname : string) (params : list Val) : Redex * option SideEffect :=
match convert_string_to_code (mname, fname), params with
| BListToAtom, [v] =>
  match mk_ascii_list v with
  | None => (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); v])), None)
  | Some sl => (RValSeq [VLit (Atom (string_of_list_ascii(sl)))], Some (AtomCreation, [VLit (Atom (string_of_list_ascii(sl)))]))
  end
| BIntegerToList, [v] =>
  match v with
  | VLit (Integer z) => (RValSeq [string_to_vcons (NilZero.string_of_int (Z.to_int z))], None)
  | _ => (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); v])), None)
  end
| _                     , _   => (RExc (undef (VLit (Atom fname))), None)
end.

(** Comparison for Core Erlang *)
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

(** Helper function for the length of a proper list *)
Fixpoint len (l : Val) : option nat :=
match l with
| VNil => Some 0
| VCons v1 v2 => match len v2 with
                 | Some n2 => Some (S n2)
                 | _ => None
                 end
| _ => None
end.

(** Length of a proper list *)
Definition eval_length (params : list Val) : Redex :=
match params with
| [v] => match len v with
         | Some n => RValSeq [VLit (Integer (Z.of_nat n))]
         | None => RExc (badarg (VTuple [VLit (Atom "length"); v]))
         end
| _ => RExc (undef (VLit (Atom "length")))
end.

(** Tuple size (for any tuple) *)
Definition eval_tuple_size (params : list Val) : Redex :=
match params with
| [VTuple l] => RValSeq [VLit (Integer (Z.of_nat (length l)))]
| [v] => RExc (badarg (VTuple [VLit (Atom "tuple_size"); v]))
| _ => RExc (undef (VLit (Atom "tuple_size")))
end.

(** hd and tl function for (any) Core Erlang lists *)
Definition eval_hd_tl (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BHd, [VCons x y] => RValSeq [x]
| BHd, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| BTl, [VCons x y] => RValSeq [y]
| BTl, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| _, _ => RExc (undef (VLit (Atom fname)))
end.

(**
  Obtaining and modifying a single element of a tuple
*)
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

(** Type checks of Core Erlang *)
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

(** Error handling functions *)
Definition eval_error (mname : string) (fname : string) (params : list Val) : option Exception :=
match convert_string_to_code (mname, fname), params with
| BError, [reason]              => Some (Error, reason, VNil) (* TODO stacktrace! *)
| BError, [reason;args]         => Some (Error, reason, args) (* TODO stacktrace! *)
| BError, [reason;args;options] => Some (Error, reason, args) (* TODO options, stacktrace! *)
| BThrow, [reason]              => Some (Throw, reason, VNil) (* TODO stacktrace! *)
| BExit, [reason]               => Some (Exit, reason, VNil) (* TODO stacktrace! *)
(** This line corresponds to the concurrent exit/2 BIF! It is not defined here,
    its semantics is in ProcessSemantics.v *)
| BExit, [_;_]                  => None
(***)
| _, _                          => Some (undef (VLit (Atom fname)))
end.

(** Primitive operations for errors *)
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

(** Simulated primary operations *)
Definition primop_eval (fname : string) (params : list Val) : option (Redex * (option SideEffect)) :=
match convert_primop_to_code fname with
  | PMatchFail | PRaise =>
    match (eval_primop_error fname params) with
    | Some exc => Some (RExc exc, None)
    | None => None (* this is a compile-time error *)
    end
(** These are concurrent primops: *)
  | PRecvNext | PRemoveMsg | PPeekMsg
  | PRecvWaitTimeout => None
(***)
  | _ => Some (RExc (undef (VLit (Atom fname))), None)
end.

(** Function info of Core Erlang. We depend on this info when we argue about
    the equivalence relations: in `CIU_Val_compat_closed_reverse` (`CIU.v`). *)
Definition eval_funinfo (params : list Val) : Redex :=
match params with
| [VClos ext id params e;v] =>
  if v =ᵥ VLit "arity"%string
  then RValSeq [VLit (Z.of_nat params)]
  else RExc (badarg (VTuple [VLit "fun_info"%string;VClos ext id params e;v]))
| [v1;v2] => RExc (badarg (VTuple [VLit "fun_info"%string;v1;v2]))
| _ => RExc (undef (VLit "fun_info"%string))
end.

(** This function returns None, for the correct parametherisation of the
    concurrent BIFs, otherwise an exception is created. *)
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
(**
  This function defines the simulated semantics of BIFs and standard functions.
*)
Definition eval (mname : string) (fname : string) (params : list Val) 
   : option (Redex * option SideEffect) :=
match convert_string_to_code (mname, fname) with
| BPlus | BMinus | BMult | BDivide | BRem | BDiv
| BSl   | BSr    | BAbs                           => Some (eval_arith mname fname params, None)
| BFwrite | BFread                                => Some (eval_io mname fname params)
| BAnd | BOr | BNot                               => Some (eval_logical mname fname params, None)
| BEq | BTypeEq | BNeq | BTypeNeq                 => Some (eval_equality mname fname params, None)
| BApp | BMinusMinus | BSplit                     => Some (eval_transform_list mname fname params, None)
| BTupleToList | BListToTuple                     => Some (eval_list_tuple mname fname params, None)
| BListToAtom | BIntegerToList                    => Some (eval_convert mname fname params)
| BLt | BGt | BLe | BGe                           => Some (eval_cmp mname fname params, None)
| BLength                                         => Some (eval_length params, None)
| BTupleSize                                      => Some (eval_tuple_size params, None)
| BHd | BTl                                       => Some (eval_hd_tl mname fname params, None)
| BElement | BSetElement                          => Some (eval_elem_tuple mname fname params, None)
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean   => Some (eval_check mname fname params, None)
| BError | BExit | BThrow                         => match (eval_error mname fname params) with
                                                      | Some exc => Some (RExc exc, None)
                                                      | None => None
                                                     end
| BFunInfo                                        => Some (eval_funinfo params, None)
(** undefined functions *)
| BNothing                                        => Some (RExc (undef (VLit (Atom fname))), None)
(* concurrent BIFs *)
| BSend | BSpawn | BSpawnLink | BSelf | BProcessFlag
| BLink | BUnLink                                 => match eval_concurrent mname fname params with
                                                     | Some exc => Some (RExc exc, None)
                                                     | None => None
                                                     end
end.

(** The correctness of `++` *)
Theorem eval_append_correct :
  forall l l',
    eval_append (meta_to_cons l) (meta_to_cons l') = RValSeq [meta_to_cons (l ++ l')].
Proof.
  induction l; simpl; intros.
  * reflexivity.
  * now rewrite IHl.
Qed.

(** `meta_to_cons` and `mk_list` are the inverse of eachother *)
Lemma meta_to_cons_mk_list : forall l, mk_list (meta_to_cons l) = Some l.
Proof.
  induction l.
  now simpl.
  simpl. now rewrite IHl.
Qed.

Lemma mk_list_meta_to_cons : forall l l', mk_list l = Some l' ->
  meta_to_cons l' = l.
Proof.
  induction l; intros; inv H.
  * now simpl.
  * break_match_hyp. 2: congruence.
    inv H1. simpl. f_equal.
    now apply IHl2.
Qed.

(** Scope of transforming a Core Erlang list to a Coq list *)
Lemma mk_list_closed :
  forall l l' Γ,
    VAL Γ ⊢ l ->
    mk_list l = Some l' -> Forall (ValScoped Γ) l'.
Proof.
  induction l; intros; inv H0. now constructor.
  break_match_hyp; try congruence.
  inv H2. constructor. now inv H.
  apply IHl2.
  now inv H.
  reflexivity.
Qed.

(** Scope of transforming a Coq list into a Core Erlang list *)
Lemma meta_to_cons_closed :
  forall l Γ,
    Forall (ValScoped Γ) l ->
    VAL Γ ⊢ meta_to_cons l.
Proof.
  induction l; intros; inv H; simpl; constructor.
  assumption.
  now apply IHl.
Qed.

(** Different commutativity theorems for addition: *)
Proposition plus_comm_basic {e1 e2 t : Val} eff: 
  eval "erlang"%string "+"%string [e1 ; e2] = Some (RValSeq [t], eff)
->
  eval "erlang"%string "+"%string [e2; e1] = Some (RValSeq [t], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inv H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inv H3).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

Proposition plus_comm_basic_Val {e1 e2 v : Val} eff: 
  eval "erlang"%string "+"%string [e1 ; e2] = Some (RValSeq [v], eff)
->
  eval "erlang"%string "+"%string [e2; e1] = Some (RValSeq [v], eff).
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity || inv H1).
  all: try(destruct l); try(destruct l0); try(reflexivity || inv H3).
  * unfold eval, eval_arith. simpl. rewrite <- Z.add_comm. reflexivity.
Qed.

(** Scoping and `is_closed_result` properties for BIFs: *)
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

Lemma primop_eval_is_exception :
  forall f vl r eff',
  primop_eval f vl = Some (r, eff') ->
  (exists e, r = RExc e).
Proof.
  intros. unfold primop_eval in *.
  repeat break_match_hyp; invSome; unfold undef in *; auto.
  all: unfold eval_primop_error in *; repeat break_match_hyp; try invSome; eexists; reflexivity.
Qed.

Lemma primop_eval_is_closed_result :
  forall f vl r eff',
  Forall (fun v => VALCLOSED v) vl ->
  primop_eval f vl = Some (r, eff') ->
  is_closed_result r.
Proof.
  intros. unfold primop_eval in *.
  repeat break_match_hyp; invSome; unfold undef in *; auto.
  all: unfold eval_primop_error in *; repeat break_match_hyp; destruct_foralls; try invSome; try constructor; auto.
  all: repeat constructor.
Qed.

Lemma is_closed_result_closed :
  forall r, is_closed_result r -> REDCLOSED r.
Proof.
  destruct r; intros; inv H; auto.
Qed.

Lemma string_to_vcons_closed :
  forall s, VALCLOSED (string_to_vcons s).
Proof.
  induction s; simpl; auto.
Qed.

Lemma eval_is_result :
  forall f m vl r eff,
  eval m f vl = Some (r, eff) ->
  is_result r.
Proof.
  intros. unfold eval in *.
  break_match_hyp; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_convert, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_concurrent in *; try rewrite Heqb in *; try invSome.
  all: repeat break_match_goal; try invSome; subst.
  all: try (constructor; eexists; reflexivity).
  1-2: repeat break_match_hyp; auto; try invSome.
  all: try (constructor; eexists; reflexivity).
  * clear Heqb m f. induction v; cbn.
    all: try (now constructor).
    break_match_goal.
    2: break_match_goal. 3: break_match_goal.
    all: try constructor.
  * clear Heqb m f. generalize dependent v. induction v0; intros; cbn; break_match_goal; try destruct v.
    all: try now constructor.
    all: auto.
  * destruct v; simpl.
    2: destruct l. 3: break_match_goal. 4: break_match_goal.
    all: try now constructor.
    clear -Heqo. destruct p. constructor.
  * clear Heqb m f. induction v; cbn.
    all: constructor.
  * clear Heqb m. break_match_hyp. 2: break_match_hyp.
    all: inv H1.
    all: try now constructor.
    destruct (mk_ascii_list v) eqn: a; inv H0.
    all: constructor.
  * clear Heqb m. break_match_hyp. 2: break_match_hyp.
    all: inv H1.
    all: try now constructor.
    break_match_hyp; inv H0.
    all: try now constructor.
    - break_match_hyp; inv H1; constructor.
  * clear Heqb f m. induction vl; simpl.
    constructor.
    repeat break_match_goal; auto; constructor.
  * clear Heqb f m. induction vl; simpl. constructor.
    repeat break_match_goal; auto; constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * repeat break_match_hyp; repeat invSome; try now constructor.
  * unfold eval_funinfo. repeat break_match_goal; repeat invSome.
    all: now constructor.
Qed.


Lemma eval_is_closed_result :
  forall f m vl r eff,
  Forall (fun v => VALCLOSED v) vl ->
  eval m f vl = Some (r, eff) ->
  REDCLOSED r.
Proof.
  intros. unfold eval in *.
  break_match_hyp; unfold eval_arith, eval_logical, eval_equality,
  eval_transform_list, eval_list_tuple, eval_convert, eval_cmp, eval_io,
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_concurrent in *; try rewrite Heqb in *; try invSome.
  all: repeat break_match_goal; try invSome; subst.
  all: try now constructor; auto.
  all: destruct_foralls; destruct_redex_scopes.
  all: try now constructor; auto.
  all: try constructor; try constructor; try (apply indexed_to_forall; repeat constructor; auto).
  all: auto.
  1-2: repeat break_match_hyp; auto; try invSome.
  all: try now do 3 constructor.
  * rewrite Forall_nth in H. specialize (H 1 ErrorVal ltac:(lia)).
    scope_solver_v1.
  * clear Heqb m f. induction v; cbn.
    all: try (do 2 constructor; apply indexed_to_forall; do 2 constructor; now auto).
    - now do 2 constructor.
    - destruct_redex_scopes. apply IHv1 in H4 as H4'. break_match_goal.
      2: break_match_goal. 3: break_match_goal.
      all: subst; scope_solver_v1.
      apply IHv2 in H5. destruct_redex_scopes.
      destruct_foralls. scope_solver_v1.
  * clear Heqb m f. generalize dependent v. induction v0; intros; cbn; break_match_goal; try destruct v.
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
  * clear Heqb m f. induction v; cbn.
    all: destruct_redex_scopes; try (do 2 constructor; apply indexed_to_forall; now repeat constructor).
    do 2 constructor; auto. induction l; constructor.
    - apply (H1 0). simpl. lia.
    - apply IHl. intros. apply (H1 (S i)). simpl. lia.
  * clear Heqb m f. generalize dependent v. induction l0; cbn; intros.
    - constructor. simpl. lia.
    - destruct v; cbn in Heqo; try congruence.
      destruct_redex_scopes. 
      repeat break_match_hyp; inversion Heqo; subst.
      constructor. apply indexed_to_forall. constructor; auto.
      apply IHl0 in Heqo0; auto.
      inversion Heqo0. now rewrite <- indexed_to_forall in H1.
  * clear Heqb m. inv H; unfold undef in H2; inv H2.
    - auto.
    - destruct l.
      ++ destruct (mk_ascii_list x) eqn: a; inv H3; auto.
         unfold badarg. repeat constructor; auto.
         apply indexed_to_forall. do 2 constructor; auto.
      ++ inv H3. auto.
  * clear Heqb m. inv H; unfold undef in H2; inv H2.
    - auto.
    - destruct l.
      ++ destruct x; try inv H3.
         1,3-9: constructor; auto.
         1-8: constructor; apply indexed_to_forall; now repeat (constructor; try assumption).
         destruct l.
         -- inv H2. do 2 constructor. apply indexed_to_forall; now repeat (constructor; try assumption).
         -- inv H2. do 2 constructor. 2: constructor.
            apply string_to_vcons_closed.
      ++ inv H3. auto.
  * clear Heqb f m. induction H; simpl; unfold undef; auto.
    repeat break_match_goal; auto.
    do 2 constructor. apply indexed_to_forall. now repeat constructor.
  * clear Heqb f m. induction H; simpl; unfold undef; auto. destruct x, l; unfold badarg; auto.
    all: inv H; do 2 constructor; apply indexed_to_forall; repeat constructor; auto.
  * epose proof (proj1 (nth_error_Some l2 (Init.Nat.pred (Pos.to_nat p))) _).
    Unshelve. 2: { intro. rewrite H in Heqo. congruence. }
    eapply nth_error_nth with (d := VNil) in Heqo. subst. now apply H2.
  * remember (Init.Nat.pred (Pos.to_nat p)) as k. clear Heqk Heqb m f p.
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

Corollary closed_primop_eval : forall f vl r eff',
  Forall (fun v => VALCLOSED v) vl ->
  (primop_eval f vl) = Some (r, eff') ->
  REDCLOSED r.
Proof.
  intros.
  apply is_closed_result_closed. eapply primop_eval_is_closed_result; eassumption.
Qed.

(** The result of `length` is always a number (if it is not an exception) *)
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

(** The length of a non-empty list is positive *)
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

Goal eval "erlang" "+" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer (-1))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "+" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "+" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "+" [VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo")])), None).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal eval "erlang" "bsl" [VLit (Integer 10); VLit (Integer 20)] = Some (RValSeq [VLit (Integer 10485760)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Integer 10); VLit (Integer 20)] = Some (RValSeq [VLit (Integer 0)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsl" [VLit (Atom "foo"); VLit (Integer 2)] 
    = Some (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsl" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsl" [VLit (Atom "foo")]
    = Some (RExc (undef (VLit (Atom "bsl"))), None).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Atom "foo")]
    = Some (RExc (undef (VLit (Atom "bsr"))), None).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal eval "erlang" "not" [ttrue] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "not" [ffalse] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "not" [VLit (Integer 5)] = Some (RExc (badarg (VTuple [VLit (Atom "not"); VLit (Integer 5)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "not" [VLit (Integer 5); VEmptyTuple] = Some (RExc (undef (VLit (Atom "not"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "and" [ttrue; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ttrue; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ffalse; ttrue] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ffalse; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ttrue; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "and"); ttrue; VTuple []])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue]) = Some (RExc (undef (VLit (Atom "and"))), None). Proof. reflexivity. Qed.

Goal eval "erlang" "or" [ttrue; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ttrue; ffalse] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ffalse; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ffalse; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ttrue; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "or"); ttrue; VTuple []])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ttrue] = Some (RExc (undef (VLit (Atom "or"))), None).
Proof. reflexivity. Qed.

Goal eval "io" "fwrite" [ttrue] = Some (RValSeq [ok], (Some (Output, [ttrue]))).
Proof. reflexivity. Qed.
Goal eval "io" "fwrite" [VMap [(ttrue, ttrue)]] = Some (RValSeq [ok], Some (Output, [VMap [(ttrue, ttrue)]])).
Proof. reflexivity. Qed.
Goal eval "io" "fwrite" [] = Some (RExc (undef (VLit (Atom "fwrite"))), None).
Proof. reflexivity. Qed.

Goal eval "io" "fread" [VLit (Atom "foo.txt"); ttrue] = Some 
   (RValSeq [VTuple [ok; ttrue]], Some (Input, [VLit (Atom "foo.txt"); ttrue])).
Proof. reflexivity. Qed.
Goal eval "io" "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]] = Some 
   (RValSeq [VTuple [ok; VMap [(ttrue, ttrue)]]], Some (Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])).
Proof. reflexivity. Qed.
Goal eval "io" "fread" [] = Some (RExc (undef (VLit (Atom "fread"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "==" [ttrue; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [ttrue; ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [VClos [] 1 0 EEmptyMap; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "/=" [ttrue; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [ttrue; ffalse] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed. 
Goal eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [ttrue] = Some (RExc (undef (VLit (Atom "/="))), None).
Proof. reflexivity. Qed.

Definition l1 : Val := VCons ttrue VNil.
Definition l2 : Val := VCons ttrue ttrue.
Definition l3 : Val := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Val := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Val := VCons ttrue (VCons ttrue ttrue).

Goal eval "erlang" "++" [ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "++"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l1; l1] = Some (RValSeq [VCons ttrue (VCons ttrue VNil)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l1; l2] = Some
  (RValSeq [VCons ttrue (VCons ttrue ttrue)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l1; l3] = Some
  (RValSeq [VCons ttrue (VCons (VCons ttrue ttrue) ttrue)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l3; l3] = Some
  (RExc (badarg (VTuple [VLit (Atom "++"); VCons (VCons ttrue ttrue) ttrue; VCons (VCons ttrue ttrue) ttrue])), None).
Proof.  unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal eval "erlang" "++" [l1; ErrorVal] = Some (RValSeq [VCons ttrue ErrorVal], None).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.

Goal eval "lists" "split" [VLit (Integer 0); VNil] = Some (RValSeq [VTuple [VNil; VNil]], None).
Proof. reflexivity. Qed.
Goal eval "lists" "split" [VLit (Integer 0); VCons ttrue (VCons ttrue VNil)] = Some (RValSeq [VTuple [VNil; VCons ttrue (VCons ttrue VNil)]], None).
Proof. cbn. reflexivity. Qed.
Goal exists x, (eval "lists" "split" [VLit (Integer 4); VCons ttrue (VCons ttrue VNil)]) = Some (RExc (badarg x), None).
Proof. eexists. reflexivity. Qed.
Goal eval "lists" "split" [VLit (Integer 4); VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue VNil)))))] = Some (RValSeq [VTuple [VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue VNil))); VCons ttrue (VCons ttrue VNil)]], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "--" [ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "--"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l1; l1] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l1; l2] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons ttrue ttrue])), None).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal eval "erlang" "--" [l1; l3] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons (VCons ttrue ttrue) ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l3; l3] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue;
                        VCons (VCons ttrue ttrue) ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l3; l1] =
  Some (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue; VCons ttrue VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l4; l4] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [VCons (VLit (Integer 0)) (VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) (VCons VNil VNil))));
  VCons VNil (VCons (VLit (Integer 0)) VNil)
]
=
  Some (RValSeq [(VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) VNil)))], None).
Proof. unfold eval, eval_transform_list, eval_subtract. simpl. reflexivity. Qed.

Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue (VCons ttrue ttrue)) 
                                 (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] =
  Some (RValSeq [VCons ttrue (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue ttrue) (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [ttrue] = Some
  (RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "list_to_tuple" [l1] = Some (RValSeq [VTuple [VLit (Atom "true")]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l2] =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l3] =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons (VCons ttrue ttrue) ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l4] =
  Some (RValSeq [VTuple [VLit (Atom "true"); VLit (Atom "true"); VLit (Atom "true")]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l5] =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); l5])), None).
Proof. cbn. reflexivity. Qed.

Definition hello_list : Val :=
  VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil))))).
Definition not_a_char_list : Val := VCons (VLit (Atom "hello")) (VNil).
Definition improper_l1 : Val := VCons (VCons (VLit 104%Z) (VLit 101%Z)) (VLit 108%Z).
Definition improper_l2 : Val := VCons (VLit 104%Z) (VCons (VLit 101%Z) (VLit 108%Z)).

Goal (eval "erlang" "list_to_atom" [VNil]) = Some (RValSeq [VLit (Atom "")], Some (AtomCreation, [VLit (Atom "")])).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [hello_list]) = Some (RValSeq [VLit (Atom "hello")], Some (AtomCreation, [VLit (Atom "hello")])).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [not_a_char_list]) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); not_a_char_list])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [improper_l1]) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); improper_l1])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [improper_l2]) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); improper_l2])), None).
Proof. reflexivity. Qed.

Goal (eval "erlang" "list_to_atom" [VNil]) = Some (RValSeq [VLit (Atom "")], Some (AtomCreation, [VLit (Atom "")])).
Proof. reflexivity. Qed.
Goal (eval "erlang" "integer_to_list" [VLit (Integer 10)]) = Some
  (RValSeq [VCons (VLit 49%Z) (VCons (VLit 48%Z) VNil)], None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "integer_to_list" [VLit (Atom "apple")]) = Some
  (RExc (badarg (VTuple [VLit "integer_to_list"%string; VLit "apple"%string])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "integer_to_list" []) = Some
  (RExc (undef (VLit "integer_to_list"%string)), None).
Proof. reflexivity. Qed.

Goal (eval "erlang" "<" [ttrue; ttrue]) = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [ttrue; ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "=<" [ttrue; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [ttrue; ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.

Goal eval "erlang" ">" [ttrue; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [ffalse; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [VEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.

Goal eval "erlang" ">=" [ttrue; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [ffalse; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [VEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "length" [l1] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "length" [l2] = Some (RExc (badarg (VTuple [VLit (Atom "length");l2])), None).
Proof. cbn. reflexivity. Qed.
Goal eval "erlang" "length" [l3] = Some (RExc (badarg (VTuple [VLit (Atom "length");l3])), None).
Proof. cbn. reflexivity. Qed.
Goal eval "erlang" "length" [l4] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "length" [l5] = Some (RExc (badarg (VTuple [VLit (Atom "length");l5])), None).
Proof. cbn. reflexivity. Qed.
Goal eval "erlang" "length" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "length");ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "length" [l5;l3] = Some (RExc (undef (VLit (Atom "length"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "tuple_size" [l3] = Some (RExc (badarg (VTuple [VLit (Atom "tuple_size");l3])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_size" [VTuple []] = Some (RValSeq [VLit (Integer 0)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]; ErrorVal] = Some (RExc (undef (VLit (Atom "tuple_size"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "hd" [l1] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [VNil] = Some (RExc (badarg (VTuple [VLit (Atom "hd");VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l2] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l3] = Some (RValSeq [(VCons ttrue ttrue)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l4] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l5] = Some (RValSeq [ttrue], None).
Proof. unfold l5. reflexivity. Qed.
Goal eval "erlang" "hd" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "hd");ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l5;l3] = Some (RExc (undef (VLit (Atom "hd"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "tl" [l1] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [VNil] = Some (RExc (badarg (VTuple [VLit (Atom "tl");VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l2] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l3] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l4] = Some (RValSeq [(VCons ttrue (VCons ttrue VNil))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l5] = Some (RValSeq [VCons ttrue ttrue], None).
Proof. unfold l5. reflexivity. Qed.
Goal eval "erlang" "tl" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "tl");ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l5;l3] = Some (RExc (undef (VLit (Atom "tl"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "element" [VLit (Integer 2); VTuple [ttrue]] = Some (RExc (badarg (VTuple [VLit (Atom "element"); VLit (Integer 2); VTuple [ttrue]])), None).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal eval "erlang" "element" [VLit (Integer 1); VTuple [ttrue]] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "element" [ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "element"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "element" [ttrue] = Some (RExc (undef (VLit (Atom "element"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "setelement" [VLit (Integer 2); VTuple [ttrue]; ffalse] = Some (RExc (badarg (VTuple [VLit (Atom "setelement"); VLit (Integer 2); VTuple [ttrue]; ffalse])), None).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal eval "erlang" "setelement" [VLit (Integer 1); VTuple [ttrue]; ffalse] = Some (RValSeq [VTuple [ffalse]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "setelement" [ttrue; ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "setelement"); ttrue; ttrue; ttrue])), None).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal eval "erlang" "setelement" [ttrue] = Some (RExc (undef (VLit (Atom "setelement"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_number" [VLit (Integer 2)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_number"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [VLit (Integer 2)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_integer"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Integer 2)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Atom "foo")] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_atom"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [VLit (Integer 2)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_boolean"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "error" [ffalse; ffalse] = Some (RExc (Error, ffalse, ffalse), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [ffalse] = Some (RExc (Error, ffalse, VNil), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [] = Some (RExc (undef ErrorVal), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "fun_info" [ffalse; ffalse] = Some (RExc (badarg (VTuple [VLit "fun_info"%string; ffalse; ffalse])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "fun_info" [ffalse] = Some (RExc (undef (VLit "fun_info"%string)), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "fun_info" [VClos [] 0 2 (˝VNil); VLit "arity"%string] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.

End Tests.
