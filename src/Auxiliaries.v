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

From CoreErlang Require Export SideEffects
                               ScopingLemmas
                               Equalities
                               Maps.
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

(* Erlang module:
   is_binary, is_bitstring
   byte_size, bit_size
   binary_to_list
   bitstring_to_list
   
   *)
Inductive BIFCode :=
(** arithmetics *)
| BPlus | BMinus | BMult | BDivide | BRem | BDiv
| BSl | BSr | BAbs | BBXor | BBNot | BBOr | BBAnd
(** io *)
| BFwrite | BFread 
(** boolean ops *)
| BAnd | BOr | BNot | BXor
(** equality *)
| BEq | BTypeEq | BNeq | BTypeNeq
(** data ops (lists, tuples, maps) *)
| BApp | BMinusMinus | BSplit
| BMember | BKeyfind | BKeymember | BReverse
(** conversions *)
| BTupleToList | BListToTuple
| BListToAtom | BIntegerToList
| BListToInteger | BBinaryToInteger | BAtomToList | BBinaryToAtom
| BListToBinary | BIolistToBinary | BIolistSize

(** comparison *)
| BLt | BLe | BGt | BGe

(** further data ops *)
| BLength | BTupleSize
| BTl | BHd
| BElement | BSetElement

(** type checks *)
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean | BIsBinary | BIsBitstring
| BIsList | BIsTuple | BIsFunction | BIsMap | BIsPid | BIsPort
(** exceptions *)
| BError | BExit | BThrow
(** !, spawn, process_flag, self, link, unlink, exit/2:
   these BIF and primops are handled on the process-local level, they behave
   here as undefined  *)
| BSend | BSpawn | BSpawnLink | BProcessFlag | BSelf | BLink | BUnLink
| BNothing
| BFunInfo
(* map primitives *)
| BGet | BPut
(* binary/bitstring operations *)
| BByteSize | BBitSize | BBinaryToList | BBitstringToList
(* further data ops *)
| BDeleteElement | BInsertElement | BMakeTuple | BSize
| BMapSize | BFromKeys | BMax | BMin | BSplitBinary
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

| ("erlang"%string, "bxor"%string) => BBXor
| ("erlang"%string, "bnot"%string) => BBNot
| ("erlang"%string, "band"%string) => BBAnd
| ("erlang"%string, "bor"%string) => BBOr

| ("io"%string, "fwrite"%string) => BFwrite
| ("io"%string, "fread"%string) => BFread

| ("erlang"%string, "and"%string) => BAnd
| ("erlang"%string, "or"%string) => BOr
| ("erlang"%string, "not"%string) => BNot
| ("erlang"%string, "xor"%string) => BXor
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
| ("erlang"%string, "is_binary"%string) => BIsBinary
| ("erlang"%string, "is_bitstring"%string) => BIsBitstring
| ("erlang"%string, "is_tuple"%string) => BIsTuple
| ("erlang"%string, "is_list"%string) => BIsList

(** binaries, bitstrings *)
| ("erlang"%string, "byte_size"%string) => BByteSize
| ("erlang"%string, "bit_size"%string) => BBitSize
| ("erlang"%string, "binary_to_list"%string) => BBinaryToList
| ("erlang"%string, "bitstring_to_list"%string) => BBitstringToList
| ("erlang"%string, "split_binary"%string) => BSplitBinary
| ("erlang"%string, "iolist_to_binary"%string) => BIolistToBinary
| ("erlang"%string, "iolist_size"%string) => BIolistSize
| ("erlang"%string, "list_to_binary"%string) => BListToBinary

(** further type checks *)
| ("erlang"%string, "is_function"%string) => BIsFunction
| ("erlang"%string, "is_map"%string) => BIsMap
| ("erlang"%string, "is_pid"%string) => BIsPid
| ("erlang"%string, "is_port"%string) => BIsPort

(** conversions *)
| ("erlang"%string, "list_to_integer"%string) => BListToInteger
| ("erlang"%string, "binary_to_integer"%string) => BBinaryToInteger
| ("erlang"%string, "atom_to_list"%string) => BAtomToList
| ("erlang"%string, "binary_to_atom"%string) => BBinaryToAtom

(** tuples, maps, misc *)
| ("erlang"%string, "delete_element"%string) => BDeleteElement
| ("erlang"%string, "insert_element"%string) => BInsertElement
| ("erlang"%string, "make_tuple"%string) => BMakeTuple
| ("erlang"%string, "size"%string) => BSize
| ("erlang"%string, "map_size"%string) => BMapSize
| ("erlang"%string, "max"%string) => BMax
| ("erlang"%string, "min"%string) => BMin

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
| ("lists"%string, "member"%string) => BMember
| ("lists"%string, "keyfind"%string) => BKeyfind
| ("lists"%string, "keymember"%string) => BKeymember
| ("lists"%string, "reverse"%string) => BReverse
(** maps *)
| ("maps"%string, "get"%string) => BGet
| ("maps"%string, "put"%string) => BPut
| ("maps"%string, "from_keys"%string) => BFromKeys
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
(** bnot *)
| BBNot, [VLit (Integer a)]                   => RValSeq [VLit (Integer (Z.lnot a))]
| BBNot, [a]                                  => RExc (badarith (VTuple [VLit (Atom fname); a]))
(** band *)
| BBAnd, [VLit (Integer a); VLit (Integer b)]  => RValSeq [VLit (Integer (Z.land a b))]
| BBAnd, [a; b]                                => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** bor *)
| BBOr, [VLit (Integer a); VLit (Integer b)]  => RValSeq [VLit (Integer (Z.lor a b))]
| BBOr, [a; b]                                => RExc (badarith (VTuple [VLit (Atom fname); a; b]))
(** bxor *)
| BBXor, [VLit (Integer a); VLit (Integer b)]  => RValSeq [VLit (Integer (Z.lxor a b))]
| BBXor, [a; b]                                => RExc (badarith (VTuple [VLit (Atom fname); a; b]))

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
(** logical xor *)
| BXor, [a; b] =>
   if Val_eqb a ttrue
   then
    if Val_eqb b ttrue
    then RValSeq [ffalse]
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

(** Value of a digit in bases up to 36 *)
Definition digit_value (c : ascii) : option nat :=
  let n := nat_of_ascii c in
  if (48 <=? n) && (n <=? 57) then Some (n - 48)
  else if (97 <=? n) && (n <=? 122) then Some (n - 97 + 10)
  else if (65 <=? n) && (n <=? 90) then Some (n - 65 + 10)
  else None.

Fixpoint parse_digits (base : nat) (l : list ascii) (acc : Z) : option Z :=
match l with
| [] => Some acc
| c :: cs => match digit_value c with
             | Some d => if d <? base
                         then parse_digits base cs (acc * Z.of_nat base + Z.of_nat d)
                         else None
             | None => None
             end
end.

(** Parsing of integers with an optional sign (as list_to_integer does it) *)
Definition parse_integer (base : nat) (l : list ascii) : option Z :=
  if negb ((2 <=? base) && (base <=? 36)) then None else
  match l with
  | [] => None
  | c :: cs => if Ascii.eqb c "-"%char
               then match cs with
                    | [] => None
                    | _  => option_map Z.opp (parse_digits base cs 0)
                    end
               else if Ascii.eqb c "+"%char
               then match cs with
                    | [] => None
                    | _  => parse_digits base cs 0
                    end
               else parse_digits base l 0
  end.

Definition digit_char (d : Z) : ascii :=
  if (d <? 10)%Z then ascii_of_nat (48 + Z.to_nat d) else ascii_of_nat (55 + Z.to_nat d).

(** The digits of a natural number in a given base (most significant first).
    The fuel is the number of digits, which is at most the number of bits. *)
Fixpoint integer_digits (fuel : nat) (base : Z) (n : Z) (acc : list ascii) : list ascii :=
match fuel with
| O => acc
| S fuel' => let acc' := digit_char (n mod base) :: acc in
             if (n <? base)%Z then acc' else integer_digits fuel' base (n / base) acc'
end.

Definition integer_to_digits (base : Z) (z : Z) : list ascii :=
  let digits := integer_digits (S (Z.to_nat (Z.log2 (Z.abs z)))) base (Z.abs z) [] in
  if (z <? 0)%Z then "-"%char :: digits else digits.

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
| BIntegerToList, [VLit (Integer z); VLit (Integer base)] =>
  if negb ((2 <=? base)%Z && (base <=? 36)%Z)
  then (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); VLit (Integer z); VLit (Integer base)])), None)
  else (RValSeq [string_to_vcons (string_of_list_ascii (integer_to_digits base z))], None)
| BIntegerToList, [v1; v2] => (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); v1; v2])), None)
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
(** max and min return the first argument if the two are equal *)
| BMax, [v1; v2] => if Val_ltb v1 v2 then RValSeq [v2] else RValSeq [v1]
| BMin, [v1; v2] => if Val_ltb v2 v1 then RValSeq [v2] else RValSeq [v1]
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

(**
  Removing and inserting an element, creating a tuple, size of tuples and binaries
*)
Definition eval_tuple_bifs (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BDeleteElement, [VLit (Integer i); VTuple l] =>
    if ((1 <=? i)%Z && (i <=? Z.of_nat (length l))%Z)
    then RValSeq [VTuple (firstn (Z.to_nat i - 1) l ++ skipn (Z.to_nat i) l)]
    else RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l]))
| BDeleteElement, [v1; v2] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2]))
| BInsertElement, [VLit (Integer i); VTuple l; v] =>
    if ((1 <=? i)%Z && (i <=? Z.of_nat (length l) + 1)%Z)
    then RValSeq [VTuple (firstn (Z.to_nat i - 1) l ++ v :: skipn (Z.to_nat i - 1) l)]
    else RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer i); VTuple l; v]))
| BInsertElement, [v1; v2; v3] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2; v3]))
| BMakeTuple, [VLit (Integer n); v] =>
    if (0 <=? n)%Z
    then RValSeq [VTuple (repeat v (Z.to_nat n))]
    else RExc (badarg (VTuple [VLit (Atom fname); VLit (Integer n); v]))
| BMakeTuple, [v1; v2] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2]))
| BSize, [VTuple l] => RValSeq [VLit (Integer (Z.of_nat (length l)))]
| BSize, [VBitstring b] =>
    RValSeq [VLit (Integer (Z.of_N (N.div (bvn_n b) 8 +
                 if N.eqb (N.modulo (bvn_n b) 8%N) 0%N then 0 else 1)))]
| BSize, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
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
| BIsBinary, [VBitstring b] => if N.eqb (N.modulo (bvn_n b) 8%N) 0%N
                               then RValSeq [ttrue]
                               else RValSeq [ffalse]
| BIsBinary, [_] => RValSeq [ffalse]
| BIsBitstring, [VBitstring b] => RValSeq [ttrue]
| BIsBitstring, [_] => RValSeq [ffalse]
| BIsList, [VCons _ _] => RValSeq [ttrue]
| BIsList, [VNil] => RValSeq [ttrue]
| BIsList, [_] => RValSeq [ffalse]
| BIsTuple, [VTuple b] => RValSeq [ttrue]
| BIsTuple, [_] => RValSeq [ffalse]
| BIsMap, [VMap _] => RValSeq [ttrue]
| BIsMap, [_] => RValSeq [ffalse]
| BIsPid, [VPid _] => RValSeq [ttrue]
| BIsPid, [_] => RValSeq [ffalse]
(** there are no ports in the model *)
| BIsPort, [_] => RValSeq [ffalse]
| BIsFunction, [VClos _ _ _ _] => RValSeq [ttrue]
| BIsFunction, [_] => RValSeq [ffalse]
| BIsFunction, [VClos ext id params e; VLit (Integer n)] =>
    if (n <? 0)%Z
    then RExc (badarg (VTuple [VLit (Atom fname); VClos ext id params e; VLit (Integer n)]))
    else if Z.eqb (Z.of_nat params) n then RValSeq [ttrue] else RValSeq [ffalse]
| BIsFunction, [v; VLit (Integer n)] =>
    if (n <? 0)%Z
    then RExc (badarg (VTuple [VLit (Atom fname); v; VLit (Integer n)]))
    else RValSeq [ffalse]
| BIsFunction, [v1; v2] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2]))
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
  (* Erlang raises error:function_clause, the arguments belong to the stacktrace *)
  | [VTuple (VLit (Atom a) :: args)] =>
    if String.eqb a "function_clause"%string
    then Some (Error, VLit (Atom a), VTuple args)
    else Some (Error, VTuple (VLit (Atom a) :: args), VNil)
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

Definition eval_map_bifs (mname fname : string)
                         (params : list Val) : Redex :=
match convert_string_to_code (mname, fname) with
| BPut => match params with
          | key :: value :: map :: [] =>
            match map with
            | VMap contents => RValSeq [VMap (map_put key value contents)]
            | _ => RExc (badmap (VTuple [VLit "put"%string;key;value;map]))
            end
          | _ => RExc (undef (VLit (Atom fname)))
          end
| BGet => match params with
          | key :: map :: [] =>
            match map with
            | VMap contents =>
              match map_get key contents with
              | Some v => RValSeq [v]
              | None   => RExc (badkey key)
              end
            | _ => RExc (badmap map)
            end
          | key :: map :: default :: [] =>
            match map with
            | VMap contents =>
              match map_get key contents with
              | Some v => RValSeq [v]
              | None   => RValSeq [default]
              end
            | _ => RExc (badmap map)
            end
          | _ => RExc (undef (VLit (Atom fname)))
          end
| BMapSize => match params with
               | [VMap contents] => RValSeq [VLit (Integer (Z.of_nat (length contents)))]
               | [map] => RExc (badmap map)
               | _ => RExc (undef (VLit (Atom fname)))
               end
| BFromKeys => match params with
               | [keys; value] =>
                 match mk_list keys with
                 | Some l => RValSeq [VMap (fold_left (fun m k => map_put k value m) l [])]
                 | None => RExc (badarg (VTuple [VLit (Atom fname); keys; value]))
                 end
               | _ => RExc (undef (VLit (Atom fname)))
               end
| _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_bin_size (mname fname : string)
                         (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BByteSize, [VBitstring b] =>
    RValSeq [VLit (Integer (Z.of_N (N.div (bvn_n b) 8 +
                 if N.eqb (N.modulo (bvn_n b) 8%N) 0%N then 0 else 1)))]
| BByteSize, [v]            => RExc (badarg (VTuple [VLit (Atom fname); v]))
| BBitSize, [VBitstring b]  => RValSeq [VLit (Integer (Z.of_N (bvn_n b)))]
| BBitSize, [v]             => RExc (badarg (VTuple [VLit (Atom fname); v]))
| _, _                      => RExc (undef (VLit (Atom fname)))
end.

Definition Z_to_bv_little (n : N) (z : Z) : bv n :=
  let k := N.div (n + 7) 8 in (* number of bytes = ceil(n/8) *)
  let last_width := (n - 8 * (k - 1))%N in  (* bits of the last chunk *)
  let high_bytes := Z_to_little_endian (Z.of_N (k - 1)) 8 z in   (* d0..d_{k-2}, LSB-first, all full bytes *)
  let high_part := little_endian_to_Z 8 (reverse high_bytes) in  (* re-assembled MSB-first, d0 highest *)
  let last_digit := (Z.shiftr z (Z.of_N (8 * (k - 1))) mod 2 ^ Z.of_N last_width)%Z in
  Z_to_bv n (high_part * 2 ^ Z.of_N last_width + last_digit).

Goal Z_to_bv_little 16 10000 = 4135%bv. vm_compute. by apply bv_eq. Qed.
Goal Z_to_bv_little 13 10000 = 519%bv. vm_compute. by apply bv_eq. Qed.
Goal Z_to_bv 13 10000 = 1808%bv. vm_compute. by apply bv_eq. Qed.

Definition get_bin_size (v : Val) (unit : nat) (default : N) : option N :=
match v with
| VLit (Integer x) => if (x <? 0)%Z then None else Some (Z.abs_N x * N.of_nat unit)%N
| VLit (Atom a)    => if string_dec a "all"%string then Some default else None
| _ => None
end.

Definition segment_to_bitstring (v size : Val) (unit : nat) (type : BinType)
  (* (sign : BinSign) - "Signedness - The signedness specification can be either signed or unsigned. Notice that signedness only matters for matching." (https://www.erlang.org/doc/system/bit_syntax.html) *)
  (endian : BinEnd) : option Redex :=
  match type with
  | IntType =>
    match size with
    | VLit (Integer vsize) =>
      if (vsize <? 0)%Z
      then Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
      else let fullsize := (Z.abs_N vsize * N.of_nat unit)%N in
        match v with
        | VLit (Integer x) =>
          match endian with
          | LittleEndian => Some (RValSeq [VBitstring (Z_to_bv_little fullsize x)])
          | BigEndian | NativeEndian 
                         => Some (RValSeq [VBitstring (Z_to_bv fullsize x)])
          end
        | _ => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
        end
    | _ => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
    end
  | BinaryType =>
    match v with
    | VBitstring bits =>
      match get_bin_size size unit (bvn_n bits) with
      | Some fullsize => if (N.modulo fullsize 8 =? 0)%N && (N.to_nat fullsize <=? N.to_nat (bvn_n bits))
                         then Some (RValSeq [VBitstring (bv_to_bvn (bv_extract (bvn_n bits - fullsize) fullsize (bvn_val bits)))])
                         else Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
      | None => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
      end
    | _ => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
    end
  | BitstringType =>
    if Nat.eqb unit 1
    then
      match v with
      | VBitstring bits =>
        match get_bin_size size unit (bvn_n bits) with
        | Some fullsize => if (N.to_nat fullsize <=? N.to_nat (bvn_n bits))
                           then Some (RValSeq [VBitstring (bv_to_bvn (bv_extract (bvn_n bits - fullsize) fullsize (bvn_val bits)))])
                           else Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
        | None => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
        end
      | _ => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]])))
      end
    else Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple [v;size]]))) (* according to tests, unit value of bitstring types cannot be other than 1 *)
  | FloatType | Utf8Type | Utf16Type | Utf32Type => None
  end.

Definition bvn_to_bytes (b : bvn) : list Z * bvn :=
  let n := bvn_n b in
  let r := N.modulo n 8 in
  let m := N.div n 8 in
  (reverse (Z_to_little_endian (Z.of_N m) 8 (Z.shiftr (bvn_unsigned b) (Z.of_N r))),
   bv_to_bvn (bv_extract 0 r (bvn_val b))).

Definition eval_bin_to_list (mname fname : string)
                            (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BBitstringToList, [VBitstring b] => 
   match bvn_to_bytes b with
   | (bytes, rems) => RValSeq [meta_to_cons (map (VLit ∘ Integer) bytes ++ if N.eqb (N.modulo (bvn_n b) 8%N) 0%N then [] else [VBitstring rems])]
   end
| BBitstringToList, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| BBinaryToList, [VBitstring b] =>
    if N.eqb (N.modulo (bvn_n b) 8%N) 0%N
    then match bvn_to_bytes b with
         | (bytes, rems) => RValSeq [meta_to_cons (map (VLit ∘ Integer) bytes)]
         end
    else RExc (badarg (VTuple [VLit (Atom fname); VBitstring b]))
| BBinaryToList, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| _, _ => RExc (undef (VLit (Atom fname)))
end.

(** Helper functions for binaries and IO lists *)
Definition bvn_empty : bvn := bv_to_bvn (Z_to_bv 0 0).

Definition bvn_app (a b : bvn) : bvn :=
  bv_to_bvn (bv_concat (bvn_n a + bvn_n b) (bvn_val a) (bvn_val b)).

Definition bvn_byte (z : Z) : bvn := bv_to_bvn (Z_to_bv 8 z).

(** Binaries are bitstrings whose size is a multiple of 8 *)
Definition bvn_aligned (b : bvn) : bool := N.eqb (N.modulo (bvn_n b) 8%N) 0%N.

(** The bytes of a binary as characters *)
Definition bvn_to_chars (b : bvn) : list ascii :=
  map (fun z => ascii_of_nat (Z.to_nat z)) (fst (bvn_to_bytes b)).

(** The contents of an IO list (or binary) as a binary; improper IO lists
    may end with a binary. *)
Fixpoint iolist_bits (v : Val) : option bvn :=
match v with
| VNil => Some bvn_empty
| VBitstring b => if bvn_aligned b then Some b else None
| VCons (VLit (Integer z)) t =>
    if ((0 <=? z)%Z && (z <=? 255)%Z)
    then option_map (bvn_app (bvn_byte z)) (iolist_bits t)
    else None
| VCons h t => match iolist_bits h, iolist_bits t with
               | Some a, Some b => Some (bvn_app a b)
               | _, _ => None
               end
| _ => None
end.

(** Conversions of lists, binaries and atoms *)
Definition eval_conversion (mname : string) (fname : string) (params : list Val)
  : Redex * option SideEffect :=
match convert_string_to_code (mname, fname), params with
| BListToInteger, [v] =>
    match mk_ascii_list v with
    | Some cs => match parse_integer 10 cs with
                 | Some z => (RValSeq [VLit (Integer z)], None)
                 | None => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
                 end
    | None => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
    end
| BListToInteger, [v; VLit (Integer base)] =>
    match mk_ascii_list v with
    | Some cs => match parse_integer (Z.to_nat base) cs with
                 | Some z => (RValSeq [VLit (Integer z)], None)
                 | None => (RExc (badarg (VTuple [VLit (Atom fname); v; VLit (Integer base)])), None)
                 end
    | None => (RExc (badarg (VTuple [VLit (Atom fname); v; VLit (Integer base)])), None)
    end
| BListToInteger, [v1; v2] => (RExc (badarg (VTuple [VLit (Atom fname); v1; v2])), None)
| BBinaryToInteger, [VBitstring b] =>
    match (if bvn_aligned b then parse_integer 10 (bvn_to_chars b) else None) with
    | Some z => (RValSeq [VLit (Integer z)], None)
    | None => (RExc (badarg (VTuple [VLit (Atom fname); VBitstring b])), None)
    end
| BBinaryToInteger, [VBitstring b; VLit (Integer base)] =>
    match (if bvn_aligned b then parse_integer (Z.to_nat base) (bvn_to_chars b) else None) with
    | Some z => (RValSeq [VLit (Integer z)], None)
    | None => (RExc (badarg (VTuple [VLit (Atom fname); VBitstring b; VLit (Integer base)])), None)
    end
| BBinaryToInteger, [v] => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
| BBinaryToInteger, [v1; v2] => (RExc (badarg (VTuple [VLit (Atom fname); v1; v2])), None)
| BAtomToList, [VLit (Atom a)] => (RValSeq [string_to_vcons a], None)
| BAtomToList, [v] => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
| BBinaryToAtom, [VBitstring b; VLit (Atom enc)] =>
    if bvn_aligned b && (String.eqb enc "utf8"%string || String.eqb enc "latin1"%string
                         || String.eqb enc "unicode"%string)
    then let a := string_of_list_ascii (bvn_to_chars b) in
         (RValSeq [VLit (Atom a)], Some (AtomCreation, [VLit (Atom a)]))
    else (RExc (badarg (VTuple [VLit (Atom fname); VBitstring b; VLit (Atom enc)])), None)
| BBinaryToAtom, [v1; v2] => (RExc (badarg (VTuple [VLit (Atom fname); v1; v2])), None)
| BListToBinary, [VBitstring b] => (RExc (badarg (VTuple [VLit (Atom fname); VBitstring b])), None)
| BListToBinary, [v] =>
    match iolist_bits v with
    | Some b => (RValSeq [VBitstring b], None)
    | None => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
    end
| BIolistToBinary, [v] =>
    match iolist_bits v with
    | Some b => (RValSeq [VBitstring b], None)
    | None => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
    end
| BIolistSize, [v] =>
    match iolist_bits v with
    | Some b => (RValSeq [VLit (Integer (Z.of_N (N.div (bvn_n b) 8)))], None)
    | None => (RExc (badarg (VTuple [VLit (Atom fname); v])), None)
    end
| _, _ => (RExc (undef (VLit (Atom fname))), None)
end.

(** Splitting a binary into two at a byte position *)
Definition eval_split_binary (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BSplitBinary, [VBitstring b; VLit (Integer p)] =>
    if bvn_aligned b && (0 <=? p)%Z && (p * 8 <=? Z.of_N (bvn_n b))%Z
    then let k := Z.to_N (p * 8) in
         RValSeq [VTuple [VBitstring (bv_to_bvn (bv_extract (bvn_n b - k) k (bvn_val b)));
                          VBitstring (bv_to_bvn (bv_extract 0 (bvn_n b - k) (bvn_val b)))]]
    else RExc (badarg (VTuple [VLit (Atom fname); VBitstring b; VLit (Integer p)]))
| BSplitBinary, [v1; v2] => RExc (badarg (VTuple [VLit (Atom fname); v1; v2]))
| _, _ => RExc (undef (VLit (Atom fname)))
end.

(** The element of a list of tuples whose N-th element is the key *)
Definition find_key (key : Val) (n : Z) (items : list Val) : option Val :=
  find (fun e => match e with
                 | VTuple t => match nth_error t (Z.to_nat n - 1) with
                               | Some k => Val_eqb key k
                               | None => false
                               end
                 | _ => false
                 end) items.

(** List functions of the lists module *)
Definition eval_lists_bifs (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
| BMember, [x; l] =>
    match mk_list l with
    | Some items => if existsb (Val_eqb x) items then RValSeq [ttrue] else RValSeq [ffalse]
    | None => RExc (badarg (VTuple [VLit (Atom fname); x; l]))
    end
| BKeyfind, [key; pos; l] =>
    match pos, mk_list l with
    | VLit (Integer n), Some items =>
        if (1 <=? n)%Z
        then match find_key key n items with
             | Some e => RValSeq [e]
             | None => RValSeq [ffalse]
             end
        else RExc (badarg (VTuple [VLit (Atom fname); key; pos; l]))
    | _, _ => RExc (badarg (VTuple [VLit (Atom fname); key; pos; l]))
    end
| BKeymember, [key; pos; l] =>
    match pos, mk_list l with
    | VLit (Integer n), Some items =>
        if (1 <=? n)%Z
        then match find_key key n items with
             | Some _ => RValSeq [ttrue]
             | None => RValSeq [ffalse]
             end
        else RExc (badarg (VTuple [VLit (Atom fname); key; pos; l]))
    | _, _ => RExc (badarg (VTuple [VLit (Atom fname); key; pos; l]))
    end
| BReverse, [l] =>
    match mk_list l with
    | Some items => RValSeq [meta_to_cons (List.rev items)]
    | None => RExc (badarg (VTuple [VLit (Atom fname); l]))
    end
| BReverse, [l; tail] =>
    match mk_list l with
    | Some items => RValSeq [fold_left (fun acc x => VCons x acc) items tail]
    | None => RExc (badarg (VTuple [VLit (Atom fname); l; tail]))
    end
| _, _ => RExc (undef (VLit (Atom fname)))
end.

(* Note: Always can be extended, this function simulates inter-module calls *)
(**
  This function defines the simulated semantics of BIFs and standard functions.
*)
Definition eval (mname : string) (fname : string) (params : list Val) 
   : option (Redex * option SideEffect) :=
match convert_string_to_code (mname, fname) with
| BPlus | BMinus | BMult | BDivide | BRem  | BDiv
| BSl   | BSr    | BAbs  | BBNot   | BBAnd | BBOr
| BBXor                                           => Some (eval_arith mname fname params, None)
| BFwrite | BFread                                => Some (eval_io mname fname params)
| BAnd | BOr | BNot | BXor                        => Some (eval_logical mname fname params, None)
| BEq | BTypeEq | BNeq | BTypeNeq                 => Some (eval_equality mname fname params, None)
| BApp | BMinusMinus | BSplit                     => Some (eval_transform_list mname fname params, None)
| BTupleToList | BListToTuple                     => Some (eval_list_tuple mname fname params, None)
| BListToAtom | BIntegerToList                    => Some (eval_convert mname fname params)
| BListToInteger | BBinaryToInteger | BAtomToList
| BBinaryToAtom | BListToBinary | BIolistToBinary
| BIolistSize                                     => Some (eval_conversion mname fname params)
| BSplitBinary                                    => Some (eval_split_binary mname fname params, None)
| BDeleteElement | BInsertElement | BMakeTuple
| BSize                                           => Some (eval_tuple_bifs mname fname params, None)
| BMember | BKeyfind | BKeymember | BReverse      => Some (eval_lists_bifs mname fname params, None)
| BLt | BGt | BLe | BGe | BMax | BMin            => Some (eval_cmp mname fname params, None)
| BLength                                         => Some (eval_length params, None)
| BTupleSize                                      => Some (eval_tuple_size params, None)
| BHd | BTl                                       => Some (eval_hd_tl mname fname params, None)
| BElement | BSetElement                          => Some (eval_elem_tuple mname fname params, None)
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean
| BIsBinary | BIsBitstring | BIsList | BIsTuple
| BIsFunction | BIsMap | BIsPid | BIsPort         => Some (eval_check mname fname params, None)
| BError | BExit | BThrow                         => match (eval_error mname fname params) with
                                                      | Some exc => Some (RExc exc, None)
                                                      | None => None
                                                     end
| BFunInfo                                        => Some (eval_funinfo params, None)
| BGet | BPut | BMapSize | BFromKeys => Some (eval_map_bifs mname fname params, None)
| BByteSize | BBitSize             => Some (eval_bin_size mname fname params, None)
| BBinaryToList | BBitstringToList => Some (eval_bin_to_list  mname fname params, None)

(** undefined functions *)
| BNothing                                        => Some (RExc (undef (VLit (Atom fname))), None)

(* concurrent BIFs *)
| BSend | BSpawn | BSpawnLink | BSelf | BProcessFlag
| BLink | BUnLink                                 => match eval_concurrent mname fname params with
                                                     | Some exc => Some (RExc exc, None)
                                                     | None => None
                                                     end
end.


Lemma segment_to_bitstring_final v vsize unit type endian (r : Redex):
  segment_to_bitstring v vsize unit type endian = Some r ->
  (exists exc : Exception, r = exc) \/ (exists vs : bvn, r = RValSeq [VBitstring vs]).
Proof.
  intros. unfold segment_to_bitstring in H; repeat case_match; invSome.
  all: try by left; eexists.
  all: try by right; eexists.
Qed.

Corollary segment_to_bitstring_is_result v vsize unit type endian (r : Redex):
  segment_to_bitstring v vsize unit type endian = Some r ->
  is_result r.
Proof.
  intros. apply segment_to_bitstring_final in H.
  destruct H as [[exc H]|[vs H]]; subst; try constructor.
  by destruct exc as [[? ?] ?].
Qed.

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

(** Scope of transforming a Core Erlang list to a Rocq list *)
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

(** Scope of transforming a Rocq list into a Core Erlang list *)
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
  all: inv H2.
  intros. apply (H1 (S i)). slia.
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
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_concurrent, eval_map_bifs, eval_bin_size, eval_bin_to_list in *; try rewrite Heqb in *; try invSome.
  all: repeat break_match_goal; try invSome; subst.
  all: try (constructor; eexists; reflexivity).
  1-2: repeat break_match_hyp; auto; try invSome.
  all: try (constructor; eexists; reflexivity).
  4-7: unfold eval_lists_bifs; repeat break_match_goal; try now constructor.
  7-13: unfold eval_conversion in H1; repeat break_match_hyp; inv H1; try now constructor.
  20-24: unfold eval_tuple_bifs, eval_split_binary; repeat break_match_goal; try now constructor.
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
  * clear Heqb m. repeat break_match_hyp; inv H1; try now constructor.
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

Lemma map_insert_is_closed (v v0 : Val)
(l2 : list (Val * Val)) :
  VALCLOSED v -> VALCLOSED v0 ->
  (forall i : nat,
  i < Datatypes.length l2 -> VALCLOSED (nth i (map fst l2) VNil)) ->
  (forall i : nat,
  i < Datatypes.length l2 -> VALCLOSED (nth i (map snd l2) VNil))
  ->
VALCLOSED (VMap (map_put v v0 l2)).
Proof.
  intros. induction l2; simpl.
  * constructor; simpl; destruct i; try lia; now intros.
  * destruct a as [k' v']. simpl in *.
    break_match_goal. 2: break_match_goal.
    - constructor; intros.
      all: destruct i; [|destruct i]; simpl; try assumption.
      1: apply (H1 0); lia.
      1: apply (H1 (S i)); simpl in H3; lia.
      1: apply (H2 0); lia.
      1: apply (H2 (S i)); simpl in H3; lia.
    - constructor; intros.
      all: destruct i; simpl; try assumption.
      1: apply (H1 (S i)); simpl in H3; lia.
      1: apply (H2 (S i)); simpl in H3; lia.
    - unshelve (epose proof (IHl2 _ _)).
      1: intros. apply (H1 (S i)); simpl in H3; lia.
      1: intros. apply (H2 (S i)); simpl in H3; lia.
      inv H3.
      constructor; intros.
      all: destruct i; simpl; try assumption.
      1: apply (H1 0); lia.
      2: apply (H2 0); lia.
      1: apply H5; simpl in H3; lia.
      1: apply H7; simpl in H3; lia.
Qed.


(** Scoping properties of the results of the BIFs on tuples, lists, binaries *)
Lemma badarg_closed :
  forall (f : string) args,
    Forall (fun v => VALCLOSED v) args ->
    REDCLOSED (badarg (VTuple (VLit f :: args))).
Proof.
  intros. unfold badarg. do 2 constructor.
  apply indexed_to_forall. constructor; auto.
Qed.

Lemma VTuple_closed :
  forall l, Forall (fun v => VALCLOSED v) l -> VALCLOSED (VTuple l).
Proof.
  intros. constructor. apply indexed_to_forall. assumption.
Qed.

Lemma VTuple_closed_inv :
  forall l, VALCLOSED (VTuple l) -> Forall (fun v => VALCLOSED v) l.
Proof.
  intros. inv H. rewrite <- indexed_to_forall in H2. exact H2.
Qed.

Lemma Forall_firstn_skipn :
  forall (l : list Val) n m,
    Forall (fun v => VALCLOSED v) l ->
    Forall (fun v => VALCLOSED v) (firstn n l ++ skipn m l).
Proof.
  intros. apply Forall_app; split.
  * apply Forall_take. assumption.
  * apply Forall_drop. assumption.
Qed.

Lemma find_key_closed :
  forall key n items e,
    Forall (fun v => VALCLOSED v) items ->
    find_key key n items = Some e -> VALCLOSED e.
Proof.
  unfold find_key. intros. apply find_some in H0 as [Hin _].
  rewrite Forall_forall in H. now apply H.
Qed.

Lemma fold_cons_closed :
  forall items tail,
    Forall (fun v => VALCLOSED v) items -> VALCLOSED tail ->
    VALCLOSED (fold_left (fun acc x => VCons x acc) items tail).
Proof.
  induction items; simpl; intros; auto.
  inv H. apply IHitems; auto.
Qed.

Lemma fold_map_put_closed :
  forall keys v m0,
    Forall (fun v => VALCLOSED v) keys -> VALCLOSED v -> VALCLOSED (VMap m0) ->
    VALCLOSED (VMap (fold_left (fun m k => map_put k v m) keys m0)).
Proof.
  induction keys; simpl; intros; auto.
  inv H. apply IHkeys; auto.
  inv H1. apply map_insert_is_closed; auto.
Qed.

Lemma eval_lists_bifs_closed :
  forall m f vl,
    Forall (fun v => VALCLOSED v) vl ->
    REDCLOSED (eval_lists_bifs m f vl).
Proof.
  intros. unfold eval_lists_bifs.
  destruct (convert_string_to_code (m, f)); try (unfold undef; repeat constructor; fail).
  all: repeat break_match_goal.
  all: try (now repeat constructor).
  all: try (apply badarg_closed; assumption; fail).
  all: try (unfold undef; repeat constructor; fail).
  all: try (match goal with
            | Hf : find_key _ _ ?items = Some ?e, Hm : mk_list ?l = Some ?items |- REDCLOSED (RValSeq [?e]) =>
              assert (HL : VALCLOSED l) by (rewrite Forall_forall in H; apply H; simpl; tauto);
              pose proof (mk_list_closed _ _ _ HL Hm) as Hitems;
              do 2 constructor; [eapply find_key_closed; eassumption | constructor]
            | Hm : mk_list ?l = Some ?items |- REDCLOSED (RValSeq [meta_to_cons (List.rev ?items)]) =>
              assert (HL : VALCLOSED l) by (rewrite Forall_forall in H; apply H; simpl; tauto);
              pose proof (mk_list_closed _ _ _ HL Hm) as Hitems;
              do 2 constructor; [apply meta_to_cons_closed; apply Forall_rev; assumption | constructor]
            | Hm : mk_list ?l = Some ?items |- REDCLOSED (RValSeq [fold_left _ ?items ?tail]) =>
              assert (HL : VALCLOSED l) by (rewrite Forall_forall in H; apply H; simpl; tauto);
              assert (HT : VALCLOSED tail) by (rewrite Forall_forall in H; apply H; simpl; tauto);
              pose proof (mk_list_closed _ _ _ HL Hm) as Hitems;
              do 2 constructor; [apply fold_cons_closed; assumption | constructor]
            end).
  all: idtac.
Qed.

Lemma eval_conversion_closed :
  forall m f vl r eff,
    Forall (fun v => VALCLOSED v) vl ->
    eval_conversion m f vl = (r, eff) ->
    REDCLOSED r.
Proof.
  intros. unfold eval_conversion in H0.
  destruct (convert_string_to_code (m, f)); try (inv H0; unfold undef; repeat constructor; fail).
  all: repeat break_match_hyp; inv H0.
  all: try (now repeat constructor).
  all: try (apply badarg_closed; (assumption || (repeat constructor; assumption)); fail).
  do 2 constructor. 2: constructor. apply string_to_vcons_closed.
Qed.

Lemma eval_tuple_bifs_closed :
  forall m f vl,
    Forall (fun v => VALCLOSED v) vl ->
    REDCLOSED (eval_tuple_bifs m f vl).
Proof.
  intros. unfold eval_tuple_bifs.
  destruct (convert_string_to_code (m, f)); try (unfold undef; repeat constructor; fail).
  all: repeat break_match_goal.
  all: try (now repeat constructor).
  all: try (apply badarg_closed; (assumption || (repeat constructor; assumption)); fail).
  all: try (unfold undef; repeat constructor; fail).
  * inv H. inv H3. apply VTuple_closed_inv in H1. do 2 constructor. 2: constructor.
    apply VTuple_closed. apply Forall_firstn_skipn. assumption.
  * inv H. inv H3. inv H4. apply VTuple_closed_inv in H1.
    do 2 constructor. 2: constructor. apply VTuple_closed.
    apply Forall_app; split.
    - apply Forall_take. assumption.
    - constructor; [assumption|]. apply Forall_drop. assumption.
  * inv H. inv H3. do 2 constructor. 2: constructor. apply VTuple_closed.
    apply Forall_forall. intros. apply repeat_spec in H. subst. assumption.
Qed.

Lemma eval_split_binary_closed :
  forall m f vl,
    Forall (fun v => VALCLOSED v) vl ->
    REDCLOSED (eval_split_binary m f vl).
Proof.
  intros. unfold eval_split_binary.
  destruct (convert_string_to_code (m, f)); try (unfold undef; repeat constructor; fail).
  all: repeat break_match_goal.
  all: try (now repeat constructor).
  all: try (apply badarg_closed; (assumption || (repeat constructor; assumption)); fail).
  all: try (unfold undef; repeat constructor; fail).
  all: do 2 constructor; [apply VTuple_closed; repeat constructor | constructor].
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
  eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_concurrent, eval_map_bifs, eval_bin_size, eval_bin_to_list in *; try rewrite Heqb in *; try invSome.
  all: repeat break_match_goal; try invSome; subst.
  all: try now constructor; auto.
  all: destruct_foralls; destruct_redex_scopes.
  all: try now constructor; auto.
  all: try constructor; try constructor; try (apply indexed_to_forall; repeat constructor; auto).
  all: auto.
  1-2: repeat break_match_hyp; auto; try invSome.
  all: try now do 3 constructor.
  5-8: apply eval_lists_bifs_closed; assumption.
  9-15: eapply eval_conversion_closed; eassumption.
  30-33: apply eval_tuple_bifs_closed; assumption.
  31: apply eval_split_binary_closed; assumption.
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
  * clear Heqb m. inv H.
    - repeat constructor.
    - destruct l.
      ++ destruct (mk_ascii_list x) eqn:a; inv H2; auto.
         unfold badarg. repeat constructor; auto.
         apply indexed_to_forall. do 2 constructor; auto.
      ++ inv H2. repeat constructor.
  * clear Heqb m. repeat break_match_hyp; inv H2.
    all: try (now repeat constructor).
    all: try (apply badarg_closed; (assumption || (repeat constructor; assumption)); fail).
    all: do 2 constructor; [apply string_to_vcons_closed | constructor].
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
  * clear - Heqo H4. induction l1; simpl in Heqo.
    invSome.
    destruct a as [k' v'].
    break_match_hyp.
    - apply IHl1 in Heqo. assumption.
      intros. apply (H4 (S i)). slia.
    - break_match_hyp; invSome.
      apply (H4 0). slia.
  * clear - Heqo H5. induction l2; simpl in Heqo.
    invSome.
    destruct a as [k' v'].
    break_match_hyp.
    - apply IHl2 in Heqo. assumption.
      intros. apply (H5 (S i)). slia.
    - break_match_hyp; invSome.
      apply (H5 0). slia.
  * now apply map_insert_is_closed.
  * apply meta_to_cons_closed.
    apply Forall_forall. intros.
    apply in_map_iff in H as [? [? ?]]. subst.
    constructor.
  * apply meta_to_cons_closed.
    apply Forall_forall. intros.
    apply in_app_iff in H as [? | ?].
    apply in_map_iff in H as [? [? ?]]. subst. constructor.
    inv H.
  * apply meta_to_cons_closed.
    apply Forall_forall. intros.
    apply in_app_iff in H as [? | ?].
    apply in_map_iff in H as [? [? ?]]. subst. constructor.
    inv H. constructor. inv H0.
  * apply fold_map_put_closed; [eapply mk_list_closed; [exact H2 | exact Heqo] | assumption |].
    constructor; intros; simpl in *; lia.
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

Goal eval "erlang" "band" [VLit (Integer 12); VLit (Integer 10)] = Some (RValSeq [VLit (Integer 8)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Integer (-1)); VLit (Integer 5)] = Some (RValSeq [VLit (Integer 5)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "band"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "band"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Integer 1)]
    = Some (RExc (undef (VLit (Atom "band"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "bor" [VLit (Integer 12); VLit (Integer 10)] = Some (RValSeq [VLit (Integer 14)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Integer (-8)); VLit (Integer 3)] = Some (RValSeq [VLit (Integer (-5))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "bor"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bor"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Integer 1)]
    = Some (RExc (undef (VLit (Atom "bor"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "bxor" [VLit (Integer 12); VLit (Integer 10)] = Some (RValSeq [VLit (Integer 6)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Integer (-1)); VLit (Integer 5)] = Some (RValSeq [VLit (Integer (-6))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "bxor"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bxor"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Integer 1)]
    = Some (RExc (undef (VLit (Atom "bxor"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "bnot" [VLit (Integer 5)] = Some (RValSeq [VLit (Integer (-6))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bnot" [VLit (Integer (-1))] = Some (RValSeq [VLit (Integer 0)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bnot" [VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bnot"); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bnot" [VLit (Integer 1); VLit (Integer 2)]
    = Some (RExc (undef (VLit (Atom "bnot"))), None).
Proof. reflexivity. Qed.

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

Goal eval "erlang" "xor" [ttrue; ttrue] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ttrue; ffalse] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ffalse; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ffalse; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ttrue; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "xor"); ttrue; VTuple []])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ffalse; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "xor"); ffalse; VTuple []])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [VEmptyTuple; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "xor"); VTuple []; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ttrue] = Some (RExc (undef (VLit (Atom "xor"))), None).
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
Goal eval "erlang" "is_list" [VNil] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VCons ttrue (VCons ttrue VNil)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VCons ttrue ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VTuple []] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_list"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [VTuple []] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [VTuple [ttrue; ffalse]] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [VNil] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_tuple"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; VLit (Integer 2)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; VLit (Integer 3)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [ttrue; VLit (Integer 2)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; VLit (Integer (-1))]
    = Some (RExc (badarg (VTuple [VLit (Atom "is_function"); VClos [] 1 2 EEmptyMap; VLit (Integer (-1))])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "is_function"); VClos [] 1 2 EEmptyMap; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_map" [VMap [(ttrue, ttrue)]] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_map" [VNil] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_pid" [VPid 1] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_pid" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_port" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_port" [ttrue; ttrue] = Some (RExc (undef (VLit (Atom "is_port"))), None).
Proof. reflexivity. Qed.

(** Binaries used in the tests below: "12" and "-5" as 16 bit binaries, "ff", and a bitstring of 3 bits *)
Local Definition bin_12 : Val := VBitstring (bv_to_bvn (Z_to_bv 16 12594)).
Local Definition bin_m5 : Val := VBitstring (bv_to_bvn (Z_to_bv 16 11573)).
Local Definition bin_ff : Val := VBitstring (bv_to_bvn (Z_to_bv 16 26214)).
Local Definition bits_3 : Val := VBitstring (bv_to_bvn (Z_to_bv 3 5)).

Goal eval "erlang" "list_to_integer" [string_to_vcons "123"] = Some (RValSeq [VLit (Integer 123)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "-45"] = Some (RValSeq [VLit (Integer (-45))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "+7"] = Some (RValSeq [VLit (Integer 7)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "--"]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "--"])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "12a"]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "12a"])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "ff"; VLit (Integer 16)] = Some (RValSeq [VLit (Integer 255)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "1010"; VLit (Integer 2)] = Some (RValSeq [VLit (Integer 10)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "-0a"; VLit (Integer 16)] = Some (RValSeq [VLit (Integer (-10))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "10"; VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "10"; VLit (Integer 1)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "12"; VLit (Integer 2)]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "12"; VLit (Integer 2)])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "integer_to_list" [VLit (Integer 255); VLit (Integer 16)] = Some (RValSeq [string_to_vcons "FF"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [VLit (Integer (-10)); VLit (Integer 2)] = Some (RValSeq [string_to_vcons "-1010"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [VLit (Integer 0); VLit (Integer 10)] = Some (RValSeq [string_to_vcons "0"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [VLit (Integer 5); VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); VLit (Integer 5); VLit (Integer 1)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [ttrue; VLit (Integer 10)]
    = Some (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); ttrue; VLit (Integer 10)])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "binary_to_integer" [bin_12] = Some (RValSeq [VLit (Integer 12)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bin_m5] = Some (RValSeq [VLit (Integer (-5))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bin_ff; VLit (Integer 16)] = Some (RValSeq [VLit (Integer 255)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bits_3]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_integer"); bits_3])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_integer"); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bin_12; VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_integer"); bin_12; VLit (Integer 1)])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "atom_to_list" [VLit (Atom "abc")] = Some (RValSeq [string_to_vcons "abc"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "atom_to_list" [VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "atom_to_list"); VLit (Integer 1)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_atom" [bin_12; VLit (Atom "utf8")]
    = Some (RValSeq [VLit (Atom "12")], Some (AtomCreation, [VLit (Atom "12")])).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_atom" [bin_12; VLit (Atom "foo")]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_atom"); bin_12; VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_atom" [bits_3; VLit (Atom "utf8")]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_atom"); bits_3; VLit (Atom "utf8")])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "list_to_binary" [VCons (VLit (Integer 1)) (VCons (VLit (Integer 2)) VNil)]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 16 258))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [VNil]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 0 0))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [VCons (VLit (Integer 1)) (VCons bin_12 (VCons (VCons (VLit (Integer 2)) VNil) VNil))]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 32 (1 * 2^24 + 12594 * 2^8 + 2)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [VCons (VLit (Integer 256)) VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_binary"); VCons (VLit (Integer 256)) VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [bin_12]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_binary"); bin_12])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_to_binary" [bin_12] = Some (RValSeq [bin_12], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_to_binary" [VCons bin_12 bin_12]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 32 (12594 * 2^16 + 12594)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_to_binary" [bits_3]
    = Some (RExc (badarg (VTuple [VLit (Atom "iolist_to_binary"); bits_3])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_size" [VCons (VLit (Integer 1)) (VCons bin_12 VNil)] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_size" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "iolist_size"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "delete_element" [VLit (Integer 2); VTuple [ttrue; ffalse; VNil]] = Some (RValSeq [VTuple [ttrue; VNil]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "delete_element" [VLit (Integer 0); VTuple [ttrue]]
    = Some (RExc (badarg (VTuple [VLit (Atom "delete_element"); VLit (Integer 0); VTuple [ttrue]])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "delete_element" [VLit (Integer 2); VTuple [ttrue]]
    = Some (RExc (badarg (VTuple [VLit (Atom "delete_element"); VLit (Integer 2); VTuple [ttrue]])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "delete_element" [ttrue; VTuple [ttrue]]
    = Some (RExc (badarg (VTuple [VLit (Atom "delete_element"); ttrue; VTuple [ttrue]])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 1); VTuple [ttrue; ffalse]; VNil] = Some (RValSeq [VTuple [VNil; ttrue; ffalse]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 3); VTuple [ttrue; ffalse]; VNil] = Some (RValSeq [VTuple [ttrue; ffalse; VNil]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 4); VTuple [ttrue; ffalse]; VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "insert_element"); VLit (Integer 4); VTuple [ttrue; ffalse]; VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 0); VTuple [ttrue; ffalse]; VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "insert_element"); VLit (Integer 0); VTuple [ttrue; ffalse]; VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "make_tuple" [VLit (Integer 3); ttrue] = Some (RValSeq [VTuple [ttrue; ttrue; ttrue]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "make_tuple" [VLit (Integer 0); ttrue] = Some (RValSeq [VTuple []], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "make_tuple" [VLit (Integer (-1)); ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "make_tuple"); VLit (Integer (-1)); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [VTuple [ttrue; ffalse]] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [bin_12] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [bits_3] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "size"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "map_size" [VMap [(ttrue, ttrue); (ffalse, ttrue)]] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "map_size" [ttrue] = Some (RExc (badmap ttrue), None).
Proof. reflexivity. Qed.
Goal eval "maps" "from_keys" [VCons (VLit (Integer 2)) (VCons (VLit (Integer 1)) VNil); ttrue]
    = Some (RValSeq [VMap [(VLit (Integer 1), ttrue); (VLit (Integer 2), ttrue)]], None).
Proof. reflexivity. Qed.
Goal eval "maps" "from_keys" [VNil; ttrue] = Some (RValSeq [VMap []], None).
Proof. reflexivity. Qed.
Goal eval "maps" "from_keys" [ttrue; ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "from_keys"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "max" [VLit (Integer 2); VLit (Integer 1)] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "max" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "min" [VLit (Integer 2); VLit (Integer 1)] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "min" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "min" [VLit (Integer 1)] = Some (RExc (undef (VLit (Atom "min"))), None).
Proof. reflexivity. Qed.

Goal match eval "erlang" "split_binary" [bin_12; VLit (Integer 1)] with
     | Some (RValSeq [VTuple [VBitstring a; VBitstring b]], None) =>
         bvn_eqb a (bv_to_bvn (Z_to_bv 8 49)) && bvn_eqb b (bv_to_bvn (Z_to_bv 8 50))
     | _ => false
     end = true.
Proof. reflexivity. Qed.
Goal match eval "erlang" "split_binary" [bin_12; VLit (Integer 0)] with
     | Some (RValSeq [VTuple [VBitstring a; VBitstring b]], None) =>
         bvn_eqb a (bv_to_bvn (Z_to_bv 0 0)) && bvn_eqb b (bv_to_bvn (Z_to_bv 16 12594))
     | _ => false
     end = true.
Proof. reflexivity. Qed.
Goal eval "erlang" "split_binary" [bin_12; VLit (Integer 3)]
    = Some (RExc (badarg (VTuple [VLit (Atom "split_binary"); bin_12; VLit (Integer 3)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "split_binary" [ttrue; VLit (Integer 0)]
    = Some (RExc (badarg (VTuple [VLit (Atom "split_binary"); ttrue; VLit (Integer 0)])), None).
Proof. reflexivity. Qed.

Local Definition int_list : Val := VCons (VLit (Integer 2)) (VCons (VLit (Integer 1)) VNil).
Local Definition tuple_list : Val := VCons (VTuple [VLit (Integer 1); VLit (Integer 10)])
                                       (VCons (VTuple [VLit (Integer 2); VLit (Integer 20)]) VNil).

Goal eval "lists" "member" [VLit (Integer 1); int_list] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "lists" "member" [VLit (Integer 3); int_list] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "lists" "member" [VLit (Integer 1); ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "member"); VLit (Integer 1); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 2); VLit (Integer 1); tuple_list]
    = Some (RValSeq [VTuple [VLit (Integer 2); VLit (Integer 20)]], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 20); VLit (Integer 2); tuple_list]
    = Some (RValSeq [VTuple [VLit (Integer 2); VLit (Integer 20)]], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 3); VLit (Integer 1); tuple_list] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 1); VLit (Integer 0); tuple_list]
    = Some (RExc (badarg (VTuple [VLit (Atom "keyfind"); VLit (Integer 1); VLit (Integer 0); tuple_list])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 1); ttrue; tuple_list]
    = Some (RExc (badarg (VTuple [VLit (Atom "keyfind"); VLit (Integer 1); ttrue; tuple_list])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "keymember" [VLit (Integer 2); VLit (Integer 1); tuple_list] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keymember" [VLit (Integer 3); VLit (Integer 1); tuple_list] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keymember" [VLit (Integer 1); VLit (Integer 1); ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "keymember"); VLit (Integer 1); VLit (Integer 1); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [int_list]
    = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 2)) VNil)], None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [VNil] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [int_list; VLit (Integer 3)]
    = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 2)) (VLit (Integer 3)))], None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "reverse"); ttrue])), None).
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

Goal eval "maps" "get" [VNil; VMap [(VNil, VNil)]] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VLit 2%Z; VMap [(VLit 1%Z, VLit 1%Z);(VLit 2%Z, VLit 2%Z);(VLit 3%Z, VLit 3%Z)]] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VLit 1%Z, VNil)]] = Some (RExc (badkey VNil), None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VNil, VNil)];VTuple []] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VLit 2%Z; VMap [(VLit 1%Z, VLit 1%Z);(VLit 2%Z, VLit 2%Z);(VLit 3%Z, VLit 3%Z)];VTuple []] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VLit 1%Z, VNil)];VTuple []] = Some (RValSeq [VTuple []], None).
Proof. reflexivity. Qed.


Goal eval "maps" "put" [VNil; VNil; VMap [(VNil, VLit 1%Z)]] = Some (RValSeq [VMap [(VNil, VNil)]], None).
Proof. cbn. reflexivity. Qed.
Goal eval "maps" "get" [VLit 2%Z; VMap [(VLit 1%Z, VLit 1%Z);(VLit 2%Z, VLit 2%Z);(VLit 3%Z, VLit 3%Z)]] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VLit 1%Z, VNil)]] = Some (RExc (badkey VNil), None).
Proof. reflexivity. Qed.


(** Bitstring/binary tests.
    b16 = <<433:16>>       = <<1,177>>       (byte-aligned, 16 bits)
    b19 = <<433:16,3:3>>   = <<1,177,3:3>>   (not byte-aligned, 19 bits)
    b3  = <<3:3>>          (shorter than one byte, 3 bits)

    `bv`/`bvn` bundle their value with a `Qed`-opaque well-formedness proof,
    so plain `reflexivity` can get stuck comparing two `VBitstring`s whose
    underlying values are equal but were constructed via `Z_to_bv` with
    different (though equally-wrapping) raw arguments. `bv_eq`/`bvn_eq`
    (from stdpp) reduce that comparison to just the `bv_unsigned`/
    `bvn_unsigned` value, sidestepping the opaque proof entirely. *)
Ltac reflexivity_upto_bv :=
  vm_compute;
  repeat first
    [ reflexivity
    | apply bv_eq;  reflexivity
    | apply bvn_eq; split; reflexivity
    | f_equal ].

Local Definition b16 : Val := VBitstring (Z_to_bv 16 433).
Local Definition b19 : Val := VBitstring (Z_to_bv 19 3467).
Local Definition b3  : Val := VBitstring (Z_to_bv 3 3).

Goal eval "erlang" "bit_size" [b19] = Some (RValSeq [VLit (Integer 19)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [b16] = Some (RValSeq [VLit (Integer 16)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [b3] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "bit_size"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [] = Some (RExc (undef (VLit (Atom "bit_size"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "byte_size" [b19] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [b16] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [b3] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "byte_size"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [] = Some (RExc (undef (VLit (Atom "byte_size"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "is_binary" [b16] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [b19] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [b3] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [ttrue; ttrue] = Some (RExc (undef (VLit (Atom "is_binary"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "is_bitstring" [b19] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [b16] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [b3] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [] = Some (RExc (undef (VLit (Atom "is_bitstring"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "bitstring_to_list" [b19]
  = Some (RValSeq [VCons (VLit (Integer 1))
                  (VCons (VLit (Integer 177))
                  (VCons (VBitstring (Z_to_bv 3 3)) VNil))], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [b16]
  = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 177)) VNil)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [b3]
  = Some (RValSeq [VCons (VBitstring (Z_to_bv 3 3)) VNil], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [ttrue]
  = Some (RExc (badarg (VTuple [VLit (Atom "bitstring_to_list"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [] = Some (RExc (undef (VLit (Atom "bitstring_to_list"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "binary_to_list" [b16]
  = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 177)) VNil)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "binary_to_list" [b19]
  = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_list"); b19])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "binary_to_list" [ttrue]
  = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_list"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "binary_to_list" [] = Some (RExc (undef (VLit (Atom "binary_to_list"))), None).
Proof. reflexivity_upto_bv. Qed.


End Tests.
