From CoreErlang.Concurrent Require Export ProcessSemantics NodeSemantics.

(* WRAPPERS FOR MAP AND SET EXTRACTION *)

Definition dead_lookup : PID -> gmap PID Val -> option Val :=
  fun pid links => links !! pid.

Definition dead_delete : PID -> gmap PID Val -> gmap PID Val :=
  fun pid links => delete pid links.

Definition dead_domain : gmap PID Val -> gset PID :=
  fun links => dom links.

Definition dead_size : gmap PID Val -> nat :=
  fun links => map_size links.

Definition pids_set_to_map : Val -> gset PID -> gmap PID Val :=
  fun reason links => gset_to_gmap reason links.

Definition pids_insert : PID -> gset PID -> gset PID :=
  fun new links => links ∪ {[new]}.

Definition pids_delete : PID -> gset PID -> gset PID :=
  fun to_del links => links ∖ {[to_del]}.

Definition pids_empty : gset PID := ∅.

Definition pids_member : PID -> gset PID -> bool :=
  fun pid pids =>
    if gset_elem_of_dec pid pids
    then true
    else false.

Definition pids_union : gset PID -> gset PID -> gset PID :=
  fun pids1 pids2 => pids1 ∪ pids2.

Definition pids_singleton : PID -> gset PID :=
  fun pid => {[ pid ]}.

Definition pids_toList : gset PID -> list PID :=
  fun pids => elements pids.

Definition pids_fresh : gset PID -> PID :=
  fun pids => fresh pids.

Definition pids_foldWithKey : (PID -> Val -> gset PID -> gset PID) 
                              -> gset PID -> gmap PID Val -> gset PID :=
  fun f acc linkmap => map_fold f acc linkmap.

Definition pids_map_set_union : (PID -> Val -> gset PID) -> gmap PID Val -> gset PID :=
  fun f m => @union_set _ _ _ gsetPID_elem_of _ (map_to_set f m).

Definition pool_singleton : PID -> Process -> ProcessPool :=
  fun pid proc => {[ pid := proc ]}.

Definition pool_lookup : PID -> ProcessPool -> option Process :=
  fun pid prs => prs !! pid.

Definition pool_insert : PID -> Process -> ProcessPool -> ProcessPool :=
  fun pid proc pool => pid ↦ proc ∥ pool.

Definition pool_toList : ProcessPool -> list (PID * Process) :=
  fun pool => map_to_list pool.

Definition pool_domain : gmap PID Process -> gset PID :=
  fun prs => dom prs.

Definition ether_empty : Ether := ∅.

Definition ether_lookup : (PID * PID) -> Ether -> option (list Signal) :=
  fun pids eth => eth !! pids.

Definition ether_insert : (PID * PID) -> (list Signal) -> Ether -> Ether :=
  fun pids sigs eth => <[ pids := sigs ]> eth.

Definition ether_toList : Ether -> list ((PID * PID) * list Signal) :=
  fun eth => map_to_list eth.

Definition ether_domain_toList : Ether -> list (PID * PID) :=
  fun eth => elements (dom eth).

(* WRAPPED DEFINITIONS FOR DETERMINING USED PIDS *)

Definition etherAddNew (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  match ether_lookup (source, dest) n with
  | Some l => ether_insert (source, dest) (l ++ [m]) n
  | None   => ether_insert (source, dest) [m] n
  end.

Definition etherPopNew (source dest : PID) (n : Ether) : option (Signal * Ether) :=
  match ether_lookup (source, dest) n with
  | None | Some [] => None
  | Some (x::xs) => Some (x, ether_insert (source, dest) xs n)
  end.

Definition flat_unionNew {A}
  (f : A -> gset PID) (l : list A) : gset PID :=
    foldr (fun x acc => pids_union (f x) acc) pids_empty l.

Fixpoint usedPIDsExpNew (e : Exp) : gset PID :=
match e with
 | VVal e => usedPIDsValNew e
 | EExp e => usedPIDsNValNew e
end
with usedPIDsValNew (v : Val) : gset PID :=
match v with
 | VNil => pids_empty
 | VLit l => pids_empty
 | VPid p => pids_singleton p
 | VCons hd tl => pids_union (usedPIDsValNew hd) (usedPIDsValNew tl)
 | VTuple l => flat_unionNew usedPIDsValNew l
 | VMap l => flat_unionNew (fun x => pids_union (usedPIDsValNew x.1) (usedPIDsValNew x.2)) l
 | VVar n => pids_empty
 | VFunId n => pids_empty
 | VClos ext id params e => pids_union 
                            (usedPIDsExpNew e) 
                            (flat_unionNew (fun x => usedPIDsExpNew x.2) ext)
end

with usedPIDsNValNew (n : NonVal) : gset PID :=
match n with
 | EFun vl e => usedPIDsExpNew e
 | EValues el => flat_unionNew usedPIDsExpNew el
 | ECons hd tl => pids_union (usedPIDsExpNew hd) (usedPIDsExpNew tl)
 | ETuple l => flat_unionNew usedPIDsExpNew l
 | EMap l => flat_unionNew (fun x => pids_union (usedPIDsExpNew x.1) (usedPIDsExpNew x.2)) l
 | ECall m f l => pids_union (usedPIDsExpNew m) 
                             (pids_union (usedPIDsExpNew f) (flat_unionNew usedPIDsExpNew l))
 | EPrimOp f l => flat_unionNew usedPIDsExpNew l
 | EApp exp l => pids_union (usedPIDsExpNew exp) (flat_unionNew usedPIDsExpNew l)
 | ECase e l => pids_union (usedPIDsExpNew e) 
                (flat_unionNew (fun x => pids_union (usedPIDsExpNew x.1.2) (usedPIDsExpNew x.2)) l)
 | ELet l e1 e2 => pids_union (usedPIDsExpNew e1) (usedPIDsExpNew e2)
 | ESeq e1 e2 => pids_union (usedPIDsExpNew e1) (usedPIDsExpNew e2)
 | ELetRec l e => pids_union (usedPIDsExpNew e) (flat_unionNew (fun x => usedPIDsExpNew x.2) l)
 | ETry e1 vl1 e2 vl2 e3 => pids_union 
                            (usedPIDsExpNew e1) 
                            (pids_union (usedPIDsExpNew e2) (usedPIDsExpNew e3))
end.

Definition usedPIDsRedNew (r : Redex) : gset PID :=
match r with
 | RExp e => usedPIDsExpNew e
 | RValSeq vs => flat_unionNew usedPIDsValNew vs
 | RExc e => pids_union (usedPIDsValNew e.1.2) (usedPIDsValNew e.2)
 | RBox => pids_empty
end.

Definition usedPIDsFrameIdNew (i : FrameIdent) : gset PID :=
match i with
 | IValues => pids_empty
 | ITuple => pids_empty
 | IMap => pids_empty
 | ICall m f => pids_union (usedPIDsValNew m) (usedPIDsValNew f)
 | IPrimOp f => pids_empty
 | IApp v => usedPIDsValNew v
end.

Definition usedPIDsFrameNew (f : Frame) : gset PID :=
match f with
 | FCons1 hd => usedPIDsExpNew hd
 | FCons2 tl => usedPIDsValNew tl
 | FParams ident vl el => pids_union (usedPIDsFrameIdNew ident) (
                          pids_union (flat_unionNew usedPIDsValNew vl) (
                          flat_unionNew usedPIDsExpNew el))
 | FApp1 l => flat_unionNew usedPIDsExpNew l
 | FCallMod f l => pids_union (usedPIDsExpNew f) (flat_unionNew usedPIDsExpNew l)
 | FCallFun m l => pids_union (usedPIDsValNew m) (flat_unionNew usedPIDsExpNew l)
 | FCase1 l => flat_unionNew (fun x => pids_union (usedPIDsExpNew x.1.2) (usedPIDsExpNew x.2)) l
 | FCase2 lv ex le =>
   pids_union (usedPIDsExpNew ex) (
   pids_union (flat_unionNew usedPIDsValNew lv) (
   flat_unionNew (fun x => pids_union (usedPIDsExpNew x.1.2) (usedPIDsExpNew x.2)) le))
 | FLet l e => usedPIDsExpNew e
 | FSeq e => usedPIDsExpNew e
 | FTry vl1 e2 vl2 e3 => pids_union (usedPIDsExpNew e2) (usedPIDsExpNew e3)
end.

Definition usedPIDsStackNew (fs : FrameStack) : gset PID :=
  flat_unionNew usedPIDsFrameNew fs.

Definition usedPIDsProcNew (p : Process) : gset PID :=
match p with
| inl (fs, r, mb, links, flag) => 
    pids_union (usedPIDsStackNew fs) (
    pids_union (usedPIDsRedNew r) (
    pids_union links (
    pids_union (flat_unionNew usedPIDsValNew mb.1) (
    flat_unionNew usedPIDsValNew mb.2))))
| inr links => (* should links should be considered? - Definitely *)
     (*pids_foldWithKey (fun k x acc => pids_union (pids_insert k (usedPIDsValNew x)) acc) 
                      pids_empty links*) (*<- simple, but no support with theorems *)
    pids_map_set_union (fun k x => pids_insert k (usedPIDsValNew x)) links
    (*@union_set _ _ _ gsetPID_elem_of _ (map_to_set (fun k x => pids_insert k (usedPIDsValNew x)) links)*)
end.

Definition allPIDsPoolNew (Π : ProcessPool) : gset PID :=
  flat_unionNew (fun '(ι, proc) => pids_insert ι (usedPIDsProcNew proc)) (pool_toList Π).

Definition usedPIDsSignalNew (s : Signal) : gset PID :=
match s with
 | SMessage e => usedPIDsValNew e
 | SExit r b => usedPIDsValNew r
 | SLink => pids_empty
 | SUnlink => pids_empty
end.

Definition allPIDsEtherNew (eth : Ether) : gset PID :=
  flat_unionNew (fun '((ιs, ιd), sigs) => 
    pids_union (pids_insert ιs (pids_singleton ιd)) 
    (flat_unionNew usedPIDsSignalNew sigs)) (ether_toList eth).

Definition usedInPoolNew : PID -> ProcessPool -> bool :=
  fun pid prs =>
    if pids_member pid (allPIDsPoolNew prs)
    then true
    else false.

Definition usedInEtherNew : PID -> Ether -> bool :=
  fun pid eth =>
    if pids_member pid (allPIDsEtherNew eth)
    then true
    else false.

(* WRAPPED DEFINITIONS FOR RESULT CONSTRUCTION *)

Definition convert_primop_to_code_NEW (s : string) : PrimopCode :=
  (** primops *)
  if String.eqb s "match_fail"%string
    then PMatchFail
  else if String.eqb s "raise"%string
    then PRaise
  else if String.eqb s "recv_next"%string
    then PRecvNext
  else if String.eqb s "recv_peek_message"%string
    then PPeekMsg
  else if String.eqb s "remove_message"%string
    then PRemoveMsg
  else if String.eqb s "recv_wait_timeout"%string
    then PRecvWaitTimeout
  else PNothing
.

Definition eval_primop_error_NEW (fname : string) (params : list Val) : option Exception :=
match convert_primop_to_code_NEW fname with
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

Definition primop_eval_NEW (fname : string) (params : list Val) : option (Redex * (option SideEffect)) :=
match convert_primop_to_code_NEW fname with
  | PMatchFail | PRaise =>
    match (eval_primop_error_NEW fname params) with
    | Some exc => Some (RExc exc, None)
    | None => None (* this is a compile-time error *)
    end
(** These are concurrent primops: *)
  | PRecvNext | PRemoveMsg | PPeekMsg
  | PRecvWaitTimeout => None
(***)
  | _ => Some (RExc (undef (VLit (Atom fname))), None)
end.

Definition convert_string_to_code_NEW : (string * string) -> BIFCode :=
  fun '(sf, sn) => 
    if String.eqb sf "erlang"%string
      then (
        if String.eqb sn "+"%string then BPlus
        else if String.eqb sn "-"%string then BMinus
        else if String.eqb sn "*"%string then BMult
        else if String.eqb sn "/"%string then BDivide
        else if String.eqb sn "bsl"%string then BSl
        else if String.eqb sn "bsr"%string then BSr
        else if String.eqb sn "rem"%string then BRem
        else if String.eqb sn "div"%string then BDiv
        else if String.eqb sn "abs"%string then BAbs
        else if String.eqb sn "and"%string then BAnd
        else if String.eqb sn "or"%string then BOr
        else if String.eqb sn "not"%string then BNot
        else if String.eqb sn "=="%string then BEq
        else if String.eqb sn "=:="%string then BTypeEq
        else if String.eqb sn "/="%string then BNeq
        else if String.eqb sn "=/="%string then BTypeNeq
        else if String.eqb sn "++"%string then BApp
        else if String.eqb sn "--"%string then BMinusMinus
        else if String.eqb sn "tuple_to_list"%string then BTupleToList
        else if String.eqb sn "list_to_tuple"%string then BListToTuple
        else if String.eqb sn "list_to_atom"%string then BListToAtom
        else if String.eqb sn "integer_to_list"%string then BIntegerToList
        else if String.eqb sn "<"%string then BLt
        else if String.eqb sn ">"%string then BGt
        else if String.eqb sn "=<"%string then BLe
        else if String.eqb sn ">="%string then BGe
        else if String.eqb sn "length"%string then BLength
        else if String.eqb sn "tuple_size"%string then BTupleSize
        else if String.eqb sn "hd"%string then BHd
        else if String.eqb sn "tl"%string then BTl
        else if String.eqb sn "element"%string then BElement
        else if String.eqb sn "setelement"%string then BSetElement
        else if String.eqb sn "is_number"%string then BIsNumber
        else if String.eqb sn "is_integer"%string then BIsInteger
        else if String.eqb sn "is_atom"%string then BIsAtom
        else if String.eqb sn "is_boolean"%string then BIsBoolean
        else if String.eqb sn "fun_info"%string then BFunInfo
        else if String.eqb sn "error"%string then BError
        else if String.eqb sn "exit"%string then BExit
        else if String.eqb sn "throw"%string then BThrow
        else if String.eqb sn "!"%string then BSend
        else if String.eqb sn "spawn"%string then BSpawn
        else if String.eqb sn "spawn_link"%string then BSpawnLink
        else if String.eqb sn "process_flag"%string then BProcessFlag
        else if String.eqb sn "self"%string then BSelf
        else if String.eqb sn "link"%string then BLink
        else if String.eqb sn "unlink"%string then BUnLink
        else BNothing
      )
    else if String.eqb sf "io"%string
      then (
        if String.eqb sn "fwrite"%string then BFwrite
        else if String.eqb sn "fread"%string then BFread
        else BNothing
      )
    else if String.eqb sf "lists"%string
      then (
        if String.eqb sn "split"%string then BSplit
        else BNothing
      )
    else BNothing.

Definition eval_arith_NEW (mname : string) (fname : string) (params : list Val) :  Redex :=
match convert_string_to_code_NEW (mname, fname), params with
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

Definition eval_io_NEW (mname : string) (fname : string) (params : list Val)
   : (Redex * option SideEffect) :=
match convert_string_to_code_NEW (mname, fname), length params, params with
(** writing *)
| BFwrite, 1, _ => (RValSeq [ok], Some (Output, params))
(** reading *)
| BFread, 2, e => (RValSeq [VTuple [ok; nth 1 params ErrorVal]], Some (Input, params))
(** anything else *)
| _              , _, _ => (RExc (undef (VLit (Atom fname))), None)
end.

Definition eval_logical_NEW (mname fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
(** Note: we intentionally avoid pattern matching on strings here *)
(** logical and *)
| BAnd, [a; b] =>
   if Val_eqb_strict a ttrue
   then
    if Val_eqb_strict b ttrue
    then RValSeq [ttrue]
    else
      if Val_eqb_strict b ffalse
      then RValSeq [ffalse]
      else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   else
    if Val_eqb_strict a ffalse
    then
      if Val_eqb_strict b ttrue
      then RValSeq [ffalse]
      else
        if Val_eqb_strict b ffalse
        then RValSeq [ffalse]
        else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
    else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
(** logical or *)
| BOr, [a; b] =>
   if Val_eqb_strict a ttrue
   then
    if Val_eqb_strict b ttrue
    then RValSeq [ttrue]
    else
      if Val_eqb_strict b ffalse
      then RValSeq [ttrue]
      else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
   else
    if Val_eqb_strict a ffalse
    then
      if Val_eqb_strict b ttrue
      then RValSeq [ttrue]
      else
        if Val_eqb_strict b ffalse
        then RValSeq [ffalse]
        else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
    else RExc (badarg (VTuple [VLit (Atom fname); a; b]))
(** logical not *)
| BNot, [a] =>
   if Val_eqb_strict a ttrue
   then RValSeq [ffalse]
   else
    if Val_eqb_strict a ffalse
    then RValSeq [ttrue]
    else RExc (badarg (VTuple [VLit (Atom fname); a]))
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_equality_NEW (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
| BEq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeEq, [v1; v2] => if Val_eqb v1 v2 then RValSeq [ttrue] else RValSeq [ffalse]
| BNeq,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| BTypeNeq, [v1; v2] => if Val_eqb v1 v2 then RValSeq [ffalse] else RValSeq [ttrue]
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_transform_list_NEW (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
| BApp, [v1; v2]        => eval_append v1 v2
| BMinusMinus, [v1; v2] => eval_subtract v1 v2
| BSplit, [v1; v2] => eval_split v1 v2
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_list_tuple_NEW (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
| BTupleToList, [v] => transform_tuple v
| BListToTuple, [v] => match mk_list v with
                                 | None => RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); v]))
                                 | Some l => RValSeq [VTuple l]
                                 end
| _                     , _   => RExc (undef (VLit (Atom fname)))
end.

Definition eval_convert_NEW (mname : string) (fname : string) (params : list Val) : Redex * option SideEffect :=
match convert_string_to_code_NEW (mname, fname), params with
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

Definition eval_cmp_NEW (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
| BLt,  [v1; v2] => if Val_ltb v1 v2 then RValSeq [ttrue] else RValSeq [ffalse]
| BLe, [v1; v2] => if orb (Val_ltb v1 v2) (Val_eqb v1 v2) 
                           then RValSeq [ttrue] else RValSeq [ffalse]
| BGt,  [v1; v2] => if Val_ltb v2 v1 then RValSeq [ttrue] else RValSeq [ffalse]
| BGe, [v1; v2] => if orb (Val_ltb v2 v1) (Val_eqb v1 v2) 
                           then RValSeq [ttrue] else RValSeq [ffalse]
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_hd_tl_NEW (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
| BHd, [VCons x y] => RValSeq [x]
| BHd, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| BTl, [VCons x y] => RValSeq [y]
| BTl, [v] => RExc (badarg (VTuple [VLit (Atom fname); v]))
| _, _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_elem_tuple_NEW (mname : string) (fname : string) (params : list Val) : Redex :=
match convert_string_to_code_NEW (mname, fname), params with
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

Definition eval_check_NEW (mname fname : string) (params : list Val) : Redex := 
match convert_string_to_code_NEW (mname, fname), params with
| BIsNumber, [VLit (Integer i)]     => RValSeq [ttrue]
| BIsNumber, [_]                    => RValSeq [ffalse]
| BIsInteger, [VLit (Integer i)]    => RValSeq [ttrue]
| BIsInteger, [_]                   => RValSeq [ffalse] 
| BIsAtom, [VLit (Atom a)]          => RValSeq [ttrue]
| BIsAtom, [_]                      => RValSeq [ffalse]
(** Note: we intentionally avoid pattern matching on strings here *)
| BIsBoolean, [v] => if orb (Val_eqb_strict v ttrue) (Val_eqb_strict v ffalse)
                     then RValSeq [ttrue]
                     else RValSeq [ffalse]
| _, _              => RExc (undef (VLit (Atom fname)))
end.

Definition eval_error_NEW (mname : string) (fname : string) (params : list Val) : option Exception :=
match convert_string_to_code_NEW (mname, fname), params with
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

Definition eval_funinfo_NEW (params : list Val) : Redex :=
match params with
| [VClos ext id params e;v] =>
  if Val_eqb_strict v (VLit "arity"%string)
  then RValSeq [VLit (Z.of_nat params)]
  else RExc (badarg (VTuple [VLit "fun_info"%string;VClos ext id params e;v]))
| [v1;v2] => RExc (badarg (VTuple [VLit "fun_info"%string;v1;v2]))
| _ => RExc (undef (VLit "fun_info"%string))
end.

Definition eval_concurrent_NEW (mname : string) (fname : string) (params : list Val) : option Exception :=
match convert_string_to_code_NEW (mname, fname) with
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

Definition eval_NEW (mname : string) (fname : string) (params : list Val) 
   : option (Redex * option SideEffect) :=
match convert_string_to_code_NEW (mname, fname) with
| BPlus | BMinus | BMult | BDivide | BRem | BDiv
| BSl   | BSr    | BAbs                           => Some (eval_arith_NEW mname fname params, None)
| BFwrite | BFread                                => Some (eval_io_NEW mname fname params)
| BAnd | BOr | BNot                               => Some (eval_logical_NEW mname fname params, None)
| BEq | BTypeEq | BNeq | BTypeNeq                 => Some (eval_equality_NEW mname fname params, None)
| BApp | BMinusMinus | BSplit                     => Some (eval_transform_list_NEW mname fname params, None)
| BTupleToList | BListToTuple                     => Some (eval_list_tuple_NEW mname fname params, None)
| BListToAtom | BIntegerToList                    => Some (eval_convert_NEW mname fname params)
| BLt | BGt | BLe | BGe                           => Some (eval_cmp_NEW mname fname params, None)
| BLength                                         => Some (eval_length params, None)
| BTupleSize                                      => Some (eval_tuple_size params, None)
| BHd | BTl                                       => Some (eval_hd_tl_NEW mname fname params, None)
| BElement | BSetElement                          => Some (eval_elem_tuple_NEW mname fname params, None)
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean   => Some (eval_check_NEW mname fname params, None)
| BError | BExit | BThrow                         => match (eval_error_NEW mname fname params) with
                                                      | Some exc => Some (RExc exc, None)
                                                      | None => None
                                                     end
| BFunInfo                                        => Some (eval_funinfo_NEW params, None)
(** undefined functions *)
| BNothing                                        => Some (RExc (undef (VLit (Atom fname))), None)
(* concurrent BIFs *)
| BSend | BSpawn | BSpawnLink | BSelf | BProcessFlag
| BLink | BUnLink                                 => match eval_concurrent_NEW mname fname params with
                                                     | Some exc => Some (RExc exc, None)
                                                     | None => None
                                                     end
end.

Definition create_result_NEW (ident : FrameIdent) (vl : list Val)
  : option (Redex * option SideEffect) :=
match ident with
| IValues => Some (RValSeq vl, None)
| ITuple => Some (RValSeq [VTuple vl], None)
| IMap => Some (RValSeq [VMap (make_val_map (deflatten_list vl))], None)
| ICall m f => match m, f with
               | VLit (Atom module), VLit (Atom func) =>
                  eval_NEW module func vl
               | _, _ => Some (RExc (badfun (VTuple [m; f])), None)
               end
| IPrimOp f => primop_eval_NEW f vl
| IApp (VClos ext id vars e) =>
  if Nat.eqb vars (length vl)
  then Some (RExp (e.[list_subst (convert_to_closlist ext ++ vl) idsubst]), None)
  else Some (RExc (badarity (VClos ext id vars e)), None)
| IApp v => Some (RExc (badfun v), None)
end.
