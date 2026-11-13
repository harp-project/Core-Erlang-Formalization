From CoreErlang.Concurrent Require Export ProcessSemantics NodeSemantics.
Import Notations.

(** This file contains wrapper functions and auxiliary definitions
    for the interpreter.
*)

(**
    WRAPPERS FOR MAP AND SET EXTRACTION
    
    Since using the default extracted version of std++-s "gsets" 
    and "gmaps" does not result in efficient datatype implementations,
    we chose to swap them out for Haskell's "Data.HashMap.Strict" and
    "Data.HashSet" datatypes. However, since the interfaces of the
    function are not trivially replacable, wrapper functions are
    used to bridge the gap. For the replacements, see "HaskellExtraction.v".
    
    Note that replacing the toList functions don't preserve the order
    behaviour. However, in both the interpreter and the evaluation-tree
    builder, the order given is irrelevant (see the Interpreter paper
    for details). Other functions were regression tested in Haskell
    and were found to be equivalent.
*)

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

(** 
    WRAPPED DEFINITIONS FOR DETERMINING USED PIDS
    
    To not break all the theorems proven about the semantics, it was
    decided that the functions where wrappers were needed should not be
    redefined, but a parallel definition should be given. For the
    equivalence proofs to work, equivalence lemmas were defined for
    these functions in "InterpreterAuxLemmas.v".
*)

Definition etherAdd_Interp (source dest : PID) (m : Signal) (n : Ether) : Ether :=
  match ether_lookup (source, dest) n with
  | Some l => ether_insert (source, dest) (l ++ [m]) n
  | None   => ether_insert (source, dest) [m] n
  end.

Definition etherPop_Interp (source dest : PID) (n : Ether) : option (Signal * Ether) :=
  match ether_lookup (source, dest) n with
  | None | Some [] => None
  | Some (x::xs) => Some (x, ether_insert (source, dest) xs n)
  end.

Definition flat_union_Interp {A}
  (f : A -> gset PID) (l : list A) : gset PID :=
    foldr (fun x acc => pids_union (f x) acc) pids_empty l.

Fixpoint usedPIDsExp_Interp (e : Exp) : gset PID :=
match e with
 | VVal e => usedPIDsVal_Interp e
 | EExp e => usedPIDsNVal_Interp e
end
with usedPIDsVal_Interp (v : Val) : gset PID :=
match v with
 | VNil => pids_empty
 | VLit l => pids_empty
 | VPid p => pids_singleton p
 | VCons hd tl => pids_union (usedPIDsVal_Interp hd) (usedPIDsVal_Interp tl)
 | VTuple l => flat_union_Interp usedPIDsVal_Interp l
 | VMap l => flat_union_Interp (fun x => pids_union (usedPIDsVal_Interp x.1) (usedPIDsVal_Interp x.2)) l
 | VVar n => pids_empty
 | VFunId n => pids_empty
 | VClos ext id params e => pids_union 
                            (usedPIDsExp_Interp e) 
                            (flat_union_Interp (fun x => usedPIDsExp_Interp x.2) ext)
 | VBitstring bits => pids_empty
end

with usedPIDsNVal_Interp (n : NonVal) : gset PID :=
match n with
 | EFun vl e => usedPIDsExp_Interp e
 | EValues el => flat_union_Interp usedPIDsExp_Interp el
 | ECons hd tl => pids_union (usedPIDsExp_Interp hd) (usedPIDsExp_Interp tl)
 | ETuple l => flat_union_Interp usedPIDsExp_Interp l
 | EMap l => flat_union_Interp (fun x => pids_union (usedPIDsExp_Interp x.1) (usedPIDsExp_Interp x.2)) l
 | ECall m f l => pids_union (usedPIDsExp_Interp m) 
                             (pids_union (usedPIDsExp_Interp f) (flat_union_Interp usedPIDsExp_Interp l))
 | EPrimOp f l => flat_union_Interp usedPIDsExp_Interp l
 | EApp exp l => pids_union (usedPIDsExp_Interp exp) (flat_union_Interp usedPIDsExp_Interp l)
 | ECase e l => pids_union (usedPIDsExp_Interp e)
                (flat_union_Interp
                (fun x => pids_union (pids_union (flat_union_Interp usedPIDsPat_Interp x.1.1)
                                                 (usedPIDsExp_Interp x.1.2))
                                     (usedPIDsExp_Interp x.2)) l)
 | ELet l e1 e2 => pids_union (usedPIDsExp_Interp e1) (usedPIDsExp_Interp e2)
 | ESeq e1 e2 => pids_union (usedPIDsExp_Interp e1) (usedPIDsExp_Interp e2)
 | ELetRec l e => pids_union (usedPIDsExp_Interp e) 
                             (flat_union_Interp (fun x => usedPIDsExp_Interp x.2) l)
 | ETry e1 vl1 e2 vl2 e3 => pids_union 
                            (usedPIDsExp_Interp e1) 
                            (pids_union (usedPIDsExp_Interp e2) (usedPIDsExp_Interp e3))
 | EBin l => flat_union_Interp usedPIDsExp_Interp l
 | ESeg seg => pids_union (usedPIDsExp_Interp (seg_val seg)) (usedPIDsExp_Interp (seg_size seg))
end
with usedPIDsPat_Interp (p : Pat) : gset PID :=
match p with
 | PVar => pids_empty
 | PLit l => pids_empty
 | PCons hd tl => pids_union (usedPIDsPat_Interp hd) (usedPIDsPat_Interp tl)
 | PTuple l => flat_union_Interp usedPIDsPat_Interp l
 | PMap l => flat_union_Interp (fun x => pids_union (usedPIDsPat_Interp x.1) (usedPIDsPat_Interp x.2)) l
 | PNil => pids_empty
 | PBin segments => flat_union_Interp (fun x => pids_union (usedPIDsPat_Interp (seg_val x))
                                                           (usedPIDsVal_Interp (seg_size x))) segments
end.

Definition usedPIDsRed_Interp (r : Redex) : gset PID :=
match r with
 | RExp e => usedPIDsExp_Interp e
 | RValSeq vs => flat_union_Interp usedPIDsVal_Interp vs
 | RExc e => pids_union (usedPIDsVal_Interp e.1.2) (usedPIDsVal_Interp e.2)
 | RBox => pids_empty
end.

Definition usedPIDsFrameId_Interp (i : FrameIdent) : gset PID :=
match i with
 | IBin => pids_empty
 | IValues => pids_empty
 | ITuple => pids_empty
 | IMap => pids_empty
 | ICall m f => pids_union (usedPIDsVal_Interp m) (usedPIDsVal_Interp f)
 | IPrimOp f => pids_empty
 | IApp v => usedPIDsVal_Interp v
end.

Definition usedPIDsFrame_Interp (f : Frame) : gset PID :=
match f with
 | FCons1 hd => usedPIDsExp_Interp hd
 | FCons2 tl => usedPIDsVal_Interp tl
 | FParams ident vl el => pids_union (usedPIDsFrameId_Interp ident) (
                          pids_union (flat_union_Interp usedPIDsVal_Interp vl) (
                          flat_union_Interp usedPIDsExp_Interp el))
 | FApp1 l => flat_union_Interp usedPIDsExp_Interp l
 | FCallMod f l => pids_union (usedPIDsExp_Interp f) (flat_union_Interp usedPIDsExp_Interp l)
 | FCallFun m l => pids_union (usedPIDsVal_Interp m) (flat_union_Interp usedPIDsExp_Interp l)
 | FCase1 l => flat_union_Interp (fun x => pids_union
                                 (pids_union (flat_union_Interp usedPIDsPat_Interp x.1.1)
                                             (usedPIDsExp_Interp x.1.2))
                                 (usedPIDsExp_Interp x.2)) l
 | FCase2 lv ex le =>
   pids_union (usedPIDsExp_Interp ex) (
   pids_union (flat_union_Interp usedPIDsVal_Interp lv) (
   flat_union_Interp (fun x => pids_union
                                 (pids_union (flat_union_Interp usedPIDsPat_Interp x.1.1)
                                             (usedPIDsExp_Interp x.1.2))
                                 (usedPIDsExp_Interp x.2)) le))
 | FLet l e => usedPIDsExp_Interp e
 | FSeq e => usedPIDsExp_Interp e
 | FTry vl1 e2 vl2 e3 => pids_union (usedPIDsExp_Interp e2) (usedPIDsExp_Interp e3)
 | FSeg1 s _ _ _ _ => usedPIDsExp_Interp s
 | FSeg2 v _ _ _ _ => usedPIDsVal_Interp v
end.

Definition usedPIDsStack_Interp (fs : FrameStack) : gset PID :=
  flat_union_Interp usedPIDsFrame_Interp fs.

Definition usedPIDsProc_Interp (p : Process) : gset PID :=
match p with
| inl (fs, r, mb, links, flag) => 
    pids_union (usedPIDsStack_Interp fs) (
    pids_union (usedPIDsRed_Interp r) (
    pids_union links (
    pids_union (flat_union_Interp usedPIDsVal_Interp mb.1) (
    flat_union_Interp usedPIDsVal_Interp mb.2))))
| inr links => (* should links should be considered? - Definitely *)
     (*pids_foldWithKey (fun k x acc => pids_union (pids_insert k (usedPIDsVal_Interp x)) acc) 
                      pids_empty links*) (*<- simple, but no support with theorems *)
    pids_map_set_union (fun k x => pids_insert k (usedPIDsVal_Interp x)) links
    (*@union_set _ _ _ gsetPID_elem_of _ (map_to_set (fun k x => pids_insert k (usedPIDsVal_Interp x)) links)*)
end.

Definition allPIDsPool_Interp (Π : ProcessPool) : gset PID :=
  flat_union_Interp (fun '(ι, proc) => pids_insert ι (usedPIDsProc_Interp proc)) (pool_toList Π).

Definition usedPIDsSignal_Interp (s : Signal) : gset PID :=
match s with
 | SMessage e => usedPIDsVal_Interp e
 | SExit r b => usedPIDsVal_Interp r
 | SLink => pids_empty
 | SUnlink => pids_empty
end.

Definition allPIDsEther_Interp (eth : Ether) : gset PID :=
  flat_union_Interp (fun '((ιs, ιd), sigs) => 
    pids_union (pids_insert ιs (pids_singleton ιd)) 
    (flat_union_Interp usedPIDsSignal_Interp sigs)) (ether_toList eth).

Definition usedInPool_Interp : PID -> ProcessPool -> bool :=
  fun pid prs =>
    if pids_member pid (allPIDsPool_Interp prs)
    then true
    else false.

Definition usedInEther_Interp : PID -> Ether -> bool :=
  fun pid eth =>
    if pids_member pid (allPIDsEther_Interp eth)
    then true
    else false.

(**
  Optimisation here: we define equality checking with Val_eqb_strict instead of
  Val_eqb, which is optimised as Prelude.== during extraction. This is possible
  because all uses of Val_eqb_strict in the following functions coincide with
  the use of Val_eqb (while this is not true for arbitrary parameters).
*)
Definition eval_logical_Interp (mname fname : string) (params : list Val) : Redex :=
match convert_string_to_code (mname, fname), params with
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
(** logical xor *)
| BXor, [a; b] =>
   if Val_eqb_strict a ttrue
   then
    if Val_eqb_strict b ttrue
    then RValSeq [ffalse]
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
(** anything else *)
| _ , _ => RExc (undef (VLit (Atom fname)))
end.

Definition eval_check_Interp (mname fname : string) (params : list Val) : Redex := 
match convert_string_to_code (mname, fname), params with
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

Definition eval_funinfo_Interp (params : list Val) : Redex :=
match params with
| [VClos ext id params e;v] =>
  if Val_eqb_strict v (VLit "arity"%string)
  then RValSeq [VLit (Z.of_nat params)]
  else RExc (badarg (VTuple [VLit "fun_info"%string;VClos ext id params e;v]))
| [v1;v2] => RExc (badarg (VTuple [VLit "fun_info"%string;v1;v2]))
| _ => RExc (undef (VLit "fun_info"%string))
end.

Definition eval_Interp (mname : string) (fname : string) (params : list Val) 
   : option (Redex * option SideEffect) :=
match convert_string_to_code (mname, fname) with
| BPlus | BMinus | BMult | BDivide | BRem | BDiv
| BSl   | BSr    | BAbs  | BBNot   | BBAnd | BBOr
| BBXor                                           => Some (eval_arith mname fname params, None)
| BFwrite | BFread                                => Some (eval_io mname fname params)
| BAnd | BOr | BNot | BXor                        => Some (eval_logical_Interp mname fname params, None)
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
| BIsNumber | BIsInteger | BIsAtom | BIsBoolean   => Some (eval_check_Interp mname fname params, None)
| BIsBinary | BIsBitstring | BIsList | BIsTuple
| BIsFunction | BIsMap | BIsPid | BIsPort         => Some (eval_check mname fname params, None)
| BError | BExit | BThrow                         => match (eval_error mname fname params) with
                                                      | Some exc => Some (RExc exc, None)
                                                      | None => None
                                                     end
| BFunInfo                                        => Some (eval_funinfo_Interp params, None)
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

Definition create_result_Interp (ident : FrameIdent) (vl : list Val)
  : option (Redex * option SideEffect) :=
match ident with
| IValues => Some (RValSeq vl, None)
| ITuple => Some (RValSeq [VTuple vl], None)
| IMap => Some (RValSeq [VMap (make_val_map (deflatten_list vl))], None)
| ICall m f => match m, f with
               | VLit (Atom module), VLit (Atom func) =>
                  eval_Interp module func vl
               | _, _ => Some (RExc (badfun (VTuple [m; f])), None)
               end
| IPrimOp f => primop_eval f vl
| IApp (VClos ext id vars e) =>
  if Nat.eqb vars (length vl)
  then Some (RExp (e.[list_subst (convert_to_closlist ext ++ vl) idsubst]), None)
  else Some (RExc (badarity (VClos ext id vars e) (meta_to_cons vl)), None)
| IApp v => Some (RExc (badfun v), None)
| IBin => match construct_bitstring vl with
          | Some val => Some (RValSeq [VBitstring val], None)
          | None => Some (RExc (badarg (VTuple [VLit "eval_bits"%string; VTuple vl])), None) (* TODO: not faithful completely *)
          end
end.
