From CoreErlang.Concurrent Require Export ProcessSemantics NodeSemantics.

Definition dead_lookup : PID -> gmap PID Val -> option Val :=
  fun pid links => links !! pid.

Definition dead_delete : PID -> gmap PID Val -> gmap PID Val :=
  fun pid links => delete pid links.

Definition dead_domain : gmap PID Val -> gset PID :=
  fun links => dom links.

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

Definition pool_singleton : PID -> Process -> gmap PID Process :=
  fun pid proc => {[ pid := proc ]}.

Definition pool_lookup : PID -> gmap PID Process -> option Process :=
  fun pid prs => prs !! pid.

Definition pool_insert : PID -> Process -> gmap PID Process -> gmap PID Process :=
  fun pid proc pool => pid ↦ proc ∥ pool.

Definition pool_toList : gmap PID Process -> list (PID * Process) :=
  fun pool => map_to_list pool.

Definition ether_empty : gmap (PID * PID) (list Signal) := ∅.

Definition ether_lookup : (PID * PID) -> gmap (PID * PID) (list Signal) -> option (list Signal) :=
  fun pids eth => eth !! pids.

Definition ether_insert : (PID * PID) -> (list Signal) -> gmap (PID * PID) (list Signal) ->
                            gmap (PID * PID) (list Signal) :=
  fun pids sigs eth => <[ pids := sigs ]> eth.

Definition ether_toList : gmap (PID * PID) (list Signal) -> list ((PID * PID) * list Signal) :=
  fun eth => map_to_list eth.

Definition ether_domain : gmap (PID * PID) (list Signal) -> gset (PID * PID) :=
  fun eth => dom eth.

Definition ether_pids_toList : gset (PID * PID) -> list (PID * PID) :=
  fun pids => elements pids.

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
     pids_foldWithKey (fun k x acc => pids_union (pids_insert k (usedPIDsValNew x)) acc) 
                      pids_empty links (*<- simple, but no support with theorems *)
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
