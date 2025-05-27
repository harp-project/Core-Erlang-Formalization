From CoreErlang.Concurrent Require Export ProcessSemantics NodeSemantics.

Definition link_insert : PID -> gset PID -> gset PID :=
  fun new links => links ∪ {[new]}.

Definition link_delete : PID -> gset PID -> gset PID :=
  fun to_del links => links ∖ {[to_del]}.

Definition link_member : PID -> gset PID -> bool :=
  fun source links => 
    if gset_elem_of_dec source links
    then true
    else false.

Definition link_empty : gset PID := ∅.

Definition dead_lookup : PID -> gmap PID Val -> option Val :=
  fun pid links => links !! pid.

Definition dead_delete : PID -> gmap PID Val -> gmap PID Val :=
  fun pid links => delete pid links.

Definition dead_domain : gmap PID Val -> gset PID :=
  fun links => dom links.

Definition link_set_to_map : Val -> gset PID -> gmap PID Val :=
  fun reason links => gset_to_gmap reason links.

Definition pids_member : PID -> gset PID -> bool :=
  fun pid pids =>
    if gset_elem_of_dec pid pids
    then true
    else false.

Definition pids_union : gset PID -> gset PID -> gset PID :=
  fun pids1 pids2 => pids1 ∪ pids2.

Definition pids_toList : gset PID -> list PID :=
  fun pids => elements pids.

Definition pids_fresh : gset PID -> PID :=
  fun pids => fresh pids.

Definition pool_singleton : PID -> Process -> gmap PID Process :=
  fun pid proc => {[ pid := proc ]}.

Definition pool_lookup : PID -> gmap PID Process -> option Process :=
  fun pid prs => prs !! pid.

Definition pool_insert : PID -> Process -> gmap PID Process -> gmap PID Process :=
  fun pid proc pool => pid ↦ proc ∥ pool.

Definition ether_empty : gmap (PID * PID) (list Signal) := ∅.

Definition ether_lookup : (PID * PID) -> gmap (PID * PID) (list Signal) -> option (list Signal) :=
  fun pids eth => eth !! pids.

Definition ether_insert : (PID * PID) -> (list Signal) -> gmap (PID * PID) (list Signal) ->
                            gmap (PID * PID) (list Signal) :=
  fun pids sigs eth => <[ pids := sigs ]> eth.

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

(** TODO: 
    allPIDsPool
      usedPIDsProc
        usedPIDsStack
          usedPIDsFrame
            usedPIDsExp
              usedPIDsVal
              usedPIDsNVal
        usedPIDsRed
    allPIDsEther
      usedPIDsSignal *)