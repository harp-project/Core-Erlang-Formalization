From CoreErlang.Concurrent Require Export NodeSemanticsLemmas.

Definition ACTIONCLOSED (a : Action) :=
  match a with
  | ASend _ _ s => SIGCLOSED s
  | AArrive _ _ s => SIGCLOSED s
  | ASpawn _ vl1 vl2 _ => VALCLOSED vl1 /\ VALCLOSED vl2
  | _ => True
  end.

Definition MBCLOSED (mb : Mailbox) :=
  match mb with
  | (mb1, mb2) => Forall (fun v1 => VALCLOSED v1) mb1 /\ Forall (fun v2 => VALCLOSED v2) mb2
  end.

Definition PROCCLOSED (p : Process) :=
  match p with
  | inl (fs, r, mb, links, flag) => FSCLOSED fs /\ REDCLOSED r /\ MBCLOSED mb
  | inr (links) => Forall (fun '(_, v) => VALCLOSED v) (map_to_list links)
  end.

Definition POOLCLOSED (pp : ProcessPool) :=
  Forall (fun '(_, pr) => PROCCLOSED pr) (map_to_list pp).

Definition ETHERCLOSED (eth : Ether) :=
  Forall (fun '(_, sl) => Forall (fun s => SIGCLOSED s) sl) (map_to_list eth).

Definition NODECLOSED (n : Node) :=
  match n with
  | (eth, pp) => POOLCLOSED pp /\ ETHERCLOSED eth
  end.
