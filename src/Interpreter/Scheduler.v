From CoreErlang.Interpreter Require Import StepFunctions InterpreterAux.
From CoreErlang.Concurrent  Require Import NodeSemantics.

Definition nonArrivalAction : LiveProcess -> PID -> PID -> Action :=
  fun '(fs, e, mb, links, flag) selfPID freshPID => 
    match fs with
      | [] => 
        match e with
          | RValSeq [_] => ε
          | RExc _ => ε
          | _ => τ
        end
      | FParams ident lval [] :: _ => 
        match ident with
          | ICall erlang fn => 
            match fn with
              | send => 
                match lval with
                  | [VPid destPID] => 
                    match e with
                      | RValSeq [v] => ASend selfPID destPID (SMessage v)
                      | _ => τ
                    end
                  | _ => τ
                end
              | exit =>
                match lval with
                  | [VPid destPID] =>
                    match e with
                      | RValSeq [v] => ASend selfPID destPID (SExit v false)
                      | _ => τ
                    end
                  | _ => τ
                end
              | link => 
                match lval with
                  | [] => 
                    match e with
                      | RValSeq [VPid destPID] => ASend selfPID destPID SLink
                      | _ => τ
                    end
                  | _ => τ
                end
              | unlink =>
                match lval with
                  | [] => 
                    match e with
                      | RValSeq [VPid destPID] => ASend selfPID destPID SUnlink
                      | _ => τ
                    end
                  | _ => τ
                end
              | self =>
                match lval with
                  | [] =>
                    match e with
                      | RBox => ASelf selfPID
                      | _ => τ
                    end
                  | _ => τ
                end
              | spawn =>
                match lval with
                  | [VClos ext id vars e'] =>
                    match e with
                      | RValSeq [l] => ASpawn freshPID (VClos ext id vars e') l false
                      | _ => τ
                    end
                  | _ => τ
                end
              | spawn_link =>
                match lval with
                  | [VClos ext id vars e'] =>
                    match e with
                      | RValSeq [l] => ASpawn freshPID (VClos ext id vars e') l true
                      | _ => τ
                    end
                  | _ => τ
                end
              | process_flag =>
                match lval with
                  | [VLit "trap_exit"%string] =>
                    match e with
                      | RValSeq [v] =>
                        match bool_from_lit v with
                          | Some _ => ε
                          | None => τ
                        end
                      | _ => τ
                    end
                  | _ => τ
                end
              | _ => τ
            end
          | IPrimOp "recv_peek_message" =>
            match e with
              | RBox =>
                match peekMessage mb with
                  | Some _ => τ
                  | _ => ε
                end
              | _ => τ
            end
          | _ => τ
        end
      | _ => τ
    end.

Definition arrivalActions : (* LiveProcess -> *) PID -> Ether -> list Action :=
  fun destPID eth =>
    let msgs := elements (dom eth)
    in (fix f l := 
      match l with
        | [] => []
        | (src, dst) :: l' => 
          if dst =? destPID
          then match eth !! (src, dst) with
                 | None => f l' (* shouldn't be possible, since (src, dst) is in the domain *)
                 | Some signals => ((fix g sl :=
                                      match sl with
                                        | [] => []
                                        | s :: _ => [AArrive src dst s]
                                      end
                                   ) signals) ++ f l'
               end
          else f l'
      end) msgs.

Definition deadActions : DeadProcess -> PID -> list Action :=
  fun p selfPID =>
    let links := pids_toList (dead_domain p)
    in (fix f l :=
      match l with
        | [] => []
        | linkPID :: l' => match dead_lookup linkPID p with
                             | None => f l' (* shouldn't be possible, since linkPID is in the dom *)
                             | Some reason => ASend selfPID linkPID (SExit reason true) :: f l'
                           end
      end
    ) links.

Definition possibleActions : Process -> Ether -> PID -> PID -> list Action :=
  fun p eth selfPID freshPID =>
    match p with
      | inl p' => nonArrivalAction p' selfPID freshPID :: arrivalActions selfPID eth
      | inr p' => deadActions p' selfPID
    end.

Inductive ne_list (A : Type) : Type :=
| ne_single : A → ne_list A
| ne_cons : A → ne_list A → ne_list A.

Arguments ne_single {A} _.
Arguments ne_cons {A} _ _.

Fixpoint nth_error_ne {A : Type} (l : ne_list A) (n : nat) : option A :=
  match n with
  | 0 => match l with
         | ne_single x => Some x
         | ne_cons x _ => Some x
         end
  | S n' => match l with
            | ne_single _ => None
            | ne_cons _ l' => nth_error_ne l' n'
            end
  end.

Fixpoint length_ne {A : Type} (l : ne_list A) : nat :=
  match l with
  | ne_single _ => 1
  | ne_cons _ l' => S (length_ne l')
  end.

Fixpoint delete_nth_ne {A : Type} (l : ne_list A) (n : nat) : option (ne_list A) :=
  match n with
  | 0 => match l with
         | ne_single _ => None
         | ne_cons _ l' => Some l'
         end
  | S n' => match l with
            | ne_single _ => None
            | ne_cons x l' => 
                match l' with
                | ne_single _ =>
                    match n' with
                    | 0 => Some (ne_single x)
                    | _ => None
                    end
                | ne_cons _ _ =>
                    match delete_nth_ne l' n' with
                    | Some l'' => Some (ne_cons x l'')
                    | None => None
                    end
                end
            end
  end.

Inductive RRConfig : Type :=
  | RREmpty : RRConfig
  | RRConf : ne_list PID -> nat -> RRConfig.

Definition currPID (conf : RRConfig) : option PID :=
  match conf with
  | RRConf l n => nth_error_ne l n
  | RREmpty => None
  end.

Definition nextConf (conf : RRConfig) : RRConfig :=
  match conf with
  | RREmpty => RREmpty
  | RRConf l n =>
      if S n <? length_ne l
      then RRConf l (S n)
      else RRConf l 0
  end.

Definition insertToConf (conf : RRConfig) (p : PID) : RRConfig :=
  match conf with
  | RREmpty => RRConf (ne_single p) 0
  | RRConf l n => RRConf (ne_cons p l) (S n)
  end.

Definition newConfByAction: RRConfig -> Action -> RRConfig :=
  fun conf a =>
    match a with
    | ASpawn newPID _ _ _ => insertToConf conf newPID
    | _ => conf
    end.

Definition delCurrFromConf: RRConfig -> RRConfig :=
  fun conf =>
    match conf with
    | RREmpty => RREmpty
    | RRConf l n => 
      match delete_nth_ne l n with
      | Some l' => 
        match n with
        | 0 => RRConf l' (pred (length_ne l'))
        | S n' => RRConf l' n'
        end
      | _ => RREmpty
      end
    end.

Definition unavailablePIDs: Node -> gset PID :=
  fun '(eth, prs) =>
    pids_union (allPIDsEtherNew eth) (allPIDsPoolNew prs).

Definition makeInitialNodeConf: Redex -> Node * RRConfig :=
  fun r =>
    let p := inl ([], r, emptyBox, pids_empty, false) in
    let initPID := pids_fresh (usedPIDsProcNew p) in
    ((ether_empty, pool_singleton initPID p), RRConf (ne_single initPID) 0).

Open Scope string_scope.

Definition ex_Redex : Redex :=
° ELetRec
    [(1,
      ° ECase (˝ VVar 1)
          [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z);
           ([PVar], ˝ VLit "true",
            ° ELet 1
                (° EApp (˝ VFunId (1, 1))
                     [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]])
                (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])]
    (° EApp (˝ VFunId (0, 1)) [˝ VLit 30%Z]).

Close Scope string_scope.

Definition ex_Process : Process :=
  inl ([], ex_Redex, emptyBox, pids_empty, false).

(** TODO: This way of doing things in inefficient.
          To make these 2 function more efficient, take out
          the functions constructing the actions and the interProcessStepFunc
          and incorporate everything they do in these functions. *)

Inductive Operation :=
  | LiveNonArrival (selfPID : PID) : Operation
  | LiveArrival (srcPID : PID) (dstPID : PID) : Operation
  | DeadSending (srcPID : PID) (dstPID : PID) : Operation
  .

Definition nodeFullyQualifiedStep: Node -> Operation -> option (Node * Action) :=
  fun '(eth, prs) op =>
    match op with
    | LiveNonArrival selfPID => 
      match prs !! selfPID with
      | Some (inl p) => 
        let a := nonArrivalAction p selfPID (fresh (unavailablePIDs (eth, prs))) in
        match interProcessStepFunc (eth, prs) a selfPID with
        | Some node' => Some (node', a)
        | _ => None
        end
      | _ => None
      end
    | LiveArrival srcPID dstPID => 
      match eth !! (srcPID, dstPID) with
      | Some (v :: vs) =>
        let a := AArrive srcPID dstPID v in
        match interProcessStepFunc (eth, prs) a dstPID with
        | Some node' => Some (node', a)
        | _ => None
        end
      | _ => None
      end
    | DeadSending srcPID dstPID => 
      match prs !! srcPID with
      | Some (inr p) => 
        match p !! dstPID with
        | Some reason =>
          let a := ASend srcPID dstPID (SExit reason true) in
          match interProcessStepFunc (eth, prs) a srcPID with
          | Some node' => Some (node', a)
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    end.

Definition nodeSimpleStep: Node -> PID + (PID * PID) -> option (Node * Action) :=
  fun '(eth, prs) op =>
    match op with
    | inl selfPID => 
      match pool_lookup selfPID prs with
      | Some (inl p) => 
        let a := nonArrivalAction p selfPID (pids_fresh (unavailablePIDs (eth, prs))) in
        match interProcessStepFunc (eth, prs) a selfPID with
        | Some node' => Some (node', a)
        | _ => None
        end
      | Some (inr p) =>
        match deadActions p selfPID with
        | a :: _ =>
          match interProcessStepFunc (eth, prs) a selfPID with
          | Some node' => Some (node', a)
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    (* deprecate *)
    | inr (srcPID, dstPID) => 
      match ether_lookup (srcPID, dstPID) eth with
      | Some (v :: vs) =>
        let a := AArrive srcPID dstPID v in
        match interProcessStepFunc (eth, prs) a dstPID with
        | Some node' => Some (node', a)
        | _ => None
        end
      | _ => None
      end
    end.

(* Node ->
   Highest available PID ->
   Options (SelfPID or SelfPID * DestPID) ->
   Maybe (Node * Action * Highest available PID)*)

(*
Definition nodeSimpleStepExperimental: Node -> PID -> PID + (PID * PID) -> option (Node * Action * PID) :=
  fun '(eth, prs) haPID op =>
    match op with
    | inl selfPID => 
      match prs !! selfPID with
      | Some (inl p) => 
        let a := nonArrivalAction p selfPID haPID in
        match interProcessStepFunc (eth, prs) a selfPID with
        | Some (eth', prs') =>
          match a with
          | (ASpawn _ v1  v2 _) =>
            match prs' !! haPID with
            | Some (inl newP) => let haPID' := (fresh ({[haPID]} ∪ (usedPIDsProc (inl newP)))) in
              Some((eth', prs'), a, haPID')
            | _ => None (* Impossible case though *)
            end
          | (ASend _ destPID _) => if haPID <=? destPID
                                 then Some ((eth', prs'), a, (S destPID) : PID)
                                 else Some ((eth', prs'), a, haPID)
          | _ => Some ((eth', prs'), a, haPID)
          end
        | _ => None
        end
      | Some (inr p) =>
        match deadActions p selfPID with
        | a :: _ =>
          match interProcessStepFunc (eth, prs) a selfPID with
          | Some node' => Some (node', a, haPID)
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | inr (srcPID, dstPID) => 
      match eth !! (srcPID, dstPID) with
      | Some (v :: vs) =>
        let a := AArrive srcPID dstPID v in
        match interProcessStepFunc (eth, prs) a dstPID with
        | Some node' => Some (node', a, haPID)
        | _ => None
        end
      | _ => None
      end
    end.
*)

Definition isDead: Node -> PID -> bool :=
  fun '(eth, prs) pid =>
    match pool_lookup pid prs with
    | Some (inr p) => true
    | _ => false
    end.

Definition isTotallyDead: Node -> PID -> bool :=
  fun '(eth, prs) pid =>
    match pool_lookup pid prs with
    | Some (inr p) => map_size p =? 0
    | _ => false
    end.

Definition etherNonEmpty: Node -> list (PID * PID) :=
  fun '(eth, prs) =>
    List.filter
      (fun k => match ether_lookup k eth with
                | Some (_ :: _) => true
                | _ => false
                end)
      (ether_pids_toList (ether_domain eth)).







