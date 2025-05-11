From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Concurrent  Require Import NodeSemantics.

Print LiveProcess.
Print FParams.

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

Print nonArrivalAction.

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

Print arrivalActions.

Compute arrivalActions 2 {[(1, 2) := [SLink]; (3, 4) := [SUnlink; SLink]]}.
Compute arrivalActions 4 {[(1, 2) := [SLink]; (3, 4) := [SUnlink; SLink]]}.
Compute arrivalActions 1 {[(1, 2) := [SLink]; (3, 4) := [SUnlink; SLink]]}.
Compute arrivalActions 2 {[(1, 2) := [SLink]; (3, 2) := [SUnlink; SLink]]}.

Definition deadActions : DeadProcess -> PID -> list Action :=
  fun p selfPID =>
    let links := elements (dom p)
    in (fix f l :=
      match l with
        | [] => []
        | linkPID :: l' => match p !! linkPID with
                             | None => f l' (* shouldn't be possible, since linkPID is in the dom *)
                             | Some reason => ASend selfPID linkPID (SExit reason true) :: f l'
                           end
      end
    ) links.

Compute deadActions {[2 := normal; 3 := kill; 4 := killed]} 1.

Definition possibleActions : Process -> Ether -> PID -> PID -> list Action :=
  fun p eth selfPID freshPID =>
    match p with
      | inl p' => nonArrivalAction p' selfPID freshPID :: arrivalActions selfPID eth
      | inr p' => deadActions p' selfPID
    end.

Inductive RRConfig : Type :=
  | RRConf : list PID -> nat -> RRConfig.

Definition nextPIDConf (conf : RRConfig) : (PID * RRConfig) :=
  match conf with
  | RRConf l n =>
      if S n <? length l
      then (nth n l 0, RRConf l (S n))
      else (nth n l 0, RRConf l 0)
  end.

Definition insertToConf (conf : RRConfig) (p : PID) : RRConfig :=
  match conf with
  | RRConf l n => RRConf (p :: l) (S n)
  end.

Definition newPIDByAction: RRConfig -> Action -> RRConfig :=
  fun conf a =>
    match a with
    | ASpawn newPID _ _ _ => insertToConf conf newPID
    | _ => conf
    end.

Definition unavailablePIDs: Node -> gset PID :=
  fun '(eth, prs) =>
    (allPIDsEther eth) ∪ (allPIDsPool prs).

Definition makeInitialNodeConf: Process -> Node * RRConfig :=
  fun p =>
    let initPID := fresh (usedPIDsProc p) in
    ((∅, {[initPID := p]}), RRConf [initPID] 0).

Print LiveProcess.
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
    (° EApp (˝ VFunId (0, 1)) [˝ VLit 3%Z]).

Close Scope string_scope.

Definition ex_Process : Process :=
  inl ([], ex_Redex, emptyBox, ∅, false).

Compute makeInitialNodeConf ex_Process.

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

Print nodeFullyQualifiedStep.

Definition nodeSimpleStep: Node -> PID + (PID * PID) -> option (Node * Action) :=
  fun '(eth, prs) op =>
    match op with
    | inl selfPID => 
      match prs !! selfPID with
      | Some (inl p) => 
        let a := nonArrivalAction p selfPID (fresh (unavailablePIDs (eth, prs))) in
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
    | inr (srcPID, dstPID) => 
      match eth !! (srcPID, dstPID) with
      | Some (v :: vs) =>
        let a := AArrive srcPID dstPID v in
        match interProcessStepFunc (eth, prs) a dstPID with
        | Some node' => Some (node', a)
        | _ => None
        end
      | _ => None
      end
    end.

Print nodeSimpleStep.

Definition isDead: Node -> PID -> bool :=
  fun '(eth, prs) pid =>
    match prs !! pid with
    | Some (inr p) => true
    | _ => false
    end.

Definition isTotallyDead: Node -> PID -> bool :=
  fun '(eth, prs) pid =>
    match prs !! pid with
    | Some (inr p) => map_size p =? 0
    | _ => false
    end.









