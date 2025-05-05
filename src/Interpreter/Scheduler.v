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

(*
func-actions(p, ether, config (selfpid, freshpid)) = list(actions)


constrcut action(action, p, optional config)

*)

(* 
  Implementing round robin (and other possible schedulings) using coinductive types
  
  Idea: list of PIDs, loop over them ==> Stream
  The list needs to be non-empty, otherwise the Stream won't be productive
 *)

Inductive NE_PIDList :=
  | SinglePID (p : PID)
  | ConsPID (p : PID) (pl : NE_PIDList).

Definition addToStart (np : PID) (l : NE_PIDList) : NE_PIDList :=
  ConsPID np l.

Compute addToStart 3 (ConsPID 42 (ConsPID 39 (SinglePID 21))).

(* also stored: next loop iteration + full loop 
   this is needed for adding new PID-s and deleting them for the next loop
*)
CoInductive PidStream : Type :=
  | PidCons : PID -> NE_PIDList -> NE_PIDList -> PidStream -> PidStream.

CoFixpoint round_robin (l full: NE_PIDList) : PidStream :=
  match l with
  | SinglePID p => PidCons p full full (round_robin full full)
  | ConsPID p l' => PidCons p l' full (round_robin l' full)
  end.

Definition round_robin_start (l : NE_PIDList) : PidStream :=
  round_robin l l.

Definition pidStreamHead (s : PidStream) : PID :=
  match s with
  | PidCons h _ _ _ => h
  end.

Definition pidStreamTail (s : PidStream) : PidStream :=
  match s with
  | PidCons _ _ _ t => t
  end.

Fixpoint takePid (n : nat) (s : PidStream) : (list PID * PidStream) :=
  match n with
  | 0 => ([], s)
  | S n' => 
     let (lRest, nStream) := (takePid n' (pidStreamTail s)) in
     (pidStreamHead s :: lRest, nStream)
  end.

Definition Ex_PidStream := 
  round_robin_start (ConsPID 1 (ConsPID 2 (SinglePID 3))).

Compute takePid 10 Ex_PidStream.

(* this function adds a new PID to the loop *)

Definition addPidToRoundRobin (p : PID) (s : PidStream) : PidStream :=
  match s with
  | PidCons h curr full _ => 
      let nFull := addToStart p full in
      PidCons h curr nFull (round_robin curr nFull)
  end.

Definition takeTwelveStepsThenAddFourtytwoThenTakeTwelveSteps : (list PID * PidStream) :=
  let (start, newStream) := takePid 12 Ex_PidStream in
  let newStreamAdded := addPidToRoundRobin 42 newStream in
  let (finish, finishStream) := takePid 12 newStreamAdded in
  (start ++ finish, finishStream).

Compute takeTwelveStepsThenAddFourtytwoThenTakeTwelveSteps.

Compute nth_error [1;2;3] 4.
Print nth.

Inductive RRConfig : Type :=
  | RRConf : list PID -> nat -> RRConfig.

Definition nextPIDConf (conf : RRConfig) : (PID * RRConfig) :=
  match conf with
  | RRConf l n =>
      if S n <? length l
      then (nth n l 0, RRConf l (S n))
      else (nth n l 0, RRConf l 0)
  end.















