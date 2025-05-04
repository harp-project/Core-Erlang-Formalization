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