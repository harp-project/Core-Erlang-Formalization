From CoreErlang.Interpreter Require Import StepFunctions.

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

Print nonArrivalStep.

(*
func-actions(p, ether, config (selfpid, freshpid)) = list(actions)


constrcut action(action, p, optional config)

*)