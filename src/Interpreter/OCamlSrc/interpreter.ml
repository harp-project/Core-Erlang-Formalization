open CoqExtraction

(* Mutable state to hold ((node, rr_config), pid) *)
type node_state = {
  mutable p_node : node;
  mutable conf : rRConfig;
  mutable hipid : pID;
  mutable msgs : (pID * pID) list;
}

let example_for_exec = makeInitialNodeConf (RExp (EExp testlife3))

(* Create initial state *)
let state = {
  p_node = fst (fst (fst example_for_exec));
  conf = snd (fst (fst example_for_exec));
  hipid = snd (fst example_for_exec);
  msgs = snd example_for_exec;
}

let rest = function
  | [] -> []
  | x :: xs -> xs

let action_to_msg_pids act =
  match act with
  | ASend (ps, pd, _) -> Some (ps, pd)
  | _ -> None

let string_of_lit l =
  match l with
  | Atom chars ->
      "Atom('" ^ (String.concat "" (List.map (String.make 1) chars)) ^ "')"
  | Integer i ->
      Printf.sprintf "Integer(%d)" i

let rec string_of_val v =
  match v with
  | VNil -> "VNil"
  | VLit lit -> "VLit(" ^ string_of_lit lit ^ ")"
  | VPid pid -> Printf.sprintf "VPid(P%d)" pid
  | VCons (v1, v2) ->
      "VCons(" ^ string_of_val v1 ^ ", " ^ string_of_val v2 ^ ")"
  | VTuple lst ->
      "VTuple([" ^
      String.concat ", " (List.map string_of_val lst) ^
      "])"
  | VMap kvs ->
      "VMap({" ^
      String.concat ", "
        (List.map (fun (k, v) ->
           string_of_val k ^ " -> " ^ string_of_val v
         ) kvs) ^
      "})"
  | VVar var_id -> Printf.sprintf "VVar(x%d)" var_id
  | VFunId (i, j) -> Printf.sprintf "VFunId(%d, %d)" i j
  | VClos _ -> "VClos(<fun>)"

let string_of_signal s =
  match s with
  | SMessage v -> "SMessage " ^ string_of_val v
  | SExit (v, b) -> "SExit " ^ string_of_val v ^ " " ^ string_of_bool b
  | SLink -> "SLink"
  | SUnlink -> "SUnlink"

let display_action pid = function
  | Coq__UU03c4_ -> ()
  | Coq__UU03b5_ ->
      Printf.printf "(P%d) eps\n" pid
  | ASelf _ -> ()
  | ASend (ps, pd, signal) ->
      Printf.printf "(P%d) ==[ (P%d) ]==>\n\t%s\n"
        ps pd (string_of_signal signal)
  | AArrive (ps, pd, signal) ->
      Printf.printf "(P%d) <==[ (P%d) ]==\n\t%s\n"
        pd ps (string_of_signal signal)
  | ASpawn (p, _, _, _) ->
      Printf.printf "(P%d) --{spawned}--> (P%d)\n" pid p

(* Eval K steps *)
let rec eval_k_steps k =
  if k = 0 then finish_off_if_dead ()
  else
    match currPID state.conf with
    | None -> ()
    | Some pid ->
      if isDead state.p_node pid then
        finish_off_if_dead ()
      else
        match interProcessStepFuncFast state.p_node state.hipid (Inl pid) with
        | None -> ()
        | Some ((node', action), hipid') ->
          display_action pid action;
          state.p_node <- node';
          state.conf <- newConfByAction state.conf action;
          state.hipid <- hipid';
          match action_to_msg_pids action with
          | Some msg -> 
            state.msgs <- msg :: state.msgs;
            eval_k_steps (k - 1)
          | None -> 
            eval_k_steps (k - 1)

(* Finish off if dead *)
and finish_off_if_dead () =
  match currPID state.conf with
  | None -> ()
  | Some pid ->
    if isDead state.p_node pid then
      if isTotallyDead state.p_node pid then
        state.conf <- delCurrFromConf state.conf
      else
        (match interProcessStepFuncFast state.p_node state.hipid (Inl pid) with
        | None -> ()
        | Some ((node', action), hipid') ->
          display_action pid action;
          state.p_node <- node';
          state.hipid <- hipid';
          finish_off_if_dead ())
    else ()

(* Deliver a single signal *)
let deliver_signal (src, dst) =
  match interProcessStepFuncFast state.p_node state.hipid (Inr (src, dst)) with
  | None -> ()
  | Some ((node', action), hipid') ->
    display_action dst action;
    state.p_node <- node';
    state.hipid <- hipid'

(* Deliver all signals *)
let rec deliver_all_signals () =
  match state.msgs with
  | [] -> ()
  | x :: xs ->
    deliver_signal x;
    state.msgs <- xs;
    deliver_all_signals ()

(* Empty ether *)
let empty_ether () =
  (*let signals = etherNonEmpty state.p_node in*)
  deliver_all_signals ()

(* Eval program main loop *)
let rec eval_program k n =
  if n = 10_000_000 then ()
  else
    match currPID state.conf with
    | None -> ()
    | Some _ ->
      eval_k_steps k;
      empty_ether ();
      state.conf <- nextConf state.conf;
      eval_program k (n + 1)

(* Entry point *)
let () =
  (* Initialize state *)
  state.p_node <- fst (fst (fst example_for_exec));
  state.conf <- snd (fst (fst example_for_exec));
  state.hipid <- snd (fst example_for_exec);
  state.msgs <- snd example_for_exec;

  eval_program 10_000 0;

  (* Print final state, or whatever you want *)
  print_endline "Program finished"

