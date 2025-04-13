From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang.Concurrent Require Export ProcessSemantics.
From CoreErlang.Interpreter Require Export EqualityFunctions.

Definition step_func : FrameStack -> Redex -> option (FrameStack * Redex) :=
  fun fs r =>
    match r with
      (* cool_value *)
      | ˝v => Some (fs, RValSeq [v])
      
      | RValSeq vs =>
          match fs with
          (* eval_cool_let *)
          | (FLet l e2)::xs => match length vs =? l with
                               | true => Some ( xs, RExp (e2.[ list_subst vs idsubst ]) )
                               | _ => None
                               end
          
          (* eval_step_case_match and eval_step_case_not_match *)
          | (FCase1 ((lp,e1,e2)::l))::xs => 
            match match_pattern_list lp vs with
            | Some vs' => 
                Some ((FCase2 vs e2.[list_subst vs' idsubst] l)::xs, 
                RExp (e1.[list_subst vs' idsubst]) )
            | None => Some ( (FCase1 l)::xs, RValSeq vs )
            end
          
          (* eval_cool_case_empty *)
          | (FCase1 [])::xs => Some ( xs, RExc if_clause )
          
          (* eval_cool_try_ok *)
          | (FTry vl1 e2 _ e3)::xs => match vl1 =? length vs with
                                      | true => Some ( xs, RExp e2.[ list_subst vs idsubst ] )
                                      | _ => None
                                      end
      
      (* | RValSeq [v] => *)
          (* eval_step_params *)
          | FParams ident vl (e :: el) :: xs => 
              match vs with
              | [v] => Some (FParams ident (vl ++ [v]) el :: xs , RExp e)
              | _ => None
              end
          
          (* eval_cool_params *)
          | FParams ident vl [] ::xs => 
              match vs with
              | [v] => match create_result ident (vl ++ [v]) with
                       | Some (res, l) => Some (xs, res)
                       | None => None
                       end
              | _ => None
              end
          
          (* eval_heat_call_fun *)
          | FCallMod f el :: xs => 
              match vs with
              | [v] => Some ( FCallFun v el :: xs, RExp f )
              | _ => None
              end
          
          (* eval_heat_call_params *)
          | FCallFun m el :: xs => 
              match vs with
              | [v] => Some ( (FParams (ICall m v) [] el)::xs, RBox )
              | _ => None
              end
          
          (* eval_heat_app2 *)
          | FApp1 el :: xs => 
              match vs with
              | [v] => Some ( (FParams (IApp v) [] el)::xs, RBox )
              | _ => None
              end
          
          (* eval_cool_cons_1 *)
          | (FCons1 hd )::xs => 
              match vs with
              | [v] => Some ( (FCons2 v)::xs, RExp hd )
              | _ => None
              end
          
          (* eval_cool_cons_2 *)
          | (FCons2 tl)::xs => 
              match vs with 
              | [v] => Some ( xs, RValSeq [VCons v tl] )
              | _ => None
              end
          
          (* eval_cool_seq *)
          | (FSeq e2)::xs => 
              match vs with
              | [v] => Some ( xs, RExp e2 )
              | _ => None
              end
          
          (* eval_step_case_true and eval_step_case_false *)
          | (FCase2 vs' e' l)::xs => 
              match vs with
              | [VLit (Atom "true")] => Some ( xs, RExp e' )
              | [VLit (Atom "false")] => Some ((FCase1 l)::xs, RValSeq vs' )
              | _ => None
              end
          
          | _ => None
          end
      
      (* eval_heat_values *)
      | EValues el => Some ((FParams IValues [] el)::fs , RBox)
      
      (* eval_heat_tuple *)
      | ETuple el => Some ((FParams ITuple [] el)::fs, RBox )
    
      (* eval_heat_map_0 *)
      | EMap [] => Some (fs, RValSeq [VMap []] )
      
      (* eval_heat_map *)
      | EMap ((e1, e2) :: el) =>
          Some ((FParams IMap [] (e2 :: flatten_list el))::fs, RExp e1 )
          
      (* eval_heat_call_mod *)
      | ECall m f el => Some ( FCallMod f el :: fs, RExp m )
      
      (* eval_heat_primop *)
      | EPrimOp f el => Some ( (FParams (IPrimOp f) [] el)::fs, RBox )
      
      (* eval_heat_app *)
      | EApp e l => Some (FApp1 l :: fs, RExp e)
      
      (* eval_heat_cons *)
      | ECons hd tl => Some ( (FCons1 hd)::fs, RExp tl )
      
      (* eval_heat_let *)
      | ELet l e1 e2 => Some ( (FLet l e2)::fs, RExp e1 )
      
      (* eval_heat_seq *)
      | ESeq e1 e2 => Some ( (FSeq e2)::fs, RExp e1 )

      (* eval_cool_fun *)
      | EFun vl e => Some (fs, RValSeq [ VClos [] 0 vl e ])

      (* eval_heat_case *)
      | ECase e l => Some ( (FCase1 l)::fs, RExp e )
      
      (* eval_heat_letrec *)
      | ELetRec l e => let lc := convert_to_closlist (map (fun '(x,y) => (0,x,y)) l) in
                           Some (fs, RExp e.[list_subst lc idsubst] )
      
      (* eval_heat_try *)
      | ETry e1 vl1 e2 vl2 e3 => Some ( (FTry vl1 e2 vl2 e3)::fs, RExp e1 )
      
      | RBox => match fs with
                (* eval_step_params_0 *)
                | FParams ident vl (e::el) ::xs => match ident with
                                              | IMap => None
                                              | _ => Some (FParams ident vl el :: xs, RExp e)
                                              end
                (* eval_cool_params_0 *)
                | FParams ident vl [] ::xs => match ident with
                                              | IMap => None
                                              | _ => match create_result ident vl with
                                                     | Some (res, l) => Some (xs, res)
                                                     | None => None
                                                     end
                                              end
                | _ => None
                end
      
      | RExc (class, reason, details) =>
          (* eval_cool_try_err *)
          match fs with
          | (FTry vl1 e2 3 e3)::xs =>
              Some ( xs, RExp e3.[ 
                list_subst [exclass_to_value class; reason; details] idsubst ] )
          
          (* eval_prop_exc *)
          | F::xs => match isPropagatable F with
                     | true => Some ( xs, RExc (class, reason, details) )
                     | _ => None
                     end
          
          | _ => None
          end
    end.

(* ------------------------------------------------------------- *)

Definition plsASendSExit :
  PID -> Val -> bool ->
  Process -> option Process :=

  fun ι v is_dead p =>
    if is_dead
    (* p_dead *)
    then
      match p with
      | inr links =>
        match (links !! ι) with
        | Some reason =>
          if Val_eqb_strict reason v
           then Some (inr (delete ι links))
           else None
        | _ => None
        end
      | _ => None
      end
    (* p_exit *)
    else
      match p with
      | inl (FParams (ICall erlang exit) [VPid ι'] [] :: fs, RValSeq [v'], mb, links, flag) =>
        if (Val_eqb_strict v' v && (ι' =? ι))
          then Some (inl (fs, RValSeq [ttrue], mb, links, flag))
          else None
      | _ => None
      end.

Definition processLocalStepASend : PID -> Signal -> Process ->
  option Process :=

  fun ι msg p =>
    match msg with
    (* p_send *)
    | SMessage v =>
      match p with 
      | inl (FParams (ICall erlang send) [VPid ι'] [] :: fs, RValSeq [v'], mb, links, flag) =>
        if Val_eqb_strict v' v && (ι' =? ι)
          then Some (inl (fs, RValSeq [v], mb, links, flag))
          else None
      | _ => None
      end
    (* p_link *)
    | SLink =>
      match p with
      | inl (FParams (ICall erlang link) [] [] :: fs, RValSeq [VPid ι'], mb, links, flag) =>
        if (ι' =? ι)
          then Some (inl (fs, RValSeq [ok], mb, {[ι]} ∪ links, flag))
          else None
      | _ => None
      end
    (* p_unlink *)
    | SUnlink =>
      match p with
      | inl (FParams (ICall erlang unlink) [] [] :: fs, RValSeq [VPid ι'], mb, links, flag) =>
        if (ι' =? ι)
          then Some (inl (fs, RValSeq [ok], mb, links ∖ {[ι]}, flag))
          else None
      | _ => None
      end
    (* p_dead and p_exit *)
    | SExit v is_dead => plsASendSExit ι v is_dead p
    end.

(* ------------------------------------------------------------- *)

Definition plsAArriveSExit :
  PID -> PID -> Val -> bool ->
  Process -> option Process :=
  
  fun source dest reason b p => 
    match p with
    | inl (fs, e, mb, links, flag) =>
      if flag
      then 
        if b
        then 
          if gset_elem_of_dec source links
          then Some (inl (fs, e, mailboxPush mb (VTuple [EXIT; VPid source; reason]), links, true))
          else 
            if dest =? source
            then None
            else Some p
        else
          if reason =ᵥ kill
          then Some (inr (gset_to_gmap killed links))
          else Some (inl (fs, e, mailboxPush mb (VTuple [EXIT; VPid source; reason]), links, true))
      else 
        if dest =? source
        then 
          if b
          then 
            if reason =ᵥ normal
            then Some (inr (gset_to_gmap normal links))
            else
              if gset_elem_of_dec source links
              then Some (inr (gset_to_gmap reason links))
              else None
          else
            if reason =ᵥ kill
            then Some (inr (gset_to_gmap killed links))
            else Some (inr (gset_to_gmap reason links))
        else
          if b
          then
            if reason =ᵥ normal
            then Some p
            else 
              if gset_elem_of_dec source links
              then Some (inr (gset_to_gmap reason links))
              else Some p
          else
            if reason =ᵥ normal
            then Some p
            else
              if reason =ᵥ kill
              then Some (inr (gset_to_gmap killed links))
              else Some (inr (gset_to_gmap reason links))
    | _ => None
    end.

Definition processLocalStepAArrive : PID -> PID -> Signal -> Process -> 
  option Process :=

  fun source dest msg p =>
    match msg with
    (* p_arrive *)
    | SMessage v => 
      match p with
      | inl (fs, e, mb, links, flag) => Some (inl (fs, e, mailboxPush mb v, links, flag))
      | _ => None
      end
    (* p_exit_drop, p_exit_terminate and p_exit_convert *)
    | SExit reason b => plsAArriveSExit source dest reason b p
    (* p_link_arrived *)
    | SLink => 
      match p with
      | inl (fs, e, mb, links, flag) => Some (inl (fs, e, mb, {[source]} ∪ links, flag))
      | _ => None
      end
    (* p_unlink_arrived *)
    | SUnlink => 
      match p with
      | inl (fs, e, mb, links, flag) => Some (inl (fs, e, mb, links ∖ {[source]}, flag))
      | _ => None
      end
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepASelf : PID -> Process -> option Process :=
  fun ι p =>
    match p with
    (* p_self *)
    | inl (FParams (ICall erlang self) [] [] :: fs, RBox, mb, links, flag) =>
        Some (inl (fs, RValSeq [VPid ι], mb, links, flag))
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition plsASpawnSpawn :
  PID -> list (nat * nat * Exp) -> nat -> nat -> Exp -> Val ->
  Process -> option Process :=

  fun ι ext id vars e l p =>
    match p with
    | inl (FParams (ICall erlang spawn) [lv] [] :: fs, RValSeq [l'], mb, links, flag) =>
      if (Val_eqb_strict lv (VClos ext id vars e) && Val_eqb_strict l' l)
        then Some (inl (fs, RValSeq [VPid ι], mb, links, flag))
        else None
    | _ => None
    end.

Definition plsASpawnSpawnLink :
  PID -> list (nat * nat * Exp) -> nat -> nat -> Exp -> Val ->
  Process -> option Process :=

  fun ι ext id vars e l p =>
    match p with
    | inl (FParams (ICall erlang spawn_link) [lv] [] :: fs, RValSeq [l'], mb, links, flag) =>
      if (Val_eqb_strict lv (VClos ext id vars e) && Val_eqb_strict l' l)
        then Some (inl (fs, RValSeq [VPid ι], mb, {[ι]} ∪ links, flag))
        else None
    | _ => None
    end.

Definition processLocalStepASpawn :
  PID -> list (nat * nat * Exp) -> nat -> nat -> Exp -> Val -> bool ->
  Process -> option Process :=
  
  fun ι ext id vars e l l_flag p =>
    match len l with
    | Some vars' =>
      if (vars' =? vars)
      then
        match l_flag with
        (* p_spawn *)
        | false => plsASpawnSpawn ι ext id vars e l p
        (* p_spawn_link *)
        | true => plsASpawnSpawnLink ι ext id vars e l p
        end
      else None
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepTau : Process -> option Process :=
  fun p =>
    match p with
    | inl (fs, e, mb, links, flag) =>
      (* p_local *)
      match step_func fs e with
      | Some (fs', e') => Some (inl (fs', e', mb, links, flag))
      | _ =>
        match fs with
        (* p_recv_peek_message_ok *)
        | FParams (IPrimOp "recv_peek_message") [] [] :: fs' => 
          match e with 
          | RBox =>
            match peekMessage mb with
            | Some msg => Some (inl (fs', RValSeq [ttrue;msg], mb, links, flag))
            | _ => None
            end
          | _ => None
          end
        (* p_recv_next *)
        | FParams (IPrimOp "recv_next") [] [] :: fs' =>
          match e with
          | RBox =>
            match recvNext mb with
            | Some mb' => Some (inl (fs', RValSeq [ok], mb', links, flag))
            | _ => None
            end
          | _ => None
          end
        (* p_remove_message *)
        | FParams (IPrimOp "remove_message") [] [] :: fs' =>
          match e with
          | RBox =>
            match removeMessage mb with
            | Some mb' => Some (inl (fs', RValSeq [ok], mb', links, flag))
            | _ => None
            end
          | _ => None
          end
        | FParams (IPrimOp "recv_wait_timeout") [] [] :: fs' =>
          match e with
          | RValSeq [v] =>
            match v with
            (* p_recv_wait_timeout_new_message *)
            | infinity => 
              match mb with
              | (oldmb, msg :: newmb) => 
                  Some (inl (fs', RValSeq [ffalse], (oldmb, msg :: newmb), links, flag))
              | _ => None
              end
            (* p_recv_wait_timeout_0 *)
            | VLit 0%Z => Some (inl (fs', RValSeq [ttrue], mb, links, flag))
            (* p_recv_wait_timeout_invalid *)
            | _ => Some (inl (fs', RExc (timeout_value v), mb, links, flag))
            end
          | _ => None
          end
        (* p_set_flag_exc *)
        | FParams (ICall erlang process_flag) [VLit "trap_exit"%string] [] :: fs' =>
          match e with
          | RValSeq [v] =>
            match bool_from_lit v with
            | None => Some (inl (fs', RExc (badarg v), mb, links, flag))
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      end
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepEps : Process -> option Process :=
  fun p =>
    match p with
    (* p_terminate *)
    | inl ([], RValSeq [_], _, links, _) =>
        Some (inr (gset_to_gmap normal links))
    (* p_terminate_exc *)
    | inl ([], RExc exc, _, links, _) =>
        Some (inr (gset_to_gmap exc.1.2 links))
    | inl (FParams ident vl [] :: fs, e, mb, links, flag) =>
      (* p_set_flag *)
      match ident with
      | ICall erlang process_flag =>
        match vl with
        | [VLit (Atom "trap_exit"%string)] =>
          match e with
          | RValSeq [v] =>
            match bool_from_lit v with
            | Some y =>
                Some (inl (fs, RValSeq [lit_from_bool flag], mb, links, y))
            | None => None
            end
          | _ => None
          end
        | _ => None
        end
      (* p_recv_peek_message_no_message *)
      | IPrimOp "recv_peek_message"%string =>
        match vl with
        | [] =>
          match e with
          | RBox => 
            match peekMessage mb with
            | None => Some (inl (fs, RValSeq [ffalse; ErrorVal], mb, links, flag))
            | _ => None
            end
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | _ => None
    end.

(* ------------------------------------------------------------- *)

Definition processLocalStepFunc : Process -> Action -> option Process :=
  fun p a =>
    match a with
    | ASend _ ι msg => processLocalStepASend ι msg p
    | AArrive source dest msg => processLocalStepAArrive source dest msg p
    | ASelf ι => processLocalStepASelf ι p
    | ASpawn ι (VClos ext id vars e) l l_flag =>
        processLocalStepASpawn ι ext id vars e l l_flag p
    | τ => processLocalStepTau p
    | ε => processLocalStepEps p
    | _ => None
    end.