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
          | ICall (VLit (Atom str_erlang)) (VLit (Atom fn)) => 
            if String.eqb str_erlang "erlang"
            then
              if String.eqb fn "!"
              then
                match lval with
                  | [VPid destPID] => 
                    match e with
                      | RValSeq [v] => ASend selfPID destPID (SMessage v)
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "exit"
              then
                match lval with
                  | [VPid destPID] =>
                    match e with
                      | RValSeq [v] => ASend selfPID destPID (SExit v false)
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "link"
              then
                match lval with
                  | [] => 
                    match e with
                      | RValSeq [VPid destPID] => ASend selfPID destPID SLink
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "unlink"
              then
                match lval with
                  | [] => 
                    match e with
                      | RValSeq [VPid destPID] => ASend selfPID destPID SUnlink
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "self"
              then
                match lval with
                  | [] =>
                    match e with
                      | RBox => ASelf selfPID
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "spawn"
              then
                match lval with
                  | [VClos ext id vars e'] =>
                    match e with
                      | RValSeq [l] => ASpawn freshPID (VClos ext id vars e') l false
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "spawn_link"
              then
                match lval with
                  | [VClos ext id vars e'] =>
                    match e with
                      | RValSeq [l] => ASpawn freshPID (VClos ext id vars e') l true
                      | _ => τ
                    end
                  | _ => τ
                end
              else if String.eqb fn "process_flag"
              then
                match lval with
                  | [VLit (Atom str_trap_exit)] =>
                    if String.eqb str_trap_exit "trap_exit"
                    then
                      match e with
                        | RValSeq [v] =>
                          match bool_from_lit v with
                            | Some _ => ε
                            | None => τ
                          end
                        | _ => τ
                      end
                    else τ
                  | _ => τ
                end
              else τ
            else τ
          | IPrimOp str_recv_peek_message =>
            if String.eqb str_recv_peek_message "recv_peek_message"
            then
              match e with
                | RBox =>
                  match peekMessage mb with
                    | Some _ => τ
                    | _ => ε
                  end
                | _ => τ
              end
            else τ
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

Definition makeInitialNode: Redex -> Node :=
  fun r =>
    let p := inl ([], r, emptyBox, pids_empty, false) in
    let initPID := pids_fresh (usedPIDsProcNew p) in
    (ether_empty, pool_singleton initPID p).

Definition makeInitialNodeConf: Redex -> Node * RRConfig * PID * list (PID * PID) :=
  fun r =>
    let p := inl ([], r, emptyBox, pids_empty, false) in
    let initPID := pids_fresh (usedPIDsProcNew p) in
    ((ether_empty, pool_singleton initPID p), RRConf (ne_single initPID) 0, S initPID, []).

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

Definition interProcessStepFuncFast : Node -> PID -> PID + (PID * PID) -> option (Node * Action * PID) :=
  fun '(eth, prs) hiPID op =>
    match op with
    | inl pid => 
      match pool_lookup pid prs with
      | Some (inl p) => 
        let a := nonArrivalAction p pid (S hiPID) in
        match a with
        | ASend sourcePID destPID sig => 
          if sourcePID =? pid
          then
            match processLocalStepFunc (inl p) a with
            | Some p' => Some (etherAddNew sourcePID destPID sig eth, pool_insert pid p' prs, a, hiPID)
            | _ => None
            end
          else None
        | ASpawn freshPID v1 v2 link_flag => 
          match mk_list v2 with
          | Some l => 
            match create_result_NEW (IApp v1) l with
            | Some (r, eff) =>
              match processLocalStepFunc (inl p) a with
              | Some p' =>
                  Some ((eth,
                  pool_insert freshPID 
                    (inl ([], r, emptyBox, if link_flag 
                                           then pids_singleton pid else pids_empty, false))
                    (pool_insert pid p' prs)), a, S hiPID)
              | _ => None
              end
            | _ => None
            end
          | _ => None
          end
        | ASelf selfPID =>
          if selfPID =? pid
          then
            match processLocalStepFunc (inl p) a with
            | Some p' => Some (eth, pool_insert pid p' prs, a, hiPID)
            | _ => None
            end
          else None
        | τ | ε => 
          match processLocalStepFunc (inl p) a with
          | Some p' => Some ((eth, pool_insert pid p' prs), a, hiPID)
          | _ => None
          end
        | _ => None
        end
      | Some (inr p) =>
        match deadActions p pid with
        | a :: _ =>
          match a with
          | ASend sourcePID destPID sig => 
              if sourcePID =? pid
              then
                match processLocalStepFunc (inr p) a with
                | Some p' => Some (etherAddNew sourcePID destPID sig eth, pool_insert pid p' prs, a, hiPID)
                | _ => None
                end
              else None
          | _ => None
          end
        | _ => None
        end
      | _ => None
      end
    | inr (srcPID, dstPID) => 
      match pool_lookup dstPID prs with
      | Some p =>
        match ether_lookup (srcPID, dstPID) eth with
        | Some (v :: vs) =>
          let a := AArrive srcPID dstPID v in
            match etherPopNew srcPID dstPID eth with
            | Some (t, eth') =>
              match processLocalStepFunc p a with
              | Some p' => Some (eth', pool_insert dstPID p' prs, a, hiPID)
              | _ => None
              end
            | _ => None
            end
        | _ => None
        end
      | _ => None
      end
    end.

(* Attempts to make a Tau step first.
   If doesn't succeed, then figures out the proper action
   and return the unchanged node with the list of actions to execute.
   
   Params:
   node:    Node config
   pid:     Self PID
   Returns: Node config and the action list
*)
Definition nodeTauFirstStep: Node -> PID -> option (Node * list Action) :=
  fun '(eth, prs) pid =>
    match pool_lookup pid prs with
    | Some (inl p) =>
      match processLocalStepTau (inl p) with
      | Some p' => Some ((eth, pool_insert pid p' prs), [])
      | _ =>
        match nonArrivalAction p pid (pids_fresh (unavailablePIDs (eth, prs))) with
        | τ => None
        | a => Some ((eth, prs), [a])
        end
      end
    | Some (inr p) => let al := deadActions p pid in Some ((eth, prs), al)
    | _ => None
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
            | Some (inl newP) => let haPID' := (fresh ({[haPID]} ∪ (usedPIDsProcNew (inl newP)))) in
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
    | Some (inr p) => dead_size p =? 0
    | _ => false
    end.

Definition etherNonEmpty: Node -> list (PID * PID) :=
  fun '(eth, prs) =>
    List.filter
      (fun k => match ether_lookup k eth with
                | Some (_ :: _) => true
                | _ => false
                end)
      (ether_domain_toList eth).

Definition currentProcessList: Node -> list PID :=
  fun '(eth, prs) =>
    pids_toList (pool_domain prs).

Require Import CoreErlang.Concurrent.NodeSemanticsLemmas.

Theorem livingNonArrivalDet: forall eth pp n' n'' a a' pid O,
  (forall src dst sig, a  <> AArrive src dst sig) ->
  (forall src dst sig, a' <> AArrive src dst sig) ->
  (eth, pp) -[a | pid]ₙ-> n'  with O ->
  (eth, pp) -[a'| pid]ₙ-> n'' with O ->
  (forall src dst sig p, a = ASend src dst sig -> pp !! src <> Some (inr p)) ->
  (forall fpid fpid' v1 v1' v2 v2' b b', 
      a = ASpawn fpid v1 v2 b -> a' = ASpawn fpid' v1' v2' b' -> fpid = fpid') ->
  a = a'.
Proof.
  intros. revert H4. intros Hsp.
  inv H1.
  * inv H2.
    + clear H H0.
      apply insert_eq in H5. subst.
      inv H9; inv H8; try reflexivity.
      specialize (H3 pid ι' (SExit reason true) links eq_refl).
      setoid_rewrite lookup_insert in H3. congruence.
    + specialize (H0 ι0 pid t0). congruence.
    + clear H H0.
      apply insert_eq in H4. subst.
      destruct H10.
      - subst.
        inv H9; inv H5;[inv H8|inv H8|inv H7|inv H7].
      - destruct H.
        ** subst. inv H9; inv H5.
        ** subst. inv H9; inv H5.
    + clear H H0.
      apply insert_eq in H4. subst.
      inv H9; inv H14.
  * specialize (H ι0 pid t). congruence.
  * inv H2.
    + clear H H0.
      apply insert_eq in H5. subst.
      destruct H10.
      - subst. inv H6; inv H9;inv H.
      - destruct H.
        ** subst. inv H6; inv H9.
        ** subst. inv H6; inv H9.
    + specialize (H0 ι0 pid t). congruence. 
    + clear H H0.
      apply insert_eq in H4. subst.
      destruct H10.
      - subst. destruct H11.
        ** subst. reflexivity.
        ** destruct H.
           ++ subst. inv H6; inv H5; inv H.
           ++ subst. inv H6; inv H5; inv H. rewrite <- H8 in H1. discriminate.
      - destruct H.
        ** subst. destruct H11.
           ++ subst. inv H6; inv H5; inv H7.
           ++ destruct H.
              -- subst. reflexivity.
              -- subst. inv H6; inv H5.
        ** destruct H11.
           ++ subst. inv H6; inv H5;[inv H8|inv H8| |inv H7|inv H7]. rewrite <- H8 in H. discriminate.
           ++ destruct H0.
              -- subst. inv H6; inv H5.
              -- subst. reflexivity.
    + clear H H0.
      apply insert_eq in H4. subst.
      destruct H10.
      - subst. inv H6; inv H15; inv H.
      - destruct H.
        ** subst. inv H6; inv H15.
        ** subst. inv H6; inv H15.
  * inv H2.
    + clear H H0.
      apply insert_eq in H5. subst.
      inv H13; inv H14.
    + specialize (H0 ι0 pid t). congruence.
    + clear H H0.
      apply insert_eq in H4. subst.
      destruct H15.
      - subst. inv H5; inv H14; inv H.
      - destruct H.
        ** subst. inv H5; inv H14.
        ** subst. inv H5; inv H14.
    + clear H H0.
      apply insert_eq in H4. subst.
      specialize (Hsp ι' ι'0 v1 v0 v2 v3 link_flag link_flag0 eq_refl eq_refl). subst.
      inv H19; inv H14; try reflexivity.
Qed.
