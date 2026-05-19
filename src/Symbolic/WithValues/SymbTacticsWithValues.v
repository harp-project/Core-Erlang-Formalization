From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.

From CoreErlang.Interpreter Require Import StepFunctions Equivalences.
From CoreErlang.Symbolic Require Import SymbTheorems.
From CoreErlang.Symbolic Require Import SymbTactics.

From CoreErlang.Symbolic.WithValues Require Import SymbPreconditions.
From CoreErlang.Symbolic.WithValues Require Import SymbLemmasWithValues.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

Ltac toNextRec :=
stepOne;
toRec.

Ltac2 print_it m := print (of_constr m).

(*Introductions based on an identifier list*)
Ltac2 introl (t : ident list) :=
  List.iter (fun x => intro $x) t.

(*Introductions based on an identifier list*)
Ltac2 revertl (t : ident list) :=
  List.iter (fun x => revert $x) (List.rev t).

(*Debug for printing the focused hypotheses context - Note: fails if not exactly one goal is focused*)
Ltac2 print_hyps () :=
  print (of_string "---- start of context ----");
  match! goal with
  | [h : ?t |- _] =>
      print (concat (of_ident h) (concat (of_string " : ") (of_constr t)));
      fail
  | [_ : _ |- _] => print (of_string  "---- end of context ----")
  end.

(*Debug for printing the focused goal - Note: fails if not exactly one goal is focused*)
Ltac2 print_goal () :=
match! goal with
| [_:_ |- ?g] => print (of_constr g)
end.

(*Duplicate the precondition, so that it is preserved for later use*)
Ltac2 duplicate_precond () :=
match! goal with
| [hyp: ?hyp_term |- _] => 
  if Ident.equal hyp @precond then 
    assert ($hyp_term) as Destr_precond by assumption
  else
    fail
end.

(* Remove manually named precondition parts, so that it can be recut*)
Ltac2 clear_fresh_hyps () :=
let hyps := Control.hyps () in
List.iter (fun (id, _, _) =>
  let s := Ident.to_string id in
  if Char.equal (String.get s 0)  (Char.of_int 95) then
    Std.clear [id]
  else ()
) hyps.

(*Note: what about other forms of precondititon? e.g. disjunctive statements about values*)
Ltac2 rec disect_precondition2 precond :=
  let precond_hyp := Control.hyp precond in
  lazy_match! goal with
  | [h: ?t |- _] =>
    if Ident.equal h precond then
      lazy_match! t with
      | ?a /\ ?b => let h1 := match! a with
                              | VALCLOSED _ => Fresh.in_goal @_PrecondScope
                              | _ => Fresh.in_goal @_PrecondVal
                              end
                    in
                    let h2 := Fresh.in_goal @_PrecondStripped in
                    destruct $precond_hyp as [$h1 $h2];
                    disect_precondition2 h2
      | ?t_w => ()      
      end
    else
      ()
  | [_: ?t |- ?g ] =>  print  (of_string "Done destructing conjuctive precondition.") 
  end
.

Ltac2 rec disect_scopes ():=
  lazy_match! goal with
  | [h: VALCLOSED (VCons _ _) |- _] =>
    let h_t := Control.hyp h in
    print (concat (of_string "inversion in ") (of_ident h));
    inversion $h_t;
    Std.clear [@H];
    disect_scopes ()
    (*Note: In the future, extend for tuples, etc...*)
  | [_:_ |- _] => ()
  end.

Ltac2 recut_preconds () :=
  clear_fresh_hyps ();
  duplicate_precond ();
  disect_precondition2 @Destr_precond.


Ltac2 destruct_val_var_for_all_goals val hypoth :=
Control.enter
  (fun () => print (concat (of_string "destructing val variable after Z var ") (of_constr val));
    print_hyps ();
    destruct $val;
    print (of_string "done");
    (*--- specific to the current form of preconditions! ---*)

    simpl in $hypoth;
    
    (*---*)
    try ltac1:(nia)

    ).
  
Ltac2 destruct_formed_nat add val hypoth :=
let h_add_eq := Fresh.in_goal @H_formed_add_eq in
destruct $add eqn:$h_add_eq;
simpl in precond;
try (ltac1:(nia));
Control.enter (fun () => 
  print (of_string "entering destruct_val_var_for_all_goals");
  print_hyps ();
  destruct_val_var_for_all_goals val hypoth
).

Ltac2 match_action t val valInner hypoth addittionalParam := 
  if Constr.equal val valInner then
    print (concat (of_string "working with val variable: ") (of_constr val));
    match addittionalParam with
    | None => ()
    | Some add => 
          let checkIfZVar zVar := 
            print (concat (of_string "add is: ") (of_constr add));
            if List.mem Constr.equal zVar (List.map Control.hyp t) then
              (* destruct $add *)
              print_hyps (); print_goal ();
              print (concat (of_string "destructed additional variable ") (of_constr add));
              let h_add_eq := Fresh.in_goal @H_add_eq in
              destruct $add eqn:$h_add_eq;
              
              let gn := Control.numgoals () in
              print (concat (of_string "making goals' no: ") (of_int gn));
              destruct_val_var_for_all_goals val hypoth;
              let gn := Control.numgoals () in
              print (concat (of_string "making goals' no: ") (of_int gn))
              
            else 
              Control.enter (fun () => 
              print (concat (of_string "destructing val variable ") (of_constr val));
              destruct $val;
              (*--- specific to the current form of preconditions! ---*)
              simpl in $hypoth;
              (*---*)
              try ltac1:(nia))
          in

          lazy_match! add with
          | Z.to_nat (Z.pos ?p) => 
                print (of_string "A positive value is found");
                pose (Zpos_is_S_n $p) as HP;
                let hp_t := Control.hyp @HP in
                
                destruct $hp_t as [n0 HP2];
                print_hyps ();
                let hp2_t := Control.hyp @HP2 in
                rewrite $hp2_t in $hypoth;
      
                destruct_formed_nat '(Z.to_nat (Z.pos $p)) val hypoth
          | _ ?zVar => checkIfZVar zVar; Control.enter (fun () => print (of_string "BAR"))
          | ?zVar => checkIfZVar zVar; print (of_string "FOO")
          end;
          print (of_string "A-out")
    end;
    print (of_string "B-out")     
  else         
    fail.

Ltac2 check_and_destruct_match_preconds () := 
lazy_match! goal with
| [hypoth: match ?val with _ => _ end |- _] =>
                        print (concat (of_string "destructing val variable in match ") (of_constr val));
                        destruct $val;
                        simpl in $hypoth;
                        try ltac1:(nia)
| [_:_ |- _] => ()
end.

Ltac2 rec destruct_val_variables t v :=
match! goal with
  | [hyp: ValScoped _ ?val |- context [substVal _ ?val]] => print (of_string "nou 1");
    print (concat (of_ident hyp) (concat (of_string " ") (concat (of_constr 'True) (concat (of_string " ") (of_constr val)))));
    Std.clear [hyp];
    destruct_val_variables t v
  | [hyp: ?prop ?addittionalParam ?val |- context [substVal _ ?val]] => print (of_string "yaay 2");
    print (concat (of_ident hyp) (concat (of_string " ") (concat (of_constr prop) (concat (of_string " ") (of_constr val)))));
    match_action t val val hyp (Some addittionalParam)
  | [_: _ |- _] => print (of_string "VAL VARIABLE DESTRUCTION FINISHED (It is possible that nothing happened, patterns need to be extended)")
end.

(*Note: Redundant, since VALCLOSED values are "immune" to any substitution, but it does not need that precondition*)
Ltac2 solve_idsubsts () :=
  print (of_string "Solving idsubsts");
  lazy_match! goal with
  | [_:_ |- context[?val.[idsubst]ᵥ]] => 
    print (of_constr val);
    pose idsubst_is_id as IDS0;

    assert ($val.[idsubst]ᵥ = $val) as ID_SUBST;
    Control.focus 1 1 (fun () =>
      destruct IDS0 as [IDS1 IDS2];
      destruct IDS2 as [IDS2 IDS3];
      let iDS3_t := Control.hyp @IDS3 in
      apply $iDS3_t
    );
    let iD_SUBST_t := Control.hyp @ID_SUBST in
    rewrite $iD_SUBST_t;
    Std.clear [@ID_SUBST ;  @IDS0]
  end.

Ltac2 solve_idsubsts_in hyp :=
  print (concat (of_string "Solving idsubsts in hypothesis ") (of_ident hyp));
  let hyp_t := Control.hyp hyp in
  let hyp_t_t := Constr.type hyp_t in
  lazy_match! hyp_t_t with
  | context[?val.[idsubst]ᵥ] => 
    print (of_constr val);
    pose idsubst_is_id as IDS0;

    assert ($val.[idsubst]ᵥ = $val) as ID_SUBST;
    Control.focus 1 1 (fun () =>
      destruct IDS0 as [IDS1 IDS2];
      destruct IDS2 as [IDS2 IDS3];
      let iDS3_t := Control.hyp @IDS3 in
      apply $iDS3_t
    );
    let iD_SUBST_t := Control.hyp @ID_SUBST in
    rewrite $iD_SUBST_t in $hyp;
    Std.clear [@ID_SUBST ;  @IDS0]
  end.


Ltac2 rec get_root (t : constr) (close : constr) :=
  lazy_match! t with
  | ?val.[?close2]ᵥ => get_root val close2 
  | _ => t , close             
end.

(*TODO: Extension needed, can it be generalized?*)
Ltac2 solve_closesubst () :=
  print (of_string "Solve value substitution over any close");
  lazy_match! goal with
  | [h: VALCLOSED ?val |- context[?val.[?close]ᵥ]] =>
      let (root_val , root_close) := get_root val close in
      print (concat (of_string "found val ") (concat (of_constr root_val) (of_constr root_close)));
      
      let gn := Control.numgoals () in
      Control.focus gn gn (fun () =>
        print (of_string "Any val case with existsing VALCLOSED");
        print (of_constr root_val);
        pose (vclosed_ignores_sub $root_val $root_close) as IGN_SUB;
        let ign_sub_t := Control.hyp @IGN_SUB in
        let h_t := Control.hyp h in
        specialize ($ign_sub_t $h_t);
        rewrite $ign_sub_t;
        Std.clear [@IGN_SUB]
      )
  | [_:_ |- context[?val.[?close]ᵥ]] =>
      let (root_val , root_close) := get_root val close in
      print (concat (of_string "found val ") (concat (of_constr root_val) (of_constr root_close)));
      assert (VALCLOSED $root_val) as H_CLOSED by (try assumption);
      

      let gn := Control.numgoals () in
      Control.focus gn gn (fun () =>
        print (of_string "Any val case with asserted VALCLOSED");
        print (of_constr root_val);
        pose (vclosed_ignores_sub $root_val $root_close) as IGN_SUB;
        let ign_sub_t := Control.hyp @IGN_SUB in
        let h_t := Control.hyp @H_CLOSED in
        specialize ($ign_sub_t $h_t);
        rewrite $ign_sub_t;
        Std.clear [@IGN_SUB ; @H_CLOSED]
      )
  end.

Ltac2 solve_closesubst_in hyp :=
  print (concat (of_string "Solving value substitution over any close in hypothesis ") (of_ident hyp));
  let hyp_t := Control.hyp hyp in
  let hyp_t_t := Constr.type hyp_t in
  lazy_match! goal with
  | [_:_ |- VALCLOSED _] => ()
  | [_:_ |- _] => lazy_match! hyp_t_t with
                  | context[?val.[?close]ᵥ] =>
                      let (root_val , root_close) := get_root val close in
                      print (concat (of_string "found val ") (concat (of_constr root_val) (of_constr root_close)));
                      Control.unshelve (fun () => 
                        assert (VALCLOSED $root_val) as H_CLOSED;
                        Control.focus 1 1 (fun () =>
                          Control.shelve ()
                        );
                        
                        print (of_string "Any val with asserted VALCLOSED");
                        print (of_constr root_val);
                        pose (vclosed_ignores_sub $root_val $root_close) as IGN_SUB;
                        let ign_sub_t := Control.hyp @IGN_SUB in
                        let h_t := Control.hyp @H_CLOSED in
                        specialize ($ign_sub_t $h_t);
                        rewrite $ign_sub_t in $hyp;
                        Std.clear [@IGN_SUB ; @H_CLOSED]
                      )
                  end
  end.
  

Ltac2 solve_renaming () :=
  print (of_string "Solve renamings in goal");
  lazy_match! goal with
  | [h: VALCLOSED ?val |- context[renameVal ?s ?val]] =>
      print (of_string "Rename any val case with existsing VALCLOSED");
      pose (vclosed_ignores_ren $val $s) as IGN_REN;
      let ign_ren_t := Control.hyp @IGN_REN in
      let h_t := Control.hyp h in
      specialize ($ign_ren_t $h_t);
      rewrite $ign_ren_t;
      Std.clear [@IGN_REN]
  | [_:_ |- context[renameVal ?s ?val]] =>
    print (concat (of_string "found val ") (of_constr val));
    Control.unshelve (fun () => 
      assert (VALCLOSED $val) as H_CLOSED;
      Control.focus 1 1 (fun () =>
        Control.shelve ()
      );
      
      print (of_string "Renaming with existsing VALCLOSED");
      print (of_constr val);
      pose (vclosed_ignores_ren $val $s) as IGN_REN;
      let ign_ren_t := Control.hyp @IGN_REN in
      let h_t := Control.hyp @H_CLOSED in
      specialize ($ign_ren_t $h_t);
      rewrite $ign_ren_t;
      Std.clear [@IGN_REN ; @H_CLOSED]
    )
end.

Ltac2 solve_renaming_in hyp :=
  print (concat (of_string "Solving renamings in hypothesis ") (of_ident hyp));
  let hyp_t := Control.hyp hyp in
  let hyp_t_t := Constr.type hyp_t in
  lazy_match! goal with
  | [_:_ |- VALCLOSED _] => ()
  | [_:_ |- _] => lazy_match! hyp_t_t with
                  | context[renameVal ?s ?val] =>
                      print (concat (of_string "found val ") (of_constr val));
                      Control.unshelve (fun () => 
                        assert (VALCLOSED $val) as H_CLOSED;
                        Control.focus 1 1 (fun () =>
                          Control.shelve ()
                        );
                        
                        print (of_string "Renaming with existsing VALCLOSED");
                        print (of_constr val);
                        pose (vclosed_ignores_ren $val $s) as IGN_REN;
                        let ign_ren_t := Control.hyp @IGN_REN in
                        let h_t := Control.hyp @H_CLOSED in
                        specialize ($ign_ren_t $h_t);
                        rewrite $ign_ren_t in $hyp;
                        Std.clear [@IGN_REN ; @H_CLOSED]
                      )
                  end
  end.

Ltac2 solve_substitutions () :=
print (of_string "Solve subtitutions in the goal");
try (repeat (solve_idsubsts ()));
try (repeat (solve_renaming ()));
try (repeat (solve_closesubst ()));
try reflexivity
.

Ltac2 solve_substitutions_in hyp :=
print (concat (of_string "Solve subtitutions in hypothesis ") (of_ident hyp));
try (repeat (solve_idsubsts_in hyp));
try (repeat (solve_renaming_in hyp));
try (repeat (solve_closesubst_in hyp));
try reflexivity
.


Ltac solve_final_state_with_val := 
  exists 0; (* This is for the step number, which is always irrelevant (|- nat) when this tactic is called *)
     first [ auto (* The program indeed terminated at ([], r) where is_result r *)
           | idtac "Unexpected end state 
                    (can be due to an exception in the Erlang program,
                     a result when an exception was expected,
                     non-termination in the given depth or
                     an impossible input that was not ruled out)"
           ].

Ltac solve_final_postcond_with_val :=
  first [ nia
        | auto
        | idtac "Could not solve postcondition"
        ].

Ltac solve_terminated_with_val :=
  idtac "starting solve_terminated_with_val";
  lazymatch goal with
  | _ : ?H |- ?g => idtac "in solve_terminated_with_val"; idtac H; idtac g
  end;
  lazymatch goal with
  | |- context[sequentialStepMaxK] => idtac "fail"; fail "The program has not yet terminated"
  | |- _ => 
    lazymatch goal with
    | |- ex _ => idtac "eexists"; eexists;solve_terminated_with_val
    | |- _ /\ _ => idtac "split"; split;[solve_final_state_with_val | solve_final_postcond_with_val]
    | |- _ => idtac "idtac in solve_terminated_with_val"
    end
  end.
  
Ltac2 rewritePosToSn p preconds :=
pose (Zpos_is_S_n $p) as Pos_is_S_n;
let p_t_0 := Control.hyp @Pos_is_S_n in
destruct $p_t_0 as [l_n Pos_is_S_n2];
let p_t := Control.hyp @Pos_is_S_n2 in
List.iter (fun (pr) =>
  rewrite $p_t in $pr;
  simpl in $pr
) preconds;
Std.clear [@Pos_is_S_n2].


Ltac2 rec_case_mult_inner_with_val h t v :=
  print (of_string "Preparing inductive hypothesis");
  ltac1:(toNextRec);

  print (of_string "Destructing remaining and created variables, which are peresent in match expressions in the context");
  repeat (check_and_destruct_match_preconds ());

  print (of_string "Destructing IH, additional variables are free");
    
  let ih_t := Control.hyp @IH in
  let ih_t_t := Constr.type ih_t in
  lazy_match! ih_t_t with
  | context[exists (y : _), (exists (n : nat), _) /\ _] => edestruct IH as [IHRes IHStripped];
  
  
        let gn := Control.numgoals () in
        Control.focus gn gn (fun () =>  
          lazy_match! goal with
          | [_:_ |- exists (y : Val), exists (n : nat), _] => eexists
          | [_:_ |- exists (y : Val), ((exists (n : nat), _) /\ _)] => eexists
          | [_:_ |- exists (y : Z), exists (n : nat), _] => eexists
          | [_:_ |- exists (y : Z), ((exists (n : nat), _) /\ _)] => eexists
          | [_:_ |- _] => print (of_string "Existential Val or Z variable is not introduced!")
          end;

          try (disect_scopes (); subst);
          solve_substitutions_in @IHStripped;
          solve_substitutions ();
          
          simpl;

          let gn := Control.numgoals () in
          Control.focus gn gn (fun () => 
                  
            Control.enter (fun () =>
              print (of_string "---------------------------------------------------------------------- -------------------------");
              first [
                print (of_string "Trying the current form of IH");
                let ih := Control.hyp @IHStripped in
                print_hyps ();
                print_goal ();
                exact $ih
              |
                print (of_string "No luck, needs IHExp_fic and transitivity...");
                print (of_string "Destructing IHStripped");
                destruct IHStripped as [IHExp IHPost];
                let ih_exp_t := Control.hyp @IHExp in
                pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic;
                simpl in IHExp_fic;
                print (of_string "Posed IHExp_fic");

                print (of_string "Applying transitivity");
                
                eapply maxKTransitive' >
                [
                  first [
                    print (of_string "Applying IHExp_fic");
                    let iHExp_fic_t := Control.hyp @IHExp_fic in
                    apply $iHExp_fic_t
                  |
                    print (of_string "Couldn't apply IHExp_fic :(")
                  ]
                |
                  ltac1:(stepThousand);
                  print (of_string "Leftover");
                  split >
                  [
                    exists 0;
                    reflexivity
                  |
                    try (ltac1:(lia))
                  ]
                ]
              | 
                print (of_string "No success, no inductive theroem could be applied :(")
              ]
            )
          )
        );

        let ng := Control.numgoals () in
        Control.focus 3 ng (fun () =>
          Control.enter (fun () =>
            disect_scopes ();
            first [
              assumption
              |
              (*WARNING! it assumes VALCLOSED VNil, if proof cannot be done fully and variable is in the goal*)
              (* ltac1:(scope_solver_v1) *)
              ()
            ]
          )
        );

        Control.focus 2 2 (fun () =>
          repeat split;

          Control.enter (fun () => 
            lazy_match! goal with
              | [z_is_sn: Z.to_nat (Z.pos ?p) = (S ?n), precond: ?meta ?n ?val |- ?meta (Z.to_nat _) ?val] =>
                    print (of_string "Found precond in goal with Z conversion");
                    assert ($n = Z.to_nat (Z.pos $p - 1)) as Len by ltac1:(lia);
                    let len_t := Control.hyp @Len in
                    rewrite $len_t in $precond;
                    let precond_t := Control.hyp precond in
                    exact $precond_t
              | [precond: ?meta ?n ?tl |- ?meta (Z.to_nat _) (VCons ?hd ?tl)] =>
                    let precond_t := Control.hyp precond in
                    pose (wellFormedList_can_be_appended $hd $tl $n $precond_t) as Len;
                    pose (Nat2Z.id (S $n)) as ToZ;
                    let toz_t := Control.hyp @ToZ in
                    let len_id := @Len in
                    rewrite <- $toz_t in $len_id;
                    let len_t := Control.hyp len_id in
                    exact $len_t
              | [_:_ |- _] => ()
            end
          )
        );
        try(ltac1:(lia));
        try(disect_scopes (); subst)
  | _ => print (of_string "Goal does not start with exists y : Val, _")
  end.


Ltac2 rec_case_mult_with_val precond heq h t v := 
  recut_preconds();
  repeat (destruct_val_variables t v);
  let gn := Control.numgoals () in
  print (concat (of_string "NO of goals: ") (of_int gn));
  Control.enter (fun () =>

    print (of_string "check 1");
    print_hyps ();
    print_goal ();

    Control.enter (fun () =>

    recut_preconds ();
    solve_substitutions ();
    rec_case_mult_inner_with_val h t v;
    print (of_string "check 2?")
    )
  )
  .

(*Things to consider about Z variables: present in the execution or just 
a pseudo variable representing the list?*)

Ltac2 base_case_mult_inner_with_val h t v :=
  (* Do a thousand reduction steps. *)
  
  print (of_string "Identifying val variables");
  repeat (destruct_val_variables t v);
  
  let gn := Control.numgoals () in
  print (concat (of_string "NO OF GOALS: ") (of_int gn));
  Control.enter (fun () =>
    recut_preconds ();
    ltac1:(stepThousand); (*TODO: repeat*)
    try (ltac1:(solve_terminated));
    try (disect_scopes (); solve_substitutions ())
  )

  .

Ltac my_ltac1_tactic H :=
  ltac2:(print_it '(0 <= 10000)%Z).

Goal forall (n : Z), (0 <= n)%Z -> True.
Proof.
  intro.
  print_it 'n.
Admitted.

Ltac2 base_case_mult_with_val precond heq' h t v := 
  (* We need to return h and the precondition to the goal, before the loop begins. *)
  print (of_string "Solving base case");

  duplicate_precond ();
  disect_precondition2 @Destr_precond;

  base_case_mult_inner_with_val h t v.

Ltac2 solve_induction_mult_with_val (h : ident) (t : ident list) (v : ident list) :=
  print (of_string "Start induction");
  (* To solve using induction, first introduce the variables and the precondition. *)
  intro $h;

  print (of_ident h);
  introl t;
  introl v;

  intros precond;

  (* IH needs to be as general as possible, but we need to know that 0 <= h, which is in the
     precondition. So we need to assert it with lia, before reverting the precondition. *)
  (* let heq := fresh "Heq" in *)

  let h_term := Control.hyp h in
  assert (Heq : (0 <= $h_term)%Z);
  Control.focus 1 1 (fun () => ltac1:(lia));

  
  revert precond;
  revertl t;
  revertl v;

  (* Induction is performed. In the new goal, the symbolic variable h is universally quantified
     again, the introduced version is irrelevant along with Heq, thus they can be deleted when
     they are not needed anymore. *)
  print (of_string "Applying Z induction theorem");
  print_hyps ();
  print_goal ();
  apply Zlt_0_ind with (x := $h_term);
  Control.focus 2 2 (fun () => exact &Heq);

  Std.clear [@Heq ; h];

  intro $h;
  (* Since the old h was cleared, the name can be reused for its new universally quantified
     instance. The induction hypothesis is introduced as IH. We also know that 0 <= h, this is
     given by Zlt_0_ind itself. Heq can be reused, since it was cleared. It can be cleared
     again, since it directly comes from PreCond. PreCond is introduced after Heq. *)
  (* let IH := fresh "IH" in *)
  intro IH; intro heq; introl v; introl t; intro precond;

  (* Destructing h gives 3 cases, the first is a base case with 0, the second is positive,
     and the third is negative. Since we assume that the recursive function decreases on h,
     the first case will terminate (IH not needed), the second will recurse, and the third
     is impossible, because h cannot be negative. *)
  (* let heq' := fresh "Heq" in *)
  print (of_string  "Destructing primary Z variable");
  let precond_t := Control.hyp @precond in
  print_hyps ();
  let h_term := Control.hyp h in 
  destruct $h_term eqn:heq' > [ base_case_mult_with_val @precond @heq h t v
                              | rec_case_mult_with_val @precond @heq h t v
                              | ltac1:(nia)]. 

Ltac2 take_to_rec_loop_mult_with_val (h : ident) (t : ident list) (v : ident list) :=
  ltac1:(toRec);
  first [ (* If the goal might be recursive... *)
          print (of_string "Evaluating to recursion point");
          
          ltac1:(possibly_recursive);
          print (of_string "trying induction...");
          solve_induction_mult_with_val h t v;
          print (of_string "Done with solve_induction_mult_with_val")
        | (* If we can find a match expression... *)
          ltac1:(contains_match);

          (*TEMPORARY*)
          (* separate_cases_mult h t; *)
          print (of_string "skip contains_match rec while debug")
          (* solve_symbolically_internal_mult_with_val h t v *)
        | (* If we did not hit a point of recursion, or a case separation,
             the loop needs to be continued. 
             
             A single step is done manually, 
             because non-recursive functions defined in a LetRec can cause issues:
             we can get to a point of potential recursion, but since the function is
             not in fact recursive, that branch will fail. Without this stepOne, we
             can run into an infinite loop.
             *)
          ltac1:(stepOne);
          print (of_string "manual step")
          (* solve_symbolically_internal_mult_with_val h t v *)
        ].


Ltac2 solve_symbolically_internal_mult_with_val (h : ident) t v :=
  (* first [ (* If sequentialStepMaxK is still in the goal, and we did not hit recursion yet,
             then try moving forward to a point of recursion. *)
          
          (* If sequentialStepMaxK is not in the goal, we have terminated. *)
        | print (of_string "solve_terminated_with_val from root"); intros; ltac1:(solve_terminated_with_val)
        | print (of_string "Unexpected error: could not solve terminated program")
        ]. *)
    ltac1:(is_not_terminated); take_to_rec_loop_mult_with_val h t v; print (of_string "fooo").


Ltac2 Notation "solve_symbolically" h(ident) "," t(list1(ident)) ";" v(list1(ident)) := 
  (* To start, rewrite the goal from inductive to functional *)
  print (of_string "Starting symbolical solution");
  try(setoid_rewrite RTCEquiv;
  Control.focus 2 2 (fun () => auto));
  (* This is separate, because the loop does not need to rewrite with RTCEquiv *)
  solve_symbolically_internal_mult_with_val h t v.

Ltac2 Notation "solve_symbolically" h(ident) ";" v(list1(ident)) := 
  (* To start, rewrite the goal from inductive to functional *)
  print (of_string "Starting symbolical solution without additional Z parameters");
  try(setoid_rewrite RTCEquiv;
  Control.focus 2 2 (fun () => auto));
  (* This is separate, because the loop does not need to rewrite with RTCEquiv *)
  solve_symbolically_internal_mult_with_val h [] v;
  print (of_string "bar").



Ltac2 toRec_in hyp :=
let hyp_t := Control.hyp hyp in
let hyp_t_t := Constr.type hyp_t in
match! hyp_t_t with
| context[exists n : nat, sequentialStepMaxK _ _ n = _] => 
        try(apply maxKInsertCanRec in $hyp > [|constructor]); simpl in $hyp;
        try(apply maxKDone in $hyp > [|constructor])
| _ => ()
end.

Ltac2 stepOne_in hyp :=
let hyp_t := Control.hyp hyp in
let hyp_t_t := Constr.type hyp_t in
match! hyp_t_t with
| context[exists n : nat, sequentialStepMaxK _ _ n = _] =>
        apply maxKForwardOne in $hyp > [|constructor]; simpl in $hyp
| _ => ()
end.