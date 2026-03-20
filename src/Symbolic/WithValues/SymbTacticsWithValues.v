From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.

From CoreErlang.Interpreter Require Import StepFunctions Equivalences.
From CoreErlang.Symbolic Require Import SymbTheorems.
From CoreErlang.Symbolic Require Import SymbTactics.

From CoreErlang.Symbolic.WithValues Require Import SymbPreconditions.
From CoreErlang.Symbolic.WithValues Require Import SymbLemmasWithValues.

From Ltac2 Require Import Ltac2.
From Ltac2 Require Import Message.

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

(*TODO: what about other forms of precondititon? e.g. disjunctive statements about values*)
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
    print_hyps ();
    inversion $h_t;
    Std.clear [@H];
    print_hyps ();
    disect_scopes ()
    (*TODO: Extend for tuples, etc...*)
  | [_:_ |- _] => ()
  end.

Ltac2 recut_preconds () :=
  clear_fresh_hyps ();
  duplicate_precond ();
  disect_precondition2 @Destr_precond.

(* Ltac2 Eval (disect_precondition2 1 '(((0 ≤ 0)%Z
∧ (0 ≤ lh)%Z
∧ isWellFormedList_n (Z.to_nat 0) m
∧ isWellFormedList_n (Z.to_nat lh) l
∧ VALCLOSED m ∧ VALCLOSED l))). *)




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
                pose (Z_is_S_n $p) as HP;
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
                        (*--- specific to the current form of preconditions! ---*)

                        simpl in $hypoth;
                        (*---*)
                        try ltac1:(nia)
| [_:_ |- _] => ()
end.


(*TODO: seems a bit hard to use*)
Ltac2 check_and_destruct_match_goal () :=
lazy_match! goal with
(* | [_:_ |- context[match (Z.to_nat ?val) with _ => _ end]] =>
                        print (concat (of_string "destructing val variable in match in GOAL ") (of_constr val));
                        let id_m := Fresh.in_goal @_Goal_match_destructZ in
                        destruct $val eqn:$id_m;
                        simpl;
                        (*--- specific to the current form of preconditions! ---*)

                        (*---*)
                        try ltac1:(nia) *)
| [_:_ |- context[match ?val with _ => _ end]] =>
                        print (concat (of_string "destructing val variable in match in GOAL ") (of_constr val));
                        let id_m := Fresh.in_goal @_Goal_match_destruct in
                        destruct $val eqn:$id_m;
                        (*--- specific to the current form of preconditions! ---*)

                        (*---*)
                        try ltac1:(nia)
| [_:_ |- _] => print (of_string "opsie")
end.


(*TODO: Generalize destruction of val variables. Problem: When do they need destructing? 
- Probably when some match ?val with ... end structure uses them even in the evaluation or in meta result functions*)
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

(*TODO: Probably unnecessary, since VALCLOSED values are "immune" to any substitution*)
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

(*TODO: Extension needed, can it be generalized?*)
Ltac2 solve_closesubst () :=
  print (of_string "Solve value substitution over any close");
  lazy_match! goal with
  | [h: VALCLOSED (VCons ?val1 ?val2) |- context[VCons (substVal ?close1 ?val1) (substVal ?close2 ?val2)]] =>
    (*TODO: different branches for both "only one list case"*)
      print (of_string "VCons both sublists case");
      let hyp_t := Control.hyp h in 
      inversion $hyp_t as [_A | _B | _C | _D | _E | _F | _G1 _G2 _G3 H_closed1 H_closed2 | _H | _I ];
      pose vclosed_ignores_sub as IGN_SUB;
      assert ($val1.[$close1]ᵥ = $val1) as CLOSE_SUBST1;
      Control.focus 1 1 (fun () =>
        let iGN_SUB_t := Control.hyp @IGN_SUB in
        eapply $iGN_SUB_t in H_closed1;
        let h_closed1_t := Control.hyp @H_closed1 in
        apply $h_closed1_t
      );
      assert ($val2.[$close2]ᵥ = $val2) as CLOSE_SUBST2;
      Control.focus 1 1 (fun () =>
        let iGN_SUB_t := Control.hyp @IGN_SUB in
        eapply $iGN_SUB_t in H_closed2;
        let h_closed2_t := Control.hyp @H_closed2 in
        apply $h_closed2_t
      );
      let cLOSE_SUBST1_t := Control.hyp @CLOSE_SUBST1 in
      rewrite $cLOSE_SUBST1_t;
      let cLOSE_SUBST2_t := Control.hyp @CLOSE_SUBST2 in
      rewrite $cLOSE_SUBST2_t;
      Std.clear [@CLOSE_SUBST1 ; @CLOSE_SUBST2]
  | [h: VALCLOSED ?val |- context[substVal ?close ?val]] =>
      print (of_string "Any val case with existsing VALCLOSED");
      print (of_constr val);
      pose (vclosed_ignores_sub $val $close) as IGN_SUB;
      let ign_sub_t := Control.hyp @IGN_SUB in
      let h_t := Control.hyp h in
      specialize ($ign_sub_t $h_t);
      rewrite $ign_sub_t;
      Std.clear [@IGN_SUB]
  end.


Ltac2 rec get_root (t : constr) (close : constr) :=
  lazy_match! t with
  | ?val.[?close2]ᵥ => get_root val close2 
  | _ => t , close             
  end.

Ltac2 solve_closesubst_in hyp :=
  print (concat (of_string "Solving value substitution over any close in hypothesis ") (of_ident hyp));
  let hyp_t := Control.hyp hyp in
  let hyp_t_t := Constr.type hyp_t in
  lazy_match! hyp_t_t with
  | context[?val.[?close]ᵥ] =>
      let (root_val , root_close) := get_root val close in
      print (concat (of_string "found val ") (concat (of_constr root_val) (of_constr root_close)));
      assert (VALCLOSED $root_val) as H_CLOSED by assumption;
      print (of_string "bruh");
      
      print (of_string "Any val case with existsing VALCLOSED");
      print (of_constr root_val);
      pose (vclosed_ignores_sub $root_val $root_close) as IGN_SUB;
      let ign_sub_t := Control.hyp @IGN_SUB in
      let h_t := Control.hyp @H_CLOSED in
      specialize ($ign_sub_t $h_t);
      rewrite $ign_sub_t in $hyp;
      Std.clear [@IGN_SUB ; @H_CLOSED]
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
  end.

Ltac2 solve_renaming_in hyp :=
  print (concat (of_string "!NOT IMPLEMENTED, DOES NOTHING! Solving renamings in hypothesis ") (of_ident hyp));
  let hyp_t := Control.hyp hyp in
  let hyp_t_t := Constr.type hyp_t in
  (* lazy_match! goal with
  | [h: VALCLOSED ?val |- context[renameVal ?s ?val]] =>
      print (of_string "Any val case with existsing VALCLOSED");
      pose (vclosed_ignores_ren $val $s) as IGN_REN;
      let ign_ren_t := Control.hyp @IGN_REN in
      let h_t := Control.hyp h in
      specialize ($ign_ren_t $h_t);
      rewrite $ign_ren_t in $hyp;
      Std.clear [@IGN_REN]
  end. *) ().

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

Ltac separate_cases_mult_with_val h t v :=
  (* If we find a match expression, then introduce the variable h, along with the precondition. *)
  let precond := fresh "PreCond" in
  let heq := fresh "Heq" in
  intros h; intros t; intros precond;
  (* Separate the cases, using the hypothesis name Heq... *)
  case_innermost heq; simpl;
  (* ...and eliminate sequentialStepCanRec from all branches, if it exists. *)
  try (setoid_rewrite maxKInsertCanRecGeneral;try auto);
  (* A branch might not be reachable based on PreCond and Heq, try solving using nia *)
  try nia;
  (* The branch condition is merged with the precondition. *)
  let Tp := type of precond in
  let Th := type of heq in
  let precond' := fresh "PreCond" in
  assert (Tp /\ Th) as precond' by lia;
  clear heq; clear precond;
  (* Finally, we get back to the standard goal on both branches. *)
  revert h t precond'.

Ltac2 oneLessCase ih_t val :=
  print (of_constr val);
  specialize ($ih_t ($val - 1)%Z);
  assert (0 ≤ $val - 1 < $val)%Z as H_VAR by ltac1:(lia);
  let h_var_t := Control.hyp @H_VAR in
  specialize ($ih_t $h_var_t);
  Std.clear [@H_VAR]
  .

Ltac2 rec_case_mult_inner_with_val h t v :=
  print (of_string "Preparing inductive hypothesis");
  ltac1:(toRec);



  print (of_string "Specialize IH with the lead Z value");
  (*let ih_t := Control.hyp @IH in
  let ih_t_t := Constr.type ih_t in
  (*TODO: Current implementation supports only decreasing the Z value by one!*)
  lazy_match! ih_t_t with
  (*First iteration: Z.pos p - 1 is hardcoded...it can come from a variable function or from some heuristics later*)
  | context[forall y : _, (0 ≤ y < ?val)%Z -> _] => oneLessCase ih_t val
  | _ => Control.throw (Invalid_argument (Some (of_string "Cannot specialize induction hypothesis on decreasing Z")))
  end;*)

  print (of_string "Destructing remaining and created variables, which are peresent in match expressions in the context");
  repeat (check_and_destruct_match_preconds ());
  (* repeat (check_and_destruct_match_goal ()); *)


  print (of_string "Specializing IH with Val type varaibles");
  print_hyps ();
  print_goal ();
  (*TODO: How to decide which variable is needed?
    - Common case: Primary variable is a list, IH needs the tail as input*)
  (* lazy_match! goal with
  | [_:_ |- context[exists y : Val, _ ∧ y = VCons _ (_ ?val)]] => 
            print (of_string "Result is a VCons!");
            specialize ($ih_t $val)
  | [_:_ |- context[exists y : Val, _ ∧ y = _ ?v1 ?v2]] =>
            print (of_string "Result is a function with 2 parameters!");
            specialize ($ih_t $v1 $v2)
  (* | [_:_ |- context[exists y : Val, _ ∧ y = _ ?v1]] => specialize ($ih_t $v1) *)
  | [h: isWellFormedList_n  _ ?val |- context[exists y : Val, _ ∧ y = ?res]] => 
            print (of_string "Ignore result, specialize based on wellFormedList hypothesis");
            specialize ($ih_t $val)
  | [h: isWellFormedNumberList_n  _ ?val |- context[exists y : Val, _ ∧ y = ?res]] => 
            print (of_string "Ignore result, specialize based on wellFormedNumberList hypothesis"); print_hyps (); specialize ($ih_t $val)
  | [_:_ |- context[exists y : Z, _ ∧ y = ?res]] =>
            print (of_string "Result is something...");
            match! res with
            | context[_ ?vl] => if Constr.equal 'Val (Constr.type vl) then
                                  print (of_string "... a function with 1 Val parameter"); print (of_constr vl); specialize ($ih_t $vl)
                                else
                                  fail
            end
  | [_:_ |- _] => Control.throw (Invalid_argument (Some (of_string "Cannot specialize induction hypothesis on Val")))
  end; *)

  disect_scopes ();
  subst;

  solve_substitutions_in @IH;


  print (of_string "Destructing IH, additional Z variables as parameters");
  edestruct IH as [IHRes IHStripped];

  Control.enter (fun () => 
    print_hyps ();
    print_goal ()
  ).

  (***************************************)

   

  (* print (of_string "Trivial solutions for IH preconditions");
  (repeat(split; first [ltac1:(lia) | assumption | ltac1:(scope_solver_v1) | ()])); *)
 

  (*
 
  (*TODO: Goal selection is hardcoded! - Probably heavily dependent on precondition order!*)
  print (of_string "Focusing the goal before the last");
  let ng := Control.numgoals () in
  print (of_int ng);
  let precondGoalNo := Int.sub (Control.numgoals ()) 1 in
  Control.focus precondGoalNo precondGoalNo (fun () =>

    print (of_string "Checking for precondition to prove ...");
    lazy_match! goal with
      | [h1: ?precondFun ?n ?vl, h2: (Z.to_nat (Z.pos ?p) = S ?n) |- ?precondFun (Z.to_nat (Z.pos ?p - 1)) ?vl] =>
        print (of_string "Precondition is trivial, with param (Z.to_nat (Z.pos ?p - 1)), having the necessary context");
        assert ((Z.to_nat (Z.pos $p - 1)) = $n) as H_minus by ltac1:(lia);
        let h_minus_t := Control.hyp @H_minus in
        rewrite $h_minus_t;
        assumption
      | [_:_ |- ?fn _ ?val] =>
          print (of_string "Precondition is a function, 1st parameter is length, 2nd is list - hardcoded");
          let l_len := '(list_length $val) in
          print (concat (of_string "HE?: ") (of_constr l_len));
          assert ($fn $l_len $val) as _H_len;
          Control.focus 1 1 (fun () =>
              print (of_string "Proving assertion regarding the length of the list");
              simpl;
              first [exact I 
              | 
                  (*TODO: Hardcoded precondition forms - extendable, but may need refactoring*)
                  lazy_match! goal with
                    | [h: isWellFormedList_n (S ?nH) (VCons _ ?v2) |- isWellFormedList_n _ ?v2] =>
                        simpl in $h;
                        let h_t := Control.hyp h in
                        pose (wellFormedList_n_has_length_n $nH $v2 $h_t) as H_wftl
                    | [h: isWellFormedList_n ?len ?l |- isWellFormedList_n _ ?l] =>
                        simpl in $h;
                        let h_t := Control.hyp h in
                        pose (wellFormedList_n_has_length_n $len $l $h_t) as H_wftl
                    | [h: isWellFormedNumberList_n ?nH ?v2 |- isWellFormedNumberList_n _ ?v2] =>
                        print (of_string "numbaaa list");
                        print_hyps ();
                        print_goal ();


                        simpl in $h;
                        let h_t := Control.hyp h in
                        pose (wellFormedNumberList_n_has_length_n $nH $v2 $h_t) as H_wftl

                    | [_:_ |- ?g] => print_hyps (); print (of_constr g); Control.throw (Invalid_argument (Some (of_string "Can't recognize precondition assert")))
                  end;
                  let h_wftl_t := Control.hyp @H_wftl in
                      rewrite $h_wftl_t;
                      assumption
              
              ]
          );
          let _h_len_t := Control.hyp @_H_len in
          let _h_len_t_t := Constr.type _h_len_t in
          lazy_match! _h_len_t_t with
          | isWellFormedList_n ?ll ?vl =>
            print (of_string "posing lemma");
            assert ($ll = (Z.to_nat (Z.of_nat $ll))) as H_conv by ltac1:(lia)
          | isWellFormedNumberList_n ?ll ?vl =>
            print (of_string "posing lemma?");
           
            assert ($ll = (Z.to_nat (Z.of_nat $ll))) as H_conv by ltac1:(lia)
          | _ => ()
          end;
          print_hyps ();
          print_goal ();
          let _h_len := @_H_len in
          let h_conv_t := Control.hyp @H_conv in
          rewrite $h_conv_t in $_h_len;
          exact $_h_len_t
  
          
          
          (*simpl;
          exact I *)
      | [_:_ |- _] => print (of_string "Could not identify the precondition")
    end
  ). *)

  (* try (Control.focus 1 1 (fun () => 
    ltac1:(lia)
  ));
  try (Control.focus 1 1 (fun () => 
    print_hyps ();
    print_goal ();
    lazy_match! goal with
    | [h: (Z.to_nat (Z.pos ?pos) = S ?na) |- _ (Z.to_nat (Z.pos ?pos - 1)) _] =>
        assert ((Z.to_nat (Z.pos $pos - 1)) = $na) as H_decZ by ltac1:(lia);
        let h_decZ_t := Control.hyp @H_decZ in
        rewrite $h_decZ_t;
        assumption

    | [_:_ |- _] => print (of_string "No solution for precondition with decreased Z param")
    end
  ));
  print (of_string "Go to next recursive point");
  ltac1:(stepOne);
  ltac1:(toRec);
  repeat (solve_substitutions ());

  let y := Control.hyp @IHRes in
  eexists;
 
  
  let _h_len_t := Control.hyp @IHStripped in
  let _h_len_t_t := Constr.type _h_len_t in
  lazy_match! goal with
  | [_:_ |- context[_ /\ ?res = (?v1 + ?metaFn + ?v2)%Z]] =>
      print (of_string "Manual commutativity on a + b + c => b + (a + c) result");
      assert (($v1 + $metaFn + $v2)%Z = ($metaFn + ($v1 + $v2))%Z) as H_res by ltac1:(lia);

      let h_res_t := Control.hyp @H_res in
      rewrite $h_res_t
      
  | [_:_ |- _] => ()
  end;

  first [
    print (of_string "Trying the current form of IH");
    let ih := Control.hyp @IHStripped in
    exact $ih

  |
    print (of_string "No luck, needs IHExp_fic and transitivity...");
    destruct IHStripped as [IHExp IHPost];
    let ih_exp_t := Control.hyp @IHExp in
    pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic;
    simpl in IHExp_fic;

    print (of_string "Applying transitivity");
    eapply maxKTransitive' >
    [

      print (of_string "Applying IHExp_fic");
      let iHExp_fic_t := Control.hyp @IHExp_fic in
      apply $iHExp_fic_t
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
  ]
  .*)


Ltac2 rec_case_mult_with_val precond heq h t v := 
  (* Heq' is merged with the precondition, to get a new precondition. *)
  (* let precond' := fresh "PreCond" in *)
  (* let Tp := type of precond in
  let Th := type of heq' in *)
  (* assert (Tp /\ Th) as precond' by lia; clear precond; clear heq'; *)
  (* To get to the next recursive step, a single step needs to be made first, since the
     goal is already potentially recursive. *)
  (* revert precond'; revert t; revert h; *)
  recut_preconds();
  repeat (destruct_val_variables t v);
  let gn := Control.numgoals () in
  print (concat (of_string "NO of goals: ") (of_int gn));
  Control.enter (fun () =>
    print (of_string "yolopukki");
    recut_preconds ();
    solve_substitutions ();
    rec_case_mult_inner_with_val h t v;
    print (of_string "HEH?")
  )
  .

(*Things to consider about Z variables: present in the execution or just 
a pseudo variable representing the list?*)


Ltac2 destr a :=
  destruct $a.

Ltac2 base_case_mult_inner_with_val h t v :=
  (* Do a thousand reduction steps. *)
  
  print (of_string "Identifying val variables");
  print_hyps ();
  print_goal ();
  repeat (destruct_val_variables t v);
  
  let gn := Control.numgoals () in
  print (concat (of_string "NO OF GOALS: ") (of_int gn));
  Control.enter (fun () =>
    recut_preconds ();
    ltac1:(stepThousand);
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
          print (of_string "bruv")
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






(*TODO: usage of the given identifiers...maybe less heuristics and a more algorithmic approach is more general*)

Ltac2 Notation "solve_symbolically" h(ident) "," t(list1(ident)) ";" v(list1(ident)) := 
  (* To start, rewrite the goal from inductive to functional *)
  print (of_string "Starting symbolical solution");
  setoid_rewrite RTCEquiv;
  Control.focus 2 2 (fun () => auto);
  (* This is separate, because the loop does not need to rewrite with RTCEquiv *)
  solve_symbolically_internal_mult_with_val h t v.

Ltac2 Notation "solve_symbolically" h(ident) ";" v(list1(ident)) := 
  (* To start, rewrite the goal from inductive to functional *)
  print (of_string "Starting symbolical solution without additional Z parameters");
  setoid_rewrite RTCEquiv;
  Control.focus 2 2 (fun () => auto);
  (* This is separate, because the loop does not need to rewrite with RTCEquiv *)
  solve_symbolically_internal_mult_with_val h [] v;
  print (of_string "bar").


Definition reverse (lst acc : Exp) : Exp :=
  ELetRec [(2,
    °ECase (˝VVar 1)  (* match on List parameter *)
      [([PCons PVar PVar],  (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
        ˝ttrue,
        °EApp (˝VFunId (2, 2)) [˝VVar 1; °ECons (˝VVar 0) (˝VVar 4)]);  (* reverse(T, [H|Acc]) *)
      ([PNil],  (* [] *)
        ˝ttrue,
        ˝VVar 2)])]  (* return Acc *)
  (EApp (˝VFunId (0, 2)) [lst; acc]).


Lemma wellFormedList_can_be_appended : forall (l1 l2 : Val) (n : nat),
  isWellFormedList_n n l2 -> isWellFormedList_n (S n) (VCons l1 l2).
Proof.
  intros.
  simpl.
  exact H.
Qed.

Theorem reverse_One: 
  forall (n : Z) (m : Z) (l : Val) (lh : Val), (0 <= n)%Z /\ (0 <= m)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat m) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
   exists (y : Val),
   ⟨ [], (reverse (˝l) (˝lh)) ⟩ -->* RValSeq [y] /\ True.
Proof.
  solve_symbolically n , m ; l lh.

  3,6: ltac1:(toNextRec).

   3: {
    eexists.
    destruct IHStripped as [IHExp IHPost].
    let ih_exp_t := Control.hyp @IHExp in
    pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic.
    simpl in IHExp_fic.

    eapply maxKTransitive'.

    let hyp_t := Control.hyp @IHExp_fic in
    let hyp_t_t := Constr.type hyp_t in
    lazy_match! hyp_t_t with
    | context[?val.[?close]ᵥ] =>
        let (root_val , root_close) := get_root val close in
        assert (VALCLOSED $root_val)
    end.

    2: {
      repeat (solve_substitutions_in @IHExp_fic).
      

      let hyp_t := Control.hyp @IHExp_fic in
      let hyp_t_t := Constr.type hyp_t in
      lazy_match! hyp_t_t with
      | context[?val.[?close]ᵥ] =>
          let (root_val , root_close) := get_root val close in
          assert (VALCLOSED $root_val)
      end.

      2: {
        repeat (solve_substitutions_in @IHExp_fic).

        remember (VClos [(0, 2, ° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
(° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])) as Close.

        
        let iHExp_fic_t := Control.hyp @IHExp_fic in
        eapply $iHExp_fic_t.
        
      }

      ltac1:(scope_solver_v1).
    }
    assumption.

    split.
    2: exact I.
    

    exists 0.
    simpl.
    reflexivity.
  }



  2: {
    split.

    2: split.

    3: ltac1:(scope_solver_v1).

    3: {
      assert (Z.to_nat (Z.pos p - 1) = n1).
      ltac1:(lia).
      rewrite <- H in _PrecondVal1.
      exact _PrecondVal1.
    }

    3: {
      assert (isWellFormedList_n (Z.to_nat 1) (VCons &l1 VNil)).
      simpl.
      exact I.
      exact H.
    }

    ltac1:(lia).
    ltac1:(lia).

  }

  1: ltac1:(lia).


    eexists.
    destruct IHStripped as [IHExp IHPost].
    let ih_exp_t := Control.hyp @IHExp in
    pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic.
    simpl in IHExp_fic.

    eapply maxKTransitive'.

    let hyp_t := Control.hyp @IHExp_fic in
    let hyp_t_t := Constr.type hyp_t in
    lazy_match! hyp_t_t with
    | context[?val.[?close]ᵥ] =>
        let (root_val , root_close) := get_root val close in
        assert (VALCLOSED $root_val)
    end.

    2: {
      repeat (solve_substitutions_in @IHExp_fic).

      let hyp_t := Control.hyp @IHExp_fic in
      let hyp_t_t := Constr.type hyp_t in
      lazy_match! hyp_t_t with
      | context[?val.[?close]ᵥ] =>
          let (root_val , root_close) := get_root val close in
          assert (VALCLOSED $root_val)
      end.

      2: {
        repeat (solve_substitutions_in @IHExp_fic).

        remember (VClos [(0, 2, ° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
(° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])) as Close.

        
        let iHExp_fic_t := Control.hyp @IHExp_fic in
        eapply $iHExp_fic_t.
      }

      solve_substitutions ().
      ltac1:(scope_solver_v1).
    }
    assumption.

    1 : {
      split.
      2: exact I.

      exists 0.
      simpl.
      reflexivity.
    }

    2: {
      split.
      2:split.
      3:{
        split.

        1: {
          assert (Z.to_nat (Z.pos p - 1) = n1).
          ltac1:(lia).
          rewrite <- H in _PrecondVal1.
          exact _PrecondVal1.
        }

        solve_substitutions ().

        split.
        1: {
          pose (wellFormedList_can_be_appended &l1 (VCons &lh1 &lh2) (S n2)).
          assert (S (S n2) = (Z.to_nat (m + 1))).
          ltac1:(lia).
          rewrite H in i.
          
          apply i.
          assumption.
        }

        split.
        assumption.
        ltac1:(scope_solver_v1).

      }
      ltac1:(lia).
      ltac1:(lia).

    }

    ltac1:(lia).
Qed.

Fixpoint reverseMetaHelp (y : Val) (acc : Val) :=
  match y with
    | VCons hd tl => reverseMetaHelp tl (VCons hd acc)
    | VNil => acc
    | _ => VNil
  end.

Theorem reverse_is_correct: 
  forall (n : Z) (m : Z) (l : Val) (lh : Val), (0 <= n)%Z /\ (0 <= m)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat m) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
   exists (y : Val),
   ⟨ [], (reverse (˝l) (˝lh)) ⟩ -->* RValSeq [y] /\ y = reverseMetaHelp l lh.
Proof.
  solve_symbolically n , m ; l lh.
Admitted.


Ltac2 toRec_in hyp :=
let hyp_t := Control.hyp hyp in
let hyp_t_t := Constr.type hyp_t in
match! hyp_t_t with
| context[exists n : nat, sequentialStepMaxK _ _ n = _] => 
        try (setoid_rewrite <- maxKInsertCanRec in $hyp > [|constructor]); simpl;
        try (setoid_rewrite <- maxKDone in $hyp > [|constructor])
| _ => ()
end.

Ltac2 stepOne_in hyp :=
let hyp_t := Control.hyp hyp in
let hyp_t_t := Constr.type hyp_t in
match! hyp_t_t with
| context[exists n : nat, sequentialStepMaxK _ _ n = _] =>
        try (setoid_rewrite <- maxKForwardOne in $hyp > [|constructor]); simpl
| _ => ()
end.

(* Lemma wellFormedVNil *)

(*TODO: ZIP - UNZIP !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!*)

Definition zip_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (EValues [˝VVar 1 ; ˝VVar 2])
      [([PNil ; PVar],  
        ˝ttrue, 
        ˝VNil);
      ([PVar ; PNil],  
        ˝ttrue,
        ˝VNil);
      ([(PCons PVar PVar); (PCons PVar PVar)], ˝ttrue,
        (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 1; ˝VVar 3])) 
          ((°ECons ((°ETuple [˝VVar 1;˝VVar 3])) (˝VVar 0)))))
        ])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition unzip_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],   
        ˝ttrue, 
        (°ETuple [˝VNil;˝VNil]));
      ([(PCons (PTuple [PVar; PVar]) PVar)],   
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (3, 1)) [˝VVar 2])) 
          [([(PTuple [PVar;PVar])],   
            ˝ttrue, 
          (°ETuple [(°ECons (˝VVar 2) (˝VVar 0));(°ECons (˝VVar 3) (˝VVar 1))]))
          ]))
      ])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Theorem unzip_is_zip_inverse: 
  forall (n : Z) (m : Z) (l : Val) (lh : Val), (1 <= n)%Z /\ (1 <= m)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat m) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
   exists (y : Val),
   ⟨ [], unzip_1 (zip_2 (˝l) (˝lh)) ⟩ -->* RValSeq [y] /\ y = VTuple [l ; lh].
Proof.
  solve_symbolically n , m ; l lh.

  

  (* 3: {

  ltac1:(toNextRec).

  remember ((VClos [(0, 2, ° ECase (° EValues [˝ VVar 1; ˝ VVar 2]) [([PNil; PVar], ˝ VLit "true"%string, ˝ VNil); ([PVar; PNil], ˝ VLit "true"%string, ˝ VNil); ([PCons PVar PVar; PCons PVar PVar], ˝ VLit "true"%string, ° ELet 1 (° EApp (˝ VFunId (4, 2)) [˝ VVar 1; ˝ VVar 3]) (° ECons (° ETuple [˝ VVar 1; ˝ VVar 3])
  (˝ VVar 0)))])] 0 2
  (° ECase (° EValues [˝ VVar 1; ˝ VVar 2]) [([PNil; PVar], ˝ VLit "true"%string, ˝ VNil); ([PVar; PNil], ˝ VLit "true"%string, ˝ VNil); ([PCons PVar PVar; PCons PVar PVar], ˝ VLit "true"%string, ° ELet 1 (° EApp (˝ VFunId (4, 2)) [˝ VVar 1; ˝ VVar 3]) (° ECons (° ETuple [˝ VVar 1; ˝ VVar 3]) (˝ VVar 0)))]))) as ZipClose.

  remember ((VClos [(0, 1, ° ECase (˝ VVar 1) [([PNil], ˝ VLit "true"%string, ° ETuple [˝ VNil; ˝ VNil]); ([PCons (PTuple [PVar; PVar]) PVar], ˝ VLit "true"%string, ° ECase (° EApp (˝ VFunId (3, 1)) [˝ VVar 2]) [([PTuple [PVar; PVar]], ˝ VLit "true"%string, ° ETuple [° ECons (˝ VVar 2) (˝ VVar 0); ° ECons (˝ VVar 3)
  (˝ VVar 1)])])])] 0 1
  (° ECase (˝ VVar 1) [([PNil], ˝ VLit "true"%string, ° ETuple [˝ VNil; ˝ VNil]); ([PCons (PTuple [PVar; PVar]) PVar], ˝ VLit "true"%string, ° ECase (° EApp (˝ VFunId (3, 1)) [˝ VVar 2]) [([PTuple [PVar; PVar]], ˝ VLit "true"%string, ° ETuple [° ECons (˝ VVar 2) (˝ VVar 0); ° ECons (˝ VVar 3) (˝ VVar 1)])])]))) as UnzipClose.


  eexists.
  destruct IHStripped as [IHExp IHPost].
  let ih_exp_t := Control.hyp @IHExp in
  pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic.
  simpl in IHExp_fic.

  let hyp_t := Control.hyp @IHExp_fic in
  let hyp_t_t := Constr.type hyp_t in
  lazy_match! hyp_t_t with
  | context[?val.[?close]ᵥ] =>
      let (root_val , root_close) := get_root val close in
      assert (VALCLOSED $root_val)
  end.

  2: {
    repeat (solve_substitutions_in @IHExp_fic).

    let hyp_t := Control.hyp @IHExp_fic in
    let hyp_t_t := Constr.type hyp_t in
    lazy_match! hyp_t_t with
    | context[?val.[?close]ᵥ] =>
        let (root_val , root_close) := get_root val close in
        assert (VALCLOSED $root_val)
    end.

    2: {
      repeat (solve_substitutions_in @IHExp_fic).

      let iHExp_fic_t := Control.hyp @IHExp_fic in
      apply $iHExp_fic_t.

    }

  }



  } *)
Admitted.


Lemma wellFormed_means_VCons_or_VNil : forall (n : nat) (l : Val), isWellFormedList_n n l -> l = VNil \/ exists (hd tl : Val), l = VCons hd tl.
Proof.
  intros.
  destruct n.
  left.
  simpl in H.
  destruct l; try(ltac1:(nia)).
  reflexivity.
  simpl in H.
  destruct l; try(ltac1:(nia)).
  right.
  exists &l1. exists &l2. reflexivity.
Qed.

Inductive wellFormedListInd : nat -> Val -> Prop :=
 | WFNil : wellFormedListInd 0 VNil
 | WFCons : forall (n : nat) (hd tl : Val), wellFormedListInd n tl -> wellFormedListInd (S n) (VCons hd tl)
.

Lemma wellFormedList_to_ind : forall (n : nat) (l : Val), isWellFormedList_n n l -> wellFormedListInd n l.
Proof.
  intro n.
  induction n.
  {
    intros.
    simpl in H.
    destruct l; try (ltac1:(nia)).
    exact WFNil.
  }
  {
    intros.
    simpl in H.
    destruct l; try (ltac1:(nia)).
    specialize (IHn &l2).

    apply WFCons.
    apply IHn.
    exact H.
  }
  
Qed.

(* Theorem reverse_identity_IND: 
  forall (n : Z) (l : Val), (0 <= n)%Z  /\
    wellFormedListInd (Z.to_nat n) l /\
    VALCLOSED l ->
   exists (y : Val),
   ⟨ [], reverse (reverse (˝l) (˝VNil)) (˝VNil) ⟩ -->* RValSeq [y] /\ y = l.
Proof.
  (* intros.
  destruct H.
  destruct H0.

  destruct H0.

  2: {

  } *)

  

Qed. *)

Theorem reverse_identity: 
  forall (n : Z) (l : Val), (0 <= n)%Z  /\
    isWellFormedList_n (Z.to_nat n) l /\
    VALCLOSED l ->
   exists (y : Val),
   ⟨ [], reverse (reverse (˝l) (˝VNil)) (˝VNil) ⟩ -->* RValSeq [y] /\ y = l.
Proof.

  (* intros.


  pose (reverse_One n 0 l VNil). *)

  

  solve_symbolically n ; l.

  3: {

    ltac1:(toNextRec).

   

    pose (wellFormedList_to_ind n1 &l2 _PrecondVal0) as isList_l2.

    clear H_formed_add_eq.
    clear HP2 n0.
    clear IH.
    clear H3 H4.
    clear heq _PrecondVal.
    revert precond.



    

    induction isList_l2.

    2: {

       remember (VClos [(0, 2, ° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
  (° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])) as Close.

    








      eapply maxKTransitive'.

      2 : {
      
      }


      e

    }






        
    2: {
      exact IHn.
    }

   

    Locate Proper.
    Search Coq.Classes.Morphisms.Proper.

    Locate "==>".
    Search (respectful _ _ ).
    Locate "eq".
    







  }

  (* clear IH.
  clear HP2  n0.
  clear _PrecondVal.
  clear H3 H4.
  clear precond.
  clear H_formed_add_eq.
  clear heq. *)

  induction l2; destruct n1; simpl in _PrecondVal0; try (ltac1:(nia)).

  2: {
     remember (VClos [(0, 2, ° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
  (° ECase (˝ VVar 1) [([PCons PVar PVar], ˝ VLit "true"%string, ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])) as Close.

    intros.

    simpl in _PrecondVal0.

    specialize (IHn1 _PrecondVal0).

  }
  

 


  induction l2.

  simpl in _PrecondVal0.



  induction (isWellFormedList_n n1 l2);

  simpl in _PrecondVal0.
  destruct l2; try (ltac1:(nia));

  


  2: {

  eexists.

  split.

  


  assert (exists y : Val, (exists n : nat, sequentialStepMaxK [FParams (IApp Close) [VNil ; VCons &l1 VNil] []; FParams (IApp Close) [&l2] [˝ VNil]] RBox n = ([], RValSeq [y])) ∧ y = VCons &l1 &l2).

  2: {
    

  }



  (* eassert ((∃ n : nat, sequentialStepMaxK [FParams (IApp Close) [_.[up_subst (Close .: idsubst)]ᵥ.[Close/]ᵥ; VCons &l1 VNil] []; FParams (IApp Close) [] [˝ VNil]] RBox n = ([], RValSeq[IHRes])) ∧ IHRes = _).

  2: {

  }


  } *)

  }

  (* edestruct ReverseIsCorrect.
    
    1: {
        split.
        ltac1:(lia).
        split.
        ltac1:(lia).
        split.
        assert (Z.to_nat (Z.pos p - 1) = n1).
        ltac1:(lia).
        rewrite H.
        assumption.
        split.
        simpl.
        exact I.
        split; ltac1:(scope_solver_v1).

    }

    destruct H.

    setoid_rewrite RTCEquiv in H.

    eexists.
    eapply maxKTransitive'.

    unfold reverse in H.

    toRec_in @H.
    simpl in H.

    rewrite <- HeqClose in H.

    solve_substitutions_in @H.



    eapply maxKTransitive'.

    2: {
      split.
      1:exact H.
      exact H0.
    }

    ltac1:(stepOne).

    





    destruct H.

    clear H0.

    unfold reverse in H.

    assert (FParams (IApp Close) [&l2; VCons &l1 VNil] [] = FParams IValues [x] []).

    2: {
      rewrite H0.

      ltac1:(stepOne).

      eexists.

      split.


      rewrite HeqClose.
      ltac1:(toNextRec).
      rewrite <- HeqClose.


      eexists.
      destruct IHStripped as [IHExp IHPost].
      let ih_exp_t := Control.hyp @IHExp in
      pose (frame_indep_core_func _ _ _ _ $ih_exp_t) as IHExp_fic.
      simpl in IHExp_fic.

      2: reflexivity.


      let hyp_t := Control.hyp @IHExp_fic in
      let hyp_t_t := Constr.type hyp_t in
      lazy_match! hyp_t_t with
      | context[?val.[?close]ᵥ] =>
          let (root_val , root_close) := get_root val close in
          assert (VALCLOSED $root_val)
      end.

      2: {
        repeat (solve_substitutions_in @IHExp_fic).

        let iHExp_fic_t := Control.hyp @IHExp_fic in
        apply $iHExp_fic_t.
        

    eapply maxKTransitive'.


    }

    }}

  
    

    


    

    

    


    let hyp_t := Control.hyp @IHExp_fic in
    let hyp_t_t := Constr.type hyp_t in
    lazy_match! hyp_t_t with
    | context[?val.[?close]ᵥ] =>
        let (root_val , root_close) := get_root val close in
        assert (VALCLOSED $root_val)
    end.

    2: {
      repeat (solve_substitutions_in @IHExp_fic).
      
      let hyp_t := Control.hyp @IHExp_fic in
      let hyp_t_t := Constr.type hyp_t in
      lazy_match! hyp_t_t with
      | context[?val.[?close]ᵥ] =>
          let (root_val , root_close) := get_root val close in
          assert (VALCLOSED $root_val)
      end.

      2: {
        repeat (solve_substitutions_in @IHExp_fic).
        
        let iHExp_fic_t := Control.hyp @IHExp_fic in
        apply $iHExp_fic_t.
      }
      
      ltac1:(scope_solver_v1).  
    }


    ltac1:(scope_solver_v1).

  
    split.
    2: {
      reflexivity.
    }

    exists 0.
    rewrite IHPost.
    simpl.
    reflexivity.
   }

   2: {
    split.
    2: {
      split.
      2: {
        ltac1:(scope_solver_v1).
      }
      pose (wellFormedList_can_be_appended &l1 &l2 n1).
      rewrite <- H_formed_add_eq in i.
      apply i.
      assumption.
      
    }
    assumption.
   } *)
Qed.