From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.
From CoreErlang.Symbolic Require Import SymbTheorems.

Import ListNotations.

(** This file contains tactics that can be used to solve program property goals.
    The tactic "solve_symbolically i1 [i2 ...]" can solve goals for programs that
    are non-recursive, and structurally recursive programs that use their first
    argument for the recursion. This first argument needs to be an integer (Z).

    The "solve_symbolically" tactic works for goals in the following form:

          forall i1 i2... , PreCond (i1 i2 ...) ->
          exists o1 o2... , ⟨ [], prog (i1 i2 ...) ⟩ -->* REnd (o1 o2 ...)
                              /\ PostCond (i1 i2 ... o1 o2 ...)

    - i1 i2... are symbolic variables
    - PreCond (i1 i2 ...) is of type "Prop", and it's the conjunction of all
      preconditions. These preconditions depend on the symbolic variables.
      If no precondition needs to be given, PreCond (i1 i2 ...) should be "True".
    - o1 o2... are subterms of the end configuration
    - prog (i1 i2 ...) is a redex at the start of the evaluation, parameterized
      by the symbolic variables. It should be a function application, with i1 i2 ...
      being the parameters of the function.
    - REnd (o1 o2 ...) is the end configuration, parameterized by the subterms
      introduced in the exists. By the nature of the RTC, REnd (o1 o2 ...) is either
      an "RValSeq" or "RExc".
    - PostCond (i1 i2 ... o1 o2 ...) is of type Prop, and it's the conjunction
      of all postconditions. These postcondicions depend on the symbolic variables
      and the end configuration subterms. If no postconditions needs to be given,
      PostCond (i1 i2 ... o1 o2 ...) should be "True".

    If the solve_symbolically tactic receives a goal in the above form, the forms
    of goals in the subtactics will be correctly taken care of. It's especially
    important for "True" to be provided as a pre- or postcondition, in case the
    respective condition is not needed.

    An example for the kind of goal that "solve_symbolically" can prove:

          forall (z : Z), (0 <= z)%Z ->
          exists (y : Z), ⟨ [], (fact_frameStack (˝VLit z)) ⟩ -->* RValSeq [VLit y] 
                          /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z))%Z).

    For the example above,
    - i1 : Z := z
    - PreCond (i1) : Prop := (0 <= z)%Z
    - o1 : Z := y
    - prog (i1) : Redex := RExp (fact_frameStack (˝VLit z))
                           (see SymbExamples for fact_frameStack)
    - REnd (o1) : Redex := RValSeq [VLit y]
    - PostCons (i1 o1) : Prop := (y = Z.of_nat (Factorial.fact (Z.to_nat z))%Z)

    The "solve_symbolically" tactic needs to be given all symbolic variables (i1, i2, ...)
    The tactic evaluates the program symbolically. If branching is needed, the branch
    condition gets added to the precondition, and the evaluation continues on all
    branches. If the program terminates, the tactic tries to either prove the branch
    is impossible to reach, or prove the postcondition. If the studied function is
    structurally recursive, and the recursion is done on the first argument, which is
    also of type Z, the tactic can also solve the goal. If the program terminates, but the
    postcondition could not be solved, the user needs to do that manually.
 *)

(* Guard tactic to see if case separation is needed. *)
Ltac contains_match :=
  lazymatch goal with
  | |- context[match _ with _ => _ end] => idtac
  | |- _ => fail
  end.

(* Guard tactic to see if the configuration is potentially recursive. *)
Ltac possibly_recursive :=
  lazymatch goal with
  | |- context[FParams (IApp (VClos (_ :: _) _ _ _)) _ [] :: _] => idtac
  | |- _ => fail
  end.

(* The "case_innermost" tactic is for performing destruct on the innermost match expression.
   This is used during case separation, where the cases manifest as deeply-nested pattern
   matches. *)

(* This subtactic does the actual case separation. In case "=?" is used, it's also
   converted into "=" or "<>", because lia and nia work better with the latter.
   Heq will be the name of the introduced hypothesis. *)
Ltac case_innermost_term t Heq :=
  lazymatch t with
  | context[match ?x with _ => _ end] =>
      first [ case_innermost_term x Heq
            | destruct x eqn:Heq;
              first [apply Z_eqb_eq_corr in Heq
                    |apply Z_eqb_neq_corr in Heq
                    | idtac]]
  | _ => fail "No match subterm found"
  end.

(* Performing "case_innermost" in the goal. *)
Ltac case_innermost Heq :=
  match goal with
  | |- ?g => case_innermost_term g Heq
  end.

(* Performing "case_innermost" in a Hypo. *)
Ltac case_innermost_in H Heq :=
  let T := type of H in
  case_innermost_term T Heq.

(* Notations for the last 2 tactics. *)
Tactic Notation "case_innermost" ident(Heq) :=
  case_innermost Heq.

Tactic Notation "case_innermost" ident(H) ident(Heq) :=
  case_innermost_in H Heq.

(* This tactic tries to get to a potentially recursive configuration. At most 1000
   steps are performed (see SymbTheorems/maxKInsertCanRec). *)
Ltac toRec :=
match goal with
| |- context[exists n : nat, sequentialStepMaxK _ _ n = _] => 
        try (setoid_rewrite <- maxKInsertCanRec;[|constructor]);simpl;
        try (setoid_rewrite <- maxKDone;[|constructor])
| _ => idtac
end.

(* Performing at most 1 reduction step. *)
Ltac stepOne :=
match goal with
| |- context[exists n : nat, sequentialStepMaxK _ _ n = _] =>
        try (setoid_rewrite <- maxKForwardOne;[|constructor]);simpl
| _ => idtac
end.

(* Performing at most 1000 reduction steps *)
Ltac stepThousand :=
match goal with
| |- context[exists n : nat, sequentialStepMaxK _ _ n = _] =>
        try (setoid_rewrite <- maxKForwardThousand;[|constructor]);simpl
| _ => idtac
end.

(* Guard tactic to see if we can start the inductive reasoning algorithm. *)
Ltac able_to_ind :=
  lazymatch goal with
  | |- context[sequentialStepMaxK ?fs ?r] => 
       let b := eval compute in (canRec fs r) in
         lazymatch b with
         | true => idtac
         | false => fail
         end
  | |- _ => fail
  end.

(* Guard tactic to see if we have not yet terminated. *)
Ltac is_not_terminated :=
  lazymatch goal with
  | |- context[sequentialStepMaxK _ _ _] => idtac
  | |- _ => fail
  end.

(* Tactic for solving
      exists _, ([], r) = ([], ?r) 
   The unexpected end state part should never be able to run, because "solve_symbolically"
   makes sure to only call this subtactic in the case above. *)
Ltac solve_final_state := 
  exists 0; (* This is for the step number, which is always irrelevant (|- nat) when this tactic is called *)
     first [ auto (* The program indeed terminated at ([], r) where is_result r *)
           | idtac "Unexpected end state 
                    (can be due to an exception in the Erlang program,
                     a result when an exception was expected,
                     non-termination in the given depth or
                     an impossible precondition that was not ruled out)"
           ].

(* Tactic to solve the final postcondition, or impossible branch. If extra SMT solvers
   are added to the project, they should be put here. *)
Ltac solve_final_postcond :=
  first [ nia
        | auto
        | idtac "Could not solve postcondition"
        ].

(* Solving a terminated goal. This requires the max K function to not be in the goal. *)
Ltac solve_terminated :=
  lazymatch goal with
  | |- context[sequentialStepMaxK] => fail "The program has not yet terminated"
  | |- _ =>
    lazymatch goal with
    | |- ex _ => eexists;solve_terminated
    | |- _ /\ _ => split;[solve_final_state|solve_final_postcond]
    | |- _ => idtac
    end
  end.

Ltac strip_IH_precond IH :=
  (* By this point, the induction hypothesis is an implication chain, similar to this:

            IH : C1 -> C2 -> ... -> Cn -> forall s1 s2 ... , PreCond -> ...

     This tactic strips the IH of the conditions C1 ... Cn before the forall, which can
     all be solved using lia. Note that some tricks are needed, because implication is
     just syntactic sugar for a forall in Coq.

                 P -> Q      is equivalent to      forall _ : P, Q

     The trick is to first get the condition C1, use lia to prove it, then specialize IH
     with it. C1 can then be cleared.

     The problem with tha lazymatch is that (| ?p -> _) will also match on
     (forall _ : ?p, _). However, asserting (_ : ?p) cannot be solved by lia. So after this
     tactic, we've simplified IH to:

            IH : forall s1 s2 ... , PreCond -> ...
  *)
  let TIH := type of IH in
  lazymatch TIH with
  | ?p -> _ => 
    let H := fresh "Heq" in
    try (
    assert p as H by lia; specialize (IH H); clear H;
    strip_IH_precond IH)
  | _ => idtac
  end.

Ltac destruct_until_conj IH :=
  (* By this point, IH will be in the form:

            IH : exists t1 t2 ... , (Term /\ PostCond)

     Since IH is a hypothesis, destruct can be used to 'give values to' t1, t2, etc.
   *)
  lazymatch (type of IH) with
  | _ /\ _ => idtac
  | ex _ => 
    let x := fresh "x" in
    destruct IH as [x IH]; destruct_until_conj IH
  | _ => idtac
  end.

Ltac eexists_until_conj :=
  (* By this point, the goal will be in the form:

            |- exists t1 t2 ... , (Term /\ PostCond)

     eexists can be used to 'give values to' t1, t2, etc.
   *)
  lazymatch goal with
  | |- _ /\ _ => idtac
  | |- ex _ => eexists; eexists_until_conj
  | |- _ => idtac
  end.

Ltac separate_cases_mult h t :=
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

Ltac base_case_mult_inner h t :=
  (* Do a thousand reduction steps. *)
  stepThousand;
  first [ (* If we run into a match expression, separate the cases. *)
          contains_match;
          separate_cases_mult h t;
          base_case_mult_inner h t
        | (* If we do not have a match expression but we have not terminated, continue the loop. *)
          is_not_terminated;
          base_case_mult_inner h t
        | (* If we have terminated, solve the terminated state. *)
          intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated goal"
        ].

Ltac base_case_mult precond heq' h t := 
  (* This tactic is for the base case of the induction. Since "solve_symbolically" can
     only be used for structurally recursive functions, this case will definitely
     terminate. We need to get back to the standard form where symbolic variables are
     universally quantified. The precondition is unified with the branch condition,
     and everything is reverted in order. Symbolic evaluation is done in 
     "base_case_mult_inner". *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  revert precond'; revert t; revert h;
  base_case_mult_inner h t.

Ltac spec_rest_of_terms IH vl :=
  match vl with
  | [] => idtac
  | VLit ?lit :: ?vl' =>
    match lit with
    | Integer ?i => specialize (IH i)
    | Atom ?a => specialize (IH a)
    end;
    spec_rest_of_terms IH vl'
  | _ => fail "Unexpected error during induction: unsupported argument type"
  end.

Ltac rec_case_mult_inner IH h t :=
  toRec;
  first [ (* If case separation is found while getting to the next recursive step,
             continue on all branches *)
          contains_match;
          separate_cases_mult h t;
          rec_case_mult_inner IH h t
        | (* If the function is possibly recursive, we can assume that we have reached the
             next point of recursion. *)
          possibly_recursive;
          intros h; intros t;
          let precond := fresh "PreCond" in
          intros precond;
          (* The list of computed parameters needs to be extracted from the goal. In this
             tactic, the parameters are either integers or atoms. *)
          lazymatch goal with
          | |- context[FParams (IApp (VClos (_ :: _) _ _ _)) ?vl [] :: _] => 
            match vl with
            (* TODO: currently only integers and atoms are supported, extend this to
                     other types, e.g. lists *)
            | VLit ?lit :: ?vl =>
              (* IH is specialized by the variable the function is doing recursion on
                 (the first argument) *)
              match lit with
              | Integer ?i => specialize (IH i)
              | Atom ?a => specialize (IH a)
              end;
              (* IH is specialized by the condition introduced by the induction itself. *)
              strip_IH_precond IH;
              (* IH is specialized by the rest of the symbolic variables. *)
              spec_rest_of_terms IH vl
            | _ => fail "Unexpected error during induction: unsupported argument type"
            end;
            (* IH is specialzed by the precondition. *)
            strip_IH_precond IH;
            (* Terminal subterms are existential, they can be separated from IH by destruct. IH is
               then separated to the termination of the recursion, and the postcondition of said
               recursion termination. *)
            destruct_until_conj IH;
            let IHExp := fresh "IHExp" in
            let IHPostcond := fresh "IHPostcond" in
            destruct IH as [IHExp IHPostcond];
            (* The functional version of the frame_indep_core lemma is applied. *)
            let IHExp_fic := fresh "IHExp_fic" in
            pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic; simpl in IHExp_fic;
            (* Existential variables are created using eexists. *)
            eexists_until_conj;
            (* The transitivity property of the frame stack semantics is used. *)
            eapply maxKTransitive';[apply IHExp_fic|];
            clear IHExp IHExp_fic;
            (* The postcondition from the recursive step can be seen as a precondition
               for the rest of the evaluation. Thus, they are merged together. *)
            let precond' := fresh "PreCond" in
            let Tp := type of precond in
            let Th := type of IHPostcond in
            assert (Tp /\ Th) as precond' by nia;
            clear precond IHPostcond;
            (* All the variables are reverted, along with the precondition. This is because the rest
               of the goal is not recursive, thus it can be solved with the same algorithm as the
               base case. *)
            revert precond'; revert t; revert h;
            base_case_mult_inner h t
          | |- _ => fail "Could not get parameter list."
          end
        | (* If we did not reach a pattern match, or a point of recursion, but the function has
             not terminated yet, then toRec (1000 steps) was not enought, so we continue. *)
          is_not_terminated;
          rec_case_mult_inner IH h t
        | (* However, if we did terminate, then solve_terminated can solve the goal. *)
          intros; solve_terminated
        ].


Ltac rec_case_mult precond heq' IH h t := 
  (* Heq' is merged with the precondition, to get a new precondition. *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  (* To get to the next recursive step, a single step needs to be made first, since the
     goal is already potentially recursive. *)
  revert precond'; revert t; revert h;
  stepOne;
  rec_case_mult_inner IH h t.

Ltac solve_induction_mult h t :=
  (* To solve using induction, first introduce the variables and the precondition. *)
  intro h; intros t;
  let precond := fresh "PreCond" in
  intros precond;
  (* IH needs to be as general as possible, but we need to know that 0 <= h, which is in the
     precondition. So we need to assert it with lia, before reverting the precondition. *)
  let heq := fresh "Heq" in
  assert (0 <= h)%Z as heq by lia;
  revert precond; revert t;
  (* Induction is performed. In the new goal, the symbolic variable h is universally quantified
     again, the introduced version is irrelevant along with Heq, thus they can be deleted when
     they are not needed anymore. *)
  apply Zlt_0_ind with (x := h);[clear heq; clear h|exact heq];
  (* Since the old h was cleared, the name can be reused for its new universally quantified
     instance. The induction hypothesis is introduced as IH. We also know that 0 <= h, this is
     given by Zlt_0_ind itself. Heq can be reused, since it was cleared. It can be cleared
     again, since it directly comes from PreCond. PreCond is introduced after Heq. *)
  intros h;
  let IH := fresh "IH" in
  intros IH; intros heq; intros t; clear heq; intros precond;
  (* Destructing h gives 3 cases, the first is a base case with 0, the second is positive,
     and the third is negative. Since we assume that the recursive function decreases on h,
     the first case will terminate (IH not needed), the second will recurse, and the third
     is impossible, because h cannot be negative. *)
  let heq' := fresh "Heq" in
  destruct h eqn:heq';
    [clear IH;base_case_mult precond heq' h t| rec_case_mult precond heq' IH h t|nia].

Ltac take_to_rec_loop_mult h t :=
  toRec;
  first [ (* If the goal might be recursive... *)
          possibly_recursive;
          idtac "trying induction...";
          solve_induction_mult h t
        | (* If we can find a match expression... *)
          contains_match;
          separate_cases_mult h t;
          solve_symbolically_internal_mult h t
        | (* If we did not hit a point of recursion, or a case separation,
             the loop needs to be continued. 
             
             A single step is done manually, 
             because non-recursive functions defined in a LetRec can cause issues:
             we can get to a point of potential recursion, but since the function is
             not in fact recursive, that branch will fail. Without this stepOne, we
             can run into an infinite loop.
             *)
          stepOne;
          solve_symbolically_internal_mult h t
        ]
with
solve_symbolically_internal_mult h t :=
  first [ (* If sequentialStepMaxK is still in the goal, and we did not hit recursion yet,
             then try moving forward to a point of recursion. *)
          is_not_terminated; take_to_rec_loop_mult h t
          (* If sequentialStepMaxK is not in the goal, we have terminated. *)
        | intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated program"
        ].

(* HACK: it is way easier, to handle cases with 1 and more than 1 symbolic variables separately.
   Ltac is very peculiar with empty parameter lists, which is annoying.

   Tactics ending in "_0" are copies of tactics ending in "_mult", but for them only the
   first symbolic variable (h) is provided without the rest (t). We provide "Tactic Notation"
   to use "solve_symbolically_internal_mult" and "solve_symbolically_internal_0" in the cases
   where more than 1 parameter is given and only 1 parameter is given.

   The upside of this approach is the individual sub-tactics are way less complicated,
   but the downside is making changes requires refactoring in two places. *)

Tactic Notation "solve_symbolically" ident(h) ne_ident_list(t) := 
  (* To start, rewrite the goal from inductive to functional *)
  setoid_rewrite RTCEquiv;[|auto];
  (* This is separate, because the loop does not need to rewrite with RTCEquiv *)
  solve_symbolically_internal_mult h t.

Ltac separate_cases_0 h :=
  (* If we find a match expression, then introduce the variable h, along with the precondition. *)
  let precond := fresh "PreCond" in
  let heq := fresh "Heq" in
  intros h; intros precond;
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
  revert h precond'.

Ltac base_case_0_inner h :=
  (* Do a thousand reduction steps. *)
  stepThousand;
  first [ (* If we run into a match expression, separate the cases. *)
          contains_match;
          separate_cases_0 h;
          base_case_0_inner h
        | (* If we do not have a match expression but we have not terminated, continue the loop. *)
          is_not_terminated;
          base_case_0_inner h
        | (* If we have terminated, solve the terminated state. *)
          intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated goal"
        ].

Ltac base_case_0 precond heq' h := 
  (* This tactic is for the base case of the induction. Since "solve_symbolically" can
     only be used for structurally recursive functions, this case will definitely
     terminate. We need to get back to the standard form where symbolic variables are
     universally quantified. The precondition is unified with the branch condition,
     and everything is reverted in order. Symbolic evaluation is done in 
     "base_case_mult_inner". *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  revert h precond';
  base_case_0_inner h.

Ltac rec_case_0_inner IH h :=
  toRec;
  first [ (* If case separation is found while getting to the next recursive step,
             continue on all branches *)
          contains_match;
          separate_cases_0 h;
          rec_case_0_inner IH h
        | (* If the function is possibly recursive, we can assume that we have reached the
             next point of recursion. *)
          possibly_recursive;
          intros h; 
          let precond := fresh "PreCond" in
          intros precond;
          (* The list of computed parameters needs to be extracted from the goal. In this
             tactic, the function has only 1 parameter, which is either an integer or an atom. *)
          lazymatch goal with
          | |- context[FParams (IApp (VClos (_ :: _) _ _ _)) ?vl [] :: _] => 
            match vl with
            | [] => fail "Too few function parameters"
            (* TODO: currently only integers and atoms are supported, extend this to
                     other types, e.g. lists *)
            | [VLit (Integer ?i)] => specialize (IH i)
            | [VLit (Atom ?a)] => specialize (IH a)
            | _ :: _ => fail "Too many function parameters"
            | _ => fail "Unexpected error during induction"
            end;
            (* IH is specialzed by the condition introduced by the induction itself, and the
               precondition. Since this version of the tactic only takes a single symbolic variable, no
               more specialization is needed. *)
            strip_IH_precond IH;
            (* Terminal subterms are existential, they can be separated from IH by destruct. IH is
               then separated to the termination of the recursion, and the postcondition of said
               recursion termination. *)
            destruct_until_conj IH;
            let IHExp := fresh "IHExp" in
            let IHPostcond := fresh "IHPostcond" in
            destruct IH as [IHExp IHPostcond];
            (* The functional version of the frame_indep_core lemma is applied. *)
            let IHExp_fic := fresh "IHExp_fic" in
            pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic; simpl in IHExp_fic;
            (* Existential variables are created using eexists. *)
            eexists_until_conj;
            (* The transitivity property of the frame stack semantics is used. *)
            eapply maxKTransitive';[apply IHExp_fic|];
            clear IHExp IHExp_fic;
            (* The postcondition from the recursive step can be seen as a precondition
               for the rest of the evaluation. Thus, they are merged together. *)
            let precond' := fresh "PreCond" in
            let Tp := type of precond in
            let Th := type of IHPostcond in
            assert (Tp /\ Th) as precond' by nia;
            clear precond IHPostcond;
            (* The variable h is reverted, along with the precondition. This is because the rest
               of the goal is not recursive, thus it can be solved with the same algorithm as the
               base case. *)
            revert h precond';
            base_case_0_inner h
          | |- _ => fail "Could not get parameter list."
          end
        | (* If we did not reach a pattern match, or a point of recursion, but the function has
             not terminated yet, then toRec (1000 steps) was not enought, so we continue. *)
          is_not_terminated;
          rec_case_0_inner IH h
        | (* However, if we did terminate, then solve_terminated can solve the goal. *)
          intros; solve_terminated
        ].

Ltac rec_case_0 precond heq' IH h := 
  (* Heq' is merged with the precondition, to get a new precondition. *)
  let precond' := fresh "PreCond" in
  let Tp := type of precond in
  let Th := type of heq' in
  assert (Tp /\ Th) as precond' by lia; clear precond; clear heq';
  (* To get to the next recursive step, a single step needs to be made first, since the
     goal is already potentially recursive. *)
  revert h precond';
  stepOne;
  rec_case_0_inner IH h.

Ltac solve_induction_0 h :=
  (* To solve using induction, first introduce the variable and the precondition. *)
  intro h;
  let precond := fresh "PreCond" in
  intros precond;
  (* IH needs to be as general as possible, but we need to know that 0 <= h, which is in the
     precondition. So we need to assert it with lia, before reverting the precondition. *)
  let heq := fresh "Heq" in
  assert (0 <= h)%Z as heq by lia;
  revert precond;
  (* Induction is performed. In the new goal, the symbolic variable h is universally quantified
     again, the introduced version is irrelevant along with Heq, thus they can be deleted when
     they are not needed anymore. *)
  apply Zlt_0_ind with (x := h);[clear heq; clear h|exact heq];
  (* Since the old h was cleared, the name can be reused for its new universally quantified
     instance. The induction hypothesis is introduced as IH. We also know that 0 <= h, this is
     given by Zlt_0_ind itself. Heq can be reused, since it was cleared. It can be cleared
     again, since it directly comes from PreCond. PreCond is introduced after Heq. *)
  intros h;
  let IH := fresh "IH" in
  intros IH; intros heq; clear heq; intros precond;
  (* Destructing h gives 3 cases, the first is a base case with 0, the second is positive,
     and the third is negative. Since we assume that the recursive function decreases on h,
     the first case will terminate (IH not needed), the second will recurse, and the third
     is impossible, because h cannot be negative. *)
  let heq' := fresh "Heq" in
  destruct h eqn:heq';
    [clear IH;base_case_0 precond heq' h| rec_case_0 precond heq' IH h|nia].

Ltac take_to_rec_loop_0 h :=
  toRec;
  first [ (* If the goal might be recursive... *)
          possibly_recursive;
          idtac "trying induction...";
          solve_induction_0 h
        | (* If we can find a match expression... *)
          contains_match;
          separate_cases_0 h;
          solve_symbolically_internal_0 h
        | (* If we did not hit a point of recursion, or a case separation,
             the loop needs to be continued. 
             
             A single step is done manually, 
             because non-recursive functions defined in a LetRec can cause issues:
             we can get to a point of potential recursion, but since the function is
             not in fact recursive, that branch will fail. Without this stepOne, we
             can run into an infinite loop.
             *)
          stepOne;
          solve_symbolically_internal_0 h
        ]
with
solve_symbolically_internal_0 h := 
  first [ (* If sequentialStepMaxK is still in the goal, and we did not hit recursion yet,
             then try moving forward to a point of recursion. *)
          is_not_terminated; take_to_rec_loop_0 h
          (* If sequentialStepMaxK is not in the goal, we have terminated. *)
        | intros; solve_terminated
        | idtac "Unexpected error: could not solve terminated program"
        ].

Tactic Notation "solve_symbolically" ident(h) :=
  setoid_rewrite RTCEquiv; [|auto];
  solve_symbolically_internal_0 h.

(* TODO
   - technically, symbolic evaluation without any symbolic variables (i.e. just evaluating)
     is not yet supported, because the solve_symbolically tactic needs at least one variable.
   - check this on the other functions
   - look at the difference of z and x in the tactics: am I possibly messing something up?
     
     THINK/ASK ABOUT IT:
       Am I right, is it only possible to have a function application with an empty list of
       parameters left to evaluate on the *top* of the frame stack?
*)
