(**
  This file contains assignments about the semantics of Core Erlang, which can
  help the readers get familiar with it.
*)
(* From CoreErlang.BigStep Require Import FunctionalBigStep. *)
From CoreErlang.FrameStack Require SubstSemantics
                                   CIU.
From CoreErlang.FrameStack Require Import Examples.

Open Scope string_scope.

Module FrameStack.

Import FrameStack.SubstSemantics FrameStack.CIU.
Import ListNotations.
(*
  Let "e" be a parameter expression.

  letrec 'fact'/1 =
    fun(X) ->
      case <X> of
        <0> when 'true' -> 1
        <Z>  when 'true'->
          let <Y> = <apply 'fact'/1(call 'erlang':'-'(Z, 1))>
            in call 'erlang':'*'(Z,Y)
    in
      apply 'fact'/1(e)

  Define the above expression!
 *)

Definition fact (e : Exp) : Exp :=
  ELetRec [(1, 
    °ECase (˝VVar 1) 
      [([PLit (Integer 0)], ˝ttrue, ˝VLit (Integer 1)) ;
       ([PVar], ˝ttrue, 
                        °ELet 1 (°EApp (˝VFunId (1, 1)) [°ECall (˝VLit (Atom "erlang"%string)) (˝VLit (Atom "-"%string)) [˝VVar 0 ; ˝VLit (Integer 1)]])
                               (°ECall (˝VLit (Atom "erlang"%string)) (˝VLit (Atom "*"%string)) [˝VVar 0 ; ˝VVar 1]))]
      )]
  (°EApp (˝VFunId (0, 1)) [e]). (* Write the definition here *)



 Ltac match_list_solver :=
  match goal with
  (*TODO: is the first pattern neccessary?*)
  | [ |- Some _ = None] => fail
  | [ |- Some _ = Some _] => auto
  | [ |- None = None] => auto
  | _ => fail "Unexpected goal in match_list_solver"
  end.

 Ltac one_step_full_solver :=
  match goal with
  | [ |- ⟨ FParams _ _ (_ :: _) :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_step_params
  | [ |- ⟨ FParams _ _ (_ :: _) :: _ , RBox ⟩ --> ⟨ _ , _ ⟩] => apply eval_step_params_0; discriminate
  | [ |- ⟨ FParams _ _ [] :: _ , RBox ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_params_0; discriminate; auto
  | [ |- ⟨ FParams _ _ [] :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => eapply eval_cool_params; auto

  (*needs testing*)
  | [ |- ⟨ _ , RExp (° EValues _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_values
  (*needs testing*)
  | [ |- ⟨ _ , RExp (° ETuple _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_tuple
  (*needs testing*)
  | [ |- ⟨ _ , RExp (° EMap [])⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_map_0
  | [ |- ⟨ _ , RExp (° EMap ((_, _) :: _)) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_map

  | [ |- ⟨ _ , RExp (° ECall _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_mod
  | [ |- ⟨ FCallMod _ _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_fun
  | [ |- ⟨ FCallFun _ _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_call_params

  | [ |- ⟨ _ , RExp (° EPrimOp _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_primop

  | [ |- ⟨ FApp1 _ :: _  , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_app2
  | [ |- ⟨ _ , RExp (° EApp _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_app

  (*needs testing*)
  | [ |- ⟨ FCons1 _ :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_cons_1
  | [ |- ⟨ FCons2 _ :: _ , RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_cons_2
  | [ |- ⟨ _ , RExp (° ECons _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_cons

  | [ |- ⟨ FLet _ _ :: _, RValSeq _ ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_let; reflexivity
  | [ |- ⟨ _, RExp (° ELet _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_let
  (*needs testing*)
  | [ |- ⟨ FSeq _ :: _, RValSeq [ _ ] ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_seq
  (*needs testing*)
  | [ |- ⟨ _, RExp (° ESeq _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_seq
  (*needs testing*)
  | [ |- ⟨ _, RExp (° EFun _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_fun
 
  

  | [ |- ⟨ _ , RExp (° ECase _ _)⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_case
  (***)
  | [ |- ⟨ FCase1 (_ :: _) :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_not_match; cbv; match_list_solver
  | [ |- ⟨ FCase1 (_ :: _) :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_match; cbv; match_list_solver

  | [ |- ⟨ FCase2 _ _ _ :: _ , RValSeq [ VLit (Atom "true") ]⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_true
  | [ |- ⟨ FCase2 _ _ _ :: _ , RValSeq [ VLit (Atom "false") ]⟩ --> ⟨ _ , _ ⟩] => apply eval_step_case_false
  (***)
  (*needs testing*)
  | [ |- ⟨ FCase1 [] :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_case_empty

  | [ |- ⟨ _ , RExp (° ELetRec _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_letrec; auto
  (*needs testing*)
  | [ |- ⟨ FTry _ _ _ _ :: _ , RValSeq _⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_try_ok; auto
  | [ |- ⟨ FTry _ _ 3 _ :: _ , RExc (_ , _ , _)⟩ --> ⟨ _ , _ ⟩] => apply eval_cool_try_err
  | [ |- ⟨ _ , RExp (° ETry _ _ _ _ _) ⟩ --> ⟨ _ , _ ⟩] => apply eval_heat_try

  | [ |- ⟨ _ :: _ , RExc _⟩ --> ⟨ _ , _ ⟩] => apply eval_prop_exc; auto
  
  
  (*No other pattern matches, needs cooling*)
  | [ |- ⟨ _ , _ ⟩ --> ⟨ _ , _ ⟩] => apply SubstSemantics.cool_value
  
  end.

Ltac reduce_subst_semantics :=
  match goal with
  | [ |- ⟨ ?f , ?e ⟩ -[ ?k ]-> ⟨ ?f , ?e ⟩] => apply step_refl
  | [ |- ⟨ _ , _ ⟩ -[ ?k ]-> ⟨ _ , _ ⟩] => eapply step_trans; [one_step_full_solver | idtac]; cbv 
  end.

Ltac auto_proove_subst_semantics_in_k_steps := repeat reduce_subst_semantics.

Ltac auto_proove_subst_semantics := 
    eexists;
    split; [ 
    apply valseq_is_result; constructor; auto
    | cbv; auto_proove_subst_semantics_in_k_steps
    ].

 (* ---------- 1. Identity Function ---------- *)
Definition id_fun (e : Exp) : Exp :=
    °ELet
        1
        (°EFun 1 (˝VVar 0))     (* fun(X) -> X *)
        (°EApp (˝VVar 0) [e]).  (* apply id(E) *)

Goal ⟨[], id_fun (˝VLit 42%Z)⟩ -->* RValSeq [VLit 42%Z].
Proof.
    auto_proove_subst_semantics.
Qed.


(* ---------- 2. Constant Function ---------- *)
Definition const_fun (e : Exp) : Exp :=
  °ELet
    1
    (°EFun 1 (˝VLit (Atom "ok"%string)))   (* fun(_) -> ok *)
    (°EApp (˝VVar 0) [e]).

Goal ⟨[], const_fun (˝VLit 42%Z)⟩ -->* RValSeq [VLit (Atom "ok")].
Proof.
    auto_proove_subst_semantics.
Qed.

Theorem const_equiv :
CIU (const_fun (˝VLit 42%Z)) (const_fun (˝VLit 62%Z)).
Proof.
    pose proof (CIU_eval (const_fun (˝VLit 42%Z)) (RValSeq [VLit (Atom "ok")])).
    pose proof (CIU_eval (const_fun (˝VLit 62%Z)) (RValSeq [VLit (Atom "ok")])).
    destruct H.
    scope_solver.
    auto_proove_subst_semantics.
    destruct H0.
    scope_solver.
    auto_proove_subst_semantics.
    apply (CIU_transitive_closed (const_fun (˝VLit 42%Z)) (RValSeq [VLit (Atom "ok")]) (const_fun (˝VLit 62%Z)));assumption.
Qed. 
    

(* ---------- 3. Primitive Addition ---------- *)
Definition add_primitive (x y : Exp) : Exp :=
  °ECall (˝VLit (Atom "erlang"%string))
         (˝VLit (Atom "+"%string))
         [x; y].

Goal ⟨[], add_primitive (˝VLit 1%Z) (˝VLit 2%Z)⟩ -->* RValSeq [VLit 3%Z].
Proof.
    auto_proove_subst_semantics.
Qed.

(* ---------- 4. Tuple Construction ---------- *)
Definition make_tuple (xs : list Exp) : Exp :=
  °ETuple xs.

Goal ⟨[], make_tuple [˝VLit 1%Z; ˝VLit (Atom "x"%string)]⟩ -->* RValSeq [VTuple [VLit 1%Z; VLit (Atom "x")]].
Proof.
    (* eexists.
    split.
    (* is_result [VLit "ok"]  This works*)
    (* is_result [VTuple [VLit 1%Z; VLit "x"]] This does not? *)
        + apply valseq_is_result.
          constructor.
          - scope_solver.
          - auto.
        + cbv. 
        eapply step_trans.
        apply eval_heat_tuple.
        eapply step_trans.
        apply eval_step_params_0.
        discriminate.
        eapply step_trans.
        apply SubstSemantics.cool_value.
        scope_solver.
        eapply step_trans.
        apply eval_step_params.
        eapply step_trans.
        apply SubstSemantics.cool_value.
        scope_solver.
        eapply step_trans.
        eapply eval_cool_params.
        auto.
        simpl.
        apply step_refl.        *)
    auto_proove_subst_semantics.
Qed.


(* ---------- 5. List Construction ---------- *)
Definition make_list (xs : list Exp) : Exp :=
  fold_right (fun x acc => °ECons x acc) (˝VLit (Atom "nil"%string)) xs.

Goal ⟨[], make_list [˝VLit 1%Z; ˝VLit 2%Z]⟩ -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VLit (Atom "nil")))].
Proof.
    auto_proove_subst_semantics.
Qed.

(* ---------- 6. Map Construction ---------- *)
Definition make_map (pairs : list (Exp * Exp)) : Exp :=
  °EMap pairs.
Goal ⟨[], make_map [(˝VLit (Atom "a"%string), ˝VLit 1%Z)]⟩ -->* RValSeq [VMap [(VLit (Atom "a"), VLit 1%Z)]].
Proof.
    (* eexists.
    split.
    apply valseq_is_result.
    constructor.
    scope_solver.
    auto.
        + *)
auto_proove_subst_semantics.
Qed.

(* ---------- 7. Let Binding ---------- *)
Definition let_binding (rhs body : Exp) : Exp :=
  °ELet 1 rhs body.
Goal ⟨[], let_binding (add_primitive (˝VLit 5%Z) (˝VLit 7%Z)) (˝VVar 0)⟩ -->* RValSeq [VLit 12%Z].
Proof.
auto_proove_subst_semantics.
Qed.

(* ---------- 8. Case Expression ---------- *)
Definition case_expr (scrut : Exp) (branches : list (list Pat * Exp * Exp)) : Exp :=
  °ECase scrut branches.

Goal ⟨[], case_expr (˝VLit 1%Z)
       [([PLit (Integer 0)], ˝ttrue, ˝VLit (Atom "zero"%string));
        ([PLit (Integer 1)], ˝ttrue, ˝VLit (Atom "one"%string))]⟩
-->* RValSeq [VLit (Atom "one")].
Proof.
    auto_proove_subst_semantics.
Qed.


(* ---------- 10. Try / Catch ---------- *)
Definition try_example (expr handler : Exp) : Exp :=
  °ETry expr 0 (˝VLit (Atom "ok"%string)) 3 handler.

Goal ⟨[], try_example
(°ECall (˝VLit (Atom "erlang"%string))
        (˝VLit (Atom "error"%string))
        [˝VLit (Atom "oops"%string)])
(°ETuple [˝VLit (Atom "caught"%string); ˝VVar 1])⟩
-->* RValSeq [VTuple [VLit (Atom "caught"%string); VLit (Atom "oops"%string)]].
Proof.
    auto_proove_subst_semantics.
Qed.

(** Test: try/catch with successful evaluation (no exception) *)
Goal ⟨[], °ETry 
  (°ECall (˝VLit (Atom "erlang"%string))
          (˝VLit (Atom "+"%string))
          [˝VLit 5%Z; ˝VLit 3%Z])
  1       (* bind 1 value on success *)
  (˝VVar 0) (* return that value *)
  3        (* bind 3 values on exception (class, reason, details) *)
  (°ETuple [˝VLit (Atom "error"%string); ˝VVar 1])⟩
-->* RValSeq [VLit 8%Z].
Proof.
    auto_proove_subst_semantics.
Qed.

(** Test: try/catch with simple value (no exception) *)
Goal ⟨[], °ETry
  (˝VLit (Atom "success"%string))
  1
  (˝VVar 0)
  3
  (°ETuple [˝VLit (Atom "caught"%string); ˝VVar 1])⟩
-->* RValSeq [VLit (Atom "success"%string)].
Proof.
    auto_proove_subst_semantics.
Qed.


(* ========================================== *)
(* Manual Implementations of List Functions *)
(* ========================================== *)


(* ========================================== *)
(* List Functions - Complete with ELetRec *)
(* ========================================== *)

Section list_functions.

    (** lists:member/2 - Check if element is in list 
        member(Elem, List) -> 
          case List of
            [H|T] when H =:= Elem -> true;
            [_|T] -> member(Elem, T);
            []    -> false
          end.
    *)
    Definition member (elem lst : Exp) : Exp :=
      ELetRec [(2, 
        °ECase (˝VVar 2)  (* match on List parameter *)
          [([PCons PVar PVar],  (* [H|T] H = 0, T= 1,fun = 2, elem =3,List =4 *)  
            °ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0; ˝VVar 3],  (* H =:= Elem *)
            ˝VLit "true");
           ([PCons PVar PVar],  (* [_|T] _ = 0, T= 1,fun = 2, elem =3,List =4 *)  
            ˝ttrue,
            °EApp (˝VFunId (2, 2)) [˝VVar 3; ˝VVar 1]);  (* member(Elem, T) *)
           ([PNil],  (* [] *)
            ˝ttrue,
            ˝VLit "false")])]
      (EApp (˝VFunId (0, 2)) [elem; lst]).
  
    (** lists:reverse/2 - Reverse with accumulator 
        reverse(List, Acc) ->
          case List of
            [H|T] -> reverse(T, [H|Acc]);
            []    -> Acc
          end.
    *)
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
  
    (** lists:reverse/1 - Reverse a list *)
    Definition reverse1 (lst : Exp) : Exp :=
      reverse lst (˝VNil).
  
    (** lists:sum/2 - Sum with accumulator
        sum(List, Acc) ->
          case List of
            [H|T] -> sum(T, H + Acc);
            []    -> Acc
          end.
    *)
    Definition sum (lst acc : Exp) : Exp :=
      ELetRec [(2,
        °ECase (˝VVar 1)  (* match on List parameter *)
          [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
            ˝ttrue,
            °ELet 1 (ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0; ˝VVar 4])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *)
              (EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 0]));  (* sum(T, NewAcc) *)
           ([PNil],  (* [] *)
            ˝ttrue,
            ˝VVar 2)])]  (* return Acc *)
      (EApp (˝VFunId (0, 2)) [lst; acc]).
  
    (** lists:sum/1 - Sum a list *)
    Definition sum1 (lst : Exp) : Exp :=
      sum lst (˝VLit 0%Z).
  
    (** lists:append/2 - Concatenate two lists *)
    Definition append (lst1 lst2 : Exp) : Exp :=
      °ECall (˝VLit "erlang") (˝VLit "++") [lst1; lst2].
  
    (** lists:nth/2 - Get nth element (1-indexed)
        nth(1, [H|_]) -> H;
        nth(N, [_|T]) when N > 1 -> nth(N-1, T).
    *)
    Definition nth (n lst : Exp) : Exp :=
      ELetRec [(2,  (* fun = 0 , n = 1, lst = 2 **)
        °ECase (˝VVar 1)  (* match on N parameter *)
          [([PLit (Integer 1)],  (* N = 1 *)
            ˝ttrue,
            °ECase (˝VVar 2) [ (* fun = 0 , n = 1, lst = 2 **)
              ([PCons PVar PVar], ˝ttrue, ˝VVar 0)]);  (* return H,  H=0, T=1 fun = 2 , n = 3, lst = 4 *)
           ([PVar],  (* Var = 0 fun = 1 , n = 2, lst = 3 **)
            °ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit 1%Z],  (* N > 1 *)
            °ECase (˝VVar 3) [  (* match on List *)
              ([PCons PVar PVar],  (* [H|T] H = 0, T=1  Var = 2 fun = 3 , n = 4, lst = 5*)
               ˝ttrue,
               °ELet 1 (ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 4; ˝VLit 1%Z])  (* NewN = N - 1 *)
                 (EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2]))])])]  (* nth(NewN, T) *)
      (EApp (˝VFunId (0, 2)) [n; lst]).
  
  End list_functions.
(* ========================================== *)
(* Evaluation Tests *)
(* ========================================== *)

Section simple_tests.

    (** Test member - element found *)
    Goal ⟨[], member (˝VLit 2%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
      -->* RValSeq [VLit "true"].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test member - element not found *)
    Goal ⟨[], member (˝VLit 5%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))⟩
      -->* RValSeq [VLit "false"].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test reverse/1 wrapper *)
    Goal ⟨[], reverse1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
      -->* RValSeq [VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) VNil))].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test sum/1 wrapper *)
    Goal ⟨[], sum1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
      -->* RValSeq [VLit 6%Z].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test reverse empty list *)
    Goal ⟨[], reverse1 (˝VNil)⟩ -->* RValSeq [VNil].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test sum empty list *)
    Goal ⟨[], sum1 (˝VNil)⟩ -->* RValSeq [VLit 0%Z].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test append *)
    Goal ⟨[], append (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))
                      (˝VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil))⟩
      -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil)))].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test nth - get first element *)
    Goal ⟨[], nth (˝VLit 1%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") VNil)))⟩
      -->* RValSeq [VLit "a"].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
    (** Test nth - get second element *)
    Goal ⟨[], nth (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") VNil)))⟩
      -->* RValSeq [VLit "b"].
    Proof.
      auto_proove_subst_semantics.
    Qed.
  
  End simple_tests.
  