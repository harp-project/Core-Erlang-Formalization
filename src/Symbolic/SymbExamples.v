From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions Equivalences.
From CoreErlang.Symbolic Require Import SymbTheorems SymbTactics.

Import ListNotations.

Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 1%Z));
      ([PVar], ˝ttrue,
        °ELet 1 (EApp (˝VFunId (1, 1))
          [°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z]])
          (°ECall (˝VLit "erlang"%string) (˝VLit "*"%string) [˝VVar 1; ˝VVar 0])
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e])
   (* Write the definition here *)
.

Theorem fact_eval_ex:
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (fact_frameStack (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z))%Z).
Proof.
  solve_symbolically z.

  admit.
Admitted.

Definition tailrec_fact (e d : Exp) : Exp :=
  ELetRec [
    (2, °ECase (˝VVar 1) [
        ([PLit (Integer 0%Z)], ˝ttrue, ˝VVar 2);
        ([PVar], ˝ttrue,
          (°EApp (˝VFunId (1, 2)) 
            [°ECall (˝erlang) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z];
             °ECall (˝erlang) (˝VLit "*"%string) [˝VVar 0; ˝VVar 3]
            ]))
      ]
    )
  ] (EApp (˝VFunId (0, 2)) [e; d]) 
.

Theorem fact_tailrec_eval_ex:
  forall (z : Z) (z' : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (tailrec_fact (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = Z.of_nat (Factorial.fact (Z.to_nat z)) * z')%Z.
Proof.
  solve_symbolically z z'.
  
  destruct PreCond0. subst.
  rewrite Z.mul_assoc. f_equal.
  rewrite <- positive_nat_Z.
  rewrite <- Nat2Z.inj_mul. f_equal.
  assert (1%Z = Z.of_nat (Z.to_nat 1%Z))%Z by lia. rewrite H0. clear H0.
  rewrite <- Nat2Z.inj_sub;[|lia].
  do 2 rewrite Nat2Z.id.
  remember (Pos.to_nat p) as k.
  pose proof Pos2Nat.is_pos p.
  destruct k; try lia.
  simpl.
  rewrite Nat.sub_0_r. lia. 
Qed.

Definition timestwo (e : Exp) : Exp :=
  ELetRec [
      (1, °ECall (˝erlang) (˝VLit "*"%string) [˝VVar 1; ˝VLit 2%Z]
      
      )
    ] (EApp (˝VFunId (0, 1)) [e]).

Definition timestwo' (e : Exp) : Exp :=
  °ECall (˝erlang) (˝VLit "*"%string) [e; ˝VLit 2%Z].

Theorem timestwo_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (timestwo (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Theorem timestwo'_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (timestwo' (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_simple (e : Exp) : Exp :=
  (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "*"%string))) [e;(VVal (VLit (Integer (2))))])).

Theorem times_two_simple_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (times_two_simple (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_rec (e : Exp) : Exp := ELetRec [
(1, (EExp (ECase (VVal (VVar 1)) 
[
  ([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))));
  ([PVar], (VVal (VLit (Atom "true"%string))), 
    (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) 
    (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(EExp (EApp (VVal (VFunId (2, 1))) [(VVal (VVar 0))]));(VVal (VLit (Integer (2))))])))))])))] 

(EApp (VVal (VFunId (0, 1))) [e]).

Theorem times_two_rec_ex:
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (times_two_rec (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition plus_nums_simple (e f : Exp) : Exp :=
(EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [e;f])).

Theorem plus_nums_simple_ex:
  forall (z : Z) (z' : Z), True ->
  exists (y : Z),
  ⟨ [], (plus_nums_simple (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = z + z')%Z.
Proof.
  solve_symbolically z.
Qed.

Definition plus_nums_rec (e f : Exp) := ELetRec [(2, (EExp (ECase (VVal (VVar 1)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VVar 2)));([PVar], (VVal (VLit (Atom "true"%string))), (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "-"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (1))))])) (EExp (ELet 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "+"%string))) [(VVal (VVar 4));(VVal (VLit (Integer (1))))])) (EExp (EApp (VVal (VFunId (3, 2))) [(VVal (VVar 1));(VVal (VVar 0))])))))))])))] (EApp (VVal (VFunId (0, 2))) [e;f]).

Theorem plus_nums_rec_ex:
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (plus_nums_rec (˝VLit z) (˝VLit 0%Z)) ⟩ -->* RValSeq [VLit y] /\ (y = z)%Z.
Proof.
  (* This cannot be proven by induction, since the goal is too specific. *)
Abort.

Theorem plus_nums_rec_ex':
  forall (z : Z) (z' : Z), (z >= 0)%Z ->
  exists (y : Z),
  ⟨ [], (plus_nums_rec (˝VLit z) (˝VLit z')) ⟩ -->* RValSeq [VLit y] /\ (y = z + z')%Z.
Proof.
  solve_symbolically z z'.
Qed.


Definition isitzero_atom (e : Exp) : Exp :=
(EExp (ECase (e) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "true"%string))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "false"%string))))])).

Theorem isitzero_atom_ex:
  forall (z : Z), (z >= 0)%Z ->
  exists (y : string),
  ⟨ [], (isitzero_atom (˝VLit (Z.succ z))) ⟩ -->* RValSeq [VLit y] /\ (y = "false"%string)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition isitzero_num (e : Exp) : Exp :=
(EExp (ECase (e) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (1)))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))))])).

Theorem isitzero_num_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (isitzero_num (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ ((y = 0)%Z \/ (y = 1)%Z).
Proof.
  solve_symbolically z.
Qed.

Definition isitzero_num_app (e : Exp) : Exp :=
EExp ( EApp ( EFun 1 (EExp (ECase (VVal (VVar 0)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (1)))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Integer (0)))))]))) [e]).

Theorem isitzero_num_app_ex:
  forall (z : Z), True ->
  exists (y : Z),
  ⟨ [], (isitzero_num_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ ((y = 0)%Z \/ (y = 1)%Z).
Proof.
  solve_symbolically z.
Qed.

Definition isitzero_atom_app (e : Exp) : Exp :=
EExp ( EApp ( EFun 1(EExp (ECase (VVal (VVar 0)) [([(PLit (Integer (0)))], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "true"%string))));([PVar], (VVal (VLit (Atom "true"%string))), (VVal (VLit (Atom "false"%string))))]))) [e]).

Theorem isitzero_atom_app_ex:
  forall (z : Z), (z > 0)%Z ->
  exists (y : string),
  ⟨ [], (isitzero_atom_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = "false"%string).
Proof.
  solve_symbolically z.
Qed.

Theorem timestwo_ex':
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (times_two_simple (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Definition times_two_simple_app (e : Exp) : Exp :=
  EExp (EApp (EExp (EFun 1 (EExp (ECall (VVal (VLit (Atom "erlang"%string))) (VVal (VLit (Atom "*"%string))) [(VVal (VVar 0));(VVal (VLit (Integer (2))))])))) [e]).

Theorem timestwo_ex'':
  forall (z : Z),
  exists (y : Z),
  ⟨ [], (times_two_simple_app (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.

Theorem timestwo_ex''':
  forall (z : Z), (0 <= z)%Z ->
  exists (y : Z),
  ⟨ [], (times_two_rec (˝VLit z)) ⟩ -->* RValSeq [VLit y] /\ (y = z * 2)%Z.
Proof.
  solve_symbolically z.
Qed.


Definition fib_frameStack (e : list Exp) : Exp :=
  ELetRec
    [(3, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VVar 2));
      ([PVar], ˝ttrue,
        °ELet 1 (°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z]) 
          (°ELet 1 (°ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 4; ˝VVar 5]) 
            (EApp (˝VFunId (3, 3)) [˝VVar 1; ˝VVar 6;˝VVar 0]))
      )
    ])]
    (EApp (˝VFunId (0, 3)) e)
   (* Write the definition here *)
.

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

Ltac make_first_step :=
  match goal with
  | [ |- ⟨ _ , _ ⟩ -[ ?k ]-> ⟨ _ , _ ⟩] =>
       apply step_refl +
       (eapply step_trans; [one_step_full_solver | idtac]; cbv)
  end.

Ltac many_step_solver := repeat make_first_step.

Ltac star_step_solver := 
    eexists;
    split; [ 
      constructor
    | cbv; many_step_solver
    ].

Theorem fib_framestack_10th:
  ⟨ [], (fib_frameStack [˝VLit 10%Z; ˝VLit 0%Z; ˝VLit 1%Z]) ⟩ -->* RValSeq [VLit 55%Z].
Proof.
  star_step_solver.
Qed.

Fixpoint fib_helper (n: nat) (a b: Z) : Z :=
  match n with
  | 0 => a
  | S n' => fib_helper n' b (a + b)
  end.

Definition fib_fast (n: nat) := fib_helper n 0 1.

Theorem fib_framestack_general:
  forall (n : Z) (a : Z) (b : Z), (0 <= n)%Z ->
  exists (y : Z),
  ⟨ [], (fib_frameStack [˝VLit n; ˝VLit a; ˝VLit b]) ⟩ -->* RValSeq [VLit y] /\ y = fib_helper (Z.to_nat n) a b.
Proof.
  solve_symbolically n a b.
  destruct PreCond0.
  rewrite H0.
  (* unfold fib_helper at 2. *)
  destruct (Z.to_nat (Z.pos p)) eqn:Heq.
  + Search (Z.to_nat (Z.pos _)). 
    rewrite Z2Nat.inj_pos in Heq.
    Search (Pos.to_nat _).
    pose proof (Pos2Nat.is_pos p).
    destruct H1.
    discriminate.
    discriminate.
  + simpl.
    assert (n0 = Z.to_nat (Z.pos p - 1)) by lia.
    rewrite H1.
    reflexivity.
Qed.

(*
  Interesting problems regarding the automation of symbolic executions on Val types (firstly lists, but maps, tuples etc. ?):
  - meta level predicates? wellFormedList_n etc.
  - can be everything simplified back to induction on one Z typed variable? (worked on list so far, since its lenght can be bound...what about maps?)
  - statements regarding expressions? Exp variables?
*)

(*Should use Z?*)
Fixpoint isWellFormedNumberList_n (n : nat) (v : Val): Prop :=
  match n, v with
    | 0, VNil => True
    | S n0, VCons (VLit (Integer _)) tl => isWellFormedNumberList_n n0 tl
    | _, _ => False
  end.

Lemma Z_is_S_n:
  forall (p: positive), exists (n: nat), (Z.to_nat (Z.pos p)) = S n.
Proof.
  intros.
  rewrite (Z2Nat.inj_pos p).
  pose proof (Pos2Nat.is_pos p).

  destruct (Pos.to_nat p).
  + inversion H.
  + exists n. reflexivity.

Qed.


Compute match_pattern (PMap [(PLit (Atom "B"%string), PVar)]) (VMap [(VLit (Atom "B"%string), VLit (Integer 3%Z))]).

Definition build_random_map (n m : Exp) : Exp :=
  ELetRec
    [(2, °ECase (EValues [˝VVar 1; ˝VVar 2]) [
      ([PLit 0%Z; PVar], ˝ttrue, (˝VVar 0));
      ([PVar], ˝ttrue,
        °ELet 1 (°ECall (˝VLit "erlang"%string) (˝VLit "-"%string) [˝VVar 0; ˝VLit 1%Z]) 
          (°ELet 1 (°ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 4; ˝VVar 5]) 
            (EApp (˝VFunId (3, 3)) [˝VVar 1; ˝VVar 6;˝VVar 0]))
      )
    ])]
    (EApp (˝VFunId (0, 3)) [n; m])
   (* Write the definition here *)
.


Fixpoint sumMeta (v : Val) : Z :=
  match v with
    | VNil => 0%Z
    | VCons (VLit (Integer i)) tl => i + sumMeta tl
    | _ => 0
  end.

Definition sum (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °ELet 1 (ECall (˝VLit "erlang"%string) (˝VLit "+"%string) [˝VVar 0; ˝VVar 4])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *)
           (EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 0]));  (* sum(T, NewAcc) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).

 (** lists:sum/1 - Sum a list *)
Definition sum1 (lst : Exp) : Exp :=
   sum lst (˝VLit 0%Z).


(*note: the variable which is the induction can come from a proof hint provided by the programmer...
it is highly possible that, in cases like this where it is a pseudo variable, not present in the program but representing the lenght of a list
the variable should be created with help*)
Theorem sum_is_correct:
  forall (n : Z) (m : Z) (l : Val),
    (0 <= n)%Z /\
    isWellFormedNumberList_n (Z.to_nat n) l /\
    VALCLOSED l ->
    exists (y : Z),
    ⟨ [], (sum (˝l) (˝VLit m)) ⟩ -->* RValSeq [VLit y] /\ (y = sumMeta l + m)%Z.
Proof.
  setoid_rewrite RTCEquiv.
  2: auto.

  toRec.

  possibly_recursive.
  intro h. intros t l.
  intros precond.
  assert (0 <= h)%Z as heq by lia.
  revert precond. revert t l.

  apply Zlt_0_ind with (x := h).
  2: exact heq.
  clear heq. clear h.

  intro h.
  intros IH. intros heq. intros t l. clear heq. intros precond.

  destruct h eqn:heq'.
  + (*When induction is on the lenght of a list then the base case starts with destructing the list*)
    destruct precond as [precond1 precond2].
    destruct precond2 as [precond2 precond3].

    simpl in precond2.

    destruct l; try lia.

    stepThousand.
    eexists.
    split.
    {
      exists 0.
      reflexivity.
    }
    {
      lia.
    }
  + stepOne.
    toRec.

    (*Get the part of the percond that gives information about the Val type variable*)
    destruct precond as [precond1 precond2].
    destruct precond2 as [precond2 precond3].

    (*meta language precondition needs to be expanded to be simplifed to False in the invalid cases*)
    
    
    pose proof (Z_is_S_n p).
    destruct H.
    rewrite H in precond2.
    simpl in precond2.

    (*kind of case_innermost?*)
    destruct l; try lia.
    destruct l1; try lia.
    destruct l; try lia.
    simpl.

    specialize (IH (Z.pos p - 1)%Z).
    strip_IH_precond IH.
    destruct_until_conj IH.

    specialize (IH (x0 + t)%Z).
    specialize (IH l2).
    
    destruct IH as [IHPrecond IHStripped].
    - split.
      {
        lia.
      }
      {
        split.
        {
          assert ((Z.to_nat (Z.pos p - 1)) = x) by lia.
          rewrite H0.
          assumption.
        }
        {
          inversion precond3.
          assumption.
        }
      }
    - destruct IHStripped as [IHExp IHPostcond].
      pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
      simpl in IHExp_fic.

      eexists_until_conj.

      eapply maxKTransitive'.

      (*subtitutions needs to be extracted*)
      remember (VClos
        [(0, 2,
        ° ECase (˝ VVar 1)
        [([PCons PVar PVar], ˝ VLit "true"%string,
        ° ELet 1 (° ECall (˝ VLit "erlang"%string) (˝ VLit "+"%string) [˝ VVar 0; ˝ VVar 4])
        (° EApp (˝ VFunId (3, 2)) [˝ VVar 2; ˝ VVar 0])); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
        (° ECase (˝ VVar 1)
        [([PCons PVar PVar], ˝ VLit "true"%string,
        ° ELet 1 (° ECall (˝ VLit "erlang"%string) (˝ VLit "+"%string) [˝ VVar 0; ˝ VVar 4])
        (° EApp (˝ VFunId (3, 2)) [˝ VVar 2; ˝ VVar 0])); ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])) as close.
      

      assert (l2.[close/]ᵥ = (renameVal S l2.[close/]ᵥ).[VLit (x0 + t)%Z/]ᵥ) as Subst1.
      {

        inversion precond3.

        pose proof (vclosed_ignores_sub l2) as Ignores1.
        rewrite Ignores1.
        pose proof (vclosed_ignores_ren l2) as Ignores2.
        rewrite Ignores2.
        rewrite Ignores1.
        reflexivity.
        
        assumption.
        assumption.
        assumption.
      }

      rewrite Subst1 in IHExp_fic.
      apply IHExp_fic.

      split.
      {
        (* Not terminated case?*)
        stepOne.
        exists 0.
        reflexivity.
      }
      {
        rewrite IHPostcond.
        lia.
      }
  + nia.
Qed.
    
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

Definition isList (lst : Val) : Prop :=
  match lst with
    | VNil => True
    | (VCons _ _) => True
    | _ => False
  end.

Goal ⟨ [], (reverse1 (reverse1 (˝VCons (VLit 2%Z) VNil))) ⟩ -->* RValSeq [VCons (VLit 2%Z) VNil].
Proof.
  star_step_solver.
Qed.


Fixpoint reverseMetaHelp (y : Val) (acc : Val) :=
  match y with
    | VCons hd tl => reverseMetaHelp tl (VCons hd acc)
    | VNil => acc
    | _ => VNil
  end.

Definition reverseMeta (y : Val) :=
  reverseMetaHelp y VNil.

Fixpoint appendMeta (x : Val) (y : Val) : Val :=
  match x with
  | VNil => y
  | VCons h t => VCons h (appendMeta t y)
  | _ => VNil
  end.

Fixpoint isWellFormedList_n (n : nat) (v : Val): Prop :=
  match n, v with
    | 0, VNil => True
    | S n0, VCons hd tl => isWellFormedList_n n0 tl
    | _, _ => False
  end.

Compute (isWellFormedList_n 4 (VCons (VLit 12%Z) (VCons (VCons (VLit 11%Z) VNil) (VCons (VLit 11%Z) (VCons (VLit 12%Z) VNil))))).


(*!!!!!!!!!!! idea: programmer provides variable function that terminates
                    - this eliminates the need to use heuristics in
                    complex scenarios where the specialization of the 
                    inductive hypothesis is non trivial. !!!!!!!!!!!*)

(*idea: Z variables, Val (Exp?) variables, z conditions, Val conditions (meta theory predicates?), Scope conditions?*)
Theorem reverse_is_correct: 
  forall (n : Z) (m : Z) (l : Val) (lh : Val), (0 <= n)%Z /\ (0 <= m)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\  isWellFormedList_n (Z.to_nat m) lh /\
    VALCLOSED l /\ VALCLOSED lh ->
   exists (y : Val),
   ⟨ [], (reverse (˝l) (˝lh)) ⟩ -->* RValSeq [y] /\ y = reverseMetaHelp l lh.
Proof.

  

  setoid_rewrite RTCEquiv.
  2: auto.

  is_not_terminated. (*OK*)
  toRec.

  possibly_recursive. (*OK*)
  intro h. intros t l1 l2.

  intro precond.
  assert (0 <= h)%Z as heq by lia.
  revert precond. revert t l1 l2.



  apply Zlt_0_ind with (x := h).
  2: exact heq.


  clear heq. clear h.

  intro h.
  intro IH. intro heq. intros t l1 l2. clear heq. intro precond.

  (*Separation of Z and Val variables?*)

  destruct h eqn:heq'.
  + clear IH.
    let Tp := type of precond in
    let Th := type of heq' in
    assert (Tp /\ Th) as precond' by auto. (*auto can but lia can't solve????!!!!*)

    (*--- Try to get some information out of the precond ---*)
    destruct precond.
    destruct H0.
    destruct H1.
    simpl in H1.
    destruct l1; try lia. (*lia can solve False assumption*)

    
    destruct (Z.to_nat t) eqn:tHeq;
    simpl in H2;
    destruct l2; try lia.
    - (*clear precond.*) clear heq'.
      revert precond'.
      (*revert t.*) revert h.
       stepThousand.
       intros. solve_terminated.
    - (*clear precond.*) clear heq'.
      revert precond'.
      (*revert t.*) revert h. 



      stepThousand.
      intros.   solve_terminated.

      destruct H2.
      destruct H3.
      inversion H4.

      pose proof (vclosed_ignores_sub l2_1).
      pose proof (vclosed_ignores_sub l2_2).
      rewrite H10.
      rewrite H11.
      pose proof (idsubst_is_id).
      destruct H12.
      destruct H13.
      rewrite (H14 l2_1).
      rewrite (H14 l2_2).
      reflexivity.
      assumption.
      assumption.
  + 
    let Tp := type of precond in
    let Th := type of heq' in
    assert (Tp /\ Th) as precond' by auto.
    clear precond. clear heq'.



    revert precond'.
    revert t l1 l2.
    revert h.

    stepOne.
    toRec.

    contains_match. (*OK*)



    intros h. intros t l1 l2. intros precond.


    (* destruct t; try discriminate; destruct precond; destruct H; simpl in H1.

    Search (( Z.pos _)).

    pose proof (Zgt_pos_0 p).
    assert (exists n0, (Z.to_nat (Z.pos p)) = S n0). *)

    (*disgusting, but automating infromation collection regarding t is noice*)
    case_innermost heq; simpl; destruct l1;
    try discriminate; destruct precond; destruct H; (*remember (Z.to_nat (Z.pos p)) eqn:HeqpToN;*)
    destruct (Z.to_nat (Z.pos p)) eqn:nHeq; (*rewrite HeqpToN in H1;*) simpl in H1; try lia.

(* 
    (*Base case of destructing t*)
    - 
      subst.
      stepThousand.
      eexists.
      split.
      {
        simpl.
        exists 0.
        reflexivity.
      }
      {
        reflexivity.
      } *)
    specialize (IH (Z.pos p - 1)%Z). (*how to find out automaically?*)
    
    strip_IH_precond IH.
    (*spec_rest_of_terms IH vl*) (*solve the not supported part*)
    specialize (IH (t + 1)%Z l1_2 (VCons v1 l2)).

    (* strip_IH_precond IH.
    destruct_until_conj IH. *) (*adjustments needed*)

    destruct IH as [IHRes IHStripped]. (*Precond stripping needs upgrade for basic splitting*)
    {
      split.
      {
        lia.
      }
      {
        split.
        {
          lia.
        }
        {
        split.
          {
            assert (n = (Z.to_nat (Z.pos p - 1))) by lia.
     
            rewrite <- H2.
            destruct H1.
            destruct H3.
            assumption.
          }
          {
            simpl.
            destruct H1.
            destruct H2.
            destruct H3.
            destruct t; simpl in H3; simpl.
            - split.
              {
                assumption.
              }
              {
                split;destruct H4.
                {
                  inversion H4.
                  assumption.
                }
                {
                  inversion H4.
                  econstructor.
                  2: assumption.
                  inversion heq.
                  clear heq.
                  pose proof (vclosed_ignores_sub l1_1).
                  rewrite H11; assumption.
                }
              }
              
              

            - assert (exists n0 : nat, (Z.to_nat (Z.pos p0  + 1)) = S n0).
              {
                Search (Z.pos _).

                destruct (Z.to_nat (Z.pos p0 + 1)) eqn:p0Heq.
                + nia.
                + eexists. reflexivity.
              }

              destruct H5.
              rewrite H5.
              simpl.
              simpl in H4.
              split.
              {
                assert ((Z.to_nat (Z.pos p0)) = x) by lia.
                rewrite H6 in H3.
                assumption.
              }
              (*SCOPING*)
              {
                destruct H4.
                split; inversion H4.
                {
                  assumption.
                }
                {
                  inversion heq.
                  clear heq.
                  pose proof (vclosed_ignores_sub l1_1).
                  rewrite H12.
                  2: assumption.
                  scope_solver_v1.
                }
              }
              
            - nia.
          }
        }
      }
    }
    {
      destruct IHStripped as [IHExp IHPostcond].
      pose proof (frame_indep_core_func _ _ _ _ IHExp ) as IHExp_fic.
      simpl in IHExp_fic.

      eexists_until_conj.

      remember ((VClos
            [(0, 2,
            ° ECase (˝ VVar 1)
            [([PCons PVar PVar], ˝ VLit "true"%string,
            ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]);
            ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])] 0 2
            (° ECase (˝ VVar 1)
            [([PCons PVar PVar], ˝ VLit "true"%string,
            ° EApp (˝ VFunId (2, 2)) [˝ VVar 1; ° ECons (˝ VVar 0) (˝ VVar 4)]);
            ([PNil], ˝ VLit "true"%string, ˝ VVar 2)])))
      as close.

 
      simpl in heq.

      inversion heq.

      rewrite H3.
      rewrite H4.

      rewrite H4 in IHExp_fic.

      eapply maxKTransitive'.

      assert (v1.[close/]ᵥ = v1) as HECK1.
      {
        clear IHExp_fic IHExp IHPostcond heq.
        destruct H1.
        destruct H2.
        destruct H5.
        destruct H6.
        inversion H6.
        pose proof (vclosed_ignores_sub l1_1).
        rewrite H13 in H3.
        2: assumption.
        rewrite <- H3.
        rewrite H13.
        reflexivity.
        assumption.
      }

      rewrite HECK1 in IHExp_fic.

      assert ((renameVal S (renameVal S l2.[close/]ᵥ)) .[ v1,
        v2 /]ᵥ = l2.[close/]ᵥ) as HECK2.
      {
        destruct H1.
        destruct H2.
        destruct H5.
        destruct H6.
        pose proof (vclosed_ignores_sub l2).
        rewrite H8.
        2: assumption.
        pose proof (vclosed_ignores_ren l2).
        rewrite H9.
        rewrite H9.
        rewrite H8.
        reflexivity.
        assumption.
        assumption.
        assumption.
      }

      rewrite HECK2.
    
      
      apply IHExp_fic.
      stepThousand.
      split.
      {
        exists 0.
        reflexivity.
      }
      {
        rewrite IHPostcond.
        f_equal.
        f_equal.
        rewrite <- H3.

        destruct H1.
        destruct H2.
        destruct H5.
        destruct H6.
        inversion H6.
        
        pose proof (vclosed_ignores_sub l1_1).
        rewrite H13.
        reflexivity.
        assumption.
      }
    }
  + nia.
Qed.

Theorem reverse1_is_correct : 
  forall (n : Z) (l : Val), (0 <= n)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\
    VALCLOSED l ->
   exists (y : Val),
   ⟨ [], (reverse1 (˝l)) ⟩ -->* RValSeq [y] /\ y = reverseMeta l.
Proof.
    unfold reverse1.
    pose proof reverse_is_correct.

    intros.
    specialize (H n 0%Z l VNil).
    apply H.

    destruct H0.
    destruct H1.

    split.
    lia.
    split.
    lia.
    split.
    
    assumption.
    split.
    simpl.
    exact I.
    split.
    assumption.
    apply scoped_nil.
Qed.


(* Transitivity of pure functions as results? How to handle multiple function calls?*)
Theorem reverse_duplicate_is_same:
  forall (n : Z) (l : Val), (0 <= n)%Z /\
    isWellFormedList_n (Z.to_nat n) l /\
    VALCLOSED l ->
   ⟨ [], (reverse1 (reverse1 (˝l))) ⟩ -->* RValSeq [l].
Proof.
 pose proof reverse1_is_correct.
 intros.

 specialize (H n l H0).




Admitted.

Fixpoint isWellFormedList (v : Val): Prop :=
  match v with
    | VNil => True
    | VCons hd tl => isWellFormedList tl
    | _ => False
  end.

(* Theorem reverse_duplicate_is_same_simplify_statement_further:
  forall (l : Val),
    isWellFormedList l ->
   exists (y : Val),
   ⟨ [], (reverse1 (˝l)) ⟩ -->* RValSeq [y] /\ y = reverseMeta y.
Proof.
  setoid_rewrite RTCEquiv.
  2: auto.

  is_not_terminated. (*OK*)
  toRec.

  possibly_recursive. (*OK*)
  intro h.
  intro precond.
  




  (* intros precond.

  revert precond. *)
  
  (* apply Zlt_0_ind with (x := h). *)

  (*Get ready to inversion precond with various conditions: /\, \/, etc.*)
  induction h; intro precond; simpl in precond; try lia.
  (*----- base case -----*)
  stepThousand.
  eexists.
  split.
  {
    exists 0.
    reflexivity.
  }
  {
    reflexivity.
  } 
  

  specialize (IHh2 precond).

  clear IHh1. (*????*)

  (*----- rec case -----*) (* Dynamic number of induction hypotheses*)
  revert precond.
  stepOne.
  toRec.
  toNextRec.

  destruct h2; intro precond; simpl in precond; try lia; simpl.


  stepThousand.
  eexists.
  split.
  {
    exists 0.
    reflexivity.
  }
  {
    reflexivity.
  }
  
  


  possibly_recursive. (*OK*)

  (* intro precond. *)
  (* inversion precond. *)
  (* 1: discriminate. *)
  
  

  strip_IH_precond IHh2.
  destruct_until_conj IHh2.

  destruct IHh2 as [IHExp IHPostcond].
  pose proof (frame_indep_core_func _ _ _ _ IHExp) as IHExp_fic.
  simpl in IHExp_fic.

  eexists_until_conj.

  (* eexists_until_conj. *)
  (* eapply maxKTransitive'. *)
  eapply maxKTransitive'.
  apply IHExp_fic.





Admitted. *)

(* Theorem reverse_duplicate_is_same_simplify_statement:
  forall (l : Val),
    isWellFormedList l ->
   ⟨ [], (reverse1 (reverse1 (˝l))) ⟩ -->* RValSeq [l].
Proof.

  setoid_rewrite RTCEquiv.
  2: auto.

  is_not_terminated. (*OK*)
  toRec.

  possibly_recursive. (*OK*)
  intro h.




  (* intros precond.

  revert precond. *)
  
  (* apply Zlt_0_ind with (x := h). *)

  (*Get ready to inversion precond with various conditions: /\, \/, etc.*)
  induction h; intro precond; simpl in precond; try lia.
  (*----- base case -----*)
  stepThousand.
  exists 0.
  reflexivity.



  specialize (IHh2 precond).

  clear IHh1. (*????*)

  (*----- rec case -----*) (* Dynamic number of induction hypotheses*)
  revert precond.
  stepOne.
  toRec.
  toNextRec.
  simpl.


  contains_match.

  destruct h2 eqn:h2Heq; intro precond; try inversion precond.
  simpl.
  (*----- base case -----*)
  stepThousand.
  exists 0.
  simpl.
  reflexivity.


  5: {
    intro.
    inversion precond.

  }

  possibly_recursive. (*OK*)

  intro precond.
  (* inversion precond. *)
  (* 1: discriminate. *)
  
  

  (* strip_IH_precond IHh1.
  destruct_until_conj IHh1. *)

  (* destruct IHh2 as [IHExp IHPostcond]. *)
  pose proof (frame_indep_core_func _ _ _ _ IHh2) as IHExp_fic.
  simpl in IHExp_fic.

  
  eapply maxKTransitive'.

  simpl.
  apply IHExp_fic.


  (* 2: exact heq.

  clear heq. clear h.

  intro h.
  intro IH.
  intro heq.
  clear heq.
  intros tcond. (*!!! originally precond*)

  destruct h eqn:heq'. *)


Admitted. *)

Fixpoint fromValList (l : list Val) :=
  match l with
    | [] => VNil
    | h :: tl => VCons h (fromValList tl)
  end.

Compute fromValList [].
Compute fromValList [VLit 2%Z].
Compute fromValList [VLit 2%Z; VLit 2%Z].

Goal forall (l : list Val), exists hd', (fromValList l = VNil \/ fromValList l = VCons hd' (fromValList (tail l))).
Proof.
  
Admitted.


(* Theorem reverse_duplicate_is_same_back_to_Z_simplyLists:
  forall (n : Z) (l : list Val) (hd' : Val), (0 <= n)%Z /\ Z.of_nat (length l) = n /\ (fromValList l = VNil \/ fromValList l = VCons hd' (fromValList (tail l))) ->
  ⟨ [], (reverse1 (reverse1 (˝(fromValList l)))) ⟩ -->* RValSeq [(fromValList l)].
Proof.
  (* solve_symbolically n l hd'. *)
  setoid_rewrite RTCEquiv.
  2: auto.

  is_not_terminated. (*OK*)
  toRec.

  possibly_recursive. (*OK*)

  intro n. intros l hd'.
  intro precond.
  assert (0 <= n)%Z as heq by lia.
  (* assert (Z.of_nat (length l) = n) as t'heq by lia. *)
  revert precond.
  revert l hd'.

  apply Zlt_0_ind with (x := n).
  2: exact heq.

  clear heq. clear n.

  intro h.
  intro IH.
  intro heq.
  intros t hd'.
  clear heq.
  intro precond.

  destruct h eqn:heq'.
  + clear IH.
    Search (Z.to_nat 0).
    
    destruct t. (*!!!!!!!!*)
    stepThousand.
    exists 0. reflexivity.
    destruct precond. (*!!!!!!!!*)
    inversion H0. (*!!!!!!!!*)
    inversion H1. (*!!!!!!!!*)
  + let Tp := type of precond in
    let Th := type of heq' in
    assert (Tp /\ Th) as precond'. constructor. assumption. assumption. (*!!!!!!*)
    clear precond.
    clear heq'.
    revert precond'.
    revert t hd'.
    revert h.
    stepOne.
    toRec.

    contains_match. (*OK*)

    intros h.
    intros t hd'.
    intro precond.
    destruct precond.
    destruct H.
    destruct H1.

    destruct (fromValList t) eqn:HEQ; try inversion H2; try discriminate. (*!!!!!!!*)
    * simpl. stepThousand. exists 0. reflexivity.
    * simpl.
      
      specialize (IH (Z.pos p - 1)%Z). (*!!!!!!*)
      strip_IH_precond IH.

      specialize (IH (tail t)). (*!!!!!!*)

      destruct (head (tail t)) eqn:HTHeq.
      ++ specialize (IH v).
         destruct IH.
         {
          split.
           {
            lia.
           }
           {
            split.
            {
             destruct t eqn:HeqT.
             -- discriminate.
             -- simpl.
                simpl in H1.
                lia.
            }
            {
              induction (tail t).
              -- discriminate.
              -- right.
                 simpl.
                 simpl in H3.
                 inversion H3.
                 apply H3 in IHl.
                 
            }
           }
         }
      ++


      destruct (head t) eqn:headHeq.
      - specialize (IH v).
        destruct IH.
        {
          split.
            lia.
          split.
            Search (head _ = Some _).
            {
              destruct t eqn:HeqT.
              ++ discriminate.
              ++ simpl.
                 simpl in H1.
                 lia.
            }
            {
              destruct t eqn:HeqT.
              ++ simpl. left. reflexivity.
              ++ simpl. right.
                 simpl in HEQ.
                 simpl in H3.
                 inversion H3.
                 inversion headHeq.
                 subst.





            }  
                 

                 
            
        }

      - pose proof head_None t. (*!!!!!!!!!!!!!*)
        apply H4 in headHeq.
        rewrite headHeq in HEQ.
        simpl in HEQ.
        discriminate.
      
 
  + nia.

Qed. *)


Inductive quotedList {A : Set} : nat -> Type :=
  | QNil : @quotedList A 0
  | QCons : forall {n : nat}, A -> @quotedList A n -> @quotedList A (S n)
.

Check QNil.

Check (QCons 13 (QCons 12 QNil)).






Fixpoint fromQuotedList {n : nat} (l : @quotedList Val n) :=
  match l with
    | QNil => VNil
    | QCons h tl => VCons h (fromQuotedList tl)
  end.

(* 
Theorem reverse_duplicate_is_same_back_to_Z:
  forall (n : Z) (l: @quotedList Val (Z.to_nat n)), (0 <= n)%Z ->
  ⟨ [], (reverse1 (reverse1 (˝(fromQuotedList l)))) ⟩ -->* RValSeq [(fromQuotedList l)].
Proof.
  (* solve_symbolically n l. *)
  setoid_rewrite RTCEquiv.
  2: auto.

  is_not_terminated. (*OK*)
  toRec.

  possibly_recursive. (*OK*)

  intro n. intro l.
  intro precond.
  assert (0 <= n)%Z as heq by lia.
  revert precond.
  revert l.

  apply Zlt_0_ind with (x := n).
  2: exact heq.

  clear heq. clear n.

  intro h.
  intro IH.
  intro heq.
  intro t.
  clear heq.
  intro precond.

  destruct h eqn:heq'.
  + clear IH.
    Search (Z.to_nat 0).
    rewrite Z2Nat.inj_0.
    destruct t.
    stepThousand.
    exists 0. reflexivity.
    

    


Qed. *)



(* Theorem reverse_duplicate_is_same:
  forall (l : Val), isList l ->
  ⟨ [], (reverse1 (reverse1 (˝l))) ⟩ -->* RValSeq [l].
Proof.
  setoid_rewrite RTCEquiv.
  2: auto.

  is_not_terminated. (*OK*)
  toRec.

  possibly_recursive. (*OK*)
  idtac "trying induction...".
  intro h.
  intro precond.
  destruct h; try destruct precond.
  + stepThousand. exists 0. reflexivity.
  +

  



  intro l.
  intro precond.
  (* solve_symbolically l. *)
Qed. *)





