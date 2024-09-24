From CoreErlang.FrameStack Require SubstSemantics.
From CoreErlang.FrameStack Require Export CTX.


Open Scope string_scope.


Module FrameStack.


Import FrameStack.SubstSemantics.

Import ListNotations.
Import Coq.ZArith.Znat.


Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [
      (1, °ECase (˝VVar 1)
        [
          ([PLit 0%Z], ˝VLit "true", 
            ˝VLit 1%Z);
          ([PVar], ˝VLit "true", 
            (°ELet 1 (EApp (˝VFunId (1, 1)) [(°ECall (˝VLit "erlang") (˝VLit "-")  [˝VVar 0; ˝VLit 1%Z])])
              (°ECall (˝VLit "erlang") (˝VLit "*")  [˝VVar 1; ˝VVar 0])))
        ])
    ]
  (EApp (˝VFunId (0, 1)) [e])
.


(*
  Hard task:
    Prove the following theorem about the correctness of fact!


  Use induction over n! Follow the scheme described in fact_eval_3. Check what
  theorems are available about transitive evaluation.
*)

Lemma singelton_list_inj : forall (x : Z) (y : Z),
  x = y -> RValSeq [VLit x] = RValSeq [VLit y].
 Proof.
  intros.
  rewrite H.
  reflexivity.
 Qed.

Check Z.to_N.
Check Z.to_N (Z.of_nat 1).

Lemma succ_n_to_succ_z : forall n,
  Z.of_nat (S n) = Z.succ (Z.of_nat n).
Proof.
  intro n.
  cbn.
  apply Zpos_P_of_succ_nat.
Qed.

Lemma succ_inj : forall x y,
  x = y -> Z.succ x = Z.succ y.
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Lemma succsub_to_sub_succ : forall n,
  (Z.succ (Z.succ (Z.of_nat n)) - 1)%Z  = 
  (Z.succ (Z.succ (Z.of_nat n) - 1))%Z.
Proof.
  intros.
  set (z := (Z.of_nat n)) in *.
  cbn.
  rewrite <- Z.sub_succ_l.
  reflexivity.
Qed.

Lemma possuccsub1n_eq_n : forall n,
  (Z.pos (Pos.of_succ_nat n) - 1)%Z = Z.of_nat n.
Proof.
  intros.
  rewrite Zpos_P_of_succ_nat.
  induction n.
  * cbn. reflexivity.
  * rewrite succ_n_to_succ_z.
    assert ((Z.succ (Z.of_nat n) - 1)%Z = Z.of_nat n -> (Z.succ (Z.succ (Z.of_nat n)) - 1)%Z = Z.succ (Z.of_nat n)).
    {
      rewrite succsub_to_sub_succ.
      apply succ_inj.
    }
    apply H.
    apply IHn.
Qed.

Lemma succ_nat_minus_1_equals_nat : forall n,
  eval_arith "erlang" "-" [VLit (Z.pos (Pos.of_succ_nat n)); VLit 1%Z] = RValSeq [VLit (Z.of_nat n)]. 
Proof.
  unfold eval_arith.
  unfold convert_string_to_code.
  intro n.
  assert ((Z.pos (Pos.of_succ_nat n) - 1)%Z = Z.of_nat n -> RValSeq [VLit (Z.pos (Pos.of_succ_nat n) - 1)%Z] = RValSeq [VLit (Z.of_nat n)]). 
  {
    Check Z.of_nat.
    apply singelton_list_inj.
  }
  apply H.
  apply possuccsub1n_eq_n. 
Qed.



Lemma factnplus1 : forall n,
  (n + 1) * fact n = fact n + n * fact n .
Proof.
  intro n.
  Check Nat.mul_add_distr_r.
  rewrite Nat.mul_add_distr_r.
  rewrite Nat.mul_1_l.
  rewrite Nat.add_comm.
  reflexivity. 
Qed.

Lemma of_nat_succ : forall n : nat, Z.of_nat (n + 1) = Z.pos (Pos.of_succ_nat n).
Proof.
  intros.
  rewrite Nat.add_1_r.
  simpl.
  reflexivity.
Qed.

Lemma fact_pos : forall n,
 (0 < Z.of_nat (fact n))%Z.
Proof.
  intros n.
  induction n as [|n' IH].
  - simpl. 
    apply Z.lt_0_1.
  - simpl. 
    Search "lt_0".
    lia.
Qed.

Theorem fact_eval : forall n,
  ⟨[], fact_frameStack (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.
    intros n.
    induction n.
    *   simpl. econstructor.
        {
            split.
            {
                constructor.
                constructor.
                scope_solver.
                constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                simpl. reflexivity.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                congruence.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                simpl. econstructor.
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                apply eval_step_case_match.
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. econstructor.
            {
                simpl. constructor.
            }
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            simpl. constructor.
        }
    *   inversion IHn. inversion H.
        unfold fact_frameStack.
        unfold fact_frameStack in H1.
        inv H1.
        inv H2.
        simpl in H3.
        inv H3.
        inv H1.
        simpl in H2.
        inv H2.
        inv H1.
        simpl in H3.
        inv H3.
        inv H1.
        simpl in H2.
        inv H2.
        inv H1.
        simpl in H3.
        inv H3.
        inv H1.
        simpl in H2.
        simpl. eexists.
        {
            split.
            (* VALCLOSED *)
            {
                constructor.
                constructor.
                {
                scope_solver.
                }
                constructor.
            }
            (* ELetRec *)
            simpl. econstructor.
            {
                simpl. constructor.
                simpl. constructor.
            }
            (* EApp *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FApp1 *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* <> *)
            simpl. econstructor.
            {
                simpl. constructor.
                congruence.

            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FParams *)
            simpl. econstructor.
            {
                simpl. econstructor.
                simpl. constructor.
            }
            (* ------------------------ #1 Recurzion ------------------------ *)
            (* ECase *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver. 
            }
            (* FCase1 *)
            simpl. econstructor.
            {
                apply eval_step_case_not_match.
                simpl. reflexivity.
            }
            (* FCase1 *)
            simpl. econstructor.
            {
                apply eval_step_case_match.
                simpl. reflexivity.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FCase2 *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* FLet *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* FLet *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FApp1 *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* <> *)
            simpl. econstructor.
            {
                simpl. constructor.
                congruence.
            }
            (* FParams *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FCallMod *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FCallFun *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* <> *)
            simpl. econstructor.
            {
                simpl. constructor.
                congruence.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FParams *)
            simpl. econstructor.
            {
                simpl. constructor.
            }
            (* VALCLOSED *)
            simpl. econstructor.
            {
                simpl. constructor.
                scope_solver.
            }
            (* FParams *)
            simpl. econstructor.
            {
                simpl. econstructor.
                simpl. constructor.
            }
            rewrite -> succ_nat_minus_1_equals_nat.
            
            eapply frame_indep_core in H2.
            {
                eapply transitive_eval.
                {
                    apply H2.
                }
                clear.
                cbn.
                econstructor.
                {
                  simpl. now constructor.
                }
                cbn. econstructor. 
                {
                  constructor.
                }
                cbn. econstructor. 
                {
                  constructor.
                  scope_solver.
                }
                cbn. econstructor. 
                {
                  constructor.
                }
                cbn. econstructor. 
                {
                  constructor.
                  scope_solver.
                }
                cbn. econstructor. 
                {
                  constructor.
                }
                cbn. econstructor. 
                {
                  constructor.
                  congruence.
                }
                cbn. econstructor. 
                {
                  constructor.
                  scope_solver.
                }
                cbn. econstructor. 
                {
                  constructor.
                }
                cbn. econstructor. 
                {
                  constructor.
                  scope_solver.
                }
                cbn. econstructor. 
                {
                  econstructor.
                  reflexivity.
                }
                assert (eval_arith "erlang" "*" ([VLit (Z.pos (Pos.of_succ_nat n))] ++ [VLit (Z.of_nat (fact n))]) = RValSeq [VLit (Z.of_nat (fact n + n * fact n))]).
                {
                  cbn.
                  f_equal.
                  f_equal.
                  f_equal.
                  Search fact.
                  pose proof lt_O_fact n.
                  Search Z.pos Z.lt eq.
                  Search Z.of_nat lt.
                  apply inj_lt in H1.
                  simpl in H1.
                  Search Z.pos Z.lt eq.
                  rewrite <- (Z2Pos.id (Z.of_nat (fact n))).
                  {
                    rewrite <- factnplus1.
                    rewrite Nat2Z.inj_mul.
                    Check Pos.of_succ_nat.
                    Search "of_succ_nat".
                    rewrite of_nat_succ.
                    Search "to_pos".
                    rewrite Pos2Z.inj_mul.
                    rewrite Z2Pos.id.
                    {
                      reflexivity.
                    }
                    apply fact_pos.
                  }
                  assumption.
                }
                rewrite H1.
                constructor.
            }
        }
Qed.

(*
++ ?Fs'', [VLit (Z.of_nat n)] ⟩ -[ k0 ]-> ⟨ [] ++ ?Fs'',
     [VLit (Z.of_nat (fact n))] ⟩
     
     

   FLet 1
     (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VLit (Z.pos (Pos.of_succ_nat n)); ˝ VVar 0])],
[VLit (Z.of_nat n)] ⟩ -[ ?Goal@{x:=S (S (S (S (S (S k0)))))} ]-> ⟨ 
?Fs', ?e' ⟩
*)


(*

⟨ [FParams (IApp (VClos [(0, 1, ° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])] 0 1 (° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))]))) [] []], [VLit (Z.of_nat n)] ⟩ 
    -[ k0 ]-> 
⟨ [], [VLit (Z.of_nat (Factorial.fact n))] ⟩


⟨ [FParams (IApp (VClos [(0, 1, ° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))])] 0 1 (° ECase (˝ VVar 1) [([PLit 0%Z], ˝ VLit "true", ˝ VLit 1%Z); ([PVar], ˝ VLit "true", ° ELet 1 (° EApp (˝ VFunId (1, 1)) [° ECall (˝ VLit "erlang") (˝ VLit "-") [˝ VVar 0; ˝ VLit 1%Z]]) (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VVar 1; ˝ VVar 0]))]))) [] []; FLet 1 (° ECall (˝ VLit "erlang") (˝ VLit "*") [˝ VLit (Z.pos (Pos.of_succ_nat n)); ˝ VVar 0])], eval_arith "erlang" "-" [VLit (Z.pos (Pos.of_succ_nat n)); VLit 1%Z] ⟩ 
    -[ ?k ]-> 
⟨ [], [VLit (Z.of_nat (Factorial.fact n + n * Factorial.fact n))] ⟩

*)

End FrameStack.