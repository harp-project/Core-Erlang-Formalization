From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.
From CoreErlang.Interpreter Require Import StepFunctions.

Open Scope string_scope.
Import ListNotations.

Definition fact_frameStack (e : Exp) : Exp :=
  ELetRec
    [(1, °ECase (˝VVar 1) [
      ([PLit 0%Z], ˝ttrue, (˝VLit 1%Z));
      ([PVar], ˝ttrue,
        °ELet 1 (EApp (˝VFunId (1, 1))
          [°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VLit 1%Z]])
          (°ECall (˝VLit "erlang") (˝VLit "*") [˝VVar 1; ˝VVar 0])
      )
    ])]
    (EApp (˝VFunId (0, 1)) [e])
   (* Write the definition here *)
.

Lemma Z_eqb_eq_corr : forall (z1 z2 : Z), (z1 =? z2)%Z = true -> z1 = z2. Proof. lia. Qed.
Lemma Z_eqb_neq_corr: forall (z1 z2 : Z), (z1 =? z2)%Z = false-> z1 <>z2. Proof. lia. Qed.

Ltac case_innermost_term t :=
  lazymatch t with
  | context[match ?x with _ => _ end] =>
      first [ case_innermost_term x
            | let H := fresh "Heq" in
              destruct x eqn:H;
              first [apply Z_eqb_eq_corr in H
                    |apply Z_eqb_neq_corr in H
                    | idtac]]
  | _ => fail "No match subterm found"
  end.

Ltac case_innermost :=
  match goal with
  | |- ?g => case_innermost_term g
  end.

Fixpoint ssmkInner (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match n with
    | 0 => (fs', r')
    | S n' => ssmkInner fs' r' n'
    end
  end.

Definition isEnd (fs : FrameStack) (r : Redex) : bool :=
  match fs, r with
  | [], RValSeq _ => true
  | _, _ => false
  end.

Fixpoint ssmk2 (fs : FrameStack) (r : Redex) (n : nat) : FrameStack * Redex :=
match isEnd fs r with
| true => (fs, r)
| false =>
  match n with
  | 0 => (fs, r)
  | S n' => 
    let (fs', r') := ssmkInner fs r 1000 in
    ssmk2 fs' r' n'
  end
end.

Arguments ssmkInner !_ !_ !_ /.
Arguments ssmk2 !_ !_ !_ /.

Ltac simpl_and_try_solve :=
  simpl;                                          (* simplify the goal *)
  lazymatch goal with
  | [ |- context[ssmk2] ] => try lia              (* eval not done: is the case impossible? *)
  | _ => try (eexists; split;[reflexivity|nia])   (* eval done: the result exists & postcond holds *)
  end.


Ltac solve_forward :=
  repeat (simpl_and_try_solve; case_innermost).


Theorem fact_eval_example:
  forall (z : Z), (0 <= z < 30)%Z -> exists (y : Z), ssmk2 [] (fact_frameStack (˝VLit z)) 1000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
  case_innermost.
  all:simpl_and_try_solve.
Qed.

Theorem fact_eval_example':
  forall (z : Z), (0 <= z < 30)%Z -> exists (y : Z), ssmk2 [] (fact_frameStack (˝VLit z)) 1000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros; unfold fact_frameStack.
  solve_forward.
Qed.



















