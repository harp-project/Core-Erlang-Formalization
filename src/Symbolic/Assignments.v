(* From CoreErlang.BigStep Require Import FunctionalBigStep. *)
From CoreErlang.FrameStack Require SubstSemantics SubstSemanticsLemmas.

Open Scope string_scope.

Module FrameStack.

Import FrameStack.SubstSemantics.

Import ListNotations.
(*
  Let "e" be a parameter expression.

  letrec 'fact'/1 =
    fun(X) ->
      case X of
        <0> -> 1
        <Z> -> let <Y> = apply 'fact'/1(call 'erlang':'-'(Z, 1))
                 in call 'erlang':'*'(Z,Y);
    in
      apply 'fact'/1(e)

  Define the above expression!
 *)

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


(* Hint: to solve statements about scopes (e.g., VALCLOSED), use "scope_solver"!
   Also using "(e)constructor" could help you determine which rule of the semantics
   can be used. Beware, not all semantic rules are syntax-driven, there are rules
   about ECase expressions that can applied to the same configuration.

   Since you prove the evaluation of a factorial function, thus expect repetition
   of proof steps in the script you write. This proof should not be short (>120 LOC),
   if you write out each step.

   Tactics you should use: apply, (e)constructor, simpl, relfexivity, auto, congruence
 *)
(* Prove the following theorem *)
Theorem fact_eval_3 :
  ⟨[], fact_frameStack (˝VLit 3%Z)⟩ -->* RValSeq [VLit 6%Z].
Proof.
  
Admitted.

From CoreErlang.Interpreter Require Import StepFunctions Equivalences.

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

Fixpoint sequentialStepMaxK0 (fs : FrameStack) (r : Redex) (k : nat) : option (FrameStack * Redex) :=
  match fs, r with
  | [], RValSeq _ => Some (fs, r)
  | _, _ =>
    match k with
    | 0 => Some (fs, r)
    | S k' => match sequentialStepFunc fs r with
              | Some (fs', r') => sequentialStepMaxK0 fs' r' k'
              | None => None
              end
    end
  end.

Arguments sequentialStepFunc !_ !_ /.
Arguments sequentialStepMaxK0 !_ !_ !_ /.

Theorem fact_eval_example0:
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK0 [] (fact_frameStack (˝VLit z)) 1000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Admitted.

Fixpoint sequentialStepMaxK (fs : FrameStack) (r : Redex) (k : nat) : option (FrameStack * Redex) :=
  match k with
  | 0 => Some (fs, r)
  | S k' => match sequentialStepFunc fs r with
            | Some (fs', r') => sequentialStepMaxK fs' r' k'
            | None => match fs, r with
                      | [], RValSeq _ => Some (fs, r)
                      | _, _ => None
                      end
            end
  end.

Arguments sequentialStepMaxK !_ !_ !_ /.

Theorem fact_eval_example:
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK [] (fact_frameStack (˝VLit z)) 1000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Qed.

Fixpoint sequentialStepMaxK' (fs : FrameStack) (r : Redex) (p : positive) : option (FrameStack * Redex) :=
  match p with
  | xH => 
    match sequentialStepFunc fs r with
    | Some (fs', r') => Some (fs', r')
    | None =>
      match fs, r with
      | [], RValSeq _ => Some (fs, r)
      | _, _ => None
      end
    end
  | xO p' => 
    let res := sequentialStepMaxK' fs r p' in
    match res with
    | Some (fs', r') => sequentialStepMaxK' fs' r' p'
    | None => None
    end
  | xI p' => 
    let res := sequentialStepMaxK' fs r p' in
    match res with
    | Some (fs', r') =>
      let res' := sequentialStepMaxK' fs' r' p' in
      match res' with
      | Some (fs'', r'') =>
        match sequentialStepFunc fs'' r'' with
        | Some (fs''', r''') => Some (fs''', r''')
        | None =>
          match fs'', r'' with
          | [], RValSeq _ => Some (fs'', r'')
          | _, _ => None
          end
        end
      | None => None
      end
    | None => None
    end
  end.

Arguments sequentialStepMaxK' !_ !_ !_ /.
(* Arguments Z.leb : simpl never. *)
Opaque Z.leb.

Theorem fact_eval_example':
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK' [] (fact_frameStack (˝VLit z)) 100000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Qed.

Fixpoint sequentialStepMaxK'' (fs : FrameStack) (r : Redex) (p : positive) : option (FrameStack * Redex) :=
  match fs, r with
  | [], RValSeq _ => Some (fs, r)
  | _, _ =>
    match p with
    | xH => sequentialStepFunc fs r
    | xO p' =>
      match sequentialStepMaxK'' fs r p' with
      | Some (fs', r') => sequentialStepMaxK'' fs' r' p'
      | None => None
      end
    | xI p' =>
      match sequentialStepFunc fs r with
      | Some (fs', r') =>
        match sequentialStepMaxK'' fs' r' p' with
        | Some (fs'', r'') => sequentialStepMaxK'' fs'' r'' p'
        | None => None
        end
      | None => None
      end
    end
  end.

Arguments sequentialStepMaxK'' !_ !_ !_ /.

Theorem fact_eval_example'':
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), sequentialStepMaxK'' [] (fact_frameStack (˝VLit z)) 100000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|lia].
Admitted.

Fixpoint sequentialStepMaxK''' (fs : FrameStack) (r : Redex) (p : positive) : option (FrameStack * Redex) :=
  match sequentialStepFunc fs r with
  | None => 
    match fs, r with
    | [], RValSeq _ => Some (fs, r)
    | _, _ => None
    end
  | Some (fs', r') =>
    match p with
    | xH => Some (fs', r')
    | xO p' =>
      match sequentialStepMaxK''' fs r p' with
      | Some (fs'', r'') => sequentialStepMaxK''' fs'' r'' p'
      | None => None
      end
    | xI p' =>
      match sequentialStepMaxK''' fs' r' p' with
      | Some (fs'', r'') => sequentialStepMaxK''' fs'' r'' p'
      | None => None
      end
    end
  end.

Print positive.
Print positive_ind.
Print Pos.peano_ind.
Print Pos.lt_ind.

Definition sequentialStepMaxK'''0 (fs : FrameStack) (r : Redex) (n : N) : option (FrameStack * Redex) :=
  match n with
  | N0 => Some (fs, r)
  | Npos p => sequentialStepMaxK''' fs r p
  end.

Print N.

Arguments sequentialStepMaxK''' !_ !_ !_ /.

Require Import SMTCoq.Tactics.

Theorem fact_eval_example''':
  forall (z : Z), (0 <= z < 30)%Z -> exists (y : Z), sequentialStepMaxK''' [] (fact_frameStack (˝VLit z)) 100000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. admit. cvc4. all:try lia.
  eexists. split;[reflexivity|nia].
Qed.

Fixpoint ssmk (fs : FrameStack) (r : Redex) (p : positive) : FrameStack * Redex :=
  match sequentialStepFunc fs r with
  | None => (fs, r)
  | Some (fs', r') =>
    match p with
    | xH => (fs', r')
    | xO p' =>
      let (fs'', r'') := ssmk fs r p' in ssmk fs'' r'' p'
    | xI p' =>
      let (fs'', r'') := ssmk fs' r' p' in ssmk fs'' r'' p'
    end
  end.

Arguments ssmk !_ !_ !_ /.

(*

Ltac case_innermost_term t :=
  lazymatch t with
  | context[match ?x with _ => _ end] =>
      first [ case_innermost_term x
            | destruct x eqn:?H ]
  | _ => fail "No match subterm found"
  end.

Ltac case_innermost :=
  match goal with
  | |- ?g => case_innermost_term g
  end.

*)

Require Import Psatz.

Theorem fact_eval_example'''':
  forall (z : Z), (0 <= z < 30)%Z -> exists (y : Z), ssmk [] (fact_frameStack (˝VLit z)) 10000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros. unfold fact_frameStack.
  all:simpl. all:try lia.
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
  case_innermost.
  all:simpl. all:try lia.
  eexists. split;[reflexivity|nia].
Qed.

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

Theorem fact_eval_example''''':
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

Lemma ssmaxk_can_step:
  forall (k : positive) (fs fs' : FrameStack) (r r' : Redex) (v : Val),
    fs <> [] -> r <> RValSeq [v] ->
    sequentialStepMaxK''' fs r k = Some (fs', r') -> sequentialStepFunc fs r <> None.
Proof.
  intros.
  destruct k.
  all:unfold sequentialStepMaxK''' in H1.
  all:destruct (sequentialStepFunc fs r) eqn:Hssf; auto.
  all:destruct fs; auto.
Qed.

Lemma minusplus: forall (x y : Z), (x - 1 =? y)%Z = true -> (x =? y + 1)%Z = true.
Proof. smt. Qed.

CoInductive StateStream : Type :=
| Cons : FrameStack * Redex -> StateStream -> StateStream.

CoFixpoint costep (fs : FrameStack) (r : Redex) : StateStream :=
  match sequentialStepFunc fs r with
  | Some (fs', r') => Cons (fs', r') (costep fs' r')
  | None => Cons (fs, r) (costep fs r)
  end.

Fixpoint coeval (s : StateStream) (n : nat) : FrameStack * Redex :=
  match n, s with
  | 0, Cons (fs, r) _ => (fs, r)
  | S n', Cons _ s' => coeval s' n'
  end.

Theorem fact_eval_example''''':
  forall (z : Z), (0 <= z < 5)%Z -> exists (y : Z), coeval (costep [] (fact_frameStack (˝VLit z))) 1000 = ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros.
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
Qed.

Theorem fact_eval_example'''':
  forall (z : Z), (0 <= z)%Z -> exists (y : Z), sequentialStepMaxK''' [] (fact_frameStack (˝VLit z)) 1000 = Some ([], RValSeq [VLit y]) /\ (z <= y)%Z.
Proof.
  intros.
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|lia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|nia].
  all:simpl. all:try lia.  
  case_innermost.
  eexists. split. reflexivity. (* clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11. *)
(*   assert (z = 12%Z) by smt. *)
  clear -H12.
  assert (forall z, ((z - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 - 1 =? 0)%Z = true) -> (z = 12%Z)) by smt.
  apply H in H12. subst. lia.
  
  apply H13 in H12. subst. auto.
  clear H0 H1 H12.
  assert (((z =? 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)%Z = true) -> (z = 12%Z)) by smt.
  
  assert ((z =? 0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)%Z = true). lia.
  assert ((z =? 12)%Z = true) by smt. 
  
  eexists. split;[reflexivity|nia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|nia].
  all:simpl. all:try lia.
  case_innermost.
  eexists. split;[reflexivity|nia].
  all:simpl. all:try lia.
  case_innermost.
  clear H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14.
  eexists. split. reflexivity.
  Search "_ * _"%Z "<="%Z.
  assert (z = 15%Z). admit.
  assert (z = (15 - 1 + 1)%Z). easy.
  
Admitted.

Lemma ssmaxk_steppy_steppy:
  forall (k : positive) (fs fs' fs'' : FrameStack) (r r' r'' : Redex),
    sequentialStepMaxK''' fs r k = Some (fs', r') ->
    sequentialStepFunc fs' r' = Some (fs'', r'') ->
    sequentialStepMaxK''' fs r (k + 1) = Some (fs'', r'').
Proof.
  intros k.
  Print Pos.lt_ind.
Admitted.

Theorem ssmaxk_trans:
  forall (k l: positive) (fs fs' fs'' : FrameStack) (r r' r'' : Redex),
    sequentialStepMaxK''' fs  r  k                = Some (fs',  r' ) ->
    sequentialStepMaxK''' fs' r' l                = Some (fs'', r'') ->
    sequentialStepMaxK''' fs  r  (k + l)%positive = Some (fs'', r'').
Proof.
  induction k using Pos.peano_ind.
  * induction l using Pos.peano_ind; intros.
    + assert ((1+1)%positive = 2%positive). lia. rewrite H1. clear H1.
      unfold sequentialStepMaxK'''.
      destruct (sequentialStepFunc fs r) eqn:Hssf.
      - destruct p.
        unfold sequentialStepMaxK''' in H. rewrite Hssf in H. inv H.
        destruct (sequentialStepFunc fs' r') eqn:Hssf0.
        ** destruct p. unfold sequentialStepMaxK''' in H0.
           rewrite Hssf0 in H0. auto.
        ** unfold sequentialStepMaxK''' in H0. rewrite Hssf0 in H0. auto.
      - unfold sequentialStepMaxK''' in H. rewrite Hssf in H.
        destruct fs eqn:Hfs; try discriminate. destruct r eqn:Hr; try discriminate.
        inv H. simpl in H0. exact H0.
    +
  *
Qed.


(* symbolic execution plans TODO:
    These plans come "outside in", starting with the big picture.
    Although the actual implementation is likely to be "inside out".
    
    - Start out with an Erlang module file
    - Add comments to it in a standard format, containing preconditions and postconditions about a function
      - Preconditions should be about the input of the function (be mindful about arity)
      - Postconditions should be about the output of the function (termination in RValSeq)
      - Search depth: the "k" steps required for the execution. This should also be a parameter, since
        Coq can not handle divergence.
    - Utilize and change the pretty-printer, so it prints a theorem, where the function to be
      tested is given the arguments specified in the precondition comments. The postcondition is given by the
      value the program leads to and the condition after. The standard format should look like 
      fact_eval_example' above.
      - with this approach, we don't need to develop as much metatheory.
      - however, "k" steps is still an issue. even with the arguments + bang pattern thingy. It gets slower
        as k increases. "simpl" still causes stack overflow for big enough values.
    - Make a custom tactic that tries to solve the goal. Utilize smt solvers (this is when the lack of
      metatheory is a big advantage).
      - Possibly more than 1 SMT solvers should be utilized, with a heuristic?
      - SMT solvers are utilized in 2 cases. Either finding out if the termination satisfies the goal
        (end of config execution), or finding out that a configuration is impossible (moving along with
        config execution).
        - if termination does not satisfy a goal: FAIL: the message should provide the configuration of the
          symbolic variables under which the fail (list of hypotheses). INVESTIGATE: can 'a' (or 'the')
          concrete value be given for symbolic variables under the hypotheses?
        - if termination satisfies the goal, but SMT solvers can not solve the goal: POTENTIAL FAIL: the
          message should provide the hypotheses. Maybe the goal is actually solvable, just not by the SMT
          solver. Unfortunately, because of the laws of the universe as we know it in 2025, not all goals
          are trivially solvable by SMT solvers. It's probably impossible to tell this point and the
          previous one apart (at least I think).
        - if moving along with a configuration can not happen, and the SMT solver find that it can not happen:
          HAPPINESS: goal should be solved automatically.
        - if moving along with a configuration can not happen, and the SMT solver does not find out:
          UNHAPPINESS, TRY MOVING ALONG: this stinks, but as I've stated not all goals are solvable by SMT
          solvers. Maybe we get to configurations that can be solvable? Unfortunately I don't
          think we can do induction automatically (if we can, I think it's a big big hassle).
        - if moving along with the configuration can happen: HAPPINESS, TRY MOVING ALONG: this is a standard
          case. Again, I do not think that we can differentiate between this point and the previous one.
      - The output of the tactic should be a list of goals that could not be solved automatically.
    - Have a way to try to prove everything without even opening the Coq file. So generate the file with the
      new pretty printer from the Erlang source code, and have a 'running' file that tries compiling the
      coq file. If the custom tactic can solve everything, inform the user. If it can not solve everything,
      display the unsolved goals. The user should only have to open Coq for unsolved goals if absolutely
      necessary.
    
    PROS for this approach:
      - The tool should easily integrate with the Erlang code
      - Writing preconditions and postconditions in a standardized way should make goal generation standard
      - If goal generation is standard, metatheory in Coq should not be needed to be developed
      - If metatheory is not needed, integrating SMT solvers should be more straightforward
    CONS (or more precisely, THINGS TO SOLVE):
      - developing the standard way of writing pre- and postconditions in the Erlang file is not
        as easy as it first seems. Preconditions are the trickier part: Arity and symbolic variable order
        might need to be defined by hand (since the precond is just a conjunction of conditions).
        Postconditions need a special symbol for the value produced. This might also need to be hand defined.
      - SMT solvers can not solve everything. We just have to live with this fact.
      - The "k" step problem. A step count needs to be defined, or else the multi-step function is not
        descending. Defining "k" with "nat"-s causes stack overflow, even with the tactics having
        bang pattern arguments. "k" can not be existential, because that would mean that we need to be able
        to calculate it beforehand (impossible). A good solution needs to be devised. I suspect choosing
        "nat"-s for a step count also causes the proofs to be slow.
      - running out of "k" steps should be explicitly stated somehow, somewhere.
      - what about concurrency? I suspect that, since steps are not deterministic, a new way of doing
        multiple steps in a row is required. Like with the pmap example, have a list of actions taken
        along the way (at least I think that's how that works?). This would be very complicated, and honestly,
        it might go beyond the scope of the thesis. Somebody in the future will have the unfortunate task
        of figuring all that out.
      - installing SMT solvers might be a bit complex since the change from Coq to Rocq
      - what about other data types? Integers are one thing, lists, strings and maps are a whole problem
        in their own right. Especially because of bounds (if they are needed).
      - Bounds: I don't think there is a general way to have unbounded expressions. Limiting the step count
        to "k" should solve this issue somewhat. Programs without recursion should be fine, and for recursive
        programs the step limit should suffice.
    
    PLANS for the thesis:
    [x] investigate solutions for the "k" problem           <
    [x] install SMT solvers (not trivial unfortunately).    | do most of this before the trip to
        Actually, just "lia" can be used until it's done.   | Singapore, and before lab work
    [ ] Have a few nice example programs                    | kicks into high gear
    [ ] implement the solver tactic                         |
    [ ] figure out the pretty printer part                  <
    [ ] equivalence proofs
    [ ] if I have time (hopefully): look into concurrency
    [ ] write the text of the thesis
 *)

Theorem fact_eval_example:
  forall (x y : Z), (x >= 0)%Z /\ (x < 3)%Z -> ⟨[], fact_frameStack (˝VLit x)⟩ -->* RValSeq [VLit y] -> (x <= y)%Z.
Proof.
  intros. unfold step_any in H0. destruct H0. destruct H0. unfold fact_frameStack in H1.
  inv H1; apply sequentialStepEquiv in H2;[|scope_solver]; simpl in H2; inv H2.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
  destruct x eqn:Hx; inv H4.
  * inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3. Search "<="%Z 0. apply Z2Nat.neq_0_nonneg. auto. inv H1.
  * inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H2; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    inv H3; apply sequentialStepEquiv in H1;[|scope_solver]; simpl in H1; inv H1.
    destruct (if (Z.pos p - 1 =? 0)%Z then Some [] else None) eqn:Hp.
    + inv H4. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1.
      inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2.
      inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1.
      inv H3. inv H1. inv H17. inv H2.
      - Search "*"%Z. rewrite Z.mul_1_r. apply Z.le_refl.
      - inv H1.
    + inv H4. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1.
      inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2.
      inv H1. inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1.
      inv H3. inv H1. inv H2. inv H1. inv H3. inv H1. inv H2. inv H1. inv H3.
      inv H1. inv H2. admit.
  * lia. (* H is impossible *)
Admitted.

(* Define the following function in Core Erlang! To compile a Core Erlang file
   use the "from_core" option of the standard compiler/interpreter.
   For examples, we refer to the language specification:
   https://www.it.uu.se/research/group/hipe/cerl/doc/core_erlang-1.0.3.pdf
   You can also check example codes in the Erl_codes folder.
   Instead of the letrec expression, define it as a top level function *)
Definition collatz (e : Exp) : Exp :=
  ELetRec [
    (1, °ECase (˝VVar 1)
     [
       ([PLit 1%Z], ˝ttrue, ˝VNil);
       ([PVar],
          °ECall (˝erlang) (˝VLit "and") [
            °ECall (˝erlang) (˝VLit "<") [˝VLit 0%Z; ˝VVar 0];
            °ECall (˝erlang) (˝VLit "=") [
              ˝VLit 0%Z;
              °ECall (˝erlang) (˝VLit "rem") [˝VVar 0; ˝VLit 2%Z]
            ]
          ],
         °ECons (˝VVar 0) (EApp (˝VFunId (1,1)) [
           °ECall (˝erlang) (˝VLit "div") [˝VVar 0; ˝VLit 2%Z]
         ])
       );
       ([PVar], °ECall (˝erlang) (˝VLit "<") [˝VLit 0%Z; ˝VVar 0],
         °ECons (˝VVar 0) (EApp (˝VFunId (1,1)) [
           °ECall (˝erlang) (˝VLit "+")
             [°ECall (˝erlang) (˝VLit "*") [˝VLit 3%Z; ˝VVar 0];
              ˝VLit 1%Z]
         ])
       )
     ])
  ]
  (EApp (˝VFunId (0, 1)) [e]).

(*
  module 'exercise' ['fun_func'/1,
                    'module_info'/0,
                    'module_info'/1]
    attributes []
  'collatz'/1 =
    (fun (_0) ->
      (case <_0> of
        <1> when 'true' -> []
        <X> when
          call 'erlang':'and'(
            call 'erlang':'<'(0, _0),
            call 'erlang':'=='(0, call 'erlang':'rem'(_0, 2))
          ) ->
          [X|apply 'collatz'/1(call 'erlang':'div'(X,2))]
   <X> when
      call 'erlang':'<'(0, _0) ->
          [X|apply 'collatz'/1(call 'erlang':'+'
     (call 'erlang':'*'(3, X), 1))]
        end
        -| [{'function',{'fun_func',1}}] )
      -| [{'function',{'fun_func',1}}] )

%% Needed by erlc

  'module_info'/0 =
    ( fun () ->
      call 'erlang':'get_module_info'
        ('exercise')
      -| [{'function',{'module_info',0}}] )
  'module_info'/1 =
    ( fun (_0) ->
      call 'erlang':'get_module_info'
        ('exercise', ( _0
          -| [{'function',{'module_info',1}}] ))
      -| [{'function',{'module_info',1}}] )
end
*)

(* Erlang def

  collatz(1) -> [];
  collatz(X) when ((0 == (X rem 2)) band (0 < X)) ->
    [X | collatz(X div 2)];
  collatz(X) when 0 < X ->
    [X | collatz(3 * X + 1)].

*)


(*
  Hard task:
    Prove the following theorem about the correctness of fact!

  Use induction over n! Follow the scheme described in fact_eval_3. Check what
  theorems are available about transitive evaluation.
*)

Ltac do_step := econstructor; [constructor;auto|simpl].

Theorem fact_eval : forall n,
  ⟨[], fact_frameStack (˝VLit (Z.of_nat n))⟩ -->* RValSeq [VLit (Z.of_nat (Factorial.fact n))].
Proof.
  (*
  induction n; intros.
  - unfold step_any. eexists. split.
    + apply valseq_is_result. apply Forall_cons.
      scope_solver.
      apply Forall_nil.
    + do 3 do_step. scope_solver.
      do 2 do_step. discriminate.
      do 1 do_step. scope_solver.
      econstructor. eapply eval_cool_params. reflexivity. simpl.
      do 2 do_step. scope_solver.
      econstructor. apply eval_step_case_match. reflexivity. simpl.
      econstructor. apply cool_value. scope_solver.
      econstructor. apply eval_step_case_true.
      econstructor. apply cool_value. scope_solver.
      econstructor.

  - unfold step_any.
      inv IHn. inv H. unfold fact_frameStack in H1.
      inv H1. inv H. simpl in H2. inv H2. inv H. inv H1. inv H.
      inv H2. inv H. inv H1. inv H. clear H10 H4 H0. inv H2. inv H.
      inv H0. inv H. simpl in H8. inv H8. cbn in H1.

      eexists. split.

    + apply valseq_is_result. apply Forall_cons.
      scope_solver.
      apply Forall_nil.
    + do 3 do_step. scope_solver.
      do 2 do_step. discriminate.
      econstructor. apply cool_value. scope_solver.
      econstructor. eapply eval_cool_params. reflexivity. simpl.

      do 2 do_step. scope_solver.
      econstructor. apply eval_step_case_not_match. reflexivity.
      econstructor. apply eval_step_case_match. reflexivity. simpl. (* Ask about it *)
      econstructor. apply cool_value. scope_solver.
      do 4 do_step. scope_solver.
      do 2 do_step. discriminate.
      do 2 do_step. scope_solver.
      do 2 do_step. scope_solver.
      do 2 do_step. discriminate.
      econstructor. apply cool_value. scope_solver.
      do 2 do_step. scope_solver.
      econstructor. eapply eval_cool_params. reflexivity.
      Search Pos.of_succ_nat Z.of_nat. rewrite Znat.Zpos_P_of_succ_nat. simpl.
      econstructor. eapply eval_cool_params. reflexivity. simpl.

      replace (Z.succ (Z.of_nat n) - 1)%Z with (Z.of_nat n)%Z by lia.
      eapply FrameStack.SubstSemanticsLemmas.transitive_eval.

      ++ eapply (FrameStack.SubstSemanticsLemmas.frame_indep_nil _ _ _ _ H1).

      ++ clear H1 H3. do 7 do_step. congruence.
         do 3 do_step. econstructor. econstructor. econstructor. simpl.
         unfold eval_arith. simpl.
         rewrite Znat.Nat2Z.inj_add. rewrite Z.add_comm.
         rewrite <- Znat.Nat2Z.inj_succ.
         rewrite Znat.Nat2Z.inj_mul.
         replace ((Z.of_nat n) * (Z.of_nat (Factorial.fact n)))%Z with ((Z.of_nat (Factorial.fact n)) * Z.of_nat n)%Z by lia.
         Search Zmult. rewrite Zmult_succ_r_reverse. rewrite Z.mul_comm. rewrite <- Znat.Nat2Z.inj_succ. econstructor.
         *)
Admitted.


End FrameStack.

Module BigStep.



End BigStep.


	
