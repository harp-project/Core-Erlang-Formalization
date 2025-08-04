From CoreErlang.FrameStack Require Import Examples.
Import ListNotations.

Open Scope string_scope.

Section increment.
  Context (v : Val)
          (Hv : VALCLOSED v).
  Definition inc : Exp :=
    EFun 1 (ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0;˝VLit 1%Z]).
  Definition inc_app : Exp := EApp inc [˝v].

  Local Definition final (v : Val) : Redex :=
  match v with
  | VLit (Integer x) => RValSeq [VLit (x + 1)%Z]
  | _ => badarith (VTuple [VLit "+"; v; VLit 1%Z])
  end.
  Local Lemma inc_eval : forall K, exists k,
    ⟨K, inc_app⟩ -[k]-> ⟨K, final v⟩.
  Proof.
    intros. eexists.
    (* evaluation *)
    unfold inc.
    do 4 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 6 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. simpl.
    cbn.
    (* final result: *)
    destruct v. 2: destruct l.
    all: simpl; apply step_refl.
  Qed.

End increment.

Section map.

  Local Lemma map_eval n :
    ⟨[], EApp (˝@map_clos n) [inc; ˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil))]⟩ -->* RValSeq [VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil))].
  Proof.
    eexists. split.
    {
      constructor. scope_solver.
    }
    do 2 do_step. scope_solver.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* 1st application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_not_match. reflexivity.
    econstructor. eapply eval_step_case_match. reflexivity.
    do 5 do_step. scope_solver.
    do 2 do_step.
    do_step. scope_solver.
    do 2 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* 2nd application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_not_match. reflexivity.
    econstructor. eapply eval_step_case_match. reflexivity.
    do 5 do_step. scope_solver.
    do 2 do_step.
    do_step. scope_solver.
    do 2 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* 3rd application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_not_match. reflexivity.
    econstructor. eapply eval_step_case_match. reflexivity.
    do 5 do_step. scope_solver.
    do 2 do_step.
    do_step. scope_solver.
    do 2 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* final application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_match. reflexivity. simpl.
    do 2 do_step.
    (* applying +1 to each element *)
    do 4 do_step. scope_solver.
    do 2 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 4 do_step. scope_solver.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. cbn.
    (**)
    do 4 do_step. scope_solver.
    do 2 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 4 do_step. scope_solver.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. cbn.
    (**)
    do 4 do_step. scope_solver.
    do 2 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 4 do_step. scope_solver.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. cbn.
    (**)
    do_step.
    apply step_refl.
  Qed.

End map.