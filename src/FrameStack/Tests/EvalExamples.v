(**
  This file contains step-by-step evaluation examples in the frame stack
  semantics:
  - incrementing a value with an anonymous function (`inc_eval`);
  - mapping this increment function over a three-element list with the
    recursive `map` closure of `Examples.v` (`map_eval`).
*)

From CoreErlang.FrameStack Require Import Examples.
Import ListNotations.

Open Scope string_scope.

(** The increment function: `fun(X) -> X + 1` *)
Definition inc : Exp :=
  EFun 1 (ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0;˝VLit 1%Z]).

(** * Applying the increment function to an arbitrary value *)
Section increment.
  Context (v : Val).

  (** The application `inc(v)` *)
  Definition inc_app : Exp := EApp inc [˝v].

  (** The expected result of `inc_app`: the incremented value for integers,
      and a `badarith` exception otherwise. *)
  Local Definition final : Redex :=
  match v with
  | VLit (Integer x) => RValSeq [VLit (x + 1)%Z]
  | _ => badarith (VTuple [VLit "+"; v; VLit 1%Z])
  end.

  (** `inc_app` evaluates to `final` in any frame stack. *)
  Local Lemma inc_eval : forall K, exists k,
    ⟨K, inc_app⟩ -[k]-> ⟨K, final⟩.
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
    (* final result: *)
    unfold final. destruct v. 2: destruct l.
    all: simpl; apply step_refl.
  Qed.

End increment.

(** * Mapping the increment function over a list *)

(** `map(inc, [1, 2, 3])` evaluates to `[2, 3, 4]`. *)
Local Lemma map_eval n :
  ⟨[], EApp (˝@map_clos n) [inc; ˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil))]⟩ -->* RValSeq [VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil))].
Proof.
  eexists. split.
  - constructor.
  - do 2 do_step.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* 1st application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_not_match. reflexivity.
    econstructor. eapply eval_step_case_match. reflexivity.
    do 5 do_step.
    do 2 do_step.
    do_step.
    do 2 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* 2nd application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_not_match. reflexivity.
    econstructor. eapply eval_step_case_match. reflexivity.
    do 5 do_step.
    do 2 do_step.
    do_step.
    do 2 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* 3rd application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_not_match. reflexivity.
    econstructor. eapply eval_step_case_match. reflexivity.
    do 5 do_step.
    do 2 do_step.
    do_step.
    do 2 do_step.
    econstructor. econstructor. reflexivity. simpl.
    (* final application of map *)
    do 2 do_step.
    econstructor. eapply eval_step_case_match. reflexivity. simpl.
    do 2 do_step.
    (* applying +1 to the 3rd element *)
    do 4 do_step.
    do 2 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 4 do_step.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. cbn.
    (* applying +1 to the 2nd element *)
    do 4 do_step.
    do 2 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 4 do_step.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. cbn.
    (* applying +1 to the 1st element *)
    do 4 do_step.
    do 2 do_step.
    do_step.
    econstructor. econstructor. reflexivity. simpl.
    do 4 do_step.
    do 2 do_step.
    do 3 do_step.
    econstructor. econstructor. reflexivity. cbn.
    (* final result *)
    do_step.
    apply step_refl.
Qed.
