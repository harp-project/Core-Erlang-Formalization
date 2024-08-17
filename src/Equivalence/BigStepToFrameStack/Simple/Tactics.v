From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Export MeasureLemmas.

(**
* Basics
  - do_step [Exists]
  - clear_refl
* Remember
  - rmb_sbt_mval
  - rmb_sbt_mval_tmp
  - rmb_sbt_mval_spl
  - rmb_sbt_mval_spl_step
*)

(**
Note: Move Basics to CoreErlangBasics
*)



(* Basics *)



  Ltac do_step
    :=
  econstructor;
  [constructor;auto| simpl].



  Ltac clear_refl
    :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.



(* Remember *)



  Ltac rmb_sbt_mval
    v     (* : Value *)
    name  (* remember as *)
    Hname (* remember eqn *)
    :=
  remember
    (subst_env (measure_val v))
    as name
    eqn:Hname.



  Ltac rmb_sbt_mval_tmp
    v (* : Value *)
    :=
  remember
    (subst_env (measure_val v))
    as _tmp
    eqn:Heq_tmp.



  Ltac rmb_sbt_mval_spl
    v (* : Value *)
    :=
  rmb_sbt_mval_tmp v;
  simpl;
  inversion Heq_tmp;
  subst;
  clear_refl.



  Ltac rmb_sbt_mval_spl_step
    v (* : Value *)
    :=
  rmb_sbt_mval_tmp v;
  simpl;
  do_step;
  inversion Heq_tmp;
  subst;
  clear_refl.