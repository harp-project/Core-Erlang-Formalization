From CoreErlang.Eq.BsFs Require Export B21CreateResultLemmas.

Import BigStep.

(* STRUCTURE:
* Remember
  - rem_sbt
  - rem_sbt_smp
*)












(* Remember *)

Tactic Notation "rem_sbt"
  ":"   constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt.

Tactic Notation "rem_sbt"
  ":"   constr(v1) constr(v2)
  :=
  remember
    (subst_env (measure_val v1))
    as sbt1
    eqn:Hsbt1;
  remember
    (subst_env (measure_val v2))
    as sbt2
    eqn:Hsbt2;
  clear Hsbt1 Hsbt2.

Tactic Notation "rem_sbt"
  ":"   constr(v1) constr(v2) constr(v3)
  :=
  remember
    (subst_env (measure_val v1))
    as sbt1
    eqn:Hsbt1;
  remember
    (subst_env (measure_val v2))
    as sbt2
    eqn:Hsbt2;
  remember
    (subst_env (measure_val v3))
    as sbt3
    eqn:Hsbt3;
  clear Hsbt1 Hsbt2 Hsbt3.



Tactic Notation "rem_sbt_smp"
  ":" constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt;
  simpl;
  inversion Hsbt;
  subst;
  clear_refl.