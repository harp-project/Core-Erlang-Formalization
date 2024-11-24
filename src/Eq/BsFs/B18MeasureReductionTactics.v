From CoreErlang.Eq.BsFs Require Export B17ConvertDefinitions.

Import BigStep.

(* STRUCTURE:
* Trivial
  - trv_le_solver
* Less or Equal
  - ass_le
  - as_le_trn
* Measure Reduction Value Solver
  - mred_solver
* Measure Reduction Expression Solver
  - mred_solver
*)












(* Trivial *)

Ltac trv_le_solver := 
  smp;
  try unfold measure_env_exp;
  try unfold measure_env;
  try unfold measure_list;
  try unfold measure_map;
  try rewrite map_app, list_sum_app;
  sli.






(* Less or Equal *)

Tactic Notation "ass_le"
  "as"  ident(Ile)
  ":"   constr(Cle)
  :=
  assert Cle as Ile by trv_le_solver.

Tactic Notation "ass_le"
  ">"   constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2;
    trv_le_solver).

Tactic Notation "ass_le"
  ">"   constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2) hyp(Hm3)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2, Hm3;
    trv_le_solver).



Tactic Notation "ass_le_trn"
  ">"   constr(Cle_n1_n3)
  "as"  ident(Ile_n1_n3)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3)
  :=
  assert Cle_n1_n3 as Ile_n1_n3 by
    (eapply Nat.le_trans;
      [exact Hle_n1_n2 | exact Hle_n2_n3]).

Tactic Notation "ass_le_trn"
  ">"   constr(Cle_n1_n4)
  "as"  ident(Ile_n1_n4)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3) hyp(Hle_n3_n4)
  :=
  assert Cle_n1_n4 as Ile_n1_n4 by
    (eapply Nat.le_trans;
      [eapply Nat.le_trans;
        [exact Hle_n1_n2 | exact Hle_n2_n3]
      | exact Hle_n3_n4]).






(* Measure Reduction Value Solver *)

Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n1) constr(n2)
  :=
  ass_le as Hle1: (mv <= n1);
  ass_le as Hle2: (mv <= n2);
  solve [ase - theorem: v n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n2)
  :=
  ass_le as Hle2: (mv <= n2);
  solve [ase - theorem: v n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_le as Hle2: (n2 <= n2);
  solve [ase - theorem: v n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(v) ident(Hle)
  ":" constr(theorem) constr(mv) constr(n)
  :=
  ass_le as Hle: (mv <= n);
  solve [ase - theorem: v n Hle].






(* Measure Reduction Expression Solver *)

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n1) constr(n2)
  :=
  ass_le as Hle1: (me <= n1);
  ass_le as Hle2: (me <= n2);
  solve [ase - theorem: env e n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n2)
  :=
  ass_le as Hle2: (me <= n2);
  solve [ase - theorem: env e n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_le as Hle2: (n2 <= n2);
  solve [ase - theorem: env e n1 n2 Hle1 Hle2].

Tactic Notation "mred_solver"
  "-" ident(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_le as Hle: (me <= n);
  solve [ase - theorem: env e n Hle].

Tactic Notation "mred_solver"
  ">" constr(env) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_le as Hle: (me <= n);
  solve [ase - theorem: env e n Hle].