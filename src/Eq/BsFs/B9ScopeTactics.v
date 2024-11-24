From CoreErlang.Eq.BsFs Require Export B8ScopeLemmas.

Import SubstSemantics.

(* STRUCTURE:
* Help
  - scope_solver_triv
  - scope_solver_by
  - scope_solver_cons
  - scope_solver_tuple
  - scope_solver_map
* Main
  - scope
*)












(* Help: *)

Ltac scope_solver_triv :=
  constructor;
  solve [scope_solver].

Ltac scope_solver_by H1 :=
  solve [exact H1].

Ltac scope_solver_cons v1 v2 Hresult_v1 Hresult_v2 :=
  pose proof scope_cons v1 v2 Hresult_v1 Hresult_v2;
  solve [auto].

Ltac scope_solver_tuple v vl Hresult_v Hresult_vl :=
  pose proof scope_tuple v vl Hresult_v Hresult_vl;
  solve [auto].

Ltac scope_solver_map v1 v2 vl Hresult_v1 Hresult_v2 Hresult_vl :=
  pose proof scope_map v1 v2 vl Hresult_v1 Hresult_v2 Hresult_vl;
  solve [auto].









(* Main: *)

Tactic Notation "scope"
  :=
  eexists;
  split;
  [ scope_solver_triv
  | idtac ].

Tactic Notation "scope"
  "-"   ident(I1)
  :=
  eexists;
  split;
  [ scope_solver_by I1
  | clear I1].

Tactic Notation "scope"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  eexists;
  split;
  [ (scope_solver_cons I1 I2 I3 I4
  + scope_solver_tuple I1 I2 I3 I4)
  | clear I3 I4].

Tactic Notation "scope"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5) ident(I6)
  :=
  eexists;
  split;
  [ scope_solver_map I1 I2 I3 I4 I5 I6
  | clear I4 I5 I6].