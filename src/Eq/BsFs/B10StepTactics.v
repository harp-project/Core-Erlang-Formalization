From CoreErlang.Eq.BsFs Require Export B9ScopeTactics.

Import SubstSemantics.

(* STRUCTURE:
* Help
  - do_framestack_step
  - do_framestack_transitive
* Main
  - step
*)












(* Help: *)


Ltac do_framestack_step
  :=
  (econstructor;
  [ (constructor; auto + scope_solver + congruence)
  + (econstructor; constructor)
  + (econstructor;
    [ congruence
    | constructor ])
  | simpl ])
  + (cbn; constructor).



Ltac do_framestack_transitive H
  :=
  eapply transitive_eval;
  [ eapply frame_indep_core in H;
    exact H
  | clear H;
    simpl ].









(* Main: *)

Tactic Notation "step"
  :=
  repeat do_framestack_step.

Tactic Notation "step"
  "-"   hyp(H)
  :=
  repeat do_framestack_step;
  (solve [exact H] + do_framestack_transitive H).

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
    clear I1 I2 I3 I4 I5.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "step"
  ":"   tactic(T)
  :=
  repeat do_framestack_step + T.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1)
  :=
  repeat do_framestack_step + T;
  clear I1.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3 I4.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3 I4 I5.