(**
DOCUMENTATION:
* itr - intros
* exs - exists
* rev - revert
* gen - generalize dependent
* clr - clear
* sym - symmetry
* bym - by symmetry
* smp - simpl
* bmp - by simpl
* sbn - cbn
* bbn - by cbn
* fld - fold
* ufl - unfold
* rfl - refold
* tfl - tryfold
*)



(**
STRUCTURE:
* Intros
* Exists
* Revert
* Generalize Dependent
* Clear
* Simplifiy
* CBN
* Fold
* Unfold
* Refold
* Tryfold
*)









(* Intros *)



Tactic Notation "itr"
  :=
  intros.

Tactic Notation "itr"
  "-" ident(I1)
  :=
  intros I1.

Tactic Notation "itr"
  "-" ident(I1) ident(I2)
  :=
  intros I1 I2.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3)
  :=
  intros I1 I2 I3.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  intros I1 I2 I3 I4.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  intros I1 I2 I3 I4 I5.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6)
  :=
  intros I1 I2 I3 I4 I5 I6.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7)
  :=
  intros I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18) ident(I19)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18) ident(I19) ident(I20)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20.









(* Exists *)



Tactic Notation "exs"
  "-" constr(C1)
  :=
  exists C1.

Tactic Notation "exs"
  "-" constr(C1) constr(C2)
  :=
  exs - C1;
  exists C2.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3)
  :=
  exs - C1 C2;
  exists C3.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  exs - C1 C2 C3;
  exists C4.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  exs - C1 C2 C3 C4;
  exists C5.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  exs - C1 C2 C3 C4 C5;
  exists C6.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  exs - C1 C2 C3 C4 C5 C6;
  exists C7.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  exs - C1 C2 C3 C4 C5 C6 C7;
  exists C8.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  exs - C1 C2 C3 C4 C5 C6 C7 C8;
  exists C9.

Tactic Notation "exs"
  "-" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  exs - C1 C2 C3 C4 C5 C6 C7 C8 C9;
  exists C10.



Ltac eex := eexists.









(* Revert *)



Tactic Notation "rev"
  "-" ident(I1)
  :=
  revert I1.

Tactic Notation "rev"
  "-" ident(I1) ident(I2)
  :=
  rev - I1;
  revert I2.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3)
  :=
  rev - I1 I2;
  revert I3.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  rev - I1 I2 I3;
  revert I4.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  rev - I1 I2 I3 I4;
  revert I5.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6)
  :=
  rev - I1 I2 I3 I4 I5;
  revert I6.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7)
  :=
  rev - I1 I2 I3 I4 I5 I6;
  revert I7.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8)
  :=
  rev - I1 I2 I3 I4 I5 I6 I7;
  revert I8.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  rev - I1 I2 I3 I4 I5 I6 I7 I8;
  revert I9.

Tactic Notation "rev"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  rev - I1 I2 I3 I4 I5 I6 I7 I8 I9;
  revert I10.









(* Generalize Dependent *)



Tactic Notation "gen"
  "-" ident(x)
  :=
  generalize dependent x.

Tactic Notation "gen"
  "-" ident(I1) ident(I2)
  :=
  gen - I1;
  generalize dependent I2.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3)
  :=
  gen - I1 I2;
  generalize dependent I3.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  gen - I1 I2 I3;
  generalize dependent I4.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  gen - I1 I2 I3 I4;
  generalize dependent I5.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6)
  :=
  gen - I1 I2 I3 I4 I5;
  generalize dependent I6.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7)
  :=
  gen - I1 I2 I3 I4 I5 I6;
  generalize dependent I7.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8)
  :=
  gen - I1 I2 I3 I4 I5 I6 I7;
  generalize dependent I8.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  gen - I1 I2 I3 I4 I5 I6 I7 I8;
  generalize dependent I9.

Tactic Notation "gen"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  gen - I1 I2 I3 I4 I5 I6 I7 I8 I9;
  generalize dependent I10.









(* Clear *)



Ltac clear_refl :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.



Tactic Notation "clr"
  "-" ident(I1)
  :=
  clear_refl;
  clear I1.

Tactic Notation "clr"
  "-" ident(I1) ident(I2)
  :=
  clear_refl;
  clear I1 I2.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3)
  :=
  clear_refl;
  clear I1 I2 I3.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear_refl;
  clear I1 I2 I3 I4.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear_refl;
  clear I1 I2 I3 I4.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4)  ident(I5)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18) ident(I19)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19.

Tactic Notation "clr"
  "-" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18) ident(I19) ident(I20)
  :=
  clear_refl;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20.






Tactic Notation "clr"
  "+" ident(I1)
  :=
  clear_refl;
  clear - I1.

Tactic Notation "clr"
  "+" ident(I1) ident(I2)
  :=
  clear_refl;
  clear - I1 I2.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3)
  :=
  clear_refl;
  clear - I1 I2 I3.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear_refl;
  clear - I1 I2 I3 I4.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear_refl;
  clear - I1 I2 I3 I4.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4)  ident(I5)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18) ident(I19)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19.

Tactic Notation "clr"
  "+" ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
      ident(I16) ident(I17) ident(I18) ident(I19) ident(I20)
  :=
  clear_refl;
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10
    I11 I12 I13 I14 I15 I16 I17 I18 I19 I20.








(* Symmetry *)



Tactic Notation "sym"
  :=
  symmetry.

Tactic Notation "sym"
  "*"
  :=
  symmetry in *.



Tactic Notation "sym"
  "-" hyp(H1)
  :=
  symmetry in H1.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2)
  :=
  clear_refl;
  symmetry in H1, H2.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  symmetry in H1, H2, H3.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  symmetry in H1, H2, H3, H4.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  symmetry in H1, H2, H3, H4, H5.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6)
  :=
  symmetry in H1, H2, H3, H4, H5, H6.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "sym"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.






Tactic Notation "sym"
  "+" hyp(H1)
  :=
  symmetry in H1 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2)
  :=
  symmetry in H1, H2 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3)
  :=
  symmetry in H1, H2, H3 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  symmetry in H1, H2, H3, H4 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  symmetry in H1, H2, H3, H4, H5 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6)
  :=
  symmetry in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "sym"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.



Ltac bym := sym; auto.









(* Simplify *)



Tactic Notation "smp"
  :=
  simpl.

Tactic Notation "smp"
  "*"
  :=
  simpl in *.



Tactic Notation "smp"
  "-" hyp(H1)
  :=
  simpl in H1.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2)
  :=
  clear_refl;
  simpl in H1, H2.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  simpl in H1, H2, H3.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  simpl in H1, H2, H3, H4.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  simpl in H1, H2, H3, H4, H5.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6)
  :=
  simpl in H1, H2, H3, H4, H5, H6.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "smp"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.






Tactic Notation "smp"
  "+" hyp(H1)
  :=
  simpl in H1 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2)
  :=
  simpl in H1, H2 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3)
  :=
  simpl in H1, H2, H3 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  simpl in H1, H2, H3, H4 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  simpl in H1, H2, H3, H4, H5 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6)
  :=
  simpl in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "smp"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.



Ltac bmp := smp; auto.









(* CBN *)



Tactic Notation "sbn"
  :=
  cbn.

Tactic Notation "sbn"
  "*"
  :=
  cbn in *.



Tactic Notation "sbn"
  "-" hyp(H1)
  :=
  cbn in H1.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2)
  :=
  clear_refl;
  cbn in H1, H2.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  cbn in H1, H2, H3.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  cbn in H1, H2, H3, H4.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  cbn in H1, H2, H3, H4, H5.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6)
  :=
  cbn in H1, H2, H3, H4, H5, H6.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "sbn"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.






Tactic Notation "sbn"
  "+" hyp(H1)
  :=
  cbn in H1 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2)
  :=
  cbn in H1, H2 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3)
  :=
  cbn in H1, H2, H3 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  cbn in H1, H2, H3, H4 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  cbn in H1, H2, H3, H4, H5 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6)
  :=
  cbn in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "sbn"
  "+" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
      hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.



Ltac bbn := sbn; auto.









(* Fold *)



Tactic Notation "fld"
  "-" smart_global(G1)
  :=
  fold G1.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2)
  :=
  fld - G1;
  fold G2.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2) smart_global(G3)
  :=
  fld - G1 G2;
  fold G3.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  :=
  fld - G1 G2 G3;
  fold G4.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5)
  :=
  fld - G1 G2 G3 G4;
  fold G5.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6)
  :=
  fld - G1 G2 G3 G4 G5;
  fold G6.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7)
  :=
  fld - G1 G2 G3 G4 G5 G6;
  fold G7.

Tactic Notation "fld"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  :=
  fld - G1 G2 G3 G4 G5 G6 G7;
  fold G8.






Tactic Notation "fld"
  "-"   smart_global(G1)
  "in"  hyp(H1)
  :=
  fold G1 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  fld - G1 in H1;
  fold G2 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  fld - G1 G2 in H1;
  fold G3 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  fld - G1 G2 G3 in H1;
  fold G4 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  fld - G1 G2 G3 G4 in H1;
  fold G5 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  fld - G1 G2 G3 G4 G5 in H1;
  fold G6 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  fld - G1 G2 G3 G4 G5 G6 in H1;
  fold G7 in H1.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  fld - G1 G2 G3 G4 G5 G6 G7 in H1;
  fold G8 in H1.






Tactic Notation "fld"
  "+"   smart_global(G1)
  "in"  hyp(H1)
  :=
  fold G1 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  fld + G1 in H1;
  fold G2 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  fld + G1 G2 in H1;
  fold G3 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  fld + G1 G2 G3 in H1;
  fold G4 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  fld + G1 G2 G3 G4 in H1;
  fold G5 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  fld + G1 G2 G3 G4 G5 in H1;
  fold G6 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  fld + G1 G2 G3 G4 G5 G6 in H1;
  fold G7 in H1 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  fld + G1 G2 G3 G4 G5 G6 G7 in H1;
  fold G8 in H1 |- *.






Tactic Notation "fld"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  fold G1 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 in H1 H2;
  fold G2 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 G2 in H1 H2;
  fold G3 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 G2 G3 in H1 H2;
  fold G4 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 G2 G3 G4 in H1 H2;
  fold G5 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 G2 G3 G4 G5 in H1 H2;
  fold G6 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 G2 G3 G4 G5 G6 in H1 H2;
  fold G7 in H1, H2.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  fold G8 in H1, H2.






Tactic Notation "fld"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  fold G1 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 in H1 H2;
  fold G2 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 G2 in H1 H2;
  fold G3 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 G2 G3 in H1 H2;
  fold G4 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 G2 G3 G4 in H1 H2;
  fold G5 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 G2 G3 G4 G5 in H1 H2;
  fold G6 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 G2 G3 G4 G5 G6 in H1 H2;
  fold G7 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  fold G8 in H1, H2 |- *.






Tactic Notation "fld"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fold G1 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 in H1 H2 H3;
  fold G2 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 G2 in H1 H2 H3;
  fold G3 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 G2 G3 in H1 H2 H3;
  fold G4 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 G2 G3 G4 in H1 H2 H3;
  fold G5 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 G2 G3 G4 G5 in H1 H2 H3;
  fold G6 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  fold G7 in H1, H2, H3.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  fold G8 in H1, H2, H3.






Tactic Notation "fld"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fold G1 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 in H1 H2 H3;
  fold G2 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 G2 in H1 H2 H3;
  fold G3 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 G2 G3 in H1 H2 H3;
  fold G4 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 G2 G3 G4 in H1 H2 H3;
  fold G5 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 G2 G3 G4 G5 in H1 H2 H3;
  fold G6 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  fold G7 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  fold G8 in H1, H2, H3 |- *.






Tactic Notation "fld"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fold G1 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 in H1 H2 H3 H4;
  fold G2 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 G2 in H1 H2 H3 H4;
  fold G3 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 G2 G3 in H1 H2 H3 H4;
  fold G4 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 G2 G3 G4 in H1 H2 H3 H4;
  fold G5 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  fold G6 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  fold G7 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  fold G8 in H1, H2, H3, H4.






Tactic Notation "fld"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fold G1 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 in H1 H2 H3 H4;
  fold G2 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 G2 in H1 H2 H3 H4;
  fold G3 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 G2 G3 in H1 H2 H3 H4;
  fold G4 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 G2 G3 G4 in H1 H2 H3 H4;
  fold G5 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  fold G6 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  fold G7 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  fold G8 in H1, H2, H3, H4 |- *.






Tactic Notation "fld"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fold G1 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 in H1 H2 H3 H4 H5;
  fold G2 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 G2 in H1 H2 H3 H4 H5;
  fold G3 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 G2 G3 in H1 H2 H3 H4 H5;
  fold G4 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  fold G5 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  fold G6 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  fold G7 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  fold G8 in H1, H2, H3, H4, H5.






Tactic Notation "fld"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fold G1 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 in H1 H2 H3 H4 H5;
  fold G2 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 G2 in H1 H2 H3 H4 H5;
  fold G3 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 G2 G3 in H1 H2 H3 H4 H5;
  fold G4 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  fold G5 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  fold G6 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  fold G7 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  fold G8 in H1, H2, H3, H4, H5 |- *.









(* Unfold *)



Tactic Notation "ufl"
  "-" smart_global(G1)
  :=
  unfold G1.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2)
  :=
  ufl - G1;
  unfold G2.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3)
  :=
  ufl - G1 G2;
  unfold G3.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  :=
  ufl - G1 G2 G3;
  unfold G4.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5)
  :=
  ufl - G1 G2 G3 G4;
  unfold G5.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6)
  :=
  ufl - G1 G2 G3 G4 G5;
  unfold G6.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7)
  :=
  ufl - G1 G2 G3 G4 G5 G6;
  unfold G7.

Tactic Notation "ufl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  :=
  ufl - G1 G2 G3 G4 G5 G6 G7;
  unfold G8.






Tactic Notation "ufl"
  "-"   smart_global(G1)
  "in"  hyp(H1)
  :=
  unfold G1 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  ufl - G1 in H1;
  unfold G2 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  ufl - G1 G2 in H1;
  unfold G3 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  ufl - G1 G2 G3 in H1;
  unfold G4 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  ufl - G1 G2 G3 G4 in H1;
  unfold G5 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  ufl - G1 G2 G3 G4 G5 in H1;
  unfold G6 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  ufl - G1 G2 G3 G4 G5 G6 in H1;
  unfold G7 in H1.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  ufl - G1 G2 G3 G4 G5 G6 G7 in H1;
  unfold G8 in H1.






Tactic Notation "ufl"
  "+"   smart_global(G1)
  "in"  hyp(H1)
  :=
  unfold G1 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  ufl + G1 in H1;
  unfold G2 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  ufl + G1 G2 in H1;
  unfold G3 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  ufl + G1 G2 G3 in H1;
  unfold G4 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  ufl + G1 G2 G3 G4 in H1;
  unfold G5 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  ufl + G1 G2 G3 G4 G5 in H1;
  unfold G6 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  ufl + G1 G2 G3 G4 G5 G6 in H1;
  unfold G7 in H1 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  ufl + G1 G2 G3 G4 G5 G6 G7 in H1;
  unfold G8 in H1 |- *.






Tactic Notation "ufl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  unfold G1 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 in H1 H2;
  unfold G2 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 G2 in H1 H2;
  unfold G3 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 G2 G3 in H1 H2;
  unfold G4 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 G2 G3 G4 in H1 H2;
  unfold G5 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 G2 G3 G4 G5 in H1 H2;
  unfold G6 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 G2 G3 G4 G5 G6 in H1 H2;
  unfold G7 in H1, H2.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  unfold G8 in H1, H2.






Tactic Notation "ufl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  unfold G1 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 in H1 H2;
  unfold G2 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 G2 in H1 H2;
  unfold G3 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 G2 G3 in H1 H2;
  unfold G4 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 G2 G3 G4 in H1 H2;
  unfold G5 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 G2 G3 G4 G5 in H1 H2;
  unfold G6 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 G2 G3 G4 G5 G6 in H1 H2;
  unfold G7 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  unfold G8 in H1, H2 |- *.






Tactic Notation "ufl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  unfold G1 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 in H1 H2 H3;
  unfold G2 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 G2 in H1 H2 H3;
  unfold G3 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 G2 G3 in H1 H2 H3;
  unfold G4 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 G2 G3 G4 in H1 H2 H3;
  unfold G5 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 G2 G3 G4 G5 in H1 H2 H3;
  unfold G6 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  unfold G7 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  unfold G8 in H1, H2, H3.






Tactic Notation "ufl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  unfold G1 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 in H1 H2 H3;
  unfold G2 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 G2 in H1 H2 H3;
  unfold G3 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 G2 G3 in H1 H2 H3;
  unfold G4 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 G2 G3 G4 in H1 H2 H3;
  unfold G5 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 G2 G3 G4 G5 in H1 H2 H3;
  unfold G6 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  unfold G7 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  unfold G8 in H1, H2, H3 |- *.






Tactic Notation "ufl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  unfold G1 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 in H1 H2 H3 H4;
  unfold G2 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 G2 in H1 H2 H3 H4;
  unfold G3 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 G2 G3 in H1 H2 H3 H4;
  unfold G4 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 G2 G3 G4 in H1 H2 H3 H4;
  unfold G5 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  unfold G6 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  unfold G7 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  unfold G8 in H1, H2, H3, H4.






Tactic Notation "ufl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  unfold G1 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 in H1 H2 H3 H4;
  unfold G2 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 G2 in H1 H2 H3 H4;
  unfold G3 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 G2 G3 in H1 H2 H3 H4;
  unfold G4 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 G2 G3 G4 in H1 H2 H3 H4;
  unfold G5 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  unfold G6 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  unfold G7 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  unfold G8 in H1, H2, H3, H4 |- *.






Tactic Notation "ufl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  unfold G1 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 in H1 H2 H3 H4 H5;
  unfold G2 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 G2 in H1 H2 H3 H4 H5;
  unfold G3 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 G2 G3 in H1 H2 H3 H4 H5;
  unfold G4 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  unfold G5 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  unfold G6 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  unfold G7 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  unfold G8 in H1, H2, H3, H4, H5.






Tactic Notation "ufl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  unfold G1 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 in H1 H2 H3 H4 H5;
  unfold G2 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 G2 in H1 H2 H3 H4 H5;
  unfold G3 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 G2 G3 in H1 H2 H3 H4 H5;
  unfold G4 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  unfold G5 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  unfold G6 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  unfold G7 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  unfold G8 in H1, H2, H3, H4, H5 |- *.









(* Refold *)



Tactic Notation "refold"
  smart_global(G)
  :=
  unfold G;
  fold G.

Tactic Notation "refold"
        smart_global(G)
  "in"  hyp(H1)
  :=
  unfold G in H1;
  fold G in H1.

Tactic Notation "refold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2)
  :=
  unfold G in H1, H2;
  fold G in H1, H2.

Tactic Notation "refold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3)
  :=
  unfold G in H1, H2, H3;
  fold G in H1, H2, H3.

Tactic Notation "refold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4)
  :=
  unfold G in H1, H2, H3, H4;
  fold G in H1, H2, H3, H4.

Tactic Notation "refold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) "," hyp(H5)
  :=
  unfold G in H1, H2, H3, H4, H5;
  fold G in H1, H2, H3, H4, H5.






Tactic Notation "rfl"
  "-" smart_global(G1)
  :=
  refold G1.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2)
  :=
  rfl - G1;
  refold G2.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3)
  :=
  rfl - G1 G2;
  refold G3.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  :=
  rfl - G1 G2 G3;
  refold G4.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5)
  :=
  rfl - G1 G2 G3 G4;
  refold G5.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6)
  :=
  rfl - G1 G2 G3 G4 G5;
  refold G6.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7)
  :=
  rfl - G1 G2 G3 G4 G5 G6;
  refold G7.

Tactic Notation "rfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  :=
  rfl - G1 G2 G3 G4 G5 G6 G7;
  refold G8.






Tactic Notation "rfl"
  "-"   smart_global(G1)
  "in"  hyp(H1)
  :=
  refold G1 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  rfl - G1 in H1;
  refold G2 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  rfl - G1 G2 in H1;
  refold G3 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  rfl - G1 G2 G3 in H1;
  refold G4 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  rfl - G1 G2 G3 G4 in H1;
  refold G5 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  rfl - G1 G2 G3 G4 G5 in H1;
  refold G6 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  rfl - G1 G2 G3 G4 G5 G6 in H1;
  refold G7 in H1.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  rfl - G1 G2 G3 G4 G5 G6 G7 in H1;
  refold G8 in H1.






Tactic Notation "rfl"
  "+"   smart_global(G1)
  "in"  hyp(H1)
  :=
  refold G1 in H1;
  refold G1.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  rfl + G1 in H1;
  refold G2 in H1;
  refold G2.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  rfl + G1 G2 in H1;
  refold G3 in H1;
  refold G3.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  rfl + G1 G2 G3 in H1;
  refold G4 in H1;
  refold G4.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  rfl + G1 G2 G3 G4 in H1;
  refold G5 in H1;
  refold G5.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  rfl + G1 G2 G3 G4 G5 in H1;
  refold G6 in H1;
  refold G6.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  rfl + G1 G2 G3 G4 G5 G6 in H1;
  refold G7 in H1;
  refold G7.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  rfl + G1 G2 G3 G4 G5 G6 G7 in H1;
  refold G8 in H1;
  refold G8.






Tactic Notation "rfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  refold G1 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 in H1 H2;
  refold G2 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 G2 in H1 H2;
  refold G3 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 G2 G3 in H1 H2;
  refold G4 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 G2 G3 G4 in H1 H2;
  refold G5 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 G2 G3 G4 G5 in H1 H2;
  refold G6 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 G2 G3 G4 G5 G6 in H1 H2;
  refold G7 in H1, H2.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  refold G8 in H1, H2.






Tactic Notation "rfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  refold G1 in H1, H2;
  refold G1.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 in H1 H2;
  refold G2 in H1, H2;
  refold G2.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 G2 in H1 H2;
  refold G3 in H1, H2;
  refold G3.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 G2 G3 in H1 H2;
  refold G4 in H1, H2;
  refold G4.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 G2 G3 G4 in H1 H2;
  refold G5 in H1, H2;
  refold G5.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 G2 G3 G4 G5 in H1 H2;
  refold G6 in H1, H2;
  refold G6.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 G2 G3 G4 G5 G6 in H1 H2;
  refold G7 in H1, H2;
  refold G7.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  refold G8 in H1, H2;
  refold G8.






Tactic Notation "rfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  refold G1 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 in H1 H2 H3;
  refold G2 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 G2 in H1 H2 H3;
  refold G3 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 G2 G3 in H1 H2 H3;
  refold G4 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 G2 G3 G4 in H1 H2 H3;
  refold G5 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 G2 G3 G4 G5 in H1 H2 H3;
  refold G6 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  refold G7 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  refold G8 in H1, H2, H3.






Tactic Notation "rfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  refold G1 in H1, H2, H3;
  refold G1.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 in H1 H2 H3;
  refold G2 in H1, H2, H3;
  refold G2.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 G2 in H1 H2 H3;
  refold G3 in H1, H2, H3;
  refold G3.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 G2 G3 in H1 H2 H3;
  refold G4 in H1, H2, H3;
  refold G4.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 G2 G3 G4 in H1 H2 H3;
  refold G5 in H1, H2, H3;
  refold G5.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 G2 G3 G4 G5 in H1 H2 H3;
  refold G6 in H1, H2, H3;
  refold G6.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  refold G7 in H1, H2, H3;
  refold G7.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  refold G8 in H1, H2, H3;
  refold G8.






Tactic Notation "rfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  refold G1 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 in H1 H2 H3 H4;
  refold G2 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 G2 in H1 H2 H3 H4;
  refold G3 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 G2 G3 in H1 H2 H3 H4;
  refold G4 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 G2 G3 G4 in H1 H2 H3 H4;
  refold G5 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  refold G6 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  refold G7 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  refold G8 in H1, H2, H3, H4.






Tactic Notation "rfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  refold G1 in H1, H2, H3, H4;
  refold G1.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 in H1 H2 H3 H4;
  refold G2 in H1, H2, H3, H4;
  refold G2.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 G2 in H1 H2 H3 H4;
  refold G3 in H1, H2, H3, H4;
  refold G3.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 G2 G3 in H1 H2 H3 H4;
  refold G4 in H1, H2, H3, H4;
  refold G4.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 G2 G3 G4 in H1 H2 H3 H4;
  refold G5 in H1, H2, H3, H4;
  refold G5.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  refold G6 in H1, H2, H3, H4;
  refold G6.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  refold G7 in H1, H2, H3, H4;
  refold G7.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  refold G8 in H1, H2, H3, H4;
  refold G8.






Tactic Notation "rfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  refold G1 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 in H1 H2 H3 H4 H5;
  refold G2 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 G2 in H1 H2 H3 H4 H5;
  refold G3 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 G2 G3 in H1 H2 H3 H4 H5;
  refold G4 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  refold G5 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  refold G6 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  refold G7 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  refold G8 in H1, H2, H3, H4, H5.






Tactic Notation "rfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  refold G1 in H1, H2, H3, H4, H5;
  refold G1.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 in H1 H2 H3 H4 H5;
  refold G2 in H1, H2, H3, H4, H5;
  refold G2.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 G2 in H1 H2 H3 H4 H5;
  refold G3 in H1, H2, H3, H4, H5;
  refold G3.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 G2 G3 in H1 H2 H3 H4 H5;
  refold G4 in H1, H2, H3, H4, H5;
  refold G4.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  refold G5 in H1, H2, H3, H4, H5;
  refold G5.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  refold G6 in H1, H2, H3, H4, H5;
  refold G6.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  refold G7 in H1, H2, H3, H4, H5;
  refold G7.

Tactic Notation "rfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  refold G8 in H1, H2, H3, H4, H5;
  refold G8.









(* Refold *)



Tactic Notation "tryfold"
  smart_global(G)
  :=
  try unfold G;
  fold G.

Tactic Notation "tryfold"
        smart_global(G)
  "in"  hyp(H1)
  :=
  try unfold G in H1;
  fold G in H1.

Tactic Notation "tryfold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2)
  :=
  try unfold G in H1;
  fold G in H1;
  try unfold G in H2;
  fold G in H2.

Tactic Notation "tryfold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3)
  :=
  try unfold G in H1;
  fold G in H1;
  try unfold G in H2;
  fold G in H2;
  try unfold G in H3;
  fold G in H3.

Tactic Notation "tryfold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4)
  :=
  try unfold G in H1;
  fold G in H1;
  try unfold G in H2;
  fold G in H2;
  try unfold G in H3;
  fold G in H3;
  try unfold G in H4;
  fold G in H4.

Tactic Notation "tryfold"
        smart_global(G)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) "," hyp(H5)
  :=
  try unfold G in H1;
  fold G in H1;
  try unfold G in H2;
  fold G in H2;
  try unfold G in H3;
  fold G in H3;
  try unfold G in H4;
  fold G in H4;
  try unfold G in H5;
  fold G in H5.






Tactic Notation "tfl"
  "-" smart_global(G1)
  :=
  tryfold G1.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2)
  :=
  tfl - G1;
  tryfold G2.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3)
  :=
  tfl - G1 G2;
  tryfold G3.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  :=
  tfl - G1 G2 G3;
  tryfold G4.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5)
  :=
  tfl - G1 G2 G3 G4;
  tryfold G5.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6)
  :=
  tfl - G1 G2 G3 G4 G5;
  tryfold G6.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7)
  :=
  tfl - G1 G2 G3 G4 G5 G6;
  tryfold G7.

Tactic Notation "tfl"
  "-" smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
      smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  :=
  tfl - G1 G2 G3 G4 G5 G6 G7;
  tryfold G8.






Tactic Notation "tfl"
  "-"   smart_global(G1)
  "in"  hyp(H1)
  :=
  tryfold G1 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  tfl - G1 in H1;
  tryfold G2 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  tfl - G1 G2 in H1;
  tryfold G3 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  tfl - G1 G2 G3 in H1;
  tryfold G4 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  tfl - G1 G2 G3 G4 in H1;
  tryfold G5 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  tfl - G1 G2 G3 G4 G5 in H1;
  tryfold G6 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  tfl - G1 G2 G3 G4 G5 G6 in H1;
  tryfold G7 in H1.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  tfl - G1 G2 G3 G4 G5 G6 G7 in H1;
  tryfold G8 in H1.






Tactic Notation "tfl"
  "+"   smart_global(G1)
  "in"  hyp(H1)
  :=
  tryfold G1 in H1;
  tryfold G1.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1)
  :=
  tfl + G1 in H1;
  tryfold G2 in H1;
  tryfold G2.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1)
  :=
  tfl + G1 G2 in H1;
  tryfold G3 in H1;
  tryfold G3.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1)
  :=
  tfl + G1 G2 G3 in H1;
  tryfold G4 in H1;
  tryfold G4.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1)
  :=
  tfl + G1 G2 G3 G4 in H1;
  tryfold G5 in H1;
  tryfold G5.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1)
  :=
  tfl + G1 G2 G3 G4 G5 in H1;
  tryfold G6 in H1;
  tryfold G6.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1)
  :=
  tfl + G1 G2 G3 G4 G5 G6 in H1;
  tryfold G7 in H1;
  tryfold G7.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1)
  :=
  tfl + G1 G2 G3 G4 G5 G6 G7 in H1;
  tryfold G8 in H1;
  tryfold G8.






Tactic Notation "tfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  tryfold G1 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 in H1 H2;
  tryfold G2 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 G2 in H1 H2;
  tryfold G3 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 G2 G3 in H1 H2;
  tryfold G4 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 G2 G3 G4 in H1 H2;
  tryfold G5 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 G2 G3 G4 G5 in H1 H2;
  tryfold G6 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 G2 G3 G4 G5 G6 in H1 H2;
  tryfold G7 in H1, H2.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  tryfold G8 in H1, H2.






Tactic Notation "tfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2)
  :=
  tryfold G1 in H1, H2;
  tryfold G1.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 in H1 H2;
  tryfold G2 in H1, H2;
  tryfold G2.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 G2 in H1 H2;
  tryfold G3 in H1, H2;
  tryfold G3.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 G2 G3 in H1 H2;
  tryfold G4 in H1, H2;
  tryfold G4.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 G2 G3 G4 in H1 H2;
  tryfold G5 in H1, H2;
  tryfold G5.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 G2 G3 G4 G5 in H1 H2;
  tryfold G6 in H1, H2;
  tryfold G6.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 G2 G3 G4 G5 G6 in H1 H2;
  tryfold G7 in H1, H2;
  tryfold G7.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2;
  tryfold G8 in H1, H2;
  tryfold G8.






Tactic Notation "tfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tryfold G1 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 in H1 H2 H3;
  tryfold G2 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 G2 in H1 H2 H3;
  tryfold G3 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 G2 G3 in H1 H2 H3;
  tryfold G4 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 G2 G3 G4 in H1 H2 H3;
  tryfold G5 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 G2 G3 G4 G5 in H1 H2 H3;
  tryfold G6 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  tryfold G7 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  tryfold G8 in H1, H2, H3.






Tactic Notation "tfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tryfold G1 in H1, H2, H3;
  tryfold G1.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 in H1 H2 H3;
  tryfold G2 in H1, H2, H3;
  tryfold G2.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 G2 in H1 H2 H3;
  tryfold G3 in H1, H2, H3;
  tryfold G3.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 G2 G3 in H1 H2 H3;
  tryfold G4 in H1, H2, H3;
  tryfold G4.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 G2 G3 G4 in H1 H2 H3;
  tryfold G5 in H1, H2, H3;
  tryfold G5.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 G2 G3 G4 G5 in H1 H2 H3;
  tryfold G6 in H1, H2, H3;
  tryfold G6.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 G2 G3 G4 G5 G6 in H1 H2 H3;
  tryfold G7 in H1, H2, H3;
  tryfold G7.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3;
  tryfold G8 in H1, H2, H3;
  tryfold G8.






Tactic Notation "tfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tryfold G1 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 in H1 H2 H3 H4;
  tryfold G2 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 G2 in H1 H2 H3 H4;
  tryfold G3 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 G2 G3 in H1 H2 H3 H4;
  tryfold G4 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 G2 G3 G4 in H1 H2 H3 H4;
  tryfold G5 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  tryfold G6 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  tryfold G7 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  tryfold G8 in H1, H2, H3, H4.






Tactic Notation "tfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tryfold G1 in H1, H2, H3, H4;
  tryfold G1.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 in H1 H2 H3 H4;
  tryfold G2 in H1, H2, H3, H4;
  tryfold G2.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 G2 in H1 H2 H3 H4;
  tryfold G3 in H1, H2, H3, H4;
  tryfold G3.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 G2 G3 in H1 H2 H3 H4;
  tryfold G4 in H1, H2, H3, H4;
  tryfold G4.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 G2 G3 G4 in H1 H2 H3 H4;
  tryfold G5 in H1, H2, H3, H4;
  tryfold G5.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 G2 G3 G4 G5 in H1 H2 H3 H4;
  tryfold G6 in H1, H2, H3, H4;
  tryfold G6.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4;
  tryfold G7 in H1, H2, H3, H4;
  tryfold G7.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4;
  tryfold G8 in H1, H2, H3, H4;
  tryfold G8.






Tactic Notation "tfl"
  "-"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tryfold G1 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 in H1 H2 H3 H4 H5;
  tryfold G2 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 G2 in H1 H2 H3 H4 H5;
  tryfold G3 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 G2 G3 in H1 H2 H3 H4 H5;
  tryfold G4 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  tryfold G5 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  tryfold G6 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  tryfold G7 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  tryfold G8 in H1, H2, H3, H4, H5.






Tactic Notation "tfl"
  "+"   smart_global(G1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tryfold G1 in H1, H2, H3, H4, H5;
  tryfold G1.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 in H1 H2 H3 H4 H5;
  tryfold G2 in H1, H2, H3, H4, H5;
  tryfold G2.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 G2 in H1 H2 H3 H4 H5;
  tryfold G3 in H1, H2, H3, H4, H5;
  tryfold G3.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 G2 G3 in H1 H2 H3 H4 H5;
  tryfold G4 in H1, H2, H3, H4, H5;
  tryfold G4.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 G2 G3 G4 in H1 H2 H3 H4 H5;
  tryfold G5 in H1, H2, H3, H4, H5;
  tryfold G5.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 G2 G3 G4 G5 in H1 H2 H3 H4 H5;
  tryfold G6 in H1, H2, H3, H4, H5;
  tryfold G6.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 G2 G3 G4 G5 G6 in H1 H2 H3 H4 H5;
  tryfold G7 in H1, H2, H3, H4, H5;
  tryfold G7.

Tactic Notation "tfl"
  "+"   smart_global(G1) smart_global(G2) smart_global(G3) smart_global(G4)
        smart_global(G5) smart_global(G6) smart_global(G7) smart_global(G8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + G1 G2 G3 G4 G5 G6 G7 in H1 H2 H3 H4 H5;
  tryfold G8 in H1, H2, H3, H4, H5;
  tryfold G8.