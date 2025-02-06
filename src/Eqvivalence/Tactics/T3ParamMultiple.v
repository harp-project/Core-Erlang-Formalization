(** STRUCTURE:
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



(** DOCUMENTATION:

* itr   -->   intros
              _
              - [ident]:1-20



* exi   -->   exists
              - [constr]:1-10

* eei   -->   eexists



* rev   -->   revert
              - [ident]:1-10


* gen   -->   generalize dependent
              - [ident]:1-10



*       ==>   clear_refl (Clears all reflexive hypothesis)

* clr   -->   clear
              - [ident]:1-10
              + [ident]:1-10



* sym   -->   symmetry
              _
              *
              - [ident]:1-10
              + [ident]:1-10
              ~ constr
              ~ constr - ident


* smp   -->   simpl
              _
              *
              - [ident]:1-10
              + [ident]:1-10


* sbn   -->   cbn
              _
              *
              - [ident]:1-10
              + [ident]:1-10



* fld   -->   fold
              - [constr]:1-8
              - [constr]:1-8 in *
              - [constr]:1-8 in [hyp]:1-5
              + [constr]:1-8 in [hyp]:1-5


* ufl   -->   unfold
              - [constr]:1-8
              - [constr]:1-8 in *
              - [constr]:1-8 in [hyp]:1-5
              + [constr]:1-8 in [hyp]:1-5


* rfl   -->   refold
              - [constr]:1-8
              - [constr]:1-8 in *
              - [constr]:1-8 in [hyp]:1-5
              + [constr]:1-8 in [hyp]:1-5


* tfl   -->   tryfold
              - [constr]:1-8
              - [constr]:1-8 in *
              - [constr]:1-8 in [hyp]:1-5
              + [constr]:1-8 in [hyp]:1-5
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// INTROS /////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "itr"
  :=
  intros.

Tactic Notation "itr"
  "-"   ident(I1)
  :=
  intros I1.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2)
  :=
  intros I1 I2.

Tactic Notation "itr"
  "-" ident(I1) ident(I2) ident(I3)
  :=
  intros I1 I2 I3.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  intros I1 I2 I3 I4.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  intros I1 I2 I3 I4 I5.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  intros I1 I2 I3 I4 I5 I6.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  intros I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18) ident(I19)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19.

Tactic Notation "itr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18) ident(I19) ident(I20)
  :=
  intros I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20.












(*
////////////////////////////////////////////////////////////////////////////////
//// EXISTS ////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "exi"
  "-"   constr(C1)
  :=
  exists C1.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2)
  :=
  exi - C1;
  exists C2.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  exi - C1 C2;
  exists C3.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  exi - C1 C2 C3;
  exists C4.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  exi - C1 C2 C3 C4;
  exists C5.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  exi - C1 C2 C3 C4 C5;
  exists C6.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  exi - C1 C2 C3 C4 C5 C6;
  exists C7.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  exi - C1 C2 C3 C4 C5 C6 C7;
  exists C8.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  exi - C1 C2 C3 C4 C5 C6 C7 C8;
  exists C9.

Tactic Notation "exi"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  exi - C1 C2 C3 C4 C5 C6 C7 C8 C9;
  exists C10.






Ltac eei := eexists.












(*
////////////////////////////////////////////////////////////////////////////////
//// REVERT ////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Tactic Notation "rev"
  "-"   ident(I1)
  :=
  revert I1.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2)
  :=
  rev - I1;
  revert I2.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3)
  :=
  rev - I1 I2;
  revert I3.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  rev - I1 I2 I3;
  revert I4.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  rev - I1 I2 I3 I4;
  revert I5.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  rev - I1 I2 I3 I4 I5;
  revert I6.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  rev - I1 I2 I3 I4 I5 I6;
  revert I7.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  rev - I1 I2 I3 I4 I5 I6 I7;
  revert I8.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  rev - I1 I2 I3 I4 I5 I6 I7 I8;
  revert I9.

Tactic Notation "rev"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  rev - I1 I2 I3 I4 I5 I6 I7 I8 I9;
  revert I10.












(*
////////////////////////////////////////////////////////////////////////////////
//// GENERALIZE_DEPENDENT //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "gen"
  "-"   ident(I1)
  :=
  generalize dependent I1.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2)
  :=
  gen - I1;
  generalize dependent I2.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3)
  :=
  gen - I1 I2;
  generalize dependent I3.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  gen - I1 I2 I3;
  generalize dependent I4.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  gen - I1 I2 I3 I4;
  generalize dependent I5.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  gen - I1 I2 I3 I4 I5;
  generalize dependent I6.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  gen - I1 I2 I3 I4 I5 I6;
  generalize dependent I7.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  gen - I1 I2 I3 I4 I5 I6 I7;
  generalize dependent I8.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  gen - I1 I2 I3 I4 I5 I6 I7 I8;
  generalize dependent I9.

Tactic Notation "gen"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  gen - I1 I2 I3 I4 I5 I6 I7 I8 I9;
  generalize dependent I10.












(*
////////////////////////////////////////////////////////////////////////////////
//// CLEAR /////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Ltac clear_refl :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.






Tactic Notation "clr"
  "-"   ident(I1)
  :=
  clear I1;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2)
  :=
  clear I1 I2;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3)
  :=
  clear I1 I2 I3;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear I1 I2 I3 I4;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear I1 I2 I3 I4;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)  ident(I5)
  :=
  clear I1 I2 I3 I4 I5;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  clear I1 I2 I3 I4 I5 I6;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  clear I1 I2 I3 I4 I5 I6 I7;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18) ident(I19)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19;
  clear_refl.

Tactic Notation "clr"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18) ident(I19) ident(I20)
  :=
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19 I20;
  clear_refl.






Tactic Notation "clr"
  "+"   ident(I1)
  :=
  clear - I1;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2)
  :=
  clear - I1 I2;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3)
  :=
  clear - I1 I2 I3;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear - I1 I2 I3 I4;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  clear - I1 I2 I3 I4;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4)  ident(I5)
  :=
  clear - I1 I2 I3 I4 I5;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  clear - I1 I2 I3 I4 I5 I6;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18) ident(I19)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10 I11 I12 I13 I14 I15 I16 I17 I18 I19;
  clear_refl.

Tactic Notation "clr"
  "+"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
        ident(I11) ident(I12) ident(I13) ident(I14) ident(I15)
        ident(I16) ident(I17) ident(I18) ident(I19) ident(I20)
  :=
  clear - I1 I2 I3 I4 I5 I6 I7 I8 I9 I10
          I11 I12 I13 I14 I15 I16 I17 I18 I19 I20;
  clear_refl.












(*
////////////////////////////////////////////////////////////////////////////////
//// SYMMETRY //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "sym"
  :=
  symmetry.

Tactic Notation "sym"
  "*"
  :=
  symmetry in *.






Tactic Notation "sym"
  "-"   hyp(H1)
  :=
  symmetry in H1.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2)
  :=
  clear_refl;
  symmetry in H1, H2.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  symmetry in H1, H2, H3.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  symmetry in H1, H2, H3, H4.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  symmetry in H1, H2, H3, H4, H5.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  symmetry in H1, H2, H3, H4, H5, H6.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "sym"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.






Tactic Notation "sym"
  "+"   hyp(H1)
  :=
  symmetry in H1 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2)
  :=
  symmetry in H1, H2 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  :=
  symmetry in H1, H2, H3 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  symmetry in H1, H2, H3, H4 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  symmetry in H1, H2, H3, H4, H5 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  symmetry in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "sym"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  symmetry in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.












(*
////////////////////////////////////////////////////////////////////////////////
//// SIMPLIFY //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "smp"
  :=
  simpl.

Tactic Notation "smp"
  "*"
  :=
  simpl in *.






Tactic Notation "smp"
  "-"   hyp(H1)
  :=
  simpl in H1.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2)
  :=
  clear_refl;
  simpl in H1, H2.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  simpl in H1, H2, H3.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  simpl in H1, H2, H3, H4.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  simpl in H1, H2, H3, H4, H5.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  simpl in H1, H2, H3, H4, H5, H6.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "smp"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.






Tactic Notation "smp"
  "+"   hyp(H1)
  :=
  simpl in H1 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2)
  :=
  simpl in H1, H2 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  :=
  simpl in H1, H2, H3 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  simpl in H1, H2, H3, H4 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  simpl in H1, H2, H3, H4, H5 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  simpl in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "smp"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.






Tactic Notation "smp"
  "~"   constr(C)
  :=
  simpl C.

Tactic Notation "smp"
  "~"   constr(C)
  "-"   hyp(H1)
  :=
  simpl C in H1.












(*
////////////////////////////////////////////////////////////////////////////////
//// CBN ///////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "sbn"
  :=
  cbn.

Tactic Notation "sbn"
  "*"
  :=
  cbn in *.






Tactic Notation "sbn"
  "-"   hyp(H1)
  :=
  cbn in H1.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2)
  :=
  clear_refl;
  cbn in H1, H2.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  cbn in H1, H2, H3.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  cbn in H1, H2, H3, H4.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  cbn in H1, H2, H3, H4, H5.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  cbn in H1, H2, H3, H4, H5, H6.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "sbn"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.






Tactic Notation "sbn"
  "+"   hyp(H1)
  :=
  cbn in H1 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2)
  :=
  cbn in H1, H2 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  :=
  cbn in H1, H2, H3 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  cbn in H1, H2, H3, H4 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  cbn in H1, H2, H3, H4, H5 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  cbn in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "sbn"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  cbn in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.












(*
////////////////////////////////////////////////////////////////////////////////
//// FOLD //////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "fld"
  "-"   constr(C1)
  :=
  fold C1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  :=
  fld - C1;
  fold C2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  fld - C1 C2;
  fold C3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  fld - C1 C2 C3;
  fold C4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  :=
  fld - C1 C2 C3 C4;
  fold C5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  :=
  fld - C1 C2 C3 C4 C5;
  fold C6.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  :=
  fld - C1 C2 C3 C4 C5 C6;
  fold C7.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  :=
  fld - C1 C2 C3 C4 C5 C6 C7;
  fold C8.






Tactic Notation "fld"
  "-"   constr(C1)
  "in"  "*"
  :=
  fold C1 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  fld - C1 in *;
  fold C2 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  fld - C1 C2 in *;
  fold C3 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  fld - C1 C2 C3 in *;
  fold C4 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  "*"
  :=
  fld - C1 C2 C3 C4 in *;
  fold C5 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  "*"
  :=
  fld - C1 C2 C3 C4 C5 in *;
  fold C6 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  "*"
  :=
  fld - C1 C2 C3 C4 C5 C6 in *;
  fold C7 in *.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  fld - C1 C2 C3 C4 C5 C6 C7 in *;
  fold C8 in *.






Tactic Notation "fld"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  fold C1 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  fld - C1 in H1;
  fold C2 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  fld - C1 C2 in H1;
  fold C3 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  fld - C1 C2 C3 in H1;
  fold C4 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  fld - C1 C2 C3 C4 in H1;
  fold C5 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  fld - C1 C2 C3 C4 C5 in H1;
  fold C6 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  fld - C1 C2 C3 C4 C5 C6 in H1;
  fold C7 in H1.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  fld - C1 C2 C3 C4 C5 C6 C7 in H1;
  fold C8 in H1.






Tactic Notation "fld"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  fold C1 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  fld + C1 in H1;
  fold C2 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  fld + C1 C2 in H1;
  fold C3 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  fld + C1 C2 C3 in H1;
  fold C4 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  fld + C1 C2 C3 C4 in H1;
  fold C5 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  fld + C1 C2 C3 C4 C5 in H1;
  fold C6 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  fld + C1 C2 C3 C4 C5 C6 in H1;
  fold C7 in H1 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  fld + C1 C2 C3 C4 C5 C6 C7 in H1;
  fold C8 in H1 |- *.






Tactic Notation "fld"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  fold C1 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 in H1 H2;
  fold C2 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 C2 in H1 H2;
  fold C3 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 C2 C3 in H1 H2;
  fold C4 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 C2 C3 C4 in H1 H2;
  fold C5 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 C2 C3 C4 C5 in H1 H2;
  fold C6 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 C2 C3 C4 C5 C6 in H1 H2;
  fold C7 in H1, H2.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  fld - C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  fold C8 in H1, H2.






Tactic Notation "fld"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  fold C1 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 in H1 H2;
  fold C2 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 C2 in H1 H2;
  fold C3 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 C2 C3 in H1 H2;
  fold C4 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 C2 C3 C4 in H1 H2;
  fold C5 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 C2 C3 C4 C5 in H1 H2;
  fold C6 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 C2 C3 C4 C5 C6 in H1 H2;
  fold C7 in H1, H2 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  fld + C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  fold C8 in H1, H2 |- *.






Tactic Notation "fld"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fold C1 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 in H1 H2 H3;
  fold C2 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 C2 in H1 H2 H3;
  fold C3 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 C2 C3 in H1 H2 H3;
  fold C4 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 C2 C3 C4 in H1 H2 H3;
  fold C5 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 C2 C3 C4 C5 in H1 H2 H3;
  fold C6 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  fold C7 in H1, H2, H3.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  fold C8 in H1, H2, H3.






Tactic Notation "fld"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fold C1 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 in H1 H2 H3;
  fold C2 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 C2 in H1 H2 H3;
  fold C3 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 C2 C3 in H1 H2 H3;
  fold C4 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 C2 C3 C4 in H1 H2 H3;
  fold C5 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 C2 C3 C4 C5 in H1 H2 H3;
  fold C6 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  fold C7 in H1, H2, H3 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  fld + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  fold C8 in H1, H2, H3 |- *.






Tactic Notation "fld"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fold C1 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 in H1 H2 H3 H4;
  fold C2 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 C2 in H1 H2 H3 H4;
  fold C3 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 C2 C3 in H1 H2 H3 H4;
  fold C4 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 C2 C3 C4 in H1 H2 H3 H4;
  fold C5 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  fold C6 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  fold C7 in H1, H2, H3, H4.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  fold C8 in H1, H2, H3, H4.






Tactic Notation "fld"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fold C1 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 in H1 H2 H3 H4;
  fold C2 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 C2 in H1 H2 H3 H4;
  fold C3 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 C2 C3 in H1 H2 H3 H4;
  fold C4 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 C2 C3 C4 in H1 H2 H3 H4;
  fold C5 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  fold C6 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  fold C7 in H1, H2, H3, H4 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  fld + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  fold C8 in H1, H2, H3, H4 |- *.






Tactic Notation "fld"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fold C1 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 in H1 H2 H3 H4 H5;
  fold C2 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 C2 in H1 H2 H3 H4 H5;
  fold C3 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 C2 C3 in H1 H2 H3 H4 H5;
  fold C4 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  fold C5 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  fold C6 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  fold C7 in H1, H2, H3, H4, H5.

Tactic Notation "fld"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  fold C8 in H1, H2, H3, H4, H5.






Tactic Notation "fld"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fold C1 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 in H1 H2 H3 H4 H5;
  fold C2 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 C2 in H1 H2 H3 H4 H5;
  fold C3 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 C2 C3 in H1 H2 H3 H4 H5;
  fold C4 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  fold C5 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  fold C6 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  fold C7 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "fld"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  fld + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  fold C8 in H1, H2, H3, H4, H5 |- *.












(*
////////////////////////////////////////////////////////////////////////////////
//// UNFOLD ////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "ufl"
  "-"   constr(C1)
  :=
  unfold C1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  :=
  ufl - C1;
  unfold C2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  ufl - C1 C2;
  unfold C3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  ufl - C1 C2 C3;
  unfold C4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  :=
  ufl - C1 C2 C3 C4;
  unfold C5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  :=
  ufl - C1 C2 C3 C4 C5;
  unfold C6.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  :=
  ufl - C1 C2 C3 C4 C5 C6;
  unfold C7.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7;
  unfold C8.






Tactic Notation "ufl"
  "-"   constr(C1)
  "in"  "*"
  :=
  unfold C1 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  ufl - C1 in *;
  unfold C2 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  ufl - C1 C2 in *;
  unfold C3 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  ufl - C1 C2 C3 in *;
  unfold C4 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  "*"
  :=
  ufl - C1 C2 C3 C4 in *;
  unfold C5 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  "*"
  :=
  ufl - C1 C2 C3 C4 C5 in *;
  unfold C6 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  "*"
  :=
  ufl - C1 C2 C3 C4 C5 C6 in *;
  unfold C7 in *.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7 in *;
  unfold C8 in *.






Tactic Notation "ufl"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  unfold C1 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  ufl - C1 in H1;
  unfold C2 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  ufl - C1 C2 in H1;
  unfold C3 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  ufl - C1 C2 C3 in H1;
  unfold C4 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  ufl - C1 C2 C3 C4 in H1;
  unfold C5 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  ufl - C1 C2 C3 C4 C5 in H1;
  unfold C6 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  ufl - C1 C2 C3 C4 C5 C6 in H1;
  unfold C7 in H1.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7 in H1;
  unfold C8 in H1.






Tactic Notation "ufl"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  unfold C1 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  ufl + C1 in H1;
  unfold C2 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  ufl + C1 C2 in H1;
  unfold C3 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  ufl + C1 C2 C3 in H1;
  unfold C4 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  ufl + C1 C2 C3 C4 in H1;
  unfold C5 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  ufl + C1 C2 C3 C4 C5 in H1;
  unfold C6 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  ufl + C1 C2 C3 C4 C5 C6 in H1;
  unfold C7 in H1 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  ufl + C1 C2 C3 C4 C5 C6 C7 in H1;
  unfold C8 in H1 |- *.






Tactic Notation "ufl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  unfold C1 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 in H1 H2;
  unfold C2 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 C2 in H1 H2;
  unfold C3 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 C2 C3 in H1 H2;
  unfold C4 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 C2 C3 C4 in H1 H2;
  unfold C5 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 C2 C3 C4 C5 in H1 H2;
  unfold C6 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 C2 C3 C4 C5 C6 in H1 H2;
  unfold C7 in H1, H2.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  unfold C8 in H1, H2.






Tactic Notation "ufl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  unfold C1 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 in H1 H2;
  unfold C2 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 C2 in H1 H2;
  unfold C3 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 C2 C3 in H1 H2;
  unfold C4 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 C2 C3 C4 in H1 H2;
  unfold C5 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 C2 C3 C4 C5 in H1 H2;
  unfold C6 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 C2 C3 C4 C5 C6 in H1 H2;
  unfold C7 in H1, H2 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  ufl + C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  unfold C8 in H1, H2 |- *.






Tactic Notation "ufl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  unfold C1 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 in H1 H2 H3;
  unfold C2 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 C2 in H1 H2 H3;
  unfold C3 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 C2 C3 in H1 H2 H3;
  unfold C4 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 C2 C3 C4 in H1 H2 H3;
  unfold C5 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 C2 C3 C4 C5 in H1 H2 H3;
  unfold C6 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  unfold C7 in H1, H2, H3.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  unfold C8 in H1, H2, H3.






Tactic Notation "ufl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  unfold C1 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 in H1 H2 H3;
  unfold C2 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 C2 in H1 H2 H3;
  unfold C3 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 C2 C3 in H1 H2 H3;
  unfold C4 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 C2 C3 C4 in H1 H2 H3;
  unfold C5 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 C2 C3 C4 C5 in H1 H2 H3;
  unfold C6 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  unfold C7 in H1, H2, H3 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  ufl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  unfold C8 in H1, H2, H3 |- *.






Tactic Notation "ufl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  unfold C1 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 in H1 H2 H3 H4;
  unfold C2 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 C2 in H1 H2 H3 H4;
  unfold C3 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 C2 C3 in H1 H2 H3 H4;
  unfold C4 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 C2 C3 C4 in H1 H2 H3 H4;
  unfold C5 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  unfold C6 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  unfold C7 in H1, H2, H3, H4.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  unfold C8 in H1, H2, H3, H4.






Tactic Notation "ufl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  unfold C1 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 in H1 H2 H3 H4;
  unfold C2 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 C2 in H1 H2 H3 H4;
  unfold C3 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 C2 C3 in H1 H2 H3 H4;
  unfold C4 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 C2 C3 C4 in H1 H2 H3 H4;
  unfold C5 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  unfold C6 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  unfold C7 in H1, H2, H3, H4 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ufl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  unfold C8 in H1, H2, H3, H4 |- *.






Tactic Notation "ufl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  unfold C1 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 in H1 H2 H3 H4 H5;
  unfold C2 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 C2 in H1 H2 H3 H4 H5;
  unfold C3 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 C2 C3 in H1 H2 H3 H4 H5;
  unfold C4 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  unfold C5 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  unfold C6 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  unfold C7 in H1, H2, H3, H4, H5.

Tactic Notation "ufl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  unfold C8 in H1, H2, H3, H4, H5.






Tactic Notation "ufl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  unfold C1 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 in H1 H2 H3 H4 H5;
  unfold C2 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 C2 in H1 H2 H3 H4 H5;
  unfold C3 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 C2 C3 in H1 H2 H3 H4 H5;
  unfold C4 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  unfold C5 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  unfold C6 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  unfold C7 in H1, H2, H3, H4, H5 |- *.

Tactic Notation "ufl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ufl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  unfold C8 in H1, H2, H3, H4, H5 |- *.












(*
////////////////////////////////////////////////////////////////////////////////
//// REFOLD ////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "refold"
        constr(C)
  :=
  unfold C;
  fold C.

Tactic Notation "refold"
        constr(C)
  "in"  "*"
  :=
  unfold C in *;
  fold C in *.

Tactic Notation "refold"
        constr(C)
  "in"  hyp(H1)
  :=
  unfold C in H1;
  fold C in H1.

Tactic Notation "refold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2)
  :=
  unfold C in H1, H2;
  fold C in H1, H2.

Tactic Notation "refold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3)
  :=
  unfold C in H1, H2, H3;
  fold C in H1, H2, H3.

Tactic Notation "refold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4)
  :=
  unfold C in H1, H2, H3, H4;
  fold C in H1, H2, H3, H4.

Tactic Notation "refold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) "," hyp(H5)
  :=
  unfold C in H1, H2, H3, H4, H5;
  fold C in H1, H2, H3, H4, H5.






Tactic Notation "rfl"
  "-"   constr(C1)
  :=
  refold C1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  :=
  rfl - C1;
  refold C2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rfl - C1 C2;
  refold C3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rfl - C1 C2 C3;
  refold C4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
      constr(C5)
  :=
  rfl - C1 C2 C3 C4;
  refold C5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  :=
  rfl - C1 C2 C3 C4 C5;
  refold C6.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  :=
  rfl - C1 C2 C3 C4 C5 C6;
  refold C7.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7;
  refold C8.






Tactic Notation "rfl"
  "-"   constr(C1)
  "in"  "*"
  :=
  refold C1 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  rfl - C1 in *;
  refold C2 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  rfl - C1 C2 in *;
  refold C3 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  rfl - C1 C2 C3 in *;
  refold C4 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  "*"
  :=
  rfl - C1 C2 C3 C4 in *;
  refold C5 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  "*"
  :=
  rfl - C1 C2 C3 C4 C5 in *;
  refold C6 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  "*"
  :=
  rfl - C1 C2 C3 C4 C5 C6 in *;
  refold C7 in *.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7 in *;
  refold C8 in *.






Tactic Notation "rfl"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  refold C1 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rfl - C1 in H1;
  refold C2 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rfl - C1 C2 in H1;
  refold C3 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rfl - C1 C2 C3 in H1;
  refold C4 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  rfl - C1 C2 C3 C4 in H1;
  refold C5 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  rfl - C1 C2 C3 C4 C5 in H1;
  refold C6 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rfl - C1 C2 C3 C4 C5 C6 in H1;
  refold C7 in H1.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7 in H1;
  refold C8 in H1.






Tactic Notation "rfl"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  refold C1 in H1;
  refold C1.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rfl + C1 in H1;
  refold C2 in H1;
  refold C2.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rfl + C1 C2 in H1;
  refold C3 in H1;
  refold C3.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rfl + C1 C2 C3 in H1;
  refold C4 in H1;
  refold C4.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  rfl + C1 C2 C3 C4 in H1;
  refold C5 in H1;
  refold C5.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  rfl + C1 C2 C3 C4 C5 in H1;
  refold C6 in H1;
  refold C6.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rfl + C1 C2 C3 C4 C5 C6 in H1;
  refold C7 in H1;
  refold C7.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rfl + C1 C2 C3 C4 C5 C6 C7 in H1;
  refold C8 in H1;
  refold C8.






Tactic Notation "rfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  refold C1 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 in H1 H2;
  refold C2 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 C2 in H1 H2;
  refold C3 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 C2 C3 in H1 H2;
  refold C4 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 C2 C3 C4 in H1 H2;
  refold C5 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 C2 C3 C4 C5 in H1 H2;
  refold C6 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 C2 C3 C4 C5 C6 in H1 H2;
  refold C7 in H1, H2.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  refold C8 in H1, H2.






Tactic Notation "rfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  refold C1 in H1, H2;
  refold C1.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 in H1 H2;
  refold C2 in H1, H2;
  refold C2.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 C2 in H1 H2;
  refold C3 in H1, H2;
  refold C3.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 C2 C3 in H1 H2;
  refold C4 in H1, H2;
  refold C4.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 C2 C3 C4 in H1 H2;
  refold C5 in H1, H2;
  refold C5.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 C2 C3 C4 C5 in H1 H2;
  refold C6 in H1, H2;
  refold C6.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 C2 C3 C4 C5 C6 in H1 H2;
  refold C7 in H1, H2;
  refold C7.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  refold C8 in H1, H2;
  refold C8.






Tactic Notation "rfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  refold C1 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 in H1 H2 H3;
  refold C2 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 C2 in H1 H2 H3;
  refold C3 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 C2 C3 in H1 H2 H3;
  refold C4 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 C2 C3 C4 in H1 H2 H3;
  refold C5 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 C2 C3 C4 C5 in H1 H2 H3;
  refold C6 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  refold C7 in H1, H2, H3.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  refold C8 in H1, H2, H3.






Tactic Notation "rfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  refold C1 in H1, H2, H3;
  refold C1.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 in H1 H2 H3;
  refold C2 in H1, H2, H3;
  refold C2.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 C2 in H1 H2 H3;
  refold C3 in H1, H2, H3;
  refold C3.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 C2 C3 in H1 H2 H3;
  refold C4 in H1, H2, H3;
  refold C4.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 C2 C3 C4 in H1 H2 H3;
  refold C5 in H1, H2, H3;
  refold C5.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 C2 C3 C4 C5 in H1 H2 H3;
  refold C6 in H1, H2, H3;
  refold C6.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  refold C7 in H1, H2, H3;
  refold C7.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  refold C8 in H1, H2, H3;
  refold C8.






Tactic Notation "rfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  refold C1 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 in H1 H2 H3 H4;
  refold C2 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 C2 in H1 H2 H3 H4;
  refold C3 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 C2 C3 in H1 H2 H3 H4;
  refold C4 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 C2 C3 C4 in H1 H2 H3 H4;
  refold C5 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  refold C6 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  refold C7 in H1, H2, H3, H4.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  refold C8 in H1, H2, H3, H4.






Tactic Notation "rfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  refold C1 in H1, H2, H3, H4;
  refold C1.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 in H1 H2 H3 H4;
  refold C2 in H1, H2, H3, H4;
  refold C2.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 C2 in H1 H2 H3 H4;
  refold C3 in H1, H2, H3, H4;
  refold C3.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 C2 C3 in H1 H2 H3 H4;
  refold C4 in H1, H2, H3, H4;
  refold C4.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 C2 C3 C4 in H1 H2 H3 H4;
  refold C5 in H1, H2, H3, H4;
  refold C5.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  refold C6 in H1, H2, H3, H4;
  refold C6.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  refold C7 in H1, H2, H3, H4;
  refold C7.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  refold C8 in H1, H2, H3, H4;
  refold C8.






Tactic Notation "rfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  refold C1 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 in H1 H2 H3 H4 H5;
  refold C2 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 C2 in H1 H2 H3 H4 H5;
  refold C3 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 C2 C3 in H1 H2 H3 H4 H5;
  refold C4 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  refold C5 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  refold C6 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  refold C7 in H1, H2, H3, H4, H5.

Tactic Notation "rfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  refold C8 in H1, H2, H3, H4, H5.






Tactic Notation "rfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  refold C1 in H1, H2, H3, H4, H5;
  refold C1.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 in H1 H2 H3 H4 H5;
  refold C2 in H1, H2, H3, H4, H5;
  refold C2.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 C2 in H1 H2 H3 H4 H5;
  refold C3 in H1, H2, H3, H4, H5;
  refold C3.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 C2 C3 in H1 H2 H3 H4 H5;
  refold C4 in H1, H2, H3, H4, H5;
  refold C4.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  refold C5 in H1, H2, H3, H4, H5;
  refold C5.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  refold C6 in H1, H2, H3, H4, H5;
  refold C6.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  refold C7 in H1, H2, H3, H4, H5;
  refold C7.

Tactic Notation "rfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  refold C8 in H1, H2, H3, H4, H5;
  refold C8.












(*
////////////////////////////////////////////////////////////////////////////////
//// TRYFOLD ///////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "tryfold"
        constr(C)
  :=
  try unfold C;
  fold C.

Tactic Notation "tryfold"
        constr(C)
  "in"  "*"
  :=
  try unfold C in *;
  fold C in *.

Tactic Notation "tryfold"
        constr(C)
  "in"  hyp(H1)
  :=
  try unfold C in H1;
  fold C in H1.

Tactic Notation "tryfold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2)
  :=
  try unfold C in H1;
  fold C in H1;
  try unfold C in H2;
  fold C in H2.

Tactic Notation "tryfold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3)
  :=
  try unfold C in H1;
  fold C in H1;
  try unfold C in H2;
  fold C in H2;
  try unfold C in H3;
  fold C in H3.

Tactic Notation "tryfold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4)
  :=
  try unfold C in H1;
  fold C in H1;
  try unfold C in H2;
  fold C in H2;
  try unfold C in H3;
  fold C in H3;
  try unfold C in H4;
  fold C in H4.

Tactic Notation "tryfold"
        constr(C)
  "in"  hyp(H1) "," hyp(H2) "," hyp(H3) "," hyp(H4) "," hyp(H5)
  :=
  try unfold C in H1;
  fold C in H1;
  try unfold C in H2;
  fold C in H2;
  try unfold C in H3;
  fold C in H3;
  try unfold C in H4;
  fold C in H4;
  try unfold C in H5;
  fold C in H5.






Tactic Notation "tfl"
  "-"   constr(C1)
  :=
  tryfold C1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  :=
  tfl - C1;
  tryfold C2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  tfl - C1 C2;
  tryfold C3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  tfl - C1 C2 C3;
  tryfold C4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  :=
  tfl - C1 C2 C3 C4;
  tryfold C5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  :=
  tfl - C1 C2 C3 C4 C5;
  tryfold C6.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  :=
  tfl - C1 C2 C3 C4 C5 C6;
  tryfold C7.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7;
  tryfold C8.






Tactic Notation "tfl"
  "-"   constr(C1)
  "in"  "*"
  :=
  tryfold C1 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  tfl - C1 in *;
  tryfold C2 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  tfl - C1 C2 in *;
  tryfold C3 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  tfl - C1 C2 C3 in *;
  tryfold C4 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  "*"
  :=
  tfl - C1 C2 C3 C4 in *;
  tryfold C5 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  "*"
  :=
  tfl - C1 C2 C3 C4 C5 in *;
  tryfold C6 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  "*"
  :=
  tfl - C1 C2 C3 C4 C5 C6 in *;
  tryfold C7 in *.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7 in *;
  tryfold C8 in *.






Tactic Notation "tfl"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  tryfold C1 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  tfl - C1 in H1;
  tryfold C2 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  tfl - C1 C2 in H1;
  tryfold C3 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  tfl - C1 C2 C3 in H1;
  tryfold C4 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  tfl - C1 C2 C3 C4 in H1;
  tryfold C5 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  tfl - C1 C2 C3 C4 C5 in H1;
  tryfold C6 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  tfl - C1 C2 C3 C4 C5 C6 in H1;
  tryfold C7 in H1.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7 in H1;
  tryfold C8 in H1.






Tactic Notation "tfl"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  tryfold C1 in H1;
  tryfold C1.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  tfl + C1 in H1;
  tryfold C2 in H1;
  tryfold C2.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  tfl + C1 C2 in H1;
  tryfold C3 in H1;
  tryfold C3.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  tfl + C1 C2 C3 in H1;
  tryfold C4 in H1;
  tryfold C4.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1)
  :=
  tfl + C1 C2 C3 C4 in H1;
  tryfold C5 in H1;
  tryfold C5.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1)
  :=
  tfl + C1 C2 C3 C4 C5 in H1;
  tryfold C6 in H1;
  tryfold C6.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  tfl + C1 C2 C3 C4 C5 C6 in H1;
  tryfold C7 in H1;
  tryfold C7.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  tfl + C1 C2 C3 C4 C5 C6 C7 in H1;
  tryfold C8 in H1;
  tryfold C8.






Tactic Notation "tfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  tryfold C1 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 in H1 H2;
  tryfold C2 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 C2 in H1 H2;
  tryfold C3 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 C2 C3 in H1 H2;
  tryfold C4 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 C2 C3 C4 in H1 H2;
  tryfold C5 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 C2 C3 C4 C5 in H1 H2;
  tryfold C6 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 C2 C3 C4 C5 C6 in H1 H2;
  tryfold C7 in H1, H2.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  tryfold C8 in H1, H2.






Tactic Notation "tfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  tryfold C1 in H1, H2;
  tryfold C1.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 in H1 H2;
  tryfold C2 in H1, H2;
  tryfold C2.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 C2 in H1 H2;
  tryfold C3 in H1, H2;
  tryfold C3.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 C2 C3 in H1 H2;
  tryfold C4 in H1, H2;
  tryfold C4.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 C2 C3 C4 in H1 H2;
  tryfold C5 in H1, H2;
  tryfold C5.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 C2 C3 C4 C5 in H1 H2;
  tryfold C6 in H1, H2;
  tryfold C6.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 C2 C3 C4 C5 C6 in H1 H2;
  tryfold C7 in H1, H2;
  tryfold C7.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  tfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2;
  tryfold C8 in H1, H2;
  tryfold C8.






Tactic Notation "tfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tryfold C1 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 in H1 H2 H3;
  tryfold C2 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 C2 in H1 H2 H3;
  tryfold C3 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 C2 C3 in H1 H2 H3;
  tryfold C4 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 C2 C3 C4 in H1 H2 H3;
  tryfold C5 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 C2 C3 C4 C5 in H1 H2 H3;
  tryfold C6 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  tryfold C7 in H1, H2, H3.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  tryfold C8 in H1, H2, H3.






Tactic Notation "tfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tryfold C1 in H1, H2, H3;
  tryfold C1.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 in H1 H2 H3;
  tryfold C2 in H1, H2, H3;
  tryfold C2.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 C2 in H1 H2 H3;
  tryfold C3 in H1, H2, H3;
  tryfold C3.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 C2 C3 in H1 H2 H3;
  tryfold C4 in H1, H2, H3;
  tryfold C4.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 C2 C3 C4 in H1 H2 H3;
  tryfold C5 in H1, H2, H3;
  tryfold C5.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 C2 C3 C4 C5 in H1 H2 H3;
  tryfold C6 in H1, H2, H3;
  tryfold C6.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 C2 C3 C4 C5 C6 in H1 H2 H3;
  tryfold C7 in H1, H2, H3;
  tryfold C7.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  tfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3;
  tryfold C8 in H1, H2, H3;
  tryfold C8.






Tactic Notation "tfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tryfold C1 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 in H1 H2 H3 H4;
  tryfold C2 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 C2 in H1 H2 H3 H4;
  tryfold C3 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 C2 C3 in H1 H2 H3 H4;
  tryfold C4 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 C2 C3 C4 in H1 H2 H3 H4;
  tryfold C5 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  tryfold C6 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  tryfold C7 in H1, H2, H3, H4.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  tryfold C8 in H1, H2, H3, H4.






Tactic Notation "tfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tryfold C1 in H1, H2, H3, H4;
  tryfold C1.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 in H1 H2 H3 H4;
  tryfold C2 in H1, H2, H3, H4;
  tryfold C2.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 C2 in H1 H2 H3 H4;
  tryfold C3 in H1, H2, H3, H4;
  tryfold C3.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 C2 C3 in H1 H2 H3 H4;
  tryfold C4 in H1, H2, H3, H4;
  tryfold C4.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 C2 C3 C4 in H1 H2 H3 H4;
  tryfold C5 in H1, H2, H3, H4;
  tryfold C5.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 C2 C3 C4 C5 in H1 H2 H3 H4;
  tryfold C6 in H1, H2, H3, H4;
  tryfold C6.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4;
  tryfold C7 in H1, H2, H3, H4;
  tryfold C7.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  tfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4;
  tryfold C8 in H1, H2, H3, H4;
  tryfold C8.






Tactic Notation "tfl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tryfold C1 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 in H1 H2 H3 H4 H5;
  tryfold C2 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 C2 in H1 H2 H3 H4 H5;
  tryfold C3 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 C2 C3 in H1 H2 H3 H4 H5;
  tryfold C4 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  tryfold C5 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  tryfold C6 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  tryfold C7 in H1, H2, H3, H4, H5.

Tactic Notation "tfl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl - C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  tryfold C8 in H1, H2, H3, H4, H5.






Tactic Notation "tfl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tryfold C1 in H1, H2, H3, H4, H5;
  tryfold C1.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 in H1 H2 H3 H4 H5;
  tryfold C2 in H1, H2, H3, H4, H5;
  tryfold C2.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 C2 in H1 H2 H3 H4 H5;
  tryfold C3 in H1, H2, H3, H4, H5;
  tryfold C3.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 C2 C3 in H1 H2 H3 H4 H5;
  tryfold C4 in H1, H2, H3, H4, H5;
  tryfold C4.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 C2 C3 C4 in H1 H2 H3 H4 H5;
  tryfold C5 in H1, H2, H3, H4, H5;
  tryfold C5.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 C2 C3 C4 C5 in H1 H2 H3 H4 H5;
  tryfold C6 in H1, H2, H3, H4, H5;
  tryfold C6.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 C2 C3 C4 C5 C6 in H1 H2 H3 H4 H5;
  tryfold C7 in H1, H2, H3, H4, H5;
  tryfold C7.

Tactic Notation "tfl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
        constr(C5) constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  tfl + C1 C2 C3 C4 C5 C6 C7 in H1 H2 H3 H4 H5;
  tryfold C8 in H1, H2, H3, H4, H5;
  tryfold C8.