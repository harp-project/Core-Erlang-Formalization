From CoreErlang Require Export Basics.



(** NOTES
* FUNCTION:
  - Many of this tactics are Abridgments of already existing tactics
  - Most of them has 3 letters
  - The ones with 4 are doing the same thing as their 3 letter counterparts,
    the extra letter signifies their extra function
    + e. -> existential variable
    + b. -> solve goal after tactic (by)
    + s. -> simplification
    + c. -> cbn
    + .c -> clear (used hypothesises)
  - Some of them has linked versions, which means, that they can be used on
    multiple targets at once, instead of only one (rename, remember ...etc)
  - It also has some totaly new tactics
    + clear_refl: clear all reflexive hypothesis
    + refold: unfold then fold the same target, useful on recursive functions
* SUGGESTION:
  - Maybe replace some tactics to CoreErlang/Tactics
*)



(*
################################################################################
###### Documentation ###########################################################
################################################################################
### * SIMPLE SINGLE
###
###   - NONE
###
###     + rfl                         <-  reflexivty
###     + asm                         <-  assumption
###     + dis                         <-  discriminate
###     + con                         <-  congruence
###     + spl                         <-  split
###     + lft                         <-  left
###     + rgt                         <-  right
###     + sbt                         <-  subst
###     + aut                         <-  auto
###     + cns                         <-  constructor                     + (e.)
###     + lia                         <-  lia                       + (s. , c.)
###     + nia                         <-  nia                       + (s. , c.)
###
###   - SINGLE
###
###     + app H                       <-  apply H                         + (e.)
###     + exa H                       <-  exact H
###     + inj H                       <-  injection H
###
###   - SINGLE AS
###
###     + ass x {as H} {by t}         <-  assert x {as H} {by t}
###     + des x {as p}                <-  destruct x {as p}
###     + ind x {as p}                <-  induction x {as p}
###
### * SIMPLE MANY
###
###   - SIMPLE
###
###     + int <H>                     <-  intros <H>
###     + exi <H>+                    <-  [exists H]+                     + (e.)
###     + rev <H>+                    <-  [revert H]+
###     + gen <H>+H                   <-  [generalize dependent H]+
###     + dfd <H>+                    <-  [fold H]+
###     + ufd <H>+                    <-  [unfold H]+
###     + rfd <H>+                    <-  [unfold H; fold H]+
###     + tfd <H>+                    <-  [try unfold H; try fold H]+
###
###   - SIGNAL
###
###     + clr {-} <H>                 <-  clear {-} <H>
###
###   - In
###
###     + smp {in <H,>{+}}            <-  simpl {in (<H,> | * )}
###     + cbn {in <H,>{+}}            <-  cbn {in (<H,> | * )}
###
### * COMPLEX
###
###   - NAME
###
###     + ren <x>+ <- <y>+            <-  [rename x into y]+
###     + rep <x>+ <- <y>+            <-  [replace x with y]+
###     + rem <x>+ <- <y>+ as <H>+    <-  [rename x as y eqn:H]+
###     + inv H(: <x>+ <- <y>+).c     <-  inversion H (;subst;clr;rename) + (.c)
###
###   - TRANSFORM
###
###     + spc H{: <x>} {as H0}        <-  specialize (H <x>) {as H0}      + (.c)
###     + psp H{: <x>} {as H0}        <-  pose proof (H <x>) {as H0}      + (.c)
###     + rwr <H> {in <H0>,}          <-  rewrite -> <H> {in <H0>,}       + (.c)
###     + rwl <H> {in <H0>,}          <-  rewrite <- <H> {in <H0>,}       + (.c)
###     + rwe <H> {in <H0>,}          <-  (rwr | rwl) <H> {in <H0>,}      + (.c)
###
################################################################################
*)















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: BASE /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Ltac clear_refl :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SIMPLE SINGLE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









(*
-- SECTION: NONE ---------------------------------------------------------------
*)



Ltac rfl := reflexivity.
Ltac sym := symmetry.
Ltac asm := assumption.
Ltac dis := discriminate.
Ltac con := congruence.
Ltac spl := split.
Ltac lft := left.
Ltac rgt := right.
Ltac sbt := subst.
Ltac aut := auto.



Ltac cns := constructor.
Ltac ecns := econstructor.



(*slia*)
Ltac clia := cbn; lia.

(*snia*)
Ltac cnia := cbn; nia.









(*
-- SECTION: SINGLE -------------------------------------------------------------
*)



Ltac app H := apply H.
Ltac exa H := exact H.
Ltac inj H := injection H.









(*
-- SECTION: Single AS ----------------------------------------------------------
*)



Tactic Notation "ass"
  constr(x)
  :=
  assert x.

Tactic Notation "ass"
  constr(x)
  "as" ident(H)
  :=
  assert x as H.

Tactic Notation "ass"
  constr(x)
  "by" tactic(t)
  :=
  assert x by t.

Tactic Notation "ass"
  constr(x)
  "as" ident(H)
  "by" tactic(t)
  :=
  assert x as H by t.



Tactic Notation "des"
  constr(x)
  :=
  destruct x.

Tactic Notation "des"
  constr(x)
  "as" simple_intropattern(p)
  :=
  destruct x as p.



Tactic Notation "ind"
  constr(x)
  :=
  induction x.

Tactic Notation "ind"
  constr(x)
  "as" simple_intropattern(p)
  :=
  induction x as p.















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SIMPLE MANY //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)















(*
-- SECTION: SIMPLE -------------------------------------------------------------
*)






(*
SECTION: Intros
*)



Tactic Notation "int"
  :=
  intros.

Tactic Notation "int"
  ident(x) :=
  intros x.

Tactic Notation "int"
  ident(x1) ident(x2)
  :=
  intros x1 x2.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3)
  :=
  intros x1 x2 x3.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4)
  :=
  intros x1 x2 x3 x4.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  :=
  intros x1 x2 x3 x4 x5.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6)
  :=
  intros x1 x2 x3 x4 x5 x6.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7)
  :=
  intros x1 x2 x3 x4 x5 x6 x7.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18) ident(x19)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19.

Tactic Notation "int"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18) ident(x19) ident(x20)
  :=
  intros x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20.






(*
SECTION: Exists
*)



Tactic Notation "exi"
  ident(x)
  :=
  exists x.

Tactic Notation "exi"
  ident(x1) ident(x2)
  :=
  exi x1;
  exists x2.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3)
  :=
  exi x1 x2;
  exists x3.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4)
  :=
  exi x1 x2 x3;
  exists x4.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  :=
  exi x1 x2 x3 x4;
  exists x5.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6)
  :=
  exi x1 x2 x3 x4 x5;
  exists x6.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7)
  :=
  exi x1 x2 x3 x4 x5 x6;
  exists x7.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8)
  :=
  exi x1 x2 x3 x4 x5 x6 x7;
  exists x8.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9)
  :=
  exi x1 x2 x3 x4 x5 x6 x7 x8;
  exists x9.

Tactic Notation "exi"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  :=
  exi x1 x2 x3 x4 x5 x6 x7 x8 x9;
  exists x10.



Ltac eexi := eexists.






(*
SECTION: Revert
*)



Tactic Notation "rev"
  ident(x)
  :=
  revert x.

Tactic Notation "rev"
  ident(x1) ident(x2)
  :=
  rev x1;
  revert x2.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3)
  :=
  rev x1 x2;
  revert x3.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4)
  :=
  rev x1 x2 x3;
  revert x4.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  :=
  rev x1 x2 x3 x4;
  revert x5.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6)
  :=
  rev x1 x2 x3 x4 x5;
  revert x6.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7)
  :=
  rev x1 x2 x3 x4 x5 x6;
  revert x7.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8)
  :=
  rev x1 x2 x3 x4 x5 x6 x7;
  revert x8.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9)
  :=
  rev x1 x2 x3 x4 x5 x6 x7 x8;
  revert x9.

Tactic Notation "rev"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  :=
  rev x1 x2 x3 x4 x5 x6 x7 x8 x9;
  revert x10.






(*
SECTION: Generalize dependent
*)



Tactic Notation "gen"
  ident(x)
  :=
  generalize dependent x.

Tactic Notation "gen"
  ident(x1) ident(x2)
  :=
  gen x1;
  generalize dependent x2.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3)
  :=
  gen x1 x2;
  generalize dependent x3.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4)
  :=
  gen x1 x2 x3;
  generalize dependent x4.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  :=
  gen x1 x2 x3 x4;
  generalize dependent x5.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6)
  :=
  gen x1 x2 x3 x4 x5;
  generalize dependent x6.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7)
  :=
  gen x1 x2 x3 x4 x5 x6;
  generalize dependent x7.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8)
  :=
  gen x1 x2 x3 x4 x5 x6 x7;
  generalize dependent x8.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9)
  :=
  gen x1 x2 x3 x4 x5 x6 x7 x8;
  generalize dependent x9.

Tactic Notation "gen"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  :=
  gen x1 x2 x3 x4 x5 x6 x7 x8 x9;
  generalize dependent x10.




(*
SECTION: Fold
*)



Tactic Notation "dfd"
  constr(x)
  :=
  fold x.

Tactic Notation "dfd"
  constr(x1) constr(x2)
  :=
  dfd x1;
  fold x2.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3)
  :=
  dfd x1 x2;
  fold x3.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4)
  :=
  dfd x1 x2 x3;
  fold x4.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  :=
  dfd x1 x2 x3 x4;
  fold x5.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6)
  :=
  dfd x1 x2 x3 x4 x5;
  fold x6.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7)
  :=
  dfd x1 x2 x3 x4 x5 x6;
  fold x7.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8)
  :=
  dfd x1 x2 x3 x4 x5 x6 x7;
  fold x8.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9)
  :=
  dfd x1 x2 x3 x4 x5 x6 x7 x8;
  fold x9.

Tactic Notation "dfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  :=
  dfd x1 x2 x3 x4 x5 x6 x7 x8 x9;
  fold x10.






(*
SECTION: Unfold
*)



Tactic Notation "ufd"
  constr(x)
  :=
  unfold x.

Tactic Notation "ufd"
  constr(x1) constr(x2)
  :=
  ufd x1;
  unfold x2.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3)
  :=
  ufd x1 x2;
  unfold x3.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4)
  :=
  ufd x1 x2 x3;
  unfold x4.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  :=
  ufd x1 x2 x3 x4;
  unfold x5.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6)
  :=
  ufd x1 x2 x3 x4 x5;
  unfold x6.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7)
  :=
  ufd x1 x2 x3 x4 x5 x6;
  unfold x7.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8)
  :=
  ufd x1 x2 x3 x4 x5 x6 x7;
  unfold x8.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9)
  :=
  ufd x1 x2 x3 x4 x5 x6 x7 x8;
  unfold x9.

Tactic Notation "ufd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  :=
  ufd x1 x2 x3 x4 x5 x6 x7 x8 x9;
  unfold x10.






(*
SECTION: Refold
*)



Tactic Notation "refold" constr(d) :=
  unfold d;
  fold d.

Tactic Notation "refold" constr(d) "in" ident(H) :=
  unfold d in H;
  fold d in H.



Tactic Notation "rfd"
  constr(x)
  :=
  unfold x;
  fold x.

Tactic Notation "rfd"
  constr(x1) constr(x2)
  :=
  rfd x1;
  unfold x2;
  fold x2.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3)
  :=
  ufd x1 x2;
  unfold x3;
  fold x3.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4)
  :=
  ufd x1 x2 x3;
  unfold x4;
  fold x4.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  :=
  ufd x1 x2 x3 x4;
  unfold x5;
  fold x5.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6)
  :=
  rfd x1 x2 x3 x4 x5;
  unfold x6;
  fold x6.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7)
  :=
  rfd x1 x2 x3 x4 x5 x6;
  unfold x7;
  fold x7.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8)
  :=
  rfd x1 x2 x3 x4 x5 x6 x7;
  unfold x8;
  fold x8.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9)
  :=
  rfd x1 x2 x3 x4 x5 x6 x7 x8;
  unfold x9;
  fold x9.

Tactic Notation "rfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  :=
  rfd x1 x2 x3 x4 x5 x6 x7 x8 x9;
  unfold x10;
  fold x10.






(*
SECTION: Tryfold
*)



Tactic Notation "tfd"
  constr(x)
  :=
  try unfold x;
  try fold x.

Tactic Notation "tfd"
  constr(x1) constr(x2)
  :=
  rfd x1;
  unfold x2;
  fold x2.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3)
  :=
  tfd x1 x2;
  try unfold x3;
  try fold x3.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4)
  :=
  tfd x1 x2 x3;
  try unfold x4;
  try fold x4.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  :=
  tfd x1 x2 x3 x4;
  try unfold x5;
  try fold x5.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6)
  :=
  tfd x1 x2 x3 x4 x5;
  try unfold x6;
  try fold x6.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7)
  :=
  tfd x1 x2 x3 x4 x5 x6;
  try unfold x7;
  try fold x7.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8)
  :=
  tfd x1 x2 x3 x4 x5 x6 x7;
  try unfold x8;
  try fold x8.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9)
  :=
  tfd x1 x2 x3 x4 x5 x6 x7 x8;
  try unfold x9;
  try fold x9.

Tactic Notation "tfd"
  constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  :=
  tfd x1 x2 x3 x4 x5 x6 x7 x8 x9;
  try unfold x10;
  try fold x10.









(*
-- SECTION: SIGNAL -------------------------------------------------------------
*)






(*
SECTION: Clear
*)



Tactic Notation "clr"
  ident(x)
  :=
  clear_refl;
  clear x.

Tactic Notation "clr"
  ident(x1) ident(x2)
  :=
  clear_refl;
  clear x1 x2.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3)
  :=
  clear_refl;
  clear x1 x2 x3.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4)
  :=
  clear_refl;
  clear x1 x2 x3 x4.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18) ident(x19)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19.

Tactic Notation "clr"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18) ident(x19) ident(x20)
  :=
  clear_refl;
  clear x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20.



Tactic Notation "clr" "-"
  ident(x)
  :=
  clear_refl;
  clear - x.

Tactic Notation "clr" "-"
  ident(x1) ident(x2)
  :=
  clear_refl;
  clear - x1 x2.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3)
  :=
  clear_refl;
  clear - x1 x2 x3.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4)
  :=
  clear_refl;
  clear - x1 x2 x3 x4.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18) ident(x19)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19.

Tactic Notation "clr" "-"
  ident(x1) ident(x2) ident(x3) ident(x4) ident(x5)
  ident(x6) ident(x7) ident(x8) ident(x9) ident(x10)
  ident(x11) ident(x12) ident(x13) ident(x14) ident(x15)
  ident(x16) ident(x17) ident(x18) ident(x19) ident(x20)
  :=
  clear_refl;
  clear - x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19
    x20.









(*
-- SECTION: IN -----------------------------------------------------------------
*)






(*
SECTION: Simple
*)



Tactic Notation "smp"
  :=
  simpl.

Tactic Notation "smp"
  "in" "*"
  :=
  simpl in *.



Tactic Notation "smp"
  "in" ident(H)
  :=
  simpl in H.

Tactic Notation "smp"
  "in" ident(H1) ident(H2)
  :=
  simpl in H1, H2.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3)
  :=
  simpl in H1, H2, H3.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4)
  :=
  simpl in H1, H2, H3, H4.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  :=
  simpl in H1, H2, H3, H4, H5.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  ident(H6)
  :=
  simpl in H1, H2, H3, H4, H5, H6.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9) ident(H10)
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10.



Tactic Notation "smp"
  "in" ident(H)
  "+"
  :=
  simpl in H |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2)
  "+"
  :=
  simpl in H1, H2 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3)
  "+"
  :=
  simpl in H1, H2, H3 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4)
  "+"
  :=
  simpl in H1, H2, H3, H4 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "+"
  :=
  simpl in H1, H2, H3, H4, H5 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6)
  "+"
  :=
  simpl in H1, H2, H3, H4, H5, H6 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7)
  "+"
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8)
  "+"
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9)
  "+"
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9 |- *.

Tactic Notation "smp"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9) ident(H10)
  "+"
  :=
  simpl in H1, H2, H3, H4, H5, H6, H7, H8, H9, H10 |- *.






(*
SECTION: Cbn
*)



Ltac bcbn := cbn; auto.



Ltac cbn_in H := cbn in H.

Ltac cbn_all := cbn in *.

Ltac cbn_goal := cbn.



Tactic Notation "cbn"
  :=
  cbn.

Tactic Notation "cbn"
  "in" "*"
  :=
  cbn_all.



Tactic Notation "cbn"
  "in" ident(H)
  :=
  cbn_in H.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2)
  :=
  cbn in H1;
  cbn_in H2.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3)
  :=
  cbn in H1 H2;
  cbn_in H3.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4)
  :=
  cbn in H1 H2 H3;
  cbn_in H4.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  :=
  cbn in H1 H2 H3 H4;
  cbn_in H5.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6)
  :=
  cbn in H1 H2 H3 H4 H5;
  cbn_in H6.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7)
  :=
  cbn in H1 H2 H3 H4 H5 H6;
  cbn_in H7.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8)
  :=
  cbn in H1 H2 H3 H4 H5 H6 H7;
  cbn_in H8.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9)
  :=
  cbn in H1 H2 H3 H4 H5 H6 H7 H8;
  cbn_in H9.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9) ident(H10)
  :=
  cbn in H1 H2 H3 H4 H5 H6 H7 H8 H9;
  cbn_in H10.



Tactic Notation "cbn"
  "in" ident(H)
  "+"
  :=
  cbn_in H;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2)
  "+"
  :=
  cbn in H1;
  cbn_in H2;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3)
  "+"
  :=
  cbn in H1 H2;
  cbn_in H3;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4)
  "+"
  :=
  cbn in H1 H2 H3;
  cbn_in H4;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "+"
  :=
  cbn in H1 H2 H3 H4;
  cbn_in H5;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6)
  "+"
  :=
  cbn in H1 H2 H3 H4 H5;
  cbn_in H6;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7)
  "+"
  :=
  cbn in H1 H2 H3 H4 H5 H6;
  cbn_in H7;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8)
  "+"
  :=
  cbn in H1 H2 H3 H4 H5 H6 H7;
  cbn_in H8;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9)
  "+"
  :=
  cbn in H1 H2 H3 H4 H5 H6 H7 H8;
  cbn_in H9;
  cbn_goal.

Tactic Notation "cbn"
  "in" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
       ident(H6) ident(H7) ident(H8) ident(H9) ident(H10)
  "+"
  :=
  cbn in H1 H2 H3 H4 H5 H6 H7 H8 H9;
  cbn_in H10;
  cbn_goal.















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: COMPLEX //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









(*
-- SECTION: NAME ---------------------------------------------------------------
*)






(*
SECTION: Rename
*)



Tactic Notation "ren"
  ident(n)
  "<-" ident(o)
  :=
  rename o into n.

Tactic Notation "ren"
  ident(n1) ident(n2)
  "<-" ident(o1) ident(o2)
  :=
  ren n1 <- o1;
  rename o2 into n2.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3)
  "<-" ident(o1) ident(o2) ident(o3)
  :=
  ren n1 n2 <- o1 o2;
  rename o3 into n3.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4)
  :=
  ren n1 n2 n3 <- o1 o2 o3;
  rename o4 into n4.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4) ident(o5)
  :=
  ren n1 n2 n3 n4 <- o1 o2 o3 o4;
  rename o5 into n5.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4) ident(o5)
       ident(o6)
  :=
  ren n1 n2 n3 n4 n5 <- o1 o2 o3 o4 o5;
  rename o6 into n6.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4) ident(o5)
       ident(o6) ident(o7)
  :=
  ren n1 n2 n3 n4 n5 n6 <- o1 o2 o3 o4 o5 o6;
  rename o7 into n7.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4) ident(o5)
       ident(o6) ident(o7) ident(o8)
  :=
  ren n1 n2 n3 n4 n5 n6 n7 <- o1 o2 o3 o4 o5 o6 o7;
  rename o8 into n8.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8) ident(n9)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4) ident(o5)
       ident(o6) ident(o7) ident(o8) ident(o9)
  :=
  ren n1 n2 n3 n4 n5 n6 n7 n8 <- o1 o2 o3 o4 o5 o6 o7 o8;
  rename o9 into n9.

Tactic Notation "ren"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8) ident(n9) ident(n10)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4) ident(o5)
       ident(o6) ident(o7) ident(o8) ident(o9) ident(o10)
  :=
  ren n1 n2 n3 n4 n5 n6 n7 n8 n9 <- o1 o2 o3 o4 o5 o6 o7 o8 o9;
  rename o10 into n10.






(*
SECTION: Replace
*)



Tactic Notation "rep"
  constr(n)
  "<-" constr(o)
  :=
  replace n with o.

Tactic Notation "rep"
  constr(n1) constr(n2)
  "<-" constr(o1) constr(o2)
  :=
  rep n1 <- o1;
  replace n2 with o2.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3)
  "<-" constr(o1) constr(o2) constr(o3)
  :=
  rep n1 n2 <- o1 o2;
  replace n3 with o3.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4)
  :=
  rep n1 n2 n3 <- o1 o2 o3;
  replace n4 with o4.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4) constr(n5)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
  :=
  rep n1 n2 n3 n4 <- o1 o2 o3 o4;
  replace n5 with o5.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4) constr(n5)
  constr(n6)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6)
  :=
  rep n1 n2 n3 n4 n5 <- o1 o2 o3 o4 o5;
  replace n6 with o6.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4) constr(n5)
  constr(n6) constr(n7)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7)
  :=
  rep n1 n2 n3 n4 n5 n6 <- o1 o2 o3 o4 o5 o6;
  replace n7 with o7.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4) constr(n5)
  constr(n6) constr(n7) constr(n8)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8)
  :=
  rep n1 n2 n3 n4 n5 n6 n7 <- o1 o2 o3 o4 o5 o6 o7;
  replace n8 with o8.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4) constr(n5)
  constr(n6) constr(n7) constr(n8) constr(n9)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8) constr(o9)
  :=
  rep n1 n2 n3 n4 n5 n6 n7 n8 <- o1 o2 o3 o4 o5 o6 o7 o8;
  replace n9 with o9.

Tactic Notation "rep"
  constr(n1) constr(n2) constr(n3) constr(n4) constr(n5)
  constr(n6) constr(n7) constr(n8) constr(n9) constr(n10)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8) constr(o9) constr(o10)
  :=
  rep n1 n2 n3 n4 n5 n6 n7 n8 n9 <- o1 o2 o3 o4 o5 o6 o7 o8 o9;
  replace n10 with o10.



Tactic Notation "rep"
  constr(n)
  "<-" constr(o)
  "by" tactic(t) :=
  replace n with o by t.






(*
SECTION: Remember
*)



Tactic Notation "rem"
  ident(n)
  "<-" constr(o)
  :=
  remember o as n.

Tactic Notation "rem"
  ident(n1) ident(n2)
  "<-" constr(o1) constr(o2)
  :=
  rem n1 <- o1;
  remember o2 as n2.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3)
  "<-" constr(o1) constr(o2) constr(o3)
  :=
  rem n1 n2 <- o1 o2;
  remember o3 as n3.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4)
  :=
  rem n1 n2 n3 <- o1 o2 o3;
  remember o4 as n4.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
  :=
  rem n1 n2 n3 n4 <- o1 o2 o3 o4;
  remember o5 as n5.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6)
  :=
  rem n1 n2 n3 n4 n5 <- o1 o2 o3 o4 o5;
  remember o6 as n6.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7)
  :=
  rem n1 n2 n3 n4 n5 n6 <- o1 o2 o3 o4 o5 o6;
  remember o7 as n7.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8)
  :=
  rem n1 n2 n3 n4 n5 n6 n7 <- o1 o2 o3 o4 o5 o6 o7;
  remember o8 as n8.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8) ident(n9)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8) constr(o9)
  :=
  rem n1 n2 n3 n4 n5 n6 n7 n8 <- o1 o2 o3 o4 o5 o6 o7 o8;
  remember o9 as n9.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8) ident(n9) ident(n10)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8) constr(o9) constr(o10)
  :=
  rem n1 n2 n3 n4 n5 n6 n7 n8 n9 <- o1 o2 o3 o4 o5 o6 o7 o8 o9;
  remember o10 as n10.



Tactic Notation "rem"
  ident(n)
  "<-" constr(o)
  "as" ident(e)
  :=
  remember o as n eqn: e.

Tactic Notation "rem"
  ident(n1) ident(n2)
  "<-" constr(o1) constr(o2)
  "as" ident(e1) ident(e2)
  :=
  rem n1 <- o1 as e1;
  remember o2 as n2 eqn: e2.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3)
  "<-" constr(o1) constr(o2) constr(o3)
  "as" ident(e1) ident(e2) ident(e3)
  :=
  rem n1 n2 <- o1 o2 as e1 e2;
  remember o3 as n3 eqn: e3.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4)
  "as" ident(e1) ident(e2) ident(e3) ident(e4)
  :=
  rem n1 n2 n3 <- o1 o2 o3 as e1 e2 e3;
  remember o4 as n4 eqn: e4.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
  "as" ident(e1) ident(e2) ident(e3) ident(e4) ident(e5)
  :=
  rem n1 n2 n3 n4 <- o1 o2 o3 o4 as e1 e2 e3 e4;
  remember o5 as n5 eqn: e5.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6)
  "as" ident(e1) ident(e2) ident(e3) ident(e4) ident(e5)
       ident(e6)
  :=
  rem n1 n2 n3 n4 n5 <- o1 o2 o3 o4 o5 as e1 e2 e3 e4 e5;
  remember o6 as n6 eqn: e6.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7)
  "as" ident(e1) ident(e2) ident(e3) ident(e4) ident(e5)
       ident(e6) ident(e7)
  :=
  rem n1 n2 n3 n4 n5 n6 <- o1 o2 o3 o4 o5 o6 as e1 e2 e3 e4 e5 e6;
  remember o7 as n7 eqn: e7.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4)
       constr(o5) constr(o6) constr(o7) constr(o8)
  "as" ident(e1) ident(e2) ident(e3) ident(e4) ident(e5)
       ident(e6) ident(e7) ident(e8)
  :=
  rem n1 n2 n3 n4 n5 n6 n7 <- o1 o2 o3 o4 o5 o6 o7 as e1 e2 e3 e4 e5 e6 e7;
  remember o8 as n8 eqn: e8.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8) ident(n9)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8) constr(o9)
  "as" ident(e1) ident(e2) ident(e3) ident(e4) ident(e5)
       ident(e6) ident(e7) ident(e8) ident(e9)
  :=
  rem n1 n2 n3 n4 n5 n6 n7 n8 <- o1 o2 o3 o4 o5 o6 o7 o8 as e1 e2 e3 e4 e5 e6 e7 e8;
  remember o9 as n9 eqn: e9.

Tactic Notation "rem"
  ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  ident(n6) ident(n7) ident(n8) ident(n9) ident(n10)
  "<-" constr(o1) constr(o2) constr(o3) constr(o4) constr(o5)
       constr(o6) constr(o7) constr(o8) constr(o9) constr(o10)
  "as" ident(e1) ident(e2) ident(e3) ident(e4) ident(e5)
       ident(e6) ident(e7) ident(e8) ident(e9) ident(e10)
  :=
  rem n1 n2 n3 n4 n5 n6 n7 n8 n9 <- o1 o2 o3 o4 o5 o6 o7 o8 o9 as e1 e2 e3 e4 e5 e6 e7 e8 e9;
  remember o10 as n10 eqn: e10.






(*
SECTION: Remember
*)



Ltac inv0 H := inv H.



Tactic Notation "inv"
  ident(H)
  :=
  inversion H.

Tactic Notation "invc"
  ident(H)
  :=
  inversion H;
  subst;
  try clear H;
  clear_refl.



Tactic Notation "invc"
  ident(H)
  ":" ident(n)
  "<-" ident(o)
  :=
  invc H;
  ren n <- o.

Tactic Notation "invc"
  ident(H)
  ":" ident(n1) ident(n2)
  "<-" ident(o1) ident(o2)
  :=
  invc H : n1 <- o1;
  ren n2 <- o2.

Tactic Notation "invc"
  ident(H)
  ":" ident(n1) ident(n2) ident(n3)
  "<-" ident(o1) ident(o2) ident(o3)
  :=
  invc H : n1 n2 <- o1 o2;
  ren n3 <- o3.

Tactic Notation "invc"
  ident(H)
  ":" ident(n1) ident(n2) ident(n3) ident(n4)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4)
  :=
  invc H : n1 n2 n3 <- o1 o2 o3;
  ren n4 <- o4.

Tactic Notation "invc"
  ident(H)
  ":" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4)  ident(o5)
  :=
  invc H : n1 n2 n3 n4 <- o1 o2 o3 o4;
  ren n5 <- o5.



Tactic Notation "invc"
  ident(H')
  ":" ident(n)
  :=
  invc H';
  ren n <- H.

Tactic Notation "invc"
  ident(H')
  ":" ident(n1) ident(n2)
  :=
  invc H' : n1;
  ren n2 <- H0.

Tactic Notation "invc"
  ident(H')
  ":" ident(n1) ident(n2) ident(n3)
  :=
  invc H' : n1 n2;
  ren n3 <- H1.

Tactic Notation "invc"
  ident(H')
  ":" ident(n1) ident(n2) ident(n3) ident(n4)
  :=
  invc H' : n1 n2 n3;
  ren n4 <- H2.

Tactic Notation "invc"
  ident(H')
  ":" ident(n1) ident(n2) ident(n3) ident(n4) ident(n5)
  "<-" ident(o1) ident(o2) ident(o3) ident(o4)  ident(o5)
  :=
  invc H' : n1 n2 n3 n4;
  ren n5 <- H3.









(*
-- SECTION: TRANSFROM ----------------------------------------------------------
*)






(*
SECTION: Specialize
*)



Tactic Notation "spc"
  ident(H)
  ":" constr(x)
  :=
  specialize (H x).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2)
  :=
  spc H: x1;
  specialize (H x2).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3)
  :=
  spc H: x1 x2;
  specialize (H x3).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4)
  :=
  spc H: x1 x2 x3;
  specialize (H x4).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  :=
  spc H: x1 x2 x3 x4;
  specialize (H x5).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6)
  :=
  spc H: x1 x2 x3 x4 x5;
  specialize (H x6).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7)
  :=
  spc H: x1 x2 x3 x4 x5 x6;
  specialize (H x7).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8)
  :=
  spc H: x1 x2 x3 x4 x5 x6 x7;
  specialize (H x8).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9)
  :=
  spc H: x1 x2 x3 x4 x5 x6 x7 x8;
  specialize (H x9).

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  :=
  spc H: x1 x2 x3 x4 x5 x6 x7 x8 x9;
  specialize (H x10).



Tactic Notation "spc"
  ident(H)
  ":" constr(x)
  "as" ident(H')
  :=
  specialize (H x) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2)
  "as" ident(H')
  :=
  spc H: x1;
  specialize (H x2) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3)
  "as" ident(H')
  :=
  spc H: x1 x2;
  specialize (H x3) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4)
  "as" ident(H')
  :=
  spc H: x1 x2 x3;
  specialize (H x4) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4;
  specialize (H x5) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4 x5;
  specialize (H x6) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4 x5 x6;
  specialize (H x7) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4 x5 x6 x7;
  specialize (H x8) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4 x5 x6 x7 x8;
  specialize (H x9) as H'.

Tactic Notation "spc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4 x5 x6 x7 x8 x9;
  specialize (H x10) as H'.






Tactic Notation "spcc"
  ident(H)
  ":" constr(x)
  :=
  specialize (H x);
  try clear x.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2)
  :=
  spcc H: x1;
  specialize (H x2);
  try clear x2.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3)
  :=
  spcc H: x1 x2;
  specialize (H x3);
  try clear x3.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4)
  :=
  spcc H: x1 x2 x3;
  specialize (H x4);
  try clear x4.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  :=
  spcc H: x1 x2 x3 x4;
  specialize (H x5);
  try clear x5.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6)
  :=
  spcc H: x1 x2 x3 x4 x5;
  specialize (H x6);
  try clear x6.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7)
  :=
  spcc H: x1 x2 x3 x4 x5 x6;
  specialize (H x7);
  try clear x7.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8)
  :=
  spcc H: x1 x2 x3 x4 x5 x6 x7;
  specialize (H x8);
  try clear x8.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9)
  :=
  spcc H: x1 x2 x3 x4 x5 x6 x7 x8;
  specialize (H x9);
  try clear x9.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  :=
  spcc H: x1 x2 x3 x4 x5 x6 x7 x8 x9;
  specialize (H x10);
  try clear x10.



Tactic Notation "spcc"
  ident(H)
  ":" constr(x)
  "as" ident(H')
  :=
  specialize (H x) as H';
  clear H;
  try clear x.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2)
  "as" ident(H')
  :=
  spc H: x1;
  specialize (H x2) as H';
  clear H;
  try clear x1;
  try clear x2.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3)
  "as" ident(H')
  :=
  spc H: x1 x2;
  specialize (H x3) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4)
  "as" ident(H')
  :=
  spc H: x1 x2 x3;
  specialize (H x4) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4;
  specialize (H x5) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6)
  "as" ident(H')
  :=
  spc H: x1 x2 x3 x4 x5;
  specialize (H x6) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7)
  "as" ident(H')
  :=
  spcc H: x1 x2 x3 x4 x5 x6;
  specialize (H x7) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8)
  "as" ident(H')
  :=
  spcc H: x1 x2 x3 x4 x5 x6 x7;
  specialize (H x8) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9)
  "as" ident(H')
  :=
  spcc H: x1 x2 x3 x4 x5 x6 x7 x8;
  specialize (H x9) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x9.

Tactic Notation "spcc"
  ident(H)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
      constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  "as" ident(H')
  :=
  spcc H: x1 x2 x3 x4 x5 x6 x7 x8 x9;
  specialize (H x10) as H';
  clear H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x9;
  try clear x10.






(*
SECTION: Pose Proof
*)



Tactic Notation
  "psp" constr(p)
  :=
  pose proof p.

Tactic Notation
  "psp" constr(p)
  ":" constr(x) :=
  pose proof p x.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) :=
  pose proof p x1 x2.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) :=
  pose proof p x1 x2 x3.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) :=
  pose proof p x1 x2 x3 x4.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
  pose proof p x1 x2 x3 x4 x5.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) :=
  pose proof p x1 x2 x3 x4 x5 x6.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10.



Tactic Notation
  "psp" constr(p)
  "as" ident(H)
  :=
  pose proof p as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x)
  "as" ident(H) :=
  pose proof p x.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2)
  "as" ident(H) :=
  pose proof p x1 x2 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3)
  "as" ident(H) :=
  pose proof p x1 x2 x3 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4)
  "as" ident(H) :=
  pose proof p x1 x2 x3 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 as H.

Tactic Notation
  "psp" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 as H.



Tactic Notation
  "pspc" constr(p)
  ":" constr(x) :=
  pose proof p x;
  try clear x.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) :=
  pose proof p x1 x2;
  try clear x1;
  try clear x2.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) :=
  pose proof p x1 x2 x3;
  try clear x1;
  try clear x2;
  try clear x3.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) :=
  pose proof p x1 x2 x3;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5) :=
  pose proof p x1 x2 x3 x4 x5;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) :=
  pose proof p x1 x2 x3 x4 x5 x6;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x9.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x10.



Tactic Notation
  "pspc" constr(p)
  "as" ident(H)
  :=
  pose proof p as H.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x)
  "as" ident(H) :=
  pose proof p x;
  try clear x.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2)
  "as" ident(H) :=
  pose proof p x1 x2 as H;
  try clear x1;
  try clear x2.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3)
  "as" ident(H) :=
  pose proof p x1 x2 x3 as H;
  try clear x1;
  try clear x2;
  try clear x3.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4)
  "as" ident(H) :=
  pose proof p x1 x2 x3 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x9.

Tactic Notation
  "pspc" constr(p)
  ":" constr(x1) constr(x2) constr(x3) constr(x4) constr(x5)
  constr(x6) constr(x7) constr(x8) constr(x9) constr(x10)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x10.






(*
SECTION: Rewrite Right
*)



Tactic Notation
  "rwr" constr(H)
  :=
  rewrite -> H.

Tactic Notation
  "rwr" constr(H)
  "in" "*"
  :=
  rewrite -> H in *.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi)
  :=
  rewrite -> H in Hi.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H in Hi |- *.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H in Hi1, Hi2.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H in Hi1, Hi2 |- *.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H in Hi1, Hi2, Hi3.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwr" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwr" constr(H1) constr(H2)
  :=
  rewrite -> H1, H2.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" "*"
  :=
  rewrite -> H1, H2 in *.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2 in Hi.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2 in Hi |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2 in Hi1, Hi2.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwr" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  :=
  rewrite -> H1, H2, H3.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" "*"
  :=
  rewrite -> H1, H2, H3 in *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2, H3 in Hi.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2 |- *.
Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  :=
  rewrite -> H1, H2, H3, H4.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" "*"
  :=
  rewrite -> H1, H2, H3, H4 in *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2, H3, H4 in Hi.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4 |- *.
Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  :=
  rewrite -> H1, H2, H3, H4, H5.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" "*"
  :=
  rewrite -> H1, H2, H3, H4, H5 in *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwr" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.






Tactic Notation
  "rwrc" ident(H)
  :=
  rewrite -> H;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" "*"
  :=
  rewrite -> H in *;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi)
  :=
  rewrite -> H in Hi;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H in Hi |- *;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H in Hi1, Hi2;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H in Hi1, Hi2 |- *;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H in Hi1, Hi2, Hi3;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H in Hi1, Hi2, Hi3 |- *;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H.

Tactic Notation
  "rwrc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H.



Tactic Notation
  "rwrc" ident(H1) ident(H2)
  :=
  rewrite -> H1, H2;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" "*"
  :=
  rewrite -> H1, H2 in *;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2 in Hi;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2 in Hi |- *;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2 in Hi1, Hi2;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2 |- *;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2.

Tactic Notation
  "rwrc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2.



Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  :=
  rewrite -> H1, H2, H3;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" "*"
  :=
  rewrite -> H1, H2, H3 in *;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2, H3 in Hi;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2 |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3.



Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  :=
  rewrite -> H1, H2, H3, H4;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" "*"
  :=
  rewrite -> H1, H2, H3, H4 in *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2, H3, H4 in Hi;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4.



Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  :=
  rewrite -> H1, H2, H3, H4, H5;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" "*"
  :=
  rewrite -> H1, H2, H3, H4, H5 in *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwrc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4 H5.






(*
SECTION: Rewrite Left
*)



Tactic Notation
  "rwl" constr(H)
  :=
  rewrite <- H.

Tactic Notation
  "rwl" constr(H)
  "in" "*"
  :=
  rewrite <- H in *.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi)
  :=
  rewrite <- H in Hi.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H in Hi |- *.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H in Hi1, Hi2.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H in Hi1, Hi2 |- *.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H in Hi1, Hi2, Hi3.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwl" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwl" constr(H1) constr(H2)
  :=
  rewrite <- H1, H2.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" "*"
  :=
  rewrite <- H1, H2 in *.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2 in Hi.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2 in Hi |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2 in Hi1, Hi2.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwl" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  :=
  rewrite <- H1, H2, H3.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" "*"
  :=
  rewrite <- H1, H2, H3 in *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2, H3 in Hi.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2 |- *.
Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  :=
  rewrite <- H1, H2, H3, H4.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" "*"
  :=
  rewrite <- H1, H2, H3, H4 in *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2, H3, H4 in Hi.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4 |- *.
Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  :=
  rewrite <- H1, H2, H3, H4, H5.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" "*"
  :=
  rewrite <- H1, H2, H3, H4, H5 in *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5.

Tactic Notation
  "rwl" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.






Tactic Notation
  "rwlc" ident(H)
  :=
  rewrite <- H;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" "*"
  :=
  rewrite <- H in *;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi)
  :=
  rewrite <- H in Hi;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H in Hi |- *;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H in Hi1, Hi2;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H in Hi1, Hi2 |- *;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H in Hi1, Hi2, Hi3;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H in Hi1, Hi2, Hi3 |- *;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H.

Tactic Notation
  "rwlc" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H.



Tactic Notation
  "rwlc" ident(H1) ident(H2)
  :=
  rewrite <- H1, H2;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" "*"
  :=
  rewrite <- H1, H2 in *;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2 in Hi;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2 in Hi |- *;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2 in Hi1, Hi2;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2 |- *;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2.

Tactic Notation
  "rwlc" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2.



Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  :=
  rewrite <- H1, H2, H3;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" "*"
  :=
  rewrite <- H1, H2, H3 in *;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2, H3 in Hi;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2 |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3.



Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  :=
  rewrite <- H1, H2, H3, H4;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" "*"
  :=
  rewrite <- H1, H2, H3, H4 in *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2, H3, H4 in Hi;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4.



Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  :=
  rewrite <- H1, H2, H3, H4, H5;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" "*"
  :=
  rewrite <- H1, H2, H3, H4, H5 in *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4 H5.

Tactic Notation
  "rwlc" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4 H5.






(*
SECTION: Rewrite Either
*)



Ltac rewrite_right_goal H := rewrite -> H.
Ltac rewrite_left_goal H := rewrite <- H.

Ltac rewrite_right_all H := rewrite -> H in *.
Ltac rewrite_left_all H := rewrite <- H in *.

Ltac rewrite_right_in H Hi := rewrite -> H in Hi.
Ltac rewrite_left_in H Hi := rewrite <- H in Hi.



Ltac rewrite_either_goal H :=
  first [rewrite_right_goal H | rewrite_left_goal H].

Ltac rewrite_either_all H :=
  first [rewrite_right_all H | rewrite_left_all H].

Ltac rewrite_either_in H Hi :=
  first [rewrite_right_in H Hi | rewrite_left_in H Hi].



Tactic Notation
  "rwe" constr(H)
  :=
  rewrite_either_goal H.

Tactic Notation
  "rwe" constr(H)
  "in" "*"
  :=
  rewrite_either_all H.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi)
  :=
  rewrite_either_in H Hi.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi)
  "+"
  :=
  rewrite_either_in H Hi;
  rewrite_either_goal H.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwe H in Hi1;
  rewrite_either_in H Hi2.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwe H in Hi1 +;
  rewrite_either_in H Hi2.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwe H in Hi1 Hi2;
  rewrite_either_in H Hi3.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwe H in Hi1 Hi2 +;
  rewrite_either_in H Hi3.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwe H in Hi1 Hi2 Hi3;
  rewrite_either_in H Hi4.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwe H in Hi1 Hi2 Hi3 +;
  rewrite_either_in H Hi4.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwe H in Hi1 Hi2 Hi3 Hi4;
  rewrite_either_in H Hi5.

Tactic Notation
  "rwe" constr(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwe H in Hi1 Hi2 Hi3 Hi4 +;
  rewrite_either_in H Hi5.



Tactic Notation
  "rwe" constr(H1) constr(H2)
  :=
  rwe H1;
  rwe H2.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" "*"
  :=
  rwe H1 in *;
  rwe H2 in *.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi)
  :=
  rwe H1 in Hi;
  rwe H2 in Hi.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi)
  "+"
  :=
  rwe H1 in Hi +;
  rwe H2 in Hi +.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwe H1 in Hi1 Hi2;
  rwe H2 in Hi1 Hi2.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwe H1 in Hi1 Hi2 +;
  rwe H2 in Hi1 Hi2 +.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwe H1 in Hi1 Hi2 Hi3;
  rwe H2 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwe H1 in Hi1 Hi2 Hi3 +;
  rwe H2 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwe H1 in Hi1 Hi2 Hi3 Hi4;
  rwe H2 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwe H1 in Hi1 Hi2 Hi3 Hi4 +;
  rwe H2 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwe H1 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwe H2 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwe" constr(H1) constr(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwe H1 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwe H2 in Hi1 Hi2 Hi3 Hi4 Hi5 +.



Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  :=
  rwe H1 H2;
  rwe H3.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" "*"
  :=
  rwe H1 H2 in *;
  rwe H3 in *.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi)
  :=
  rwe H1 H2 in Hi;
  rwe H3 in Hi.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi)
  "+"
  :=
  rwe H1 H2 in Hi +;
  rwe H3 in Hi +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwe H1 H2 in Hi1 Hi2;
  rwe H3 in Hi1 Hi2.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwe H1 H2 in Hi1 Hi2 +;
  rwe H3 in Hi1 Hi2 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwe H1 H2 in Hi1 Hi2 Hi3;
  rwe H3 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwe H1 H2 in Hi1 Hi2 Hi3 +;
  rwe H3 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwe H1 H2 in Hi1 Hi2 Hi3 Hi4;
  rwe H3 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwe H1 H2 in Hi1 Hi2 Hi3 Hi4 +;
  rwe H3 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwe H1 H2 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwe H3 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwe H1 H2 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwe H3 in Hi1 Hi2 Hi3 Hi4 Hi5 +.



Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  :=
  rwe H1 H2 H3;
  rwe H4.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" "*"
  :=
  rwe H1 H2 H3 in *;
  rwe H4 in *.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi)
  :=
  rwe H1 H2 H3 in Hi;
  rwe H4 in Hi.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi)
  "+"
  :=
  rwe H1 H2 H3 in Hi +;
  rwe H4 in Hi +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwe H1 H2 H3 in Hi1 Hi2;
  rwe H4 in Hi1 Hi2.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwe H1 H2 H3 in Hi1 Hi2 +;
  rwe H4 in Hi1 Hi2 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwe H1 H2 H3 in Hi1 Hi2 Hi3;
  rwe H4 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwe H1 H2 H3 in Hi1 Hi2 Hi3 +;
  rwe H4 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwe H1 H2 H3 in Hi1 Hi2 Hi3 Hi4;
  rwe H4 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwe H1 H2 H3 in Hi1 Hi2 Hi3 Hi4 +;
  rwe H4 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwe H1 H2 H3 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwe H4 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwe H1 H2 H3 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwe H4 in Hi1 Hi2 Hi3 Hi4 Hi5 +.



Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  :=
  rwe H1 H2 H3 H4;
  rwe H5.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" "*"
  :=
  rwe H1 H2 H3 H4 in *;
  rwe H5 in *.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi)
  :=
  rwe H1 H2 H3 H4 in Hi;
  rwe H5 in Hi.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi)
  "+"
  :=
  rwe H1 H2 H3 H4 in Hi +;
  rwe H5 in Hi +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2;
  rwe H5 in Hi1 Hi2.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 +;
  rwe H5 in Hi1 Hi2 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 Hi3;
  rwe H5 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 Hi3 +;
  rwe H5 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4;
  rwe H5 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4 +;
  rwe H5 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwe H5 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwe" constr(H1) constr(H2) constr(H3) constr(H4) constr(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwe H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwe H5 in Hi1 Hi2 Hi3 Hi4 Hi5 +.






Tactic Notation
  "rwec" ident(H)
  :=
  rewrite_either_goal H;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" "*"
  :=
  rewrite_either_all H;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi)
  :=
  rewrite_either_in H Hi;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi)
  "+"
  :=
  rewrite_either_in H Hi;
  rewrite_either_goal H;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwe H in Hi1;
  rewrite_either_in H Hi2;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwe H in Hi1 +;
  rewrite_either_in H Hi2;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwe H in Hi1 Hi2;
  rewrite_either_in H Hi3;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwe H in Hi1 Hi2 +;
  rewrite_either_in H Hi3;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwe H in Hi1 Hi2 Hi3;
  rewrite_either_in H Hi4;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwe H in Hi1 Hi2 Hi3 +;
  rewrite_either_in H Hi4;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwe H in Hi1 Hi2 Hi3 Hi4;
  rewrite_either_in H Hi5;
  clear H.

Tactic Notation
  "rwec" ident(H)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwe H in Hi1 Hi2 Hi3 Hi4 +;
  rewrite_either_in H Hi5;
  clear H.



Tactic Notation
  "rwec" ident(H1) ident(H2)
  :=
  rwec H1;
  rwec H2.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" "*"
  :=
  rwec H1 in *;
  rwec H2 in *.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi)
  :=
  rwec H1 in Hi;
  rwec H2 in Hi.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi)
  "+"
  :=
  rwec H1 in Hi +;
  rwec H2 in Hi +.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwec H1 in Hi1 Hi2;
  rwec H2 in Hi1 Hi2.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwec H1 in Hi1 Hi2 +;
  rwec H2 in Hi1 Hi2 +.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwec H1 in Hi1 Hi2 Hi3;
  rwec H2 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwec H1 in Hi1 Hi2 Hi3 +;
  rwec H2 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwec H1 in Hi1 Hi2 Hi3 Hi4;
  rwec H2 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwec H1 in Hi1 Hi2 Hi3 Hi4 +;
  rwec H2 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwec H1 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwec H2 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwec" ident(H1) ident(H2)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwec H1 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwec H2 in Hi1 Hi2 Hi3 Hi4 Hi5 +.



Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  :=
  rwec H1 H2;
  rwec H3.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" "*"
  :=
  rwec H1 H2 in *;
  rwec H3 in *.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi)
  :=
  rwec H1 H2 in Hi;
  rwec H3 in Hi.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi)
  "+"
  :=
  rwec H1 H2 in Hi +;
  rwec H3 in Hi +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwec H1 H2 in Hi1 Hi2;
  rwec H3 in Hi1 Hi2.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwec H1 H2 in Hi1 Hi2 +;
  rwec H3 in Hi1 Hi2 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwec H1 H2 in Hi1 Hi2 Hi3;
  rwec H3 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwec H1 H2 in Hi1 Hi2 Hi3 +;
  rwec H3 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwec H1 H2 in Hi1 Hi2 Hi3 Hi4;
  rwec H3 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwec H1 H2 in Hi1 Hi2 Hi3 Hi4 +;
  rwec H3 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwec H1 H2 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwec H3 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwec H1 H2 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwec H3 in Hi1 Hi2 Hi3 Hi4 Hi5 +.



Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  :=
  rwec H1 H2 H3;
  rwec H4.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" "*"
  :=
  rwec H1 H2 H3 in *;
  rwec H4 in *.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi)
  :=
  rwec H1 H2 H3 in Hi;
  rwec H4 in Hi.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi)
  "+"
  :=
  rwec H1 H2 H3 in Hi +;
  rwec H4 in Hi +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwec H1 H2 H3 in Hi1 Hi2;
  rwec H4 in Hi1 Hi2.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwec H1 H2 H3 in Hi1 Hi2 +;
  rwec H4 in Hi1 Hi2 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwec H1 H2 H3 in Hi1 Hi2 Hi3;
  rwec H4 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwec H1 H2 H3 in Hi1 Hi2 Hi3 +;
  rwec H4 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwec H1 H2 H3 in Hi1 Hi2 Hi3 Hi4;
  rwec H4 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwec H1 H2 H3 in Hi1 Hi2 Hi3 Hi4 +;
  rwec H4 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwec H1 H2 H3 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwec H4 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwec H1 H2 H3 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwec H4 in Hi1 Hi2 Hi3 Hi4 Hi5 +.



Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  :=
  rwec H1 H2 H3 H4;
  rwec H5.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" "*"
  :=
  rwec H1 H2 H3 H4 in *;
  rwec H5 in *.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi)
  :=
  rwec H1 H2 H3 H4 in Hi;
  rwec H5 in Hi.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi)
  "+"
  :=
  rwec H1 H2 H3 H4 in Hi +;
  rwec H5 in Hi +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2)
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2;
  rwec H5 in Hi1 Hi2.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2)
  "+"
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 +;
  rwec H5 in Hi1 Hi2 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 Hi3;
  rwec H5 in Hi1 Hi2 Hi3.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3)
  "+"
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 Hi3 +;
  rwec H5 in Hi1 Hi2 Hi3 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4;
  rwec H5 in Hi1 Hi2 Hi3 Hi4.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4)
  "+"
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4 +;
  rwec H5 in Hi1 Hi2 Hi3 Hi4 +.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4 Hi5;
  rwec H5 in Hi1 Hi2 Hi3 Hi4 Hi5.

Tactic Notation
  "rwec" ident(H1) ident(H2) ident(H3) ident(H4) ident(H5)
  "in" ident(Hi1) ident(Hi2) ident(Hi3) ident(Hi4) ident(Hi5)
  "+"
  :=
  rwec H1 H2 H3 H4 in Hi1 Hi2 Hi3 Hi4 Hi5 +;
  rwec H5 in Hi1 Hi2 Hi3 Hi4 Hi5 +.