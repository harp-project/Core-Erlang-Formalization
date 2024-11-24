From CoreErlang Require Import Basics.
From CoreErlang.Eq.Tactics Require Import T4Name.



(** DOCUMENTATION:

* des_for --> destruct_foralls; rename
  - N:[ident]:1-10 : N:[ident]:1-10
*)









Tactic Notation "des_for"
  :=
  destruct_foralls.

Tactic Notation "des_for"
  "-"   ident(In1)
  ":"   ident(Io1)
  :=
  destruct_foralls;
  ren - In1:
        Io1.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  :=
  destruct_foralls;
  ren - In1 In2:
        Io1 Io2.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  :=
  destruct_foralls;
  ren - In1 In2 In3:
        Io1 Io2 Io3.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

Tactic Notation "des_for"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  :=
  destruct_foralls;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.