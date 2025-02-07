From CoreErlang.Eqvivalence.Tactics Require Import T2ParamSingle.
From CoreErlang.Eqvivalence.Tactics Require Import T3ParamMultiple.
From CoreErlang.Eqvivalence.Tactics Require Import T4Name.
From CoreErlang.Eqvivalence.Tactics Require Import T5Transform.



(** STRUCTURE:
*
*)



(** DOCUMENTATION:


* ivr   -->   inversion
              - hyp as simple_intropattern / M:[ident]:0-10
              - hyp as N:[ident]:1-10 : N:[ident]:1-10 / M:[ident]:0-10

* ivs   -->   inversion; subst
              - hyp as simple_intropattern / M:[ident]:0-10
              - hyp as N:[ident]:1-10 : N:[ident]:1-10 / M:[ident]:0-10

* ivc   -->   inversion; subst; clear
              - hyp as simple_intropattern / M:[ident]:0-10
              - hyp as N:[ident]:1-10 : N:[ident]:1-10 / M:[ident]:0-10



* spc   -->   specialize; clear
              - hyp {as ident}: [constr]:1-20
              + hyp as ident: [constr]:1-20
              - hyp: [constr]:1-5 / [ident]:1-5


* psc   -->   pose proof; clear
              - constr {as ident}: [constr]:1-20
              - hyp: [constr]:1-5 / [ident]:1-5



* cwr   -->   rewrite ->; clear
              - [constr]:1-10
              - [constr]:1-10 in *
              - [constr]:1-10 in [hyp]:1-5
              + [constr]:1-10 in [hyp]:1-5
              - [constr]:1-5 in * / [ident]:1-10

* cwl   -->   rewrite <-; clear
              - [constr]:1-10
              - [constr]:1-10 in *
              - [constr]:1-10 in [hyp]:1-5
              + [constr]:1-10 in [hyp]:1-5
              - [constr]:1-5 in * / [ident]:1-10
* 
*)







































(*
////////////////////////////////////////////////////////////////////////////////
//// SIMPLIFY //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Tactic Notation "smp"
  "/"   ident(Ic1)
  :=
  smp;
  clr - Ic1.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2)
  :=
  smp;
  clr - Ic1 Ic2.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  smp;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "smp"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  smp;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.





Tactic Notation "smp"
  "*"
  "/"   ident(Ic1)
  :=
  smp *;
  clr - Ic1.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2)
  :=
  smp *;
  clr - Ic1 Ic2.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "smp"
  "*"
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5) ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  smp *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.







































(*
////////////////////////////////////////////////////////////////////////////////
//// REMEMBER //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clr - Ic1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clr - Ic1.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1)
 :=
  rem - In1
     as Ia1:
        Co1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9 Ia10:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9 Co10;
  clear Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.







































(*
////////////////////////////////////////////////////////////////////////////////
//// INVERSION /////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1)
  :=
  ivr - H as SIP;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.









Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1)
  :=
  ivs - H as SIP;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.









Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1)
  :=
  ivc - H as SIP;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  simple_intropattern(SIP)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H as SIP;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.















Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1: H;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5
        Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.






Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1: H;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5
        Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.






Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1: H;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5
        Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.






Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1:
        Io1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1:
        H;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.







































(*
////////////////////////////////////////////////////////////////////////////////
//// SPECIALIZE ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1)
  :=
  specialize (H C1);
  try clear C1.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  :=
  spc - H: C1;
  specialize (H C2);
  try clear C2.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  spc - H: C1 C2;
  specialize (H C3);
  try clear C3.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  spc - H: C1 C2 C3;
  specialize (H C4);
  try clear C4.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  spc - H: C1 C2 C3 C4;
  specialize (H C5);
  try clear C5.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  spc - H: C1 C2 C3 C4 C5;
  specialize (H C6);
  try clear C6.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  spc - H: C1 C2 C3 C4 C5 C6;
  specialize (H C7);
  try clear C7.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7;
  specialize (H C8);
  try clear C8.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8;
  specialize (H C9);
  try clear C9.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9;
  specialize (H C10);
  try clear C10.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10;
  specialize (H C11);
  try clear C11.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11;
  specialize (H C12);
  try clear C12.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12;
  specialize (H C13);
  try clear C13.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13;
  specialize (H C14);
  try clear C14.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14;
  specialize (H C15);
  try clear C15.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15;
  specialize (H C16);
  try clear C16.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16;
  specialize (H C17);
  try clear C17.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17;
  specialize (H C18);
  try clear C18.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18;
  specialize (H C19);
  try clear C19.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19;
  specialize (H C20);
  try clear C20.






Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  specialize (H C1) as I;
  clear H;
  try clear C1.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2) as I;
  clear H;
  try clear C1;
  try clear C2.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17)
    as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18)
    as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19.

Tactic Notation "spc"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20) as I;
  clear H;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19;
  try clear C20.






Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  specialize (H C1) as I;
  try clear C1.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2) as I;
  try clear C1;
  try clear C2.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3) as I;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17)
    as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18)
    as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19.

Tactic Notation "spc"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20) as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19;
  try clear C20.












Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1)
  "/"   ident(Ic1)
  :=
  spc - H: C1;
  clear Ic1.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1)
  :=
  spc - H: C1 C2;
  clear Ic1.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1)
  :=
  spc - H: C1 C2 C3;
  clear Ic1.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1)
  :=
  spc - H: C1 C2 C3 C4;
  clear Ic1.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1)
  :=
  spc - H: C1 C2 C3 C4 C5;
  clear Ic1.






Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  spc - H: C1;
  clear Ic1 Ic2.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  spc - H: C1 C2;
  clear Ic1 Ic2.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  spc - H: C1 C2 C3;
  clear Ic1 Ic2.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  spc - H: C1 C2 C3 C4;
  clear Ic1 Ic2.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  spc - H: C1 C2 C3 C4 C5;
  clear Ic1 Ic2.






Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  spc - H: C1;
  clear Ic1 Ic2 Ic3.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  spc - H: C1 C2;
  clear Ic1 Ic2 Ic3.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  spc - H: C1 C2 C3;
  clear Ic1 Ic2 Ic3.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  spc - H: C1 C2 C3 C4;
  clear Ic1 Ic2 Ic3.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  spc - H: C1 C2 C3 C4 C5;
  clear Ic1 Ic2 Ic3.






Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  spc - H: C1;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  spc - H: C1 C2;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  spc - H: C1 C2 C3;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  spc - H: C1 C2 C3 C4;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  spc - H: C1 C2 C3 C4 C5;
  clear Ic1 Ic2 Ic3 Ic4.






Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  spc - H: C1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  spc - H: C1 C2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  spc - H: C1 C2 C3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  spc - H: C1 C2 C3 C4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "spc"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  spc - H: C1 C2 C3 C4 C5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.







































(*
////////////////////////////////////////////////////////////////////////////////
//// POSE_PROOF ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  pose proof C C1;
  try clear C1.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  :=
  pose proof C C1 C2;
  try clear C1;
  try clear C2.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19;
  try clear C20.






Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  pose proof C C1 as I;
  try clear C1.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  pose proof C C1 C2 as I;
  try clear C1;
  try clear C2.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3 as I;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19.

Tactic Notation "psc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9;
  try clear C10;
  try clear C11;
  try clear C12;
  try clear C13;
  try clear C14;
  try clear C15;
  try clear C16;
  try clear C17;
  try clear C18;
  try clear C19;
  try clear C20.












Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1)
  "/"   ident(Ic1)
  :=
  psc - C: C1;
  clear Ic1.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1)
  :=
  psc - C: C1 C2;
  clear Ic1.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1)
  :=
  psc - C: C1 C2 C3;
  clear Ic1.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1)
  :=
  psc - C: C1 C2 C3 C4;
  clear Ic1.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1)
  :=
  psc - C: C1 C2 C3 C4 C5;
  clear Ic1.






Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  psc - C: C1;
  clear Ic1 Ic2.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  psc - C: C1 C2;
  clear Ic1 Ic2.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  psc - C: C1 C2 C3;
  clear Ic1 Ic2.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  psc - C: C1 C2 C3 C4;
  clear Ic1 Ic2.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  psc - C: C1 C2 C3 C4 C5;
  clear Ic1 Ic2.






Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  psc - C: C1;
  clear Ic1 Ic2 Ic3.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  psc - C: C1 C2;
  clear Ic1 Ic2 Ic3.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  psc - C: C1 C2 C3;
  clear Ic1 Ic2 Ic3.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  psc - C: C1 C2 C3 C4;
  clear Ic1 Ic2 Ic3.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  psc - C: C1 C2 C3 C4 C5;
  clear Ic1 Ic2 Ic3.






Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  psc - C: C1;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  psc - C: C1 C2;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  psc - C: C1 C2 C3;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  psc - C: C1 C2 C3 C4;
  clear Ic1 Ic2 Ic3 Ic4.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  psc - C: C1 C2 C3 C4 C5;
  clear Ic1 Ic2 Ic3 Ic4.






Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  psc - C: C1;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  psc - C: C1 C2;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  psc - C: C1 C2 C3;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  psc - C: C1 C2 C3 C4;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "psc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  psc - C: C1 C2 C3 C4 C5;
  clear Ic1 Ic2 Ic3 Ic4 Ic5.




















































(*
////////////////////////////////////////////////////////////////////////////////
//// REWRITE_RIGHT /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









Tactic Notation "cwr"
  "-"   constr(C1)
  :=
  rewrite -> C1;
  clear C1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "in"  "*"
  :=
  rewrite -> C1 in *;
  clear C1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite -> C1 in H1;
  clear C1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1 in H1, H2;
  clear C1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1 in H1, H2, H3;
  clear C1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1 in H1, H2, H3, H4;
  clear C1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1 in H1, H2, H3, H4, H5;
  clear C1.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  :=
  rewrite -> C1, -> C2;
  clear C1 C2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  rewrite -> C1, -> C2 in *;
  clear C1 C2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2 in H1;
  clear C1 C2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2 in H1, H2;
  clear C1 C2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3;
  clear C1 C2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4;
  clear C1 C2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4, H5;
  clear C1 C2.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite -> C1, -> C2, -> C3;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3 in *;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3 in H1;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4, H5;
  clear C1 C2 C3.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in *;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7 C8.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.



Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.






Tactic Notation "cwr"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite -> C1 in H1 |- *;
  clear C1.

Tactic Notation "cwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1 in H1, H2 |- *;
  clear C1.

Tactic Notation "cwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1 in H1, H2, H3 |- *;
  clear C1.

Tactic Notation "cwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1 in H1, H2, H3, H4 |- *;
  clear C1.

Tactic Notation "cwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1 in H1, H2, H3, H4, H5 |- *;
  clear C1.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2 in H1 |- *;
  clear C1 C2.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2 in H1, H2 |- *;
  clear C1 C2.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3 |- *;
  clear C1 C2.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4 |- *;
  clear C1 C2.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3 in H1 |- *;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2 |- *;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3 |- *;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.



Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.












Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1)
  :=
  cwr - C1 in *;
  clr - Ic1.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwr"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwr - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1)
  :=
  cwr - C1 C2 in *;
  clr - Ic1.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwr - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwr - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwr - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwr - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.


















(*
////////////////////////////////////////////////////////////////////////////////
//// REWRITE_LEFT //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "cwl"
  "-"   constr(C1)
  :=
  rewrite <- C1;
  clear C1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "in"  "*"
  :=
  rewrite <- C1 in *;
  clear C1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite <- C1 in H1;
  clear C1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1 in H1, H2;
  clear C1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1 in H1, H2, H3;
  clear C1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1 in H1, H2, H3, H4;
  clear C1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1 in H1, H2, H3, H4, H5;
  clear C1.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  :=
  rewrite <- C1, <- C2;
  clear C1 C2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  rewrite <- C1, <- C2 in *;
  clear C1 C2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2 in H1;
  clear C1 C2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2 in H1, H2;
  clear C1 C2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3;
  clear C1 C2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4;
  clear C1 C2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4, H5;
  clear C1 C2.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite <- C1, <- C2, <- C3;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3 in *;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3 in H1;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4, H5;
  clear C1 C2 C3.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in *;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7 C8.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.



Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4, H5;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.






Tactic Notation "cwl"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite <- C1 in H1 |- *;
  clear C1.

Tactic Notation "cwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1 in H1, H2 |- *;
  clear C1.

Tactic Notation "cwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1 in H1, H2, H3 |- *;
  clear C1.

Tactic Notation "cwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1 in H1, H2, H3, H4 |- *;
  clear C1.

Tactic Notation "cwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1 in H1, H2, H3, H4, H5 |- *;
  clear C1.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2 in H1 |- *;
  clear C1 C2.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2 in H1, H2 |- *;
  clear C1 C2.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3 |- *;
  clear C1 C2.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4 |- *;
  clear C1 C2.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3 in H1 |- *;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2 |- *;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3 |- *;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9.



Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "cwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4, H5 |- *;
  clear C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.















Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1)
  :=
  cwl - C1 in *;
  clr - Ic1.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwl"
  "-"   constr(C1)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwl - C1 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1)
  :=
  cwl - C1 C2 in *;
  clr - Ic1.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwl - C1 C2 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwl - C1 C2 C3 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwl - C1 C2 C3 C4 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.






Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9.

Tactic Notation "cwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "/"   ident(Ic1) ident(Ic2) ident(Ic3) ident(Ic4) ident(Ic5)
        ident(Ic6) ident(Ic7) ident(Ic8) ident(Ic9) ident(Ic10)
  :=
  cwl - C1 C2 C3 C4 C5 in *;
  clr - Ic1 Ic2 Ic3 Ic4 Ic5 Ic6 Ic7 Ic8 Ic9 Ic10.