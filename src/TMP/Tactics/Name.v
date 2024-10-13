From CoreErlang.TMP.Tactics Require Export ParamsN.



(** STRUCTURE:
* Rename
* Replace
* Remember
* Inversion
*)



(** DOCUMENTATION:

* ren --> rename
  - N:[ident]:1-10 : N:[ident]:1-10

* rep --> replace
  - N:[constr]:1-10 : N:[constr]:1-10

* rem --> remember
  - N:[ident]:1-10 : N:[constr]:1-10
  - N:[ident]:1-10 : N:[constr]:1-10 as N:[ident]:1-10
  - N:[ident]:1-10 as N:[ident]:1-10 : N:[constr]:1-10

* ivr --> inversion
  - [hyp]:1-10
  - hyp as N:[ident]:1-10 : N:[ident]:1-10 - M:[ident]:1-10

* ivs --> inversion; subst
  - [hyp]:1-10
  - hyp as N:[ident]:1-10 : N:[ident]:1-10

* ivc --> inversion; subst; clear
  - [hyp]:1-10
  - hyp as N:[ident]:1-10 : N:[ident]:1-10

* bvs --> by inversion; subst
  - [hyp]:1-10

* avs --> by inversion; subst; auto
  - [hyp]:1-10
*)












(* Rename *)



Tactic Notation "ren"
  "-"   ident(In1)
  ":"   ident(Io1)
 :=
  rename Io1 into In1.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
 :=
  ren - In1:
        Io1;
  rename Io2 into In2.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
 :=
  ren - In1 In2:
        Io1 Io2;
  rename Io3 into In3.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
 :=
  ren - In1 In2 In3:
        Io1 Io2 Io3;
  rename Io4 into In4.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
 :=
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4;
  rename Io5 into In5.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
 :=
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5;
  rename Io6 into In6.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
 :=
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6;
  rename Io7 into In7.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
 :=
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  rename Io8 into In8.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
 :=
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  rename Io9 into In9.

Tactic Notation "ren"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
 :=
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  rename Io10 into In10.












(* Replace *)



Tactic Notation "rep"
  "-"   constr(Cn1)
  ":"   constr(Co1)
 :=
  replace Co1 with Cn1.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2)
  ":"   constr(Co1) constr(Co2)
 :=
  rep - Cn1:
        Co1;
  replace Co2 with Cn2.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rep - Cn1 Cn2:
        Co1 Co2;
  replace Co3 with Cn3.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rep - Cn1 Cn2 Cn3:
        Co1 Co2 Co3;
  replace Co4 with Cn4.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rep - Cn1 Cn2 Cn3 Cn4:
        Co1 Co2 Co3 Co4;
  replace Co5 with Cn5.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
        constr(Cn6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5:
        Co1 Co2 Co3 Co4 Co5;
  replace Co6 with Cn6.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
        constr(Cn6) constr(Cn7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  replace Co7 with Cn7.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
        constr(Cn6) constr(Cn7) constr(Cn8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6 Cn7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  replace Co8 with Cn8.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
        constr(Cn6) constr(Cn7) constr(Cn8) constr(Cn9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6 Cn7 Cn8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  replace Co9 with Cn9.

Tactic Notation "rep"
  "-"   constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
        constr(Cn6) constr(Cn7) constr(Cn8) constr(Cn9) constr(Cn10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6 Cn7 Cn8 Cn9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  replace Co10 with Cn10.












(* Remember *)



Tactic Notation "rem"
  "-"   ident(In1)
  ":"   constr(Co1)
 :=
  remember Co1 as In1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1:
        Co1;
  remember Co2 as In2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2:
        Co1 Co2;
  remember Co3 as In3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3:
        Co1 Co2 Co3;
  remember Co4 as In4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4:
        Co1 Co2 Co3 Co4;
  remember Co5 as In5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5:
        Co1 Co2 Co3 Co4 Co5;
  remember Co6 as In6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  remember Co7 as In7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  remember Co8 as In8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  remember Co9 as In9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  remember Co10 as In10.






Tactic Notation "rem"
  "-"   ident(In1)
  ":"   constr(Co1)
  "as"  ident(Ia1)
 :=
  remember Co1 as In1 eqn:Ia1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  ":"   constr(Co1) constr(Co2)
  "as"  ident(Ia1) ident(Ia2)
 :=
  rem - In1:
        Co1
     as Ia1;
  remember Co2 as In2 eqn:Ia2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  ":"   constr(Co1) constr(Co2) constr(Co3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
 :=
  rem - In1 In2:
        Co1 Co2
     as Ia1 Ia2;
  remember Co3 as In3 eqn:Ia3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
 :=
  rem - In1 In2 In3:
        Co1 Co2 Co3
     as Ia1 Ia2 Ia3;
  remember Co4 as In4 eqn:Ia4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
 :=
  rem - In1 In2 In3 In4:
        Co1 Co2 Co3 Co4
     as Ia1 Ia2 Ia3 Ia4;
  remember Co5 as In5 eqn:Ia5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
 :=
  rem - In1 In2 In3 In4 In5:
        Co1 Co2 Co3 Co4 Co5
     as Ia1 Ia2 Ia3 Ia4 Ia5;
  remember Co6 as In6 eqn:Ia6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
 :=
  rem - In1 In2 In3 In4 In5 In6:
        Co1 Co2 Co3 Co4 Co5 Co6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6;
  remember Co7 as In7 eqn:Ia7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7;
  remember Co8 as In8 eqn:Ia8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8;
  remember Co9 as In9 eqn:Ia9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9;
  remember Co10 as In10 eqn:Ia10.






Tactic Notation "rem"
  "-"   ident(In1)
  "as"  ident(Ia1)
  ":"   constr(Co1)
 :=
  remember Co1 as In1 eqn:Ia1.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2)
  "as"  ident(Ia1) ident(Ia2)
  ":"   constr(Co1) constr(Co2)
 :=
  rem - In1
     as Ia1:
        Co1;
  remember Co2 as In2 eqn:Ia2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
  ":"   constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2
     as Ia1 Ia2:
        Co1 Co2;
  remember Co3 as In3 eqn:Ia3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3
     as Ia1 Ia2 Ia3:
        Co1 Co2 Co3;
  remember Co4 as In4 eqn:Ia4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4
     as Ia1 Ia2 Ia3 Ia4:
        Co1 Co2 Co3 Co4;
  remember Co5 as In5 eqn:Ia5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5
     as Ia1 Ia2 Ia3 Ia4 Ia5:
        Co1 Co2 Co3 Co4 Co5;
  remember Co6 as In6 eqn:Ia6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6:
        Co1 Co2 Co3 Co4 Co5 Co6;
  remember Co7 as In7 eqn:Ia7.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  remember Co8 as In8 eqn:Ia8.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  remember Co9 as In9 eqn:Ia9.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7) ident(Ia8) ident(Ia9) ident(Ia10)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9
     as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9:
        Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  remember Co10 as In10 eqn:Ia10.












(* Inversion *)



Tactic Notation "ivr"
  "-"   hyp(H)
  :=
  inversion H.

Tactic Notation "ivs"
  "-"   hyp(H)
  :=
  inversion H;
  subst.

Tactic Notation "ivc"
  "-"   hyp(H)
  :=
  inversion H;
  subst;
  try clear H;
  clear_refl.









Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2)
  :=
  ivr - H1;
  ivr - H2.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  ivr - H1 H2;
  ivr - H3.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ivr - H1 H2 H3;
  ivr - H4.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ivr - H1 H2 H3 H4;
  ivr - H5.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  ivr - H1 H2 H3 H4 H5;
  ivr - H6.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  ivr - H1 H2 H3 H4 H5 H6;
  ivr - H7.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  ivr - H1 H2 H3 H4 H5 H6 H7;
  ivr - H8.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  ivr - H1 H2 H3 H4 H5 H6 H7 H8;
  ivr - H9.

Tactic Notation "ivr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  ivr - H1 H2 H3 H4 H5 H6 H7 H8 H9;
  ivr - H10.



Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2)
  :=
  ivs - H1;
  ivs - H2.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  ivs - H1 H2;
  ivs - H3.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ivs - H1 H2 H3;
  ivs - H4.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ivs - H1 H2 H3 H4;
  ivs - H5.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  ivs - H1 H2 H3 H4 H5;
  ivs - H6.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  ivs - H1 H2 H3 H4 H5 H6;
  ivs - H7.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7;
  ivs - H8.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8;
  ivs - H9.

Tactic Notation "ivs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8 H9;
  ivs - H10.



Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2)
  :=
  ivc - H1;
  ivc - H2.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  ivc - H1 H2;
  ivc - H3.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ivc - H1 H2 H3;
  ivc - H4.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ivc - H1 H2 H3 H4;
  ivc - H5.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  ivc - H1 H2 H3 H4 H5;
  ivc - H6.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  ivc - H1 H2 H3 H4 H5 H6;
  ivc - H7.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  ivc - H1 H2 H3 H4 H5 H6 H7;
  ivc - H8.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  ivc - H1 H2 H3 H4 H5 H6 H7 H8;
  ivc - H9.

Tactic Notation "ivc"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  ivc - H1 H2 H3 H4 H5 H6 H7 H8 H9;
  ivc - H10.









Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  :=
  ivr - H;
  ren - In1:
        Io1.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  :=
  ivr - H;
  ren - In1 In2:
        Io1 Io2.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  :=
  ivr - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  :=
  ivr - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

Tactic Notation "ivr"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  :=
  ivr - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.



Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1)
  :=
  ivr - Hx;
  ren - In1:
        H.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  :=
  ivr - Hx;
  ren - In1 In2:
        H H0.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  :=
  ivr - Hx;
  ren - In1 In2 In3:
        H H0 H1.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7.

Tactic Notation "ivr"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  :=
  ivr - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8.






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
  :=
  ivs - H;
  ren - In1:
        Io1.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  :=
  ivs - H;
  ren - In1 In2:
        Io1 Io2.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  :=
  ivs - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  :=
  ivs - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

Tactic Notation "ivs"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  :=
  ivs - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.



Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1)
  :=
  ivs - Hx;
  ren - In1:
        H.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  :=
  ivs - Hx;
  ren - In1 In2:
        H H0.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  :=
  ivs - Hx;
  ren - In1 In2 In3:
        H H0 H1.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7.

Tactic Notation "ivs"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  :=
  ivs - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8.









Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  :=
  ivc - H;
  ren - In1:
        Io1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  :=
  ivc - H;
  ren - In1 In2:
        Io1 Io2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  :=
  ivc - H;
  ren - In1 In2 In3:
        Io1 Io2 Io3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4:
        Io1 Io2 Io3 Io4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5:
        Io1 Io2 Io3 Io4 Io5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6:
        Io1 Io2 Io3 Io4 Io5 Io6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.



Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1)
  :=
  ivc - Hx;
  ren - In1:
        H.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2)
  :=
  ivc - Hx;
  ren - In1 In2:
        H H0.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3)
  :=
  ivc - Hx;
  ren - In1 In2 In3:
        H H0 H1.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4:
        H H0 H1 H2.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5:
        H H0 H1 H2 H3.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6:
        H H0 H1 H2 H3 H4.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7:
        H H0 H1 H2 H3 H4 H5.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8:
        H H0 H1 H2 H3 H4 H5 H6.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
        H H0 H1 H2 H3 H4 H5 H6 H7.

Tactic Notation "ivc"
  "-"   hyp(Hx)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  :=
  ivc - Hx;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
        H H0 H1 H2 H3 H4 H5 H6 H7 H8.









Tactic Notation "bvs"
  "-"   hyp(H1)
  :=
  ivs - H1;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2)
  :=
  ivs - H1 H2;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  ivs - H1 H2 H3;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ivs - H1 H2 H3 H4;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ivs - H1 H2 H3 H4 H5;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  ivs - H1 H2 H3 H4 H5 H6;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8 H9;
  solve [trivial].

Tactic Notation "bvs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8 H9 H10;
  solve [trivial].









Tactic Notation "avs"
  "-"   hyp(H1)
  :=
  ivs - H1;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2)
  :=
  ivs - H1 H2;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  ivs - H1 H2 H3;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  ivs - H1 H2 H3 H4;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  ivs - H1 H2 H3 H4 H5;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6)
  :=
  ivs - H1 H2 H3 H4 H5 H6;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8 H9;
  solve [auto].

Tactic Notation "avs"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
        hyp(H6) hyp(H7) hyp(H8) hyp(H9) hyp(H10)
  :=
  ivs - H1 H2 H3 H4 H5 H6 H7 H8 H9 H10;
  solve [auto].