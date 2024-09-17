From CoreErlang.TMP.Tactics Require Export ParamsN.



(**
DOCUMENTATION:
* ren - rename
* rep - replace
* rem - remember
* ivr - inversion
* ivs - inversion; subst
* ivc - inversion; subst; clear
*)



(**
STRUCTURE:
* Rename
* Replace
* Remember
* Inversion
*)









(* Rename *)



Tactic Notation "ren"
  "-" ident(In1)
  ":" ident(Io1)
 :=
  rename Io1 into In1.

Tactic Notation "ren"
  "-" ident(In1) ident(In2)
  ":" ident(Io1) ident(Io2)
 :=
  ren - In1: Io1;
  rename Io2 into In2.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3)
  ":" ident(Io1) ident(Io2) ident(Io3)
 :=
  ren - In1 In2: Io1 Io2;
  rename Io3 into In3.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4)
 :=
  ren - In1 In2 In3: Io1 Io2 Io3;
  rename Io4 into In4.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
 :=
  ren - In1 In2 In3 In4: Io1 Io2 Io3 Io4;
  rename Io5 into In5.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      ident(Io6)
 :=
  ren - In1 In2 In3 In4 In5: Io1 Io2 Io3 Io4 Io5;
  rename Io6 into In6.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      ident(Io6) ident(Io7)
 :=
  ren - In1 In2 In3 In4 In5 In6: Io1 Io2 Io3 Io4 Io5 Io6;
  rename Io7 into In7.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7) ident(In8)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      ident(Io6) ident(Io7) ident(Io8)
 :=
  ren - In1 In2 In3 In4 In5 In6 In7: Io1 Io2 Io3 Io4 Io5 Io6 Io7;
  rename Io8 into In8.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7) ident(In8) ident(In9)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      ident(Io6) ident(Io7) ident(Io8) ident(Io9)
 :=
  ren - In1 In2 In3 In4 In5 In6 In7 In8: Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8;
  rename Io9 into In9.

Tactic Notation "ren"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":" ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
 :=
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
    Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9;
  rename Io10 into In10.









(* Replace *)



Tactic Notation "rep"
  "-" constr(Cn1)
  ":" constr(Co1)
 :=
  replace Co1 with Cn1.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2)
  ":" constr(Co1) constr(Co2)
 :=
  rep - Cn1: Co1;
  replace Co2 with Cn2.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3)
  ":" constr(Co1) constr(Co2) constr(Co3)
 :=
  rep - Cn1 Cn2: Co1 Co2;
  replace Co3 with Cn3.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rep - Cn1 Cn2 Cn3: Co1 Co2 Co3;
  replace Co4 with Cn4.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rep - Cn1 Cn2 Cn3 Cn4: Co1 Co2 Co3 Co4;
  replace Co5 with Cn5.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
      constr(Cn6)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5: Co1 Co2 Co3 Co4 Co5;
  replace Co6 with Cn6.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
      constr(Cn6) constr(Cn7)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6: Co1 Co2 Co3 Co4 Co5 Co6;
  replace Co7 with Cn7.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
      constr(Cn6) constr(Cn7) constr(Cn8)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7) constr(Co8)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6 Cn7: Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  replace Co8 with Cn8.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
      constr(Cn6) constr(Cn7) constr(Cn8) constr(Cn9)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6 Cn7 Cn8: Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  replace Co9 with Cn9.

Tactic Notation "rep"
  "-" constr(Cn1) constr(Cn2) constr(Cn3) constr(Cn4) constr(Cn5)
      constr(Cn6) constr(Cn7) constr(Cn8) constr(Cn9) constr(Cn10)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7) constr(Co8) constr(Co9) constr(Co10)
 :=
  rep - Cn1 Cn2 Cn3 Cn4 Cn5 Cn6 Cn7 Cn8 Cn9:
    Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9;
  replace Co10 with Cn10.









(* Remember *)



Tactic Notation "rem"
  "-" ident(In1)
  ":" constr(Co1)
 :=
  remember Co1 as In1.

Tactic Notation "rem"
  "-" ident(In1) ident(In2)
  ":" constr(Co1) constr(Co2)
 :=
  rem - In1: Co1;
  remember Co2 as In2.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3)
  ":" constr(Co1) constr(Co2) constr(Co3)
 :=
  rem - In1 In2: Co1 Co2;
  remember Co3 as In3.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4)
 :=
  rem - In1 In2 In3: Co1 Co2 Co3;
  remember Co4 as In4.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
 :=
  rem - In1 In2 In3 In4: Co1 Co2 Co3 Co4;
  remember Co5 as In5.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6)
 :=
  rem - In1 In2 In3 In4 In5: Co1 Co2 Co3 Co4 Co5;
  remember Co6 as In6.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7)
 :=
  rem - In1 In2 In3 In4 In5 In6: Co1 Co2 Co3 Co4 Co5 Co6;
  remember Co7 as In7.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7) ident(In8)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7) constr(Co8)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7: Co1 Co2 Co3 Co4 Co5 Co6 Co7;
  remember Co8 as In8.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7) ident(In8) ident(In9)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
      constr(Co6) constr(Co7) constr(Co8) constr(Co9)
 :=
  rem - In1 In2 In3 In4 In5 In6 In7 In8: Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8;
  remember Co9 as In9.

Tactic Notation "rem"
  "-" ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  ":" constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
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
  rem - In1: Co1 as Ia1;
  remember Co2 as In2 eqn:Ia2.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3)
  ":"   constr(Co1) constr(Co2) constr(Co3)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3)
 :=
  rem - In1 In2: Co1 Co2 as Ia1 Ia2;
  remember Co3 as In3 eqn:Ia3.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4)
 :=
  rem - In1 In2 In3: Co1 Co2 Co3 as Ia1 Ia2 Ia3;
  remember Co4 as In4 eqn:Ia4.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
 :=
  rem - In1 In2 In3 In4: Co1 Co2 Co3 Co4 as Ia1 Ia2 Ia3 Ia4;
  remember Co5 as In5 eqn:Ia5.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6)
 :=
  rem - In1 In2 In3 In4 In5: Co1 Co2 Co3 Co4 Co5 as Ia1 Ia2 Ia3 Ia4 Ia5;
  remember Co6 as In6 eqn:Ia6.

Tactic Notation "rem"
  "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   constr(Co1) constr(Co2) constr(Co3) constr(Co4) constr(Co5)
        constr(Co6) constr(Co7)
  "as"  ident(Ia1) ident(Ia2) ident(Ia3) ident(Ia4) ident(Ia5)
        ident(Ia6) ident(Ia7)
 :=
  rem - In1 In2 In3 In4 In5 In6: Co1 Co2 Co3 Co4 Co5 Co6
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
  rem - In1 In2 In3 In4 In5 In6 In7: Co1 Co2 Co3 Co4 Co5 Co6 Co7
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
  rem - In1 In2 In3 In4 In5 In6 In7 In8: Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8
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
  rem - In1 In2 In3 In4 In5 In6 In7 In8 In9: Co1 Co2 Co3 Co4 Co5 Co6 Co7 Co8 Co9
    as Ia1 Ia2 Ia3 Ia4 Ia5 Ia6 Ia7 Ia8 Ia9;
  remember Co10 as In10 eqn:Ia10.









(* Inversion *)



Tactic Notation "ivr"
  "-" hyp(H)
  :=
  inversion H.

Tactic Notation "ivs"
  "-" hyp(H)
  :=
  inversion H;
  subst.

Tactic Notation "ivc"
  "-" hyp(H)
  :=
  inversion H;
  clear H;
  clear_refl.



Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1)
  ":"   ident(Io1)
  :=
  ivc - H;
  ren - In1: Io1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2)
  ":"   ident(Io1) ident(Io2)
  :=
  ivc - H;
  ren - In1 In2: Io1 Io1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  ":"   ident(Io1) ident(Io2) ident(Io3)
  :=
  ivc - H;
  ren - In1 In2 In3: Io1 Io2 Io3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4: Io1 Io2 Io3 Io4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5: Io1 Io2 Io3 Io4 Io5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6: Io1 Io2 Io3 Io4 Io5 Io6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7: Io1 Io2 Io3 Io4 Io5 Io6 Io7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
        ident(Io6) ident(Io7) ident(Io8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8: Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

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
  "-"   hyp(H')
  "as"  ident(In1)
  :=
  ivc - H';
  ren - In1: H.

Tactic Notation "ivc"
  "-"   hyp(H')
  "as"  ident(In1) ident(In2)
  :=
  ivc - H';
  ren - In1 In2: H H0.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3)
  :=
  ivc - H;
  ren - In1 In2 In3: H H0 H1.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4)
  :=
  ivc - H;
  ren - In1 In2 In3 In4: H H0 H1 H2.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5: H H0 H1 H2 H3.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6: H H0 H1 H2 H3 H4.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7: H H0 H1 H2 H3 H4 H5.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8: H H0 H1 H2 H3 H4 H5 H6.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9: H H0 H1 H2 H3 H4 H5 H6 H7.

Tactic Notation "ivc"
  "-"   hyp(H)
  "as"  ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
        ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
  :=
  ivc - H;
  ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10: H H0 H1 H2 H3 H4 H5 H6 H7 H8.