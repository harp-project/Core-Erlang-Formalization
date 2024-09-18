From CoreErlang.TMP.Tactics Require Export ParamsN.



(** DOCUMENTATION:
* spe - specialize      - hyp {as ident}: [constr] | + hyp as ident: [constr]
* spc - specialize; clear hyp {as ident}: [constr] | + hyp as ident: [constr]
* bpe - specialize; ato - hyp: [constr]
* pse - pose proof      - constr {as ident}: [constr] | + hyp as ident: [constr]
* psc - pose proof; clear constr {as ident}: [constr] | + hyp as ident: [constr]
* bse - pose proof; ato - constr: [constr]
* rwr - rewrite ->      - [hyp] {in [hyp]} | + [hyp] {in [hyp]} | - [hyp] in *
* cwr - rewrite ->; clear [hyp] {in [hyp]} | + [hyp] {in [hyp]} | - [hyp] in *
* bwr - by rewrite ->   - [hyp]
* rwl - rewrite <-      - [hyp] {in [hyp]} | + [hyp] {in [hyp]} | - [hyp] in *
* cwl - rewrite <-; clear [hyp] {in [hyp]} | + [hyp] {in [hyp]} | - [hyp] in *
* bwl - by rewrite <-   - [hyp]
*)



(** STRUCTURE:
* Specialize
* Pose Proof
* Rewrite Right
* Rewrite Left
*)









(* Specialize *)



Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1)
  :=
  specialize (H C1).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2)
  :=
  specialize (H C1 C2).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9).

Tactic Notation "spe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10).






Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  specialize (H C1) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10) as I;
  clear H.






Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  specialize (H C1) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10) as I.





Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1)
  :=
  specialize (H C1);
  try clear C1.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2)
  :=
  spc - H: C1;
  specialize (H C2);
  try clear C2.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3)
  :=
  spc - H: C1 C2;
  specialize (H C3);
  try clear C3.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  spc - H: C1 C2 C3;
  specialize (H C4);
  try clear C4.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  spc - H: C1 C2 C3 C4;
  specialize (H C5);
  try clear C5.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  spc - H: C1 C2 C3 C4 C5;
  specialize (H C6);
  try clear C6.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  spc - H: C1 C2 C3 C4 C5 C6;
  specialize (H C7);
  try clear C7.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7;
  specialize (H C8);
  try clear C8.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8;
  specialize (H C9);
  try clear C9.

Tactic Notation "spc"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  spc - H: C1 C2 C3 C4 C5 C6 C7 C8 C9;
  specialize (H C10);
  try clear C10.






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






Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1)
  :=
  specialize (H C1);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2)
  :=
  specialize (H C1 C2);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9);
  auto.

Tactic Notation "bpe"
  "-" hyp(H)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10);
  auto.









(* Pose Proof *)



Tactic Notation "pse"
  "-" constr(C)
  :=
  pose proof C.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1)
  :=
  pose proof C C1.

Tactic Notation "spe"
  "-" constr(C)
  ":" constr(C1) constr(C2)
  :=
  pose proof C C1 C2.
  
Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "pse"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.




Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  :=
  pose proof C as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  pose proof C C1 as I.

Tactic Notation "spe"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  pose proof C C1 C2 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 as I.






Tactic Notation "psc"
  "-" constr(C)
  ":" constr(C1)
  :=
  pose proof C C1;
  try clear C1.

Tactic Notation "psc"
  "-" constr(C)
  ":" constr(C1) constr(C2)
  :=
  pose proof C C1 C2;
  try clear C1;
  try clear C2.

Tactic Notation "psc"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "psc"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "psc"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "psc"
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
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
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
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
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
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
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
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
  "-" constr(C)
  ":" constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
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






Tactic Notation "bse"
  "-"   constr(C)
  :=
  pose proof C;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  pose proof C C1;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9;
  auto.

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10;
  auto.









(* Rewrite Rigth *)




Tactic Notation "rwr"
  "-" hyp(H1)
  :=
  rewrite -> H1.

Tactic Notation "rwr"
  "-"   hyp(H1)
  "in"  "*"
  :=
  rewrite -> H1 in *.

Tactic Notation "rwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1 in Hi1.

Tactic Notation "rwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1 in Hi1, Hi2.

Tactic Notation "rwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1 in Hi1, Hi1, Hi3.

Tactic Notation "rwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1 in Hi1, Hi1, Hi3, Hi4.

Tactic Notation "rwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1 in Hi1, Hi1, Hi3, Hi4, Hi5.



Tactic Notation "rwr"
  "-" hyp(H1) hyp(H2)
  :=
  rewrite -> H1, -> H2.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2)
  "in"  "*"
  :=
  rewrite -> H1, -> H2 in *.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2 in Hi1.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4, Hi5.



Tactic Notation "rwr"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> H1, -> H2, -> H3.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  "*"
  :=
  rewrite -> H1, -> H2, -> H3 in *.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4, Hi5.



Tactic Notation "rwr"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  "*"
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in *.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4, Hi5.



Tactic Notation "rwr"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  "*"
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in *.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4, Hi5.






Tactic Notation "rwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1 in Hi1 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1 in Hi1, Hi2 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1 in Hi1, Hi1, Hi3 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1 in Hi1, Hi1, Hi3, Hi4 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1 in Hi1, Hi1, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2 in Hi1 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.









Tactic Notation "cwr"
  "-" hyp(H1)
  :=
  rewrite -> H1;
  clear H1.

Tactic Notation "cwr"
  "-"   hyp(H1)
  "in"  "*"
  :=
  rewrite -> H1 in *;
  clear H1.

Tactic Notation "cwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1 in Hi1;
  clear H1.

Tactic Notation "cwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1 in Hi1, Hi2;
  clear H1.

Tactic Notation "cwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1 in Hi1, Hi2, Hi3;
  clear H1.

Tactic Notation "cwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1 in Hi1, Hi2, Hi3, Hi4;
  clear H1.

Tactic Notation "cwr"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1.



Tactic Notation "cwr"
  "-" hyp(H1) hyp(H2)
  :=
  rewrite -> H1, -> H2;
  clear H1 H2.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2)
  "in"  "*"
  :=
  rewrite -> H1, -> H2 in *;
  clear H1 H2.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2 in Hi1;
  clear H1 H2.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2;
  clear H1 H2.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3;
  clear H1 H2.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2.



Tactic Notation "cwr"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> H1, -> H2, -> H3;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  "*"
  :=
  rewrite -> H1, -> H2, -> H3 in *;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3.



Tactic Notation "cwr"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  "*"
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in *;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4.



Tactic Notation "cwr"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  "*"
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4 H5.






Tactic Notation "cwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1 in Hi1 |- *;
  clear H1.

Tactic Notation "cwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1 in Hi1, Hi2 |- *;
  clear H1.

Tactic Notation "cwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1 in Hi1, Hi2, Hi3 |- *;
  clear H1.

Tactic Notation "cwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1.

Tactic Notation "cwr"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1.



Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2 in Hi1 |- *;
  clear H1 H2.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2 |- *;
  clear H1 H2.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2.



Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1 |- *;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2 |- *;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3.



Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4.



Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwr"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4 H5.








Tactic Notation "bwr"
  "-" hyp(H1)
  :=
  rewrite -> H1;
  auto.

Tactic Notation "bwr"
  "-" hyp(H1) hyp(H2)
  :=
  rewrite -> H1, -> H2;
  auto.

Tactic Notation "bwr"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> H1, -> H2, -> H3;
  auto.

Tactic Notation "bwr"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4;
  auto.

Tactic Notation "bwr"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> H1, -> H2, -> H3, -> H4, -> H5;
  auto.









(* Rewrite Left *)




Tactic Notation "rwl"
  "-" hyp(H1)
  :=
  rewrite <- H1.

Tactic Notation "rwl"
  "-"   hyp(H1)
  "in"  "*"
  :=
  rewrite <- H1 in *.

Tactic Notation "rwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1 in Hi1.

Tactic Notation "rwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1 in Hi1, Hi2.

Tactic Notation "rwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1 in Hi1, Hi1, Hi3.

Tactic Notation "rwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1 in Hi1, Hi1, Hi3, Hi4.

Tactic Notation "rwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1 in Hi1, Hi1, Hi3, Hi4, Hi5.



Tactic Notation "rwl"
  "-" hyp(H1) hyp(H2)
  :=
  rewrite <- H1, <- H2.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2)
  "in"  "*"
  :=
  rewrite <- H1, <- H2 in *.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2 in Hi1.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4, Hi5.



Tactic Notation "rwl"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- H1, <- H2, <- H3.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  "*"
  :=
  rewrite <- H1, <- H2, <- H3 in *.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4, Hi5.



Tactic Notation "rwl"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  "*"
  :=
  rewrite <- H1, -> H2, <- H3, <- H4 in *.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4, Hi5.



Tactic Notation "rwl"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  "*"
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in *.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4.

Tactic Notation "rwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4, Hi5.






Tactic Notation "rwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1 in Hi1 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1 in Hi1, Hi2 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1 in Hi1, Hi1, Hi3 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1 in Hi1, Hi1, Hi3, Hi4 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1 in Hi1, Hi1, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2 in Hi1 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.



Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4 |- *.

Tactic Notation "rwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *.









Tactic Notation "cwl"
  "-" hyp(H1)
  :=
  rewrite <- H1;
  clear H1.

Tactic Notation "cwl"
  "-"   hyp(H1)
  "in"  "*"
  :=
  rewrite <- H1 in *;
  clear H1.

Tactic Notation "cwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1 in Hi1;
  clear H1.

Tactic Notation "cwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1 in Hi1, Hi2;
  clear H1.

Tactic Notation "cwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1 in Hi1, Hi2, Hi3;
  clear H1.

Tactic Notation "cwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1 in Hi1, Hi2, Hi3, Hi4;
  clear H1.

Tactic Notation "cwl"
  "-"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1.



Tactic Notation "cwl"
  "-" hyp(H1) hyp(H2)
  :=
  rewrite <- H1, <- H2;
  clear H1 H2.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2)
  "in"  "*"
  :=
  rewrite <- H1, <- H2 in *;
  clear H1 H2.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2 in Hi1;
  clear H1 H2.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2;
  clear H1 H2.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3;
  clear H1 H2.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2.



Tactic Notation "cwl"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- H1, <- H2, <- H3;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  "*"
  :=
  rewrite <- H1, <- H2, <- H3 in *;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3.



Tactic Notation "cwl"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  "*"
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in *;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4.



Tactic Notation "cwl"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  "*"
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1 H2 H3 H4 H5.






Tactic Notation "cwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1 in Hi1 |- *;
  clear H1.

Tactic Notation "cwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1 in Hi1, Hi2 |- *;
  clear H1.

Tactic Notation "cwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1 in Hi1, Hi2, Hi3 |- *;
  clear H1.

Tactic Notation "cwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1.

Tactic Notation "cwl"
  "+"   hyp(H1)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1.



Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2 in Hi1 |- *;
  clear H1 H2.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2 |- *;
  clear H1 H2.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2.



Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1 |- *;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2 |- *;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3.



Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4.



Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1 H2 H3 H4 H5.

Tactic Notation "cwl"
  "+"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  "in"  hyp(Hi1) hyp(Hi2) hyp(Hi3) hyp(Hi4) hyp(Hi5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1 H2 H3 H4 H5.








Tactic Notation "bwl"
  "-" hyp(H1)
  :=
  rewrite <- H1;
  auto.

Tactic Notation "bwl"
  "-" hyp(H1) hyp(H2)
  :=
  rewrite <- H1, <- H2;
  auto.

Tactic Notation "bwl"
  "-" hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- H1, <- H2, <- H3;
  auto.

Tactic Notation "bwl"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4;
  auto.

Tactic Notation "bwl"
  "-" hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- H1, <- H2, <- H3, <- H4, <- H5;
  auto.