From CoreErlang.TMP.Tactics Require Export ParamsN.



(** STRUCTURE:
* Specialize
* Pose Proof
* Rewrite Right
* Rewrite Left
*)



(** DOCUMENTATION:

* spe - specialize
  - hyp {as ident}: [constr]:1-20
  + hyp as ident: [constr]:1-20

* spc - specialize; clear
  - hyp {as ident}: [constr]:1-20
  + hyp as ident: [constr]:1-20

* bpe - by specialize
  - hyp: [constr]:1-20

* ape - by specialize; auto
  - hyp: [constr]:1-20

* pse - pose proof
  - constr {as ident}: [constr]:1-20

* psc - pose proof; clear
  - constr {as ident}: [constr]:1-20


* ese - epose proof
  - constr {as ident}: [constr]:1-20

* esc - epose proof; clear
  - constr {as ident}: [constr]:1-20

* bse - by pose proof
  - constr: [constr]:1-20

* ase - by pose proof; auto
  - constr: [constr]:1-20

* rwr - rewrite ->
  - [constr]:1-10
  - [constr]:1-10 in *
  - [constr]:1-10 in [hyp]:1-5
  + [constr]:1-10 in [hyp]:1-5

* cwr - rewrite ->; clear
  - [constr]:1-10
  - [constr]:1-10 in *
  - [constr]:1-10 in [hyp]:1-5
  + [constr]:1-10 in [hyp]:1-5

* bwr - by rewrite ->
  - [constr]:1-10

* awr - by rewrite ->; auto
  - [constr]:1-10

* rwl - rewrite <-
  - [constr]:1-10
  - [constr]:1-10 in *
  - [constr]:1-10 in [hyp]:1-5
  + [constr]:1-10 in [hyp]:1-5

* cwl - rewrite <-; clear
  - [constr]:1-10
  - [constr]:1-10 in *
  - [constr]:1-10 in [hyp]:1-5
  + [constr]:1-10 in [hyp]:1-5

* bwl - by rewrite <-
  - [constr]:1-10

* awl - by rewrite <-; auto
  - [constr]:1-10
*)












(* Specialize *)



Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1)
  :=
  specialize (H C1).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19).

Tactic Notation "spe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20).






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
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17)
    as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18)
    as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19) as I;
  clear H.

Tactic Notation "spe"
  "-"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20) as I;
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

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17)
    as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18)
    as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19) as I.

Tactic Notation "spe"
  "+"   hyp(H)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20) as I.









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









Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1)
  :=
  specialize (H C1);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19);
  solve [trivial].

Tactic Notation "bpe"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20);
  solve [trivial].









Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1)
  :=
  specialize (H C1);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2)
  :=
  specialize (H C1 C2);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  specialize (H C1 C2 C3);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  specialize (H C1 C2 C3 C4);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  specialize (H C1 C2 C3 C4 C5);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  specialize (H C1 C2 C3 C4 C5 C6);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19);
  solve [auto].

Tactic Notation "ape"
  "-"   hyp(H)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  specialize (H C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20);
  solve [auto].












(* Pose Proof *)



Tactic Notation "pse"
  "-"   constr(C)
  :=
  pose proof C.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  pose proof C C1.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  :=
  pose proof C C1 C2.
  
Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19.

Tactic Notation "pse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20.






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

Tactic Notation "pse"
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

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 as I.

Tactic Notation "pse"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20 as I.









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









Tactic Notation "ese"
  "-"   constr(C)
  :=
  epose proof C.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  epose proof C C1.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  :=
  epose proof C C1 C2.
  
Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  epose proof C C1 C2 C3.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  epose proof C C1 C2 C3 C4.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  epose proof C C1 C2 C3 C4 C5.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  epose proof C C1 C2 C3 C4 C5 C6.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19.

Tactic Notation "ese"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20.






Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  :=
  epose proof C as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  epose proof C C1 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  epose proof C C1 C2 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  epose proof C C1 C2 C3 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  epose proof C C1 C2 C3 C4 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  epose proof C C1 C2 C3 C4 C5 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 as I.

Tactic Notation "ese"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20 as I.









Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  epose proof C C1;
  try clear C1.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2)
  :=
  epose proof C C1 C2;
  try clear C1;
  try clear C2.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  epose proof C C1 C2 C3;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  epose proof C C1 C2 C3 C4;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  epose proof C C1 C2 C3 C4 C5;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  epose proof C C1 C2 C3 C4 C5 C6;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9.

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18;
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
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

Tactic Notation "esc"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
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






Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1)
  :=
  epose proof C C1 as I;
  try clear C1.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2)
  :=
  epose proof C C1 C2 as I;
  try clear C1;
  try clear C2.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  epose proof C C1 C2 C3 as I;
  try clear C1;
  try clear C2;
  try clear C3.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  epose proof C C1 C2 C3 C4 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  epose proof C C1 C2 C3 C4 C5 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 as I;
  try clear C1;
  try clear C2;
  try clear C3;
  try clear C4;
  try clear C5;
  try clear C6;
  try clear C7;
  try clear C8;
  try clear C9.

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 as I;
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
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

Tactic Notation "esc"
  "-"   constr(C)
  "as"  ident(I)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  epose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
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









Tactic Notation "bse"
  "-"   constr(C)
  :=
  pose proof C;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  pose proof C C1;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19;
  solve [trivial].

Tactic Notation "bse"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20;
  solve [trivial].










Tactic Notation "ase"
  "-"   constr(C)
  :=
  pose proof C;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1)
  :=
  pose proof C C1;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3)
  :=
  pose proof C C1 C2 C3;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  pose proof C C1 C2 C3 C4;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  pose proof C C1 C2 C3 C4 C5;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  pose proof C C1 C2 C3 C4 C5 C6;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19;
  solve [auto].

Tactic Notation "ase"
  "-"   constr(C)
  ":"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
        constr(C11) constr(C12) constr(C13) constr(C14) constr(C15)
        constr(C16) constr(C17) constr(C18) constr(C19) constr(C20)
  :=
  pose proof C C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18
    C19 C20;
  solve [auto].












(* Rewrite Rigth *)



Tactic Notation "rwr"
  "-"   constr(C1)
  :=
  rewrite -> C1.

Tactic Notation "rwr"
  "-"   constr(C1)
  "in"  "*"
  :=
  rewrite -> C1 in *.

Tactic Notation "rwr"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite -> C1 in H1.

Tactic Notation "rwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1 in H1, H1, H3.

Tactic Notation "rwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1 in H1, H1, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1 in H1, H1, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  :=
  rewrite -> C1, -> C2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  rewrite -> C1, -> C2 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite -> C1, -> C2, -> C3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4, H5.



Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  "*"
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in *.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4.

Tactic Notation "rwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4, H5.






Tactic Notation "rwr"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite -> C1 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1 in H1, H1, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1 in H1, H1, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1 in H1, H1, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4 |- *.

Tactic Notation "rwr"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10 in H1, H2, H3, H4, H5 |- *.









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









Tactic Notation "bwr"
  "-"   constr(C1)
  :=
  rewrite -> C1;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2)
  :=
  rewrite -> C1, -> C2;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite -> C1, -> C2, -> C3;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9;
  solve[trivial].

Tactic Notation "bwr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10;
  solve[trivial].









Tactic Notation "awr"
  "-"   constr(C1)
  :=
  rewrite -> C1;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2)
  :=
  rewrite -> C1, -> C2;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite -> C1, -> C2, -> C3;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9;
  solve[auto].

Tactic Notation "awr"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite -> C1, -> C2, -> C3, -> C4, -> C5,
          -> C6, -> C7, -> C8, -> C9, -> C10;
  solve[auto].












(* Rewrite Left *)



Tactic Notation "rwl"
  "-"   constr(C1)
  :=
  rewrite <- C1.

Tactic Notation "rwl"
  "-"   constr(C1)
  "in"  "*"
  :=
  rewrite <- C1 in *.

Tactic Notation "rwl"
  "-"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite <- C1 in H1.

Tactic Notation "rwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1 in H1, H1, H3.

Tactic Notation "rwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1 in H1, H1, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1 in H1, H1, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  :=
  rewrite <- C1, <- C2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  "in"  "*"
  :=
  rewrite <- C1, <- C2 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite <- C1, <- C2, <- C3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
      constr(C6) constr(C7) constr(C8)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4, H5.



Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  "*"
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in *.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4.

Tactic Notation "rwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4, H5.






Tactic Notation "rwl"
  "+"   constr(C1)
  "in"  hyp(H1)
  :=
  rewrite <- C1 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1 in H1, H1, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1 in H1, H1, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1 in H1, H1, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9 in H1, H2, H3, H4, H5 |- *.



Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4 |- *.

Tactic Notation "rwl"
  "+"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  "in"  hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10 in H1, H2, H3, H4, H5 |- *.









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









Tactic Notation "bwl"
  "-"   constr(C1)
  :=
  rewrite <- C1;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2)
  :=
  rewrite <- C1, <- C2;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite <- C1, <- C2, <- C3;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9;
  solve[trivial].

Tactic Notation "bwl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10;
  solve[trivial].









Tactic Notation "awl"
  "-"   constr(C1)
  :=
  rewrite <- C1;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2)
  :=
  rewrite <- C1, <- C2;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3)
  :=
  rewrite <- C1, <- C2, <- C3;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9;
  solve[auto].

Tactic Notation "awl"
  "-"   constr(C1) constr(C2) constr(C3) constr(C4) constr(C5)
        constr(C6) constr(C7) constr(C8) constr(C9) constr(C10)
  :=
  rewrite <- C1, <- C2, <- C3, <- C4, <- C5,
          <- C6, <- C7, <- C8, <- C9, <- C10;
  solve[auto].