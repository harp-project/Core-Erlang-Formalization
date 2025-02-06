From CoreErlang.Eqvivalence.Tactics Require Import T3ParamMultiple.



(** STRUCTURE:
* Specialize
* Pose Proof
* Rewrite Right
* Rewrite Left
*)



(** DOCUMENTATION:

* spe   -->   specialize
              - hyp {as ident}: [constr]:1-20
              + hyp as ident: [constr]:1-20

* spe_rfl-->  specialize (eq_refl)
              - [hyp]:1-5


* pse   -->   pose proof
              - constr {as ident}: [constr]:1-20



* rwr   -->   rewrite ->
              - [constr]:1-10
              - [constr]:1-10 in *
              - [constr]:1-10 in [hyp]:1-5
              + [constr]:1-10 in [hyp]:1-5

* rwl   -->   rewrite <-
              - [constr]:1-10
              - [constr]:1-10 in *
              - [constr]:1-10 in [hyp]:1-5
              + [constr]:1-10 in [hyp]:1-5
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// SPECIALIZE ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



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









Tactic Notation "spe_rfl"
  "-"   hyp(H1)
  :=
  specialize (H1 eq_refl).

Tactic Notation "spe_rfl"
  "-"   hyp(H1) hyp(H2)
  :=
  specialize (H1 eq_refl);
  specialize (H2 eq_refl).

Tactic Notation "spe_rfl"
  "-"   hyp(H1) hyp(H2) hyp(H3)
  :=
  specialize (H1 eq_refl);
  specialize (H2 eq_refl);
  specialize (H3 eq_refl).

Tactic Notation "spe_rfl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4)
  :=
  specialize (H1 eq_refl);
  specialize (H2 eq_refl);
  specialize (H3 eq_refl);
  specialize (H4 eq_refl).

Tactic Notation "spe_rfl"
  "-"   hyp(H1) hyp(H2) hyp(H3) hyp(H4) hyp(H5)
  :=
  specialize (H1 eq_refl);
  specialize (H2 eq_refl);
  specialize (H3 eq_refl);
  specialize (H4 eq_refl);
  specialize (H5 eq_refl).












(*
////////////////////////////////////////////////////////////////////////////////
//// POSE_PROOF ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



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












(*
////////////////////////////////////////////////////////////////////////////////
//// REWRITE_RIGHT /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



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












(*
////////////////////////////////////////////////////////////////////////////////
//// REWRITE_LEFT //////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



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