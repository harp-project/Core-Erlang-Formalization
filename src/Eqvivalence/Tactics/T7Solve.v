From CoreErlang.Eqvivalence.Tactics Require Import T2ParamSingle.
From CoreErlang.Eqvivalence.Tactics Require Import T3ParamMultiple.
From CoreErlang.Eqvivalence.Tactics Require Import T4Name.
From CoreErlang.Eqvivalence.Tactics Require Import T5Transform.



(** STRUCTURE:
* Apply
*)



(** DOCUMENTATION:

* bpp   -->   by apply
              - constr {in hyp}
              > constr {in hyp}

* aap   -->   by apply; auto
              - constr {in hyp}
              > constr {in hyp}



* bym   -->   by symmetry

* aym   -->   by symmetry; auto



* bmp   -->   by simpl

* amp   -->   by simpl; auto



* bbn   -->   by cbn

* abn   -->   by cbn; auto



* bvs   -->   by inversion; subst
              - [hyp]:1-10

* avs   -->   by inversion; subst; auto
              - [hyp]:1-10



* bpe   -->   by specialize
              - hyp: [constr]:1-20

* ape   -->   by specialize; auto
              - hyp: [constr]:1-20



* bse   -->   by pose proof
              - constr: [constr]:1-20

* ase   -->   by pose proof; auto
              - constr: [constr]:1-20



* bwr   -->   by rewrite ->
              - [constr]:1-10

* awr   -->   by rewrite ->; auto
              - [constr]:1-10


* bwl   -->   by rewrite <-
              - [constr]:1-10

* awl   -->   by rewrite <-; auto
              - [constr]:1-10
*
*)















(*
////////////////////////////////////////////////////////////////////////////////
//// APPLY /////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Tactic Notation "bpp"
  "-"   constr(C)
  :=
  apply C;
  solve [trivial].

Tactic Notation "bpp"
  "-"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H;
  solve [trivial].

Tactic Notation "bpp"
  ">"   constr(C)
  :=
  apply C;
  solve [trivial].

Tactic Notation "bpp"
  ">"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H;
  solve [trivial].






Tactic Notation "aap"
  "-"   constr(C)
  :=
  apply C;
  solve [auto].

Tactic Notation "aap"
  "-"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H;
  solve [auto].

Tactic Notation "aap"
  ">"   constr(C)
  :=
  apply C;
  solve [auto].

Tactic Notation "aap"
  ">"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H;
  solve [auto].















(*
////////////////////////////////////////////////////////////////////////////////
//// SYMMETRY //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Ltac bym := sym; solve [trivial].

Ltac aym := sym; solve [auto].















(*
////////////////////////////////////////////////////////////////////////////////
//// SIMPLIFY //////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "bmp"
  :=
  smp;
  solve [trivial].

Tactic Notation "bmp"
  "-"   hyp(H1)
  :=
  smp - H1;
  solve [trivial].

Tactic Notation "bmp"
  "*"
  :=
  smp *;
  solve [trivial].



Tactic Notation "amp"
  :=
  smp;
  solve [auto].

Tactic Notation "amp"
  "-"   hyp(H1)
  :=
  smp - H1;
  solve [auto].

Tactic Notation "amp"
  "*"
  :=
  smp *;
  solve [auto].









(*
////////////////////////////////////////////////////////////////////////////////
//// CBN ///////////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Tactic Notation "bbn"
  :=
  sbn;
  solve [trivial].

Tactic Notation "bbn"
  "-"   hyp(H1)
  :=
  sbn - H1;
  solve [trivial].

Tactic Notation "bbn"
  "*"
  :=
  sbn *;
  solve [trivial].



Tactic Notation "abn"
  :=
  sbn;
  solve [auto].

Tactic Notation "abn"
  "-"   hyp(H1)
  :=
  sbn - H1;
  solve [auto].

Tactic Notation "abn"
  "*"
  :=
  sbn *;
  solve [auto].















(*
////////////////////////////////////////////////////////////////////////////////
//// INVERSION /////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









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















(*
////////////////////////////////////////////////////////////////////////////////
//// SPECIALIZE ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









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















(*
////////////////////////////////////////////////////////////////////////////////
//// POSE_PROOF ////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









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
  ":"   constr(C1) constr(C2)
  :=
  pose proof C C1 C2;
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















(*
////////////////////////////////////////////////////////////////////////////////
//// REWRITE ///////////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)









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