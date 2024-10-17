Require Import stdpp.list.



(** STRUCTURE:
* Injection
* Exact
* Apply
* Assert
* Destruct
* Induction
* Constructor
* Transitivity
* Case Match
*)



(** DOCUMENTATION:

* inj --> injection
  - constr {as ident}

* exa --> exact
  - constr

* eea --> eexact
  - constr

* app --> apply
  - constr {as ident} {in hyp}
  + constr as ident in hyp
  - contr in hyp as ident
  + contr in hyp as ident
  - constr [|N: tactic]:1-5
  - constr : tactic [| tactic]:1-4
  - constr :- tactic [|- tactic]:1-4
  - constr : tactic |> tactic
  - constr : tactic [|- tactic]:1-4 |> tactic
  > constr {as ident} {in hyp}
  < constr as ident in hyp
  > contr in hyp as ident
  < contr in hyp as ident
  > constr [|N: tactic]:1-5
  > constr : tactic [| tactic]:1-4
  > constr :- tactic [|- tactic]:1-4
  > constr : tactic |> tactic
  > constr : tactic [|- tactic]:1-4 |> tactic

* epp --> eapply
  - constr {as ident} {in hyp}
  + constr as ident in hyp
  - contr in hyp as ident
  + contr in hyp as ident
  - constr [|N: tactic]:1-5
  - constr : tactic [| tactic]:1-4
  - constr :- tactic [|- tactic]:1-4
  - constr : tactic |> tactic
  - constr : tactic [|- tactic]:1-4 |> tactic
  > constr {as ident} {in hyp}
  < constr as ident in hyp
  > contr in hyp as ident
  < contr in hyp as ident
  > constr [|N: tactic]:1-5
  > constr : tactic [| tactic]:1-4
  > constr :- tactic [|- tactic]:1-4
  > constr : tactic |> tactic
  > constr : tactic [|- tactic]:1-4 |> tactic

* bpp --> by apply
  - constr {in hyp}
  > constr {in hyp}

* aap --> by apply; auto
  - constr {in hyp}
  > constr {in hyp}

* ass --> assert
  > constr {as ident} {by tactic}
  > constr {as ident} {: tactic}
  - as ident > constr {by tactic}
  - as ident > constr {: tactic}
  - as ident by tactic > constr
  - as ident : tactic > constr
  - by tactic > constr
  - : tactic > constr

* des --> destruct
  - ident {as {simple_intropattern} {ident}} {: tactic {|> tactic}}
  - ident {as {simple_intropattern} {ident}} {:- tactic {|> tactic}}
  - ident {as {simple_intropattern} {ident}} {:> tactic}
  > constr {as {simple_intropattern} {ident}} {: tactic {|> tactic}}
  > constr {as {simple_intropattern} {ident}} {:- tactic {|> tactic}}
  > constr {as {simple_intropattern} {ident}} {:> tactic}

* ind --> induction
  - ident {as simple_intropattern} {: tactic {|> tactic}}
  - ident {as simple_intropattern} {:- tactic {|> tactic}}
  - ident {as simple_intropattern} {:> tactic}
  + constr - ident {: tactic {|> tactic}}
  + constr - ident {:- tactic {|> tactic}}
  + constr - ident {:> tactic}
  > constr {as simple_intropattern} {: tactic {|> tactic}}
  > constr {as simple_intropattern} {:- tactic {|> tactic}}
  > constr {as simple_intropattern} {:> tactic}

* cns --> constructor
  _
  : tactic {|> tactic}
  :- tactic {|> tactic}
  :> tactic

* ens --> econstructor
  _
  : tactic {|> tactic}
  :- tactic {|> tactic}
  :> tactic

* trn --> transitivity
  _
  : tactic {|> tactic}
  :- tactic {|> tactic}
  :> tactic

* ern --> etransitivity
  _
  : tactic {|> tactic}
  :- tactic {|> tactic}
  :> tactic

* cma --> case_match
  _
  |1: tactic {|> tactic}
  |2: tactic {|> tactic}
  : tactic {|> tactic}
  :- tactic {|> tactic}
  :> tactic
*)












(* Injection *)



Tactic Notation "inj"
  "-"   constr(C)
  :=
  injection C.

Tactic Notation "inj"
  "-"   constr(C)
  "as"  ident(I)
  :=
  injection C as I.












(* Exact *)



Tactic Notation "exa"
  "-"   constr(C)
  :=
  exact C.


Tactic Notation "eea"
  "-"   constr(C)
  :=
  eexact C.












(* Apply *)



Tactic Notation "app"
  "-"   constr(C)
  :=
  apply C.

Tactic Notation "app"
  "-"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H.

Tactic Notation "app"
  "-"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  apply C in H as I;
  clear H.

Tactic Notation "app"
  "+"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  apply C in H as I.

Tactic Notation "app"
  "-"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  apply C in H as I;
  clear H.

Tactic Notation "app"
  "+"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  apply C in H as I.

Tactic Notation "app"
  "-"   constr(C)
  "|1:" tactic(T1)
  :=
  apply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  "|5:" tactic(T5)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  ":"   tactic(T1)
  :=
  apply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  "|"   tactic(T5)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  :=
  apply C;
  try solve [T1; trivial].

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial].

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial].

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial].

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial].

Tactic Notation "app"
  "-"   constr(C)
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  apply C;
  [ solve [T1; trivial] ..];
  Ta.

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  Ta.

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  Ta.

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  Ta.

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  Ta.

Tactic Notation "app"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial];
  Ta.



Tactic Notation "app"
  ">"   constr(C)
  :=
  apply C.

Tactic Notation "app"
  ">"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H.

Tactic Notation "app"
  ">"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  apply C in H as I;
  clear H.

Tactic Notation "app"
  "<"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  apply C in H as I.

Tactic Notation "app"
  ">"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  apply C in H as I;
  clear H.

Tactic Notation "app"
  "<"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  apply C in H as I.

Tactic Notation "app"
  ">"   constr(C)
  "|1:" tactic(T1)
  :=
  apply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  "|5:" tactic(T5)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  ":"   tactic(T1)
  :=
  apply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  "|"   tactic(T5)
  :=
  apply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  :=
  apply C;
  try solve [T1; trivial].

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial].

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial].

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial].

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial].

Tactic Notation "app"
  ">"   constr(C)
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  apply C;
  [ solve [T1; trivial] ..];
  Ta.

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  Ta.

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  Ta.

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  Ta.

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  Ta.

Tactic Notation "app"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  "|>"  tactic(Ta)
  :=
  apply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial];
  Ta.






Tactic Notation "epp"
  "-"   constr(C)
  :=
  eapply C.

Tactic Notation "epp"
  "-"   constr(C)
  "in"  hyp(H)
  :=
  eapply C in H.

Tactic Notation "epp"
  "-"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  eapply C in H as I;
  clear H.

Tactic Notation "epp"
  "+"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  eapply C in H as I.

Tactic Notation "epp"
  "-"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  eapply C in H as I;
  clear H.

Tactic Notation "epp"
  "+"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  eapply C in H as I.

Tactic Notation "epp"
  "-"   constr(C)
  "|1:" tactic(T1)
  :=
  eapply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  "|5:" tactic(T5)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  ":"   tactic(T1)
  :=
  eapply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  "|"   tactic(T5)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  :=
  eapply C;
  try solve [T1; trivial].

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial].

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial].

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial].

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial].

Tactic Notation "epp"
  "-"   constr(C)
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  eapply C;
  [ solve [T1; trivial] ..];
  Ta.

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  Ta.

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  Ta.

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  Ta.

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  Ta.

Tactic Notation "epp"
  "-"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial];
  Ta.



Tactic Notation "epp"
  ">"   constr(C)
  :=
  eapply C.

Tactic Notation "epp"
  ">"   constr(C)
  "in"  hyp(H)
  :=
  eapply C in H.

Tactic Notation "epp"
  ">"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  eapply C in H as I;
  clear H.

Tactic Notation "epp"
  "<"   constr(C)
  "as"  ident(I)
  "in"  hyp(H)
  :=
  eapply C in H as I.

Tactic Notation "epp"
  ">"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  eapply C in H as I;
  clear H.

Tactic Notation "epp"
  "<"   constr(C)
  "in"  hyp(H)
  "as"  ident(I)
  :=
  eapply C in H as I.

Tactic Notation "epp"
  ">"   constr(C)
  "|1:" tactic(T1)
  :=
  eapply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  "|1:" tactic(T1)
  "|2:" tactic(T2)
  "|3:" tactic(T3)
  "|4:" tactic(T4)
  "|5:" tactic(T5)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  ":"   tactic(T1)
  :=
  eapply C;
  [ solve [T1; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  ":"   tactic(T1)
  "|"   tactic(T2)
  "|"   tactic(T3)
  "|"   tactic(T4)
  "|"   tactic(T5)
  :=
  eapply C;
  [ solve [T1; trivial]
  | solve [T2; trivial]
  | solve [T3; trivial]
  | solve [T4; trivial]
  | solve [T5; trivial] | ..].

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  :=
  eapply C;
  try solve [T1; trivial].

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial].

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial].

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial].

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial].

Tactic Notation "epp"
  ">"   constr(C)
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  eapply C;
  [ solve [T1; trivial] ..];
  Ta.

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  Ta.

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  Ta.

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  Ta.

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  Ta.

Tactic Notation "epp"
  ">"   constr(C)
  ":-"  tactic(T1)
  "|-"  tactic(T2)
  "|-"  tactic(T3)
  "|-"  tactic(T4)
  "|-"  tactic(T5)
  "|>"  tactic(Ta)
  :=
  eapply C;
  try solve [T1; trivial];
  try solve [T2; trivial];
  try solve [T3; trivial];
  try solve [T4; trivial];
  try solve [T5; trivial];
  Ta.






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












(* Assert *)



Tactic Notation "ass"
  ">"   constr(C)
  :=
  assert C.

Tactic Notation "ass"
  ">"   constr(C)
  "as"  ident(I)
  :=
  assert C as I.

Tactic Notation "ass"
  ">"   constr(C)
  "as"  ident(I)
  "by"  tactic(T)
  :=
  assert C as I by T.

Tactic Notation "ass"
  ">"   constr(C)
  "as"  ident(I)
  ":"   tactic(T)
  :=
  assert C as I;
  [solve [T; trivial] | ..].

Tactic Notation "ass"
  ">"   constr(C)
  "by"  tactic(T)
  :=
  assert C by T.

Tactic Notation "ass"
  ">"   constr(C)
  ":"   tactic(T)
  :=
  assert C;
  [solve [T; trivial] | ..].

Tactic Notation "ass"
  "-"
  "as"  ident(I)
  ">"   constr(C)
  :=
  assert C as I.

Tactic Notation "ass"
  "-"
  "as"  ident(I)
  ">"   constr(C)
  "by"  tactic(T)
  :=
  assert C as I by T.

Tactic Notation "ass"
  "-"
  "as"  ident(I)
  ">"   constr(C)
  ":"   tactic(T)
  :=
  assert C as I;
  [solve [T; trivial] | ..].

Tactic Notation "ass"
  "-"
  "as"  ident(I)
  "by"  tactic(T)
  ">"   constr(C)
  :=
  assert C as I by T.

Tactic Notation "ass"
  "-"
  "as"  ident(I)
  ":"   tactic(T)
  ">"   constr(C)
  :=
  assert C as I;
  [solve [T; trivial] | ..].

Tactic Notation "ass"
  "-"
  "by"  tactic(T)
  ":"   constr(C)
  :=
  assert C by T.

Tactic Notation "ass"
  "-"
  ":"   tactic(T)
  ">"   constr(C)
  :=
  assert C;
  [solve [T; trivial] | ..].












(* Destruct *)



Tactic Notation "des"
  "-"   ident(I)
  :=
  destruct I.

Tactic Notation "des"
  "-"   ident(I)
  ":"   tactic(T)
  :=
  destruct I;
  [ solve [T; trivial] |..].

Tactic Notation "des"
  "-"   ident(I)
  ":-"  tactic(T)
  :=
  destruct I;
  try solve [T; trivial].

Tactic Notation "des"
  "-"   ident(I)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  ":>"  tactic(Ta)
  :=
  destruct I;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  "-"   ident(I)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct I;
  Ta;
  try solve [T; trivial].



Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  :=
  destruct I as SIP.

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  :=
  destruct I as SIP;
  try solve [T; trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  :=
  destruct I as SIP;
  try solve [T; trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I as SIP;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I as SIP;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  :=
  destruct I as SIP;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct I as SIP;
  Ta;
  try solve [T; trivial].



Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  :=
  destruct I eqn:Ieq.

Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  ":"   tactic(T)
  :=
  destruct I eqn:Ieq;
  [ solve [T; trivial] |..].

Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  ":-"  tactic(T)
  :=
  destruct I eqn:Ieq;
  try solve [T; trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I eqn:Ieq;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I eqn:Ieq;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  ":>"  tactic(Ta)
  :=
  destruct I eqn:Ieq;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  ident(Ieq)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct I eqn:Ieq;
  Ta;
  try solve [T; trivial].



Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  :=
  destruct I as SIP eqn:Ieq.

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":"   tactic(T)
  :=
  destruct I as SIP eqn:Ieq;
  [ solve [T; trivial] |..].

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":-"  tactic(T)
  :=
  destruct I as SIP eqn:Ieq;
  try solve [T; trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I as SIP eqn:Ieq;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct I as SIP eqn:Ieq;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":>"  tactic(Ta)
  :=
  destruct I as SIP eqn:Ieq;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  "-"   ident(I)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct I as SIP eqn:Ieq;
  Ta;
  try solve [T; trivial].






Tactic Notation "des"
  ">"   constr(C)
  :=
  destruct C.

Tactic Notation "des"
  ">"   constr(C)
  ":"   tactic(T)
  :=
  destruct C;
  [ solve [T; trivial] |..].

Tactic Notation "des"
  ">"   constr(C)
  ":-"  tactic(T)
  :=
  destruct C;
  try solve [T; trivial].

Tactic Notation "des"
  ">"   constr(C)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  ":>"  tactic(Ta)
  :=
  destruct C;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  ">"   constr(C)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct C;
  Ta;
  try solve [T; trivial].



Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  :=
  destruct C as SIP.

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  :=
  destruct C as SIP;
  try solve [T; trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  :=
  destruct C as SIP;
  try solve [T; trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C as SIP;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C as SIP;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  :=
  destruct C as SIP;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct C as SIP;
  Ta;
  try solve [T; trivial].



Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  :=
  destruct C eqn:Ieq.

Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  ":"   tactic(T)
  :=
  destruct C eqn:Ieq;
  [ solve [T; trivial] |..].

Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  ":-"  tactic(T)
  :=
  destruct C eqn:Ieq;
  try solve [T; trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C eqn:Ieq;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C eqn:Ieq;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  ":>"  tactic(Ta)
  :=
  destruct C eqn:Ieq;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  ident(Ieq)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct C eqn:Ieq;
  Ta;
  try solve [T; trivial].



Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  :=
  destruct C as SIP eqn:Ieq.

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":"   tactic(T)
  :=
  destruct C as SIP eqn:Ieq;
  [ solve [T; trivial] |..].

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":-"  tactic(T)
  :=
  destruct C as SIP eqn:Ieq;
  try solve [T; trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C as SIP eqn:Ieq;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  destruct C as SIP eqn:Ieq;
  try solve [T; trivial];
  Ta.

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":>"  tactic(Ta)
  :=
  destruct C as SIP eqn:Ieq;
  Ta;
  try solve [trivial].

Tactic Notation "des"
  ">"   constr(C)
  "as"  simple_intropattern(SIP) ident(Ieq)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  destruct C as SIP eqn:Ieq;
  Ta;
  try solve [T; trivial].












(* Induction *)



Tactic Notation "ind"
  "-"   ident(I)
  :=
  induction I.

Tactic Notation "ind"
  "-"   ident(I)
  ":"   tactic(T)
  :=
  induction I;
  [ solve [T; trivial] |..].

Tactic Notation "ind"
  "-"   ident(I)
  ":-"  tactic(T)
  :=
  induction I;
  try solve [T; trivial].

Tactic Notation "ind"
  "-"   ident(I)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  induction I;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "ind"
  "-"   ident(I)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  induction I;
  try solve [T; trivial];
  Ta.

Tactic Notation "ind"
  "-"   ident(I)
  ":>"  tactic(Ta)
  :=
  induction I;
  Ta;
  try solve [trivial].

Tactic Notation "ind"
  "-"   ident(I)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  induction I;
  Ta;
  try solve [T; trivial].



Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  :=
  induction I as SIP.

Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  :=
  induction I as SIP;
  try solve [T; trivial].

Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  :=
  induction I as SIP;
  try solve [T; trivial].

Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  induction I as SIP;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  induction I as SIP;
  try solve [T; trivial];
  Ta.

Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  :=
  induction I as SIP;
  Ta;
  try solve [trivial].

Tactic Notation "ind"
  "-"   ident(I)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  induction I as SIP;
  Ta;
  try solve [T; trivial].






Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  :=
  induction I using C.

Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  ":"   tactic(T)
  :=
  induction I using C;
  [ solve [T; trivial] |..].

Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  ":-"  tactic(T)
  :=
  induction I using C;
  try solve [T; trivial].

Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  induction I using C;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  induction I using C;
  try solve [T; trivial];
  Ta.

Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  ":>"  tactic(Ta)
  :=
  induction I using C;
  Ta;
  try solve [trivial].

Tactic Notation "ind"
  "+"   constr(C)
  "-"   ident(I)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  induction I using C;
  Ta;
  try solve [T; trivial].






Tactic Notation "ind"
  ">"   constr(C)
  :=
  induction C.

Tactic Notation "ind"
  ">"   constr(C)
  ":"   tactic(T)
  :=
  induction C;
  [ solve [T; trivial] |..].

Tactic Notation "ind"
  ">"   constr(C)
  ":-"  tactic(T)
  :=
  induction C;
  try solve [T; trivial].

Tactic Notation "ind"
  ">"   constr(C)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  induction C;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "ind"
  ">"   constr(C)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  induction C;
  try solve [T; trivial];
  Ta.

Tactic Notation "ind"
  ">"   constr(C)
  ":>"  tactic(Ta)
  :=
  induction C;
  Ta;
  try solve [trivial].

Tactic Notation "ind"
  ">"   constr(C)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  induction C;
  Ta;
  try solve [T; trivial].



Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  :=
  induction C as SIP.

Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  :=
  induction C as SIP;
  try solve [T; trivial].

Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  :=
  induction C as SIP;
  try solve [T; trivial].

Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":"   tactic(T)
  "|>"  tactic(Ta)
  :=
  induction C as SIP;
  [ solve [T; trivial] |..];
  Ta.

Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":-"  tactic(T)
  "|>"  tactic(Ta)
  :=
  induction C as SIP;
  try solve [T; trivial];
  Ta.

Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  :=
  induction C as SIP;
  Ta;
  try solve [trivial].

Tactic Notation "ind"
  ">"   constr(C)
  "as"  simple_intropattern(SIP)
  ":>"  tactic(Ta)
  ":-"  tactic(T)
  :=
  induction C as SIP;
  Ta;
  try solve [T; trivial].












(* Constructor *)



Tactic Notation "cns"
  :=
  constructor.

Tactic Notation "cns"
  ":"   tactic(T1)
  :=
  constructor;
  [ solve [T1; trivial] |..].

Tactic Notation "cns"
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  constructor;
  [ solve [T1; trivial] |..];
  Ta.

Tactic Notation "cns"
  ":-"  tactic(T1)
  :=
  constructor;
  try solve [T1; trivial].

Tactic Notation "cns"
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  constructor;
  try solve [T1; trivial];
  Ta.

Tactic Notation "cns"
  ":>"  tactic(Ta)
  :=
  constructor;
  Ta;
  try solve [trivial].






Tactic Notation "ens"
  :=
  econstructor.

Tactic Notation "ens"
  ":"   tactic(T1)
  :=
  econstructor;
  [ solve [T1; trivial] |..].

Tactic Notation "ens"
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  econstructor;
  [ solve [T1; trivial] |..];
  Ta.

Tactic Notation "ens"
  ":-"  tactic(T1)
  :=
  econstructor;
  try solve [T1; trivial].

Tactic Notation "ens"
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  econstructor;
  try solve [T1; trivial];
  Ta.

Tactic Notation "ens"
  ":>"  tactic(Ta)
  :=
  econstructor;
  Ta;
  try solve [trivial].












(* Transitivity *)



Tactic Notation "trn"
  :=
  transitivity.

Tactic Notation "trn"
  ":"   tactic(T1)
  :=
  transitivity;
  [ solve [T1; trivial] |..].

Tactic Notation "trn"
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  transitivity;
  [ solve [T1; trivial] |..];
  Ta.

Tactic Notation "trn"
  ":-"  tactic(T1)
  :=
  transitivity;
  try solve [T1; trivial].

Tactic Notation "trn"
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  transitivity;
  try solve [T1; trivial];
  Ta.

Tactic Notation "trn"
  ":>"  tactic(Ta)
  :=
  transitivity;
  Ta;
  try solve [trivial].






Tactic Notation "ern"
  :=
  etransitivity.

Tactic Notation "ern"
  ":"   tactic(T1)
  :=
  etransitivity;
  [ solve [T1; trivial] |..].

Tactic Notation "ern"
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  etransitivity;
  [ solve [T1; trivial] |..];
  Ta.

Tactic Notation "ern"
  ":-"  tactic(T1)
  :=
  etransitivity;
  try solve [T1; trivial].

Tactic Notation "ern"
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  etransitivity;
  try solve [T1; trivial];
  Ta.

Tactic Notation "ern"
  ":>"  tactic(Ta)
  :=
  etransitivity;
  Ta;
  try solve [trivial].












(* Case Match *)



Tactic Notation "cma"
  :=
  case_match.

Tactic Notation "cma"
  "|1:" tactic(T1)
  :=
  case_match;
  [ solve [T1; trivial] |..].

Tactic Notation "cma"
  "|1:" tactic(T1)
  "|>"  tactic(Ta)
  :=
  case_match;
  [ solve [T1; trivial] |..];
  Ta.

Tactic Notation "cma"
  "|2:" tactic(T2)
  :=
  case_match;
  [ idtac | solve [T2; trivial] |..].

Tactic Notation "cma"
  "|2:" tactic(T1)
  "|>"  tactic(Ta)
  :=
  case_match;
  [ idtac | solve [T1; trivial] |..];
  Ta.

Tactic Notation "cma"
  ":"   tactic(T1)
  :=
  case_match;
  [ solve [T1; trivial] |..].

Tactic Notation "cma"
  ":"   tactic(T1)
  "|>"  tactic(Ta)
  :=
  case_match;
  [ solve [T1; trivial] |..];
  Ta.

Tactic Notation "cma"
  ":-"  tactic(T1)
  :=
  case_match;
  try solve [T1; trivial].

Tactic Notation "cma"
  ":-"  tactic(T1)
  "|>"  tactic(Ta)
  :=
  case_match;
  try solve [T1; trivial];
  Ta.

Tactic Notation "cma"
  ":>"  tactic(Ta)
  :=
  case_match;
  Ta;
  try solve [trivial].