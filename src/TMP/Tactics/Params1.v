(**
DOCUMENTATION:
* exa - exact
* inj - injection
* app - apply
* ass - assert
* des - destruct
* ind - induction
*)



(**
STRUCTURE:
* Exact
* Injection
* Apply
* Assert
* Destruct
* Induction
*)









(* Exact *)

Tactic Notation "exa"
  "-" hyp(H)
  :=
  exact H.






(* Injection *)

Tactic Notation "inj"
  "-" hyp(H)
  :=
  injection H.






(* Apply *)

Tactic Notation "app"
  "-" hyp(H)
  :=
  apply H.

Tactic Notation "app"
  "-"   hyp(H)
  "in"  hyp(Hin)
  :=
  apply H in Hin.

Tactic Notation "eap"
  "-" hyp(H)
  :=
  eapply H.






(* Assert *)

Tactic Notation "ass"
  "-" constr(C)
  :=
  assert C.

Tactic Notation "ass"
  "-"   constr(C)
  "as"  ident(I)
  :=
  assert C as I.

Tactic Notation "ass"
  "-"   constr(C)
  "as"  ident(I)
  "by"  tactic(T)
  :=
  assert C as I by T.

Tactic Notation "ass"
  "-"   constr(C)
  "by"  tactic(T)
  :=
  assert C by T.

Tactic Notation "ass"
  "-" ident(I)
  ":" constr(C)
  :=
  assert C as I.

Tactic Notation "ass"
  "-"   ident(I)
  "by"  tactic(T)
  ":"   constr(C)
  :=
  assert C as I by T.






(* Destruct *)

Tactic Notation "des"
  "-" constr(C)
  :=
  destruct C.

Tactic Notation "des"
  "-"   constr(C)
  "to"  simple_intropattern(P)
  :=
  destruct C as P.

Tactic Notation "des"
  "-"   constr(C)
  "to"  simple_intropattern(P)
  "as"  ident(I)
  :=
  destruct C as P eqn:I.

Tactic Notation "des"
  "-"   constr(C)
  "as"  ident(I)
  :=
  destruct C eqn:I.






(* Induction *)

Tactic Notation "ind"
  "-" constr(C)
  :=
  induction C.

Tactic Notation "ind"
  "-"   constr(C)
  "to"  simple_intropattern(P)
  :=
  induction C as P.

Tactic Notation "ind"
  "+" constr(Cu)
  ":" constr(Ci)
  :=
  induction Ci using Cu.

Tactic Notation "ind"
  "+"   constr(Cu)
  ":"   constr(Ci)
  "to"  simple_intropattern(P)
  :=
  induction Ci as P using Cu.