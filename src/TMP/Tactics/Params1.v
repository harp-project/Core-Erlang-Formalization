(** DOCUMENTATION:
* exa - exact       - hyp
* inj - injection   - hyp
* app - apply       - constr {in hyp}
* epp - eapply      - constr
* bpp - by apply    - constr
* ass - assert      constr {as ident} {by tactic} | as ident {by tactic}: constr
                    constr {as ident} {: tactic}  | as ident {: tactic}: constr
* des - destruct    - constr {as {pattern} {ident}} {by tactic}
                    - constr {as {pattern} {ident}} {: tactic {| tactic}}
* ind - induction   - constr {: pattern} {by tactic}
                    - constr {: pattern} {: tactic {| tactic}}
                    + constr - constr {: pattern}
*)



(** STRUCTURE:
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

Tactic Notation "inj"
  "-"   hyp(H)
  "as"  ident(I)
  :=
  injection H as I.






(* Apply *)

Tactic Notation "app"
  "-" constr(C)
  :=
  apply C.

Tactic Notation "app"
  "-"   constr(C)
  "in"  hyp(H)
  :=
  apply C in H.

Tactic Notation "epp"
  "-" constr(C)
  :=
  eapply C.

Tactic Notation "bpp"
  "-" constr(C)
  :=
  apply C;
  auto.






(* Assert *)

Tactic Notation "ass"
  constr(C)
  :=
  assert C.

Tactic Notation "ass"
        constr(C)
  "as"  ident(I)
  :=
  assert C as I.

Tactic Notation "ass"
        constr(C)
  "as"  ident(I)
  "by"  tactic(T)
  :=
  assert C as I by T.

Tactic Notation "ass"
        constr(C)
  "as"  ident(I)
  ":"   tactic(T)
  :=
  assert C as I by T.

Tactic Notation "ass"
        constr(C)
  "by"  tactic(T)
  :=
  assert C by T.

Tactic Notation "ass"
  "as"  ident(I)
  ":"   constr(C)
  :=
  assert C as I.

Tactic Notation "ass"
  "as"  ident(I)
  "by"  tactic(T)
  ":"   constr(C)
  :=
  assert C as I by T.

Tactic Notation "ass"
  "as"  ident(I)
  ":"   tactic(T)
  ":"   constr(C)
  :=
  assert C by T.






(* Destruct *)

Tactic Notation "des"
  "-" constr(C)
  :=
  destruct C.

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  :=
  destruct C as P.

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
        ident(I)
  :=
  destruct C as P eqn:I.

Tactic Notation "des"
  "-"   constr(C)
  "as"  ident(I)
  :=
  destruct C eqn:I.

Tactic Notation "des"
  "-"   constr(C)
  "by"  tactic(T)
  :=
  destruct C;
  [T | ..].

Tactic Notation "des"
  "-" constr(C)
  ":" tactic(T)
  :=
  destruct C;
  [T | ..].

Tactic Notation "des"
  "-" constr(C)
  ":" tactic(T)
  "|" tactic(Ta)
  :=
  destruct C;
  [T | ..];
  [> Ta ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  "by"  tactic(T)
  :=
  destruct C as P;
  [T | ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  ":"   tactic(T)
  :=
  destruct C as P;
  [T | ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  ":"   tactic(T)
  "|"   tactic(Ta)
  :=
  destruct C as P;
  [T | ..];
  [> Ta ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
        ident(I)
  "by"  tactic(T)
  :=
  destruct C as P eqn:I;
  [T | ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
        ident(I)
  ":"   tactic(T)
  :=
  destruct C as P eqn:I;
  [T | ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  simple_intropattern(P)
        ident(I)
  ":"   tactic(T)
  "|"   tactic(Ta)
  :=
  destruct C as P eqn:I;
  [T | ..];
  [> Ta ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  ident(I)
  "by"  tactic(T)
  :=
  destruct C eqn:I;
  [T | ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  ident(I)
  ":"   tactic(T)
  :=
  destruct C eqn:I;
  [T | ..].

Tactic Notation "des"
  "-"   constr(C)
  "as"  ident(I)
  ":"   tactic(T)
  "|"   tactic(Ta)
  :=
  destruct C eqn:I;
  [T | ..];
  [> Ta ..].






(* Induction *)

Tactic Notation "ind"
  "-" constr(C)
  :=
  induction C.

Tactic Notation "ind"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  :=
  induction C as P.

Tactic Notation "ind"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  "by"  tactic(T)
  :=
  induction C as P;
  [T | ..].

Tactic Notation "ind"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  ":"   tactic(T)
  :=
  induction C as P;
  [T | ..].

Tactic Notation "ind"
  "-"   constr(C)
  "as"  simple_intropattern(P)
  ":"   tactic(T)
  "|"   tactic(Ta)
  :=
  induction C as P;
  [T | ..];
  [> Ta ..].

Tactic Notation "ind"
  "-"   constr(C)
  "by"  tactic(T)
  :=
  induction C;
  [T | ..].

Tactic Notation "ind"
  "-" constr(C)
  ":" tactic(T)
  :=
  induction C;
  [T | ..].

Tactic Notation "ind"
  "-" constr(C)
  ":" tactic(T)
  "|"   tactic(Ta)
  :=
  induction C;
  [T | ..];
  [> Ta ..].

Tactic Notation "ind"
  "+" constr(Cu)
  "-" constr(Ci)
  :=
  induction Ci using Cu.

Tactic Notation "ind"
  "+"   constr(Cu)
  "-"   constr(Ci)
  "as"  simple_intropattern(P)
  :=
  induction Ci as P using Cu.