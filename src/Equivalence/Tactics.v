From CoreErlang Require Export Basics.
Require Export stdpp.list.

(**
NOTES:  Maybe place this in CoreErlang/Tactics
*)



(* SECTION: Shorts *)




Ltac rfl := reflexivity.
Ltac sym := symmetry.
Ltac asm := assumption.
Ltac dis := discriminate.
Ltac con := congruence.
Ltac smp := simpl.
Ltac cns := constructor.
Ltac ecns := econstructor.






(* SECTION: Clear *)



Ltac clear_refl :=
  repeat match goal with
  | H : ?x = ?x |- _ => clear H
  end.






(* SECTION: Fold *)



Tactic Notation "refold" constr(d) :=
  unfold d;
  fold d.

Tactic Notation "refold" constr(d) "in" ident(H) :=
  unfold d in H;
  fold d in H.






(* SECTION: Rename *)




Tactic Notation
  "ren" ident(n)
  "<-" ident(o) :=
  rename o into n.
Tactic Notation
  "ren" ident(n1) "," ident(n2)
  "<-" ident(o1) "," ident(o2) :=
  ren n1 <- o1;
  rename o2 into n2.
Tactic Notation
  "ren" ident(n1) "," ident(n2) "," ident(n3)
  "<-" ident(o1) "," ident(o2) "," ident(o3) :=
  ren n1, n2 <- o1 , o2;
  rename o3 into n3.
Tactic Notation
  "ren" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4)
  "<-" ident(o1) "," ident(o2) "," ident(o3) "," ident(o4) :=
  ren n1, n2, n3 <- o1 , o2, o3;
  rename o4 into n4.
Tactic Notation
  "ren" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4) "," ident(n5)
  "<-" ident(o1) "," ident(o2) "," ident(o3) "," ident(o4)  "," ident(o5) :=
  ren n1, n2, n3, n4 <- o1 , o2, o3, o4;
  rename o5 into n5.






(* SECTION: Remember *)




Tactic Notation
  "rem" ident(n)
  "<-" constr(o) :=
  remember o as n.
Tactic Notation
  "rem" ident(n1) "," ident(n2)
  "<-" constr(o1) "," constr(o2) :=
  rem n1 <- o1;
  remember o2 as n2.
Tactic Notation
  "rem" ident(n1) "," ident(n2) "," ident(n3)
  "<-" constr(o1) "," constr(o2) "," constr(o3) :=
  rem n1, n2 <- o1, o2;
  remember o3 as n3.
Tactic Notation
  "rem" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4)
  "<-" constr(o1) "," constr(o2) "," constr(o3) "," constr(o4) :=
  rem n1, n2, n3 <- o1, o2, o3;
  remember o4 as n4.
Tactic Notation
  "rem" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4) "," ident(n5)
  "<-" constr(o1) "," constr(o2) "," constr(o3) "," constr(o4) "," constr(o5) :=
  rem n1, n2, n3, n4 <- o1, o2, o3, o4;
  remember o5 as n5.



Tactic Notation
  "rem" ident(n)
  "<-" constr(o)
  "as" ident(e) :=
  remember o as n eqn: e.
Tactic Notation
  "rem" ident(n1) "," ident(n2)
  "<-" constr(o1) "," constr(o2)
  "as" ident(e1) "," ident(e2) :=
  rem n1 <- o1 as e1;
  remember o2 as n2 eqn: e2.
Tactic Notation
  "rem" ident(n1) "," ident(n2) "," ident(n3)
  "<-" constr(o1) "," constr(o2) "," constr(o3)
  "as" constr(e1) "," ident(e2) "," ident(e3) :=
  rem n1, n2 <- o1, o2 as e1, e2;
  remember o3 as n3 eqn: e3.
Tactic Notation
  "rem" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4)
  "<-" constr(o1) "," constr(o2) "," constr(o3) "," constr(o4)
  "as" ident(e1) "," ident(e2) "," ident(e3) "," ident(e4) :=
  rem n1, n2, n3 <- o1, o2, o3 as e1, e2, e3;
  remember o4 as n4 eqn: e4.
Tactic Notation
  "rem" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4) "," ident(n5)
  "<-" constr(o1) "," constr(o2) "," constr(o3) "," constr(o4) "," constr(o5)
  "as" ident(e1) "," ident(e2) "," ident(e3) "," ident(e4) "," ident(e5) :=
  rem n1, n2, n3, n4 <- o1, o2, o3, o4 as e1, e2, e3, o4;
  remember o5 as n5 eqn: e5.






(* SECTION: Replace *)



Tactic Notation
  "rep" constr(n)
  "<-" constr(o) :=
  replace n with o.
Tactic Notation
  "rep" constr(n1) "," constr(n2)
  "<-" constr(o1) "," constr(o2) :=
  rep n1 <- o1;
  replace n2 with o2.
Tactic Notation
  "rep" constr(n1) "," constr(n2) "," constr(n3)
  "<-" constr(o1) "," constr(o2) "," constr(o3) :=
  rep n1, n2 <- o1, o2;
  replace n3 with o3.
Tactic Notation
  "rep" constr(n1) "," constr(n2) "," constr(n3) "," constr(n4)
  "<-" constr(o1) "," constr(o2) "," constr(o3) "," constr(o4) :=
  rep n1, n2, n3 <- o1, o2, o3;
  replace n4 with o4.
Tactic Notation
  "rep" constr(n1) "," constr(n2) "," constr(n3) "," constr(n4) "," constr(n5)
  "<-" constr(o1) "," constr(o2) "," constr(o3) "," constr(o4) "," constr(o5) :=
  rep n1, n2, n3, n4 <- o1, o2, o3, o4;
  replace n5 with o5.



Tactic Notation
  "rep" constr(n)
  "<-" constr(o)
  "by" tactic(t) :=
  replace n with o by t.






(* SECTION: Inversion *)



Ltac inver H :=
  inversion H;
  subst;
  clear H;
  clear_refl.



Tactic Notation "invc" ident(H) := inver H.



Tactic Notation
  "invc" ident(H)
  ":" ident(n)
  "<-" ident(o) :=
  invc H;
  ren n <- o.
Tactic Notation
  "invc" ident(H)
  ":" ident(n1) "," ident(n2)
  "<-" ident(o1) "," ident(o2) :=
  invc H : n1 <- o1;
  ren n2 <- o2.
Tactic Notation
  "invc" ident(H)
  ":" ident(n1) "," ident(n2) "," ident(n3)
  "<-" ident(o1) "," ident(o2) "," ident(o3) :=
  invc H : n1, n2 <- o1, o2;
  ren n3 <- o3.
Tactic Notation
  "invc" ident(H)
  ":" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4)
  "<-" ident(o1) "," ident(o2) "," ident(o3) "," ident(o4) :=
  invc H : n1, n2, n3 <- o1, o2, o3;
  ren n4 <- o4.
Tactic Notation
  "invc" ident(H)
  ":" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4) "," ident(n5)
  "<-" ident(o1) "," ident(o2) "," ident(o3) "," ident(o4)  "," ident(o5) :=
  invc H : n1, n2, n3, n4 <- o1, o2, o3, o4;
  ren n5 <- o5.



Tactic Notation
  "invc" ident(H')
  ":" ident(n) :=
  invc H';
  ren n <- H.
Tactic Notation
  "invc" ident(H')
  ":" ident(n1) "," ident(n2) :=
  invc H' : n1;
  ren n2 <- H0.
Tactic Notation
  "invc" ident(H')
  ":" ident(n1) "," ident(n2) "," ident(n3) :=
  invc H' : n1, n2;
  ren n3 <- H1.
Tactic Notation
  "invc" ident(H')
  ":" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4) :=
  invc H' : n1, n2, n3;
  ren n4 <- H2.
Tactic Notation
  "invc" ident(H')
  ":" ident(n1) "," ident(n2) "," ident(n3) "," ident(n4) "," ident(n5)
  "<-" ident(o1) "," ident(o2) "," ident(o3) "," ident(o4)  "," ident(o5) :=
  invc H' : n1, n2, n3, n4;
  ren n5 <- H3.






(* SECTION: Inversion *)



Tactic Notation
  "spc" ident(H)
  ":" constr(x) :=
  specialize (H x);
  try clear x.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) :=
  spc H: x1;
  specialize (H x2);
  try clear x2.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) :=
  spc H: x1, x2;
  specialize (H x3);
  try clear x3.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) :=
  spc H: x1, x2, x3;
  specialize (H x4);
  try clear x4.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5) :=
  spc H: x1, x2, x3, x4;
  specialize (H x5);
  try clear x5.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) :=
  spc H: x1, x2, x3, x4, x5;
  specialize (H x6);
  try clear x6.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) :=
  spc H: x1, x2, x3, x4, x5, x6;
  specialize (H x7);
  try clear x7.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) :=
  spc H: x1, x2, x3, x4, x5, x6, x7;
  specialize (H x8);
  try clear x8.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) "," constr(x9) :=
  spc H: x1, x2, x3, x4, x5, x6, x7, x8;
  specialize (H x9);
  try clear x9.
Tactic Notation
  "spc" ident(H)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) "," constr(x9) "," constr(x10) :=
  spc H: x1, x2, x3, x4, x5, x6, x7, x8, x9;
  specialize (H x10);
  try clear x10.






(* SECTION: Pose Proof *)



Tactic Notation "psp" constr(p) := pose proof p.



Tactic Notation
  "psp" constr(p)
  ":" constr(x) :=
  pose proof p x;
  try clear x.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) :=
  pose proof p x1 x2;
  try clear x1;
  try clear x2.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) :=
  pose proof p x1 x2 x3;
  try clear x1;
  try clear x2;
  try clear x3.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) :=
  pose proof p x1 x2 x3;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5) :=
  pose proof p x1 x2 x3 x4 x5;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) :=
  pose proof p x1 x2 x3 x4 x5 x6;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) "," constr(x9) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x9.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) "," constr(x9) "," constr(x10) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x10.



Tactic Notation "psp" constr(p) "as" ident(H) := pose proof p as H.



Tactic Notation
  "psp" constr(p)
  ":" constr(x)
  "as" ident(H) :=
  pose proof p x;
  try clear x.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2)
  "as" ident(H) :=
  pose proof p x1 x2 as H;
  try clear x1;
  try clear x2.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3)
  "as" ident(H) :=
  pose proof p x1 x2 x3 as H;
  try clear x1;
  try clear x2;
  try clear x3.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4)
  "as" ident(H) :=
  pose proof p x1 x2 x3 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) "," constr(x9)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x9.
Tactic Notation
  "psp" constr(p)
  ":" constr(x1) "," constr(x2) "," constr(x3) "," constr(x4) "," constr(x5)
  "," constr(x6) "," constr(x7) "," constr(x8) "," constr(x9) "," constr(x10)
  "as" ident(H) :=
  pose proof p x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 as H;
  try clear x1;
  try clear x2;
  try clear x3;
  try clear x4;
  try clear x5;
  try clear x6;
  try clear x7;
  try clear x8;
  try clear x10.






(* SECTION: Rewrite *)



Tactic Notation
  "rwr" ident(H) :=
  rewrite -> H;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" "*" :=
  rewrite -> H in *;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi) :=
  rewrite -> H in Hi;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi)
  "+":=
  rewrite -> H in Hi |- *;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite -> H in Hi1, Hi2;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite -> H in Hi1, Hi2 |- *;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite -> H in Hi1, Hi2, Hi3;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite -> H in Hi1, Hi2, Hi3 |- *;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H.
Tactic Notation
  "rwr" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite -> H in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H.



Tactic Notation
  "rwr" ident(H1) "," ident(H2) :=
  rewrite -> H1, H2;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" "*" :=
  rewrite -> H1, H2 in *;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi) :=
  rewrite -> H1, H2 in Hi;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi)
  "+":=
  rewrite -> H1, H2 in Hi |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite -> H1, H2 in Hi1, Hi2;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite -> H1, H2 in Hi1, Hi2 |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2.
Tactic Notation
  "rwr" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite -> H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2.



Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) :=
  rewrite -> H1, H2, H3;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" "*" :=
  rewrite -> H1, H2, H3 in *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi) :=
  rewrite -> H1, H2, H3 in Hi;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi)
  "+":=
  rewrite -> H1, H2, H3 in Hi |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite -> H1, H2, H3 in Hi1, Hi2;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite -> H1, H2, H3 in Hi1, Hi2 |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite -> H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2;
  clear H3.



Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) :=
  rewrite -> H1, H2, H3, H4;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" "*" :=
  rewrite -> H1, H2, H3, H4 in *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi) :=
  rewrite -> H1, H2, H3, H4 in Hi;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi)
  "+":=
  rewrite -> H1, H2, H3, H4 in Hi |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite -> H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.




Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5) :=
  rewrite -> H1, H2, H3, H4, H5;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" "*" :=
  rewrite -> H1, H2, H3, H4, H5 in *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi) :=
  rewrite -> H1, H2, H3, H4, H5 in Hi;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi)
  "+":=
  rewrite -> H1, H2, H3, H4, H5 in Hi |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwr" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite -> H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.






Tactic Notation
  "rwl" ident(H) :=
  rewrite <- H;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" "*" :=
  rewrite <- H in *;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi) :=
  rewrite <- H in Hi;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi)
  "+":=
  rewrite <- H in Hi |- *;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite <- H in Hi1, Hi2;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite <- H in Hi1, Hi2 |- *;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite <- H in Hi1, Hi2, Hi3;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite <- H in Hi1, Hi2, Hi3 |- *;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H.
Tactic Notation
  "rwl" ident(H)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite <- H in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H.



Tactic Notation
  "rwl" ident(H1) "," ident(H2) :=
  rewrite <- H1, H2;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" "*" :=
  rewrite <- H1, H2 in *;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi) :=
  rewrite <- H1, H2 in Hi;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi)
  "+":=
  rewrite <- H1, H2 in Hi |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite <- H1, H2 in Hi1, Hi2;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite <- H1, H2 in Hi1, Hi2 |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2.
Tactic Notation
  "rwl" ident(H1) "," ident(H2)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite <- H1, H2 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2.



Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) :=
  rewrite <- H1, H2, H3;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" "*" :=
  rewrite <- H1, H2, H3 in *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi) :=
  rewrite <- H1, H2, H3 in Hi;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi)
  "+":=
  rewrite <- H1, H2, H3 in Hi |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite <- H1, H2, H3 in Hi1, Hi2;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite <- H1, H2, H3 in Hi1, Hi2 |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2;
  clear H3.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite <- H1, H2, H3 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2;
  clear H3.



Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) :=
  rewrite <- H1, H2, H3, H4;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" "*" :=
  rewrite <- H1, H2, H3, H4 in *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi) :=
  rewrite <- H1, H2, H3, H4 in Hi;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi)
  "+":=
  rewrite <- H1, H2, H3, H4 in Hi |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2;
  clear H3;
  clear H4.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite <- H1, H2, H3, H4 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4.



Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5) :=
  rewrite <- H1, H2, H3, H4, H5;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" "*" :=
  rewrite <- H1, H2, H3, H4, H5 in *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi) :=
  rewrite <- H1, H2, H3, H4, H5 in Hi;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi)
  "+":=
  rewrite <- H1, H2, H3, H4, H5 in Hi |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2)
  "+":=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3)
  "+":=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4)
  "+":=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5) :=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.
Tactic Notation
  "rwl" ident(H1) "," ident(H2) "," ident(H3) "," ident(H4) "," ident(H5)
  "in" ident(Hi1) "," ident(Hi2) "," ident(Hi3) "," ident(Hi4) "," ident(Hi5)
  "+":=
  rewrite <- H1, H2, H3, H4, H5 in Hi1, Hi2, Hi3, Hi4, Hi5 |- *;
  clear H1;
  clear H2;
  clear H3;
  clear H4;
  clear H5.