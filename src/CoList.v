
From Coq Require Export Lists.List.
Import ListNotations.
Print list.

CoInductive Trace (A : Set) : Set :=
| TNil
| TCons (x : A) (xs : Trace A).

Arguments TNil {A}.
Arguments TCons {A}.

Notation "'[]ₜ'" := (TNil).
Notation "x ::ₜ xs" := (TCons x xs) (at level 60, right associativity).

Fixpoint finite_append {A : Set} (l : list A) (tail : Trace A) : Trace A :=
match l with
| [] => tail
| x :: xs => x ::ₜ finite_append xs tail
end.

Notation "xs ++ₗ ys" := (finite_append xs ys) (at level 60, right associativity, 
  format "xs ++ₗ ys").

CoFixpoint infinite_append {A : Set} (l tail : Trace A) : Trace A :=
match l with
| []ₜ => tail
| x ::ₜ xs => x ::ₜ infinite_append xs tail
end.

Notation "xs ++ₜ ys" := (infinite_append xs ys) (at level 60, right associativity, 
  format "xs ++ₜ ys").

Compute []ₜ.
Compute [1;2;3] ++ₗ 4 ::ₜ []ₜ.

Lemma trace_match {A : Set} (l : Trace A) :
  l = match l with TNil => TNil | TCons a l' => TCons a l' end.
Proof.
  destruct l; reflexivity.
Qed.

Lemma trace_append_nil T (l : Trace T):
  []ₜ ++ₜ l = l.
Proof.
  etransitivity.
  {
    apply trace_match.
  }
  simpl. now destruct l.
Qed.

Lemma trace_append_cons T x (l xs : Trace T) :
  (x ::ₜ xs) ++ₜ l = x ::ₜ (xs ++ₜ l).
Proof.
  etransitivity.
  {
    apply trace_match.
  }
  now simpl.
Qed.
