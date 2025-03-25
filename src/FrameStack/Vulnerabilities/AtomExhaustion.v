From CoreErlang.FrameStack Require Import SubstSemanticsLabeled.
From stdpp Require Export gmap sets.

Open Scope string_scope.

Module AtomExhaustion.

Import ListNotations.


Inductive generates_at_least_n_unique_atoms :
  FrameStack -> Redex -> gset string -> nat -> Prop :=
| generates_terminal fs r s:
  generates_at_least_n_unique_atoms fs r s 0

| generates_step_false fs r l fs' r' s n:
  ⟨ fs , r ⟩ -⌊ l ⌋-> ⟨ fs' , r' ⟩ ->
  (generates_at_least_n_unique_atoms fs' r' s n) ->
  generates_at_least_n_unique_atoms fs r s n

| generates_step_true_unique fs r (av: string) fs' r' s n:
  ⟨ fs , r ⟩ -⌊ Some (AtomCreation, [VLit (Atom av)]) ⌋-> ⟨ fs' , r' ⟩ ->
  av ∉ s ->
  (generates_at_least_n_unique_atoms fs' r' ({[av]} ∪ s) n) ->
  generates_at_least_n_unique_atoms fs r s (S n).

Definition call_of_list_to_atom: Exp :=
  ECall (˝VLit "erlang") (˝VLit "list_to_atom")
    [˝VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil)))))].

Ltac apply_proper_constr := 
  eapply generates_terminal || (
  eapply generates_step_true_unique;
    [econstructor; reflexivity
    |set_solver 
    |] || (
  eapply generates_step_false;
    [econstructor; try (reflexivity || scope_solver || congruence)
    |simpl]
)).

Goal generates_at_least_n_unique_atoms [] call_of_list_to_atom ∅ 1.
Proof.
  unfold call_of_list_to_atom.
  repeat apply_proper_constr.
Qed.

Definition infinite_atom_g (e : Exp) : Exp :=
  ELetRec
    [(1, °ELet 1
      (˝VCons (VLit 97%Z) (VCons (VVar 1) (VNil)))
      (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom") [˝VVar 0])
             (°ELet 1
                (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit 1%Z])
                (EApp (˝VFunId (2, 1)) [˝VVar 0]))))]
    (EApp (˝VFunId (0, 1)) [e]).

Goal generates_at_least_n_unique_atoms [] (infinite_atom_g (˝VLit (Integer 0))) ∅ 20.
Proof.
  unfold infinite_atom_g.
  repeat apply_proper_constr.
Qed.

End AtomExhaustion.