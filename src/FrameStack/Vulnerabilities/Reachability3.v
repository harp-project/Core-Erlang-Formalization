Require Import PeanoNat.
From CoreErlang.FrameStack Require Import SubstSemanticsLabeled.
Import ListNotations.

Open Scope string_scope.

Search "lt_wf_ind".

Definition infinite_atom_g (e : Exp) : Exp :=
  ELetRec
    [(1, °ELet 1
      (˝VCons (VLit 97%Z) (VCons (VVar 1) (VNil)))
      (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom") [˝VVar 0])
             (°ELet 1
                (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit 1%Z])
                (EApp (˝VFunId (2, 1)) [˝VVar 0]))))]
    (EApp (˝VFunId (0, 1)) [e]).

Ltac do_step := econstructor; [constructor;auto|simpl|auto].

Goal exists rv, ⟨[], infinite_atom_g (˝VLit (Integer 0))⟩ -->* RValSeq rv.
Proof.
  eexists. unfold step_any.
  eexists. eexists. split.
  - admit.
  - unfold infinite_atom_g.
    do 1 do_step.
    do 1 do_step.
    do 1 do_step. scope_solver.
    do 1 do_step.
    do 1 do_step. congruence.
    do 1 do_step.
    do 1 do_step.

Lemma cofix' :
  forall fs r fs' r' l n, 
  (forall n0, 
    (forall m, m < n0 -> ⟨fs, r⟩ -[m, l]-> ⟨fs', r'⟩) ->
    ⟨fs, r⟩ -[n0, l]-> ⟨fs', r'⟩
  ) ->
  ⟨fs, r⟩ -[n, l]-> ⟨fs', r'⟩.