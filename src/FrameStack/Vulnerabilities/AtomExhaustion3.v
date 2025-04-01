From CoreErlang.FrameStack Require Import SubstSemanticsLabeledLemmas.
From stdpp Require Import gmap sets list.
Require Import Coq.Program.Equality.
Require Import Lia.
Require List.

Open Scope string_scope.

Module AtomExhaustion.

Import ListNotations.

Definition mk_atom_set (l: SideEffectList): gset string :=
  list_to_set (((List.map
    (fun x => match x with
              | (_, [VLit (Atom av)]) => av
              | _ => ""
              end))
∘
  (List.filter
    (fun x => match x with
              | (AtomCreation, [VLit (Atom _)]) => true
              | _ => false
              end)))
    l).

Definition atom_exhaustion (fs: FrameStack) (r: Redex) (atom_limit: nat) :=
  exists fs' r' l, ⟨ fs , r ⟩ -[ l ]->* ⟨ fs' , r' ⟩ /\
    size (mk_atom_set l) >= atom_limit.

Definition infinite_atom_g (e : Exp) : Exp :=
  ELetRec
    [(1, °ELet 1
      (˝VCons (VLit 97%Z) (VCons (VVar 1) (VNil)))
      (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom") [˝VVar 0])
             (°ELet 1
                (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit 1%Z])
                (EApp (˝VFunId (2, 1)) [˝VVar 0]))))]
    (EApp (˝VFunId (0, 1)) [e]).

Ltac do_step :=
  eapply SubstSemanticsLabeled.step_trans; [econstructor;auto|simpl|simpl].

Goal atom_exhaustion [] (infinite_atom_g (˝VLit (Integer 0))) 10.
Proof.
  unfold atom_exhaustion. repeat eexists.
  - unfold infinite_atom_g.