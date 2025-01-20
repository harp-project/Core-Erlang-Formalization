From CoreErlang.FrameStack Require Import SubstSemantics.
From stdpp Require Export gmap sets.

Open Scope string_scope.

Module AtomExhaustion.

Import ListNotations.

Definition step_any_non_final (fs : FrameStack) (e : Redex) (fs' : FrameStack) (e' : Redex) : Prop :=
  exists k, ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩.
Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_any_non_final fs e fs' e').

Inductive atom_generating_cfg : FrameStack -> Redex -> Prop :=
| list_to_atom_frame fs (vl : list Val) (v : Val) (vs' : ValSeq) (eff' : SideEffectList):
  Some ((RValSeq vs'), eff') =
    create_result (ICall (VLit "erlang") (VLit "list_to_atom")) (vl ++ [v]) [] ->
  (atom_generating_cfg
    (FParams (ICall (VLit "erlang") (VLit "list_to_atom")) vl [] :: fs)
    (RValSeq [v])).

Definition atom_generating_step (fs: FrameStack) (r: Redex) (fs': FrameStack) (r': Redex) : Prop :=
  (atom_generating_cfg fs r) /\ ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩.

Definition generated_atom_value
  (fs: FrameStack) (r: Redex) : option (string) :=
match fs, r with
| (FParams (ICall (VLit "erlang") (VLit "list_to_atom")) vl [] :: fs), (RValSeq [v])
  =>
  match create_result (ICall (VLit "erlang") (VLit "list_to_atom")) (vl ++ [v]) [] with
  | Some ((RValSeq [VLit (Atom atom_val)]), eff') => Some atom_val
  | _ => None
  end
| _, _ => None
end.

Goal generated_atom_value
  [FParams (ICall (VLit "erlang") (VLit "list_to_atom")) [] []]
  (RValSeq
    [VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z)
    (VCons (VLit 108%Z) (VCons (VLit 111%Z) VNil))))]) = Some "hello".
Proof.
  simpl. reflexivity.
Qed.

Inductive generates_at_least_n_unique_atoms :
  FrameStack -> Redex -> gset string -> nat -> Prop :=
| generates_terminal fs r s:
  generates_at_least_n_unique_atoms fs r s 0

| generates_step_false fs r s n fs' r':
  ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩ ->
  (generates_at_least_n_unique_atoms fs' r' s n) ->
  generates_at_least_n_unique_atoms fs r s n

| generates_step_true_not_unique fs r s n fs' r' (av: string):
  (Some av) = generated_atom_value fs r -> (* gset_elem_of av s -> *)
  ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩ ->
  (generates_at_least_n_unique_atoms fs' r' s n) ->
  generates_at_least_n_unique_atoms fs r s n

| generates_step_true_unique fs r s n fs' r' (av: string):
  (Some av) = generated_atom_value fs r -> ¬(elem_of av s) ->
  ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩ ->
  (generates_at_least_n_unique_atoms fs' r' ({[av]} ∪ s) n) ->
  generates_at_least_n_unique_atoms fs r s (S n).

Definition call_of_list_to_atom: Exp :=
  ECall (˝VLit "erlang") (˝VLit "list_to_atom")
    [˝VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil)))))].

Ltac do_step := econstructor; [constructor; auto|simpl].

Ltac apply_proper_constr := 
  eapply generates_terminal || (
  eapply generates_step_true_unique;
    [simpl; reflexivity
    | set_solver
    | econstructor; reflexivity
    |] || (
  eapply generates_step_true_not_unique;
    [simpl; reflexivity
    | econstructor; reflexivity
    |] ||
  eapply generates_step_false;
    [econstructor; try (scope_solver || congruence)
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
  do 19 (apply_proper_constr; [reflexivity|simpl];
  do 6 apply_proper_constr; [reflexivity|simpl];
  do 3 apply_proper_constr; [reflexivity|simpl];
  do 21 apply_proper_constr; [reflexivity|simpl]).
  apply_proper_constr; [reflexivity|simpl].
  do 6 apply_proper_constr; [reflexivity|simpl].
  do 3 apply_proper_constr; [reflexivity|simpl].
  do 10 apply_proper_constr.
Qed.

End AtomExhaustion.