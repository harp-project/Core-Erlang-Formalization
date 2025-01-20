From CoreErlang.FrameStack Require SubstSemanticsLabeled.

Open Scope string_scope.

Module AtomExhaustion.

Import FrameStack.SubstSemanticsLabeled.
Import ListNotations.

Definition step_any_non_final (fs : FrameStack) (e : Redex) (fs' : FrameStack) (e' : Redex) : Prop :=
  exists k, ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩.
Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_any_non_final fs e fs' e').



Inductive atom_generating_cfg : FrameStack -> Redex -> Prop :=
| list_to_atom_frame fs (vl : list Val) (v : Val) (vs' : ValSeq) (eff' : SideEffectList):
  Some ((RValSeq vs'), eff') =
    create_result (ICall (VLit "erlang") (VLit "list_to_atom")) (vl ++ [v]) ->
  (atom_generating_cfg
    (FParams (ICall (VLit "erlang") (VLit "list_to_atom")) vl [] :: fs)
    (RValSeq [v])).


Definition atom_generating_step (fs: FrameStack) (r: Redex) (fs': FrameStack) (r': Redex) : Prop :=
  (atom_generating_cfg fs r) /\ ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩.


Inductive generates_at_least_n_atoms : FrameStack -> Redex -> nat -> Prop :=
| generates_0 fs r:
  generates_at_least_n_atoms fs r 0

| generates_n fs r n fs' r' fs'' r'':
  ⟨ fs , r ⟩ -->* ⟨ fs' , r' ⟩ -> (atom_generating_cfg fs' r') ->
  ⟨ fs' , r' ⟩ --> ⟨ fs'' , r'' ⟩ -> (generates_at_least_n_atoms fs'' r'' n) ->
  generates_at_least_n_atoms fs r (S n).


Inductive generates_at_least_n_atoms_three_way : FrameStack -> Redex -> nat -> Prop :=
| generates_0_tw fs r:
  generates_at_least_n_atoms_three_way fs r 0

| generates_n_step_false fs r n fs' r':
  ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩ -> (generates_at_least_n_atoms fs' r' n) ->
  generates_at_least_n_atoms_three_way fs r n

| generates_n_step_true fs r n fs' r':
  (atom_generating_cfg fs r) ->
  ⟨ fs , r ⟩ --> ⟨ fs' , r' ⟩ -> (generates_at_least_n_atoms fs' r' n) ->
  generates_at_least_n_atoms_three_way fs r (S n).


Definition call_of_list_to_atom: Exp :=
  ECall (˝VLit "erlang") (˝VLit "list_to_atom")
    [˝VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil)))))].

Ltac do_step := econstructor; [constructor; auto|simpl].

Goal generates_at_least_n_atoms [] call_of_list_to_atom 1.
Proof.
  econstructor.
  1: {
    unfold call_of_list_to_atom, step_any_non_final. eexists.
    do 6 do_step. congruence. do_step. scope_solver. apply step_refl.
  }
  all: econstructor; reflexivity.
Qed.

Lemma generates_at_least_n_atoms_rec:
  forall n fs r, generates_at_least_n_atoms fs r (S n) -> generates_at_least_n_atoms fs r n.
Proof.
  induction n.
  - econstructor.
  - intros. inv H. econstructor.
    + exact H1.
    + exact H2.
    + exact H3.
    + specialize (IHn _ _ H6). exact IHn.
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

Goal forall n fs x,
  generates_at_least_n_atoms fs (infinite_atom_g (˝VLit (Integer x))) n.
Proof.
  induction n.
  - econstructor.
  - intros. econstructor.
    + unfold step_any_non_final. eexists.
      unfold infinite_atom_g.
      do 3 do_step. scope_solver. do 2 do_step. congruence.
      do_step. eapply step_trans. eapply eval_cool_params. reflexivity. simpl.
      do 10 do_step. congruence. do_step. econstructor.
    + econstructor. reflexivity.
    + eapply eval_cool_params. reflexivity.
    + simpl. unfold eval_list_atom. simpl. clear IHn. revert fs x. induction n. 
      * econstructor.
      * intros. econstructor.
        -- unfold step_any_non_final. eexists.
           do 8 do_step. congruence. do 3 do_step.
           eapply step_trans. eapply eval_cool_params. reflexivity.
           unfold eval_arith. simpl. do 3 do_step. scope_solver.
           do 2 do_step. congruence. do_step.
           eapply step_trans. eapply eval_cool_params. reflexivity. simpl.
           do 10 do_step. congruence. do_step. econstructor.
        -- econstructor. reflexivity.
        -- eapply eval_cool_params. reflexivity.
        -- specialize (IHn fs (x + 1)%Z). assumption.
Qed.

(* Goal forall n fs x,
  generates_at_least_n_atoms_three_way fs (infinite_atom_g (˝VLit (Integer x))) n.
Proof.
  induction n.
  - econstructor.
  - intros. unfold infinite_atom_g. eapply *)

(* Construct smart tactics *)
(* how to define tactics *)

End AtomExhaustion.