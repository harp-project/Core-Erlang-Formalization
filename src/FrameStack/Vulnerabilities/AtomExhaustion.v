From CoreErlang.FrameStack Require SubstSemantics.

Open Scope string_scope.

Module AtomExhaustion.

Import FrameStack.SubstSemantics.
Import ListNotations.

Definition step_any_non_final (fs : FrameStack) (e : Redex) (fs' : FrameStack) (e' : Redex) : Prop :=
  exists k, ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩.
Notation "⟨ fs , e ⟩ -->* ⟨ fs' , e' ⟩" := (step_any_non_final fs e fs' e') (at level 50).



Inductive atom_g : FrameStack -> Redex -> Prop :=
| list_to_atom fs (vl : list Val) (v : Val) (vs' : ValSeq) (eff' : SideEffectList):
  Some ((RValSeq vs'), eff') = create_result (ICall (VLit "erlang") (VLit "list_to_atom")) (vl ++ [v]) [] ->
  (atom_g
    (FParams (ICall (VLit "erlang") (VLit "list_to_atom")) vl [] :: fs)
    (RValSeq [v])).

(* Definition generates_atom (fs: FrameStack) (r: Redex) : Prop :=
  exists fs' r', ⟨ fs , r ⟩ -->* ⟨ fs' , r' ⟩ /\ (atom_g fs' r'). *)

Fixpoint generates_at_least_N_atoms (fs: FrameStack) (r: Redex) (n: nat) : Prop :=
match n with
| 0    => True
| S n' => exists fs' r',
            ⟨ fs , r ⟩ -->* ⟨ fs' , r' ⟩ /\ (atom_g fs' r') /\
            (exists fs'' r'', ⟨ fs' , r' ⟩ --> ⟨ fs'' , r'' ⟩ /\ generates_at_least_N_atoms fs'' r'' n')
end.

Definition call_of_list_to_atom: Exp :=
  ECall (˝VLit "erlang") (˝VLit "list_to_atom")
    [˝VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil)))))].

Ltac do_step := econstructor; [constructor; auto|simpl].

(* Goal generates_atom [] call_of_list_to_atom.
Proof.
  unfold generates_atom. unfold step_any_non_final.
  eexists. eexists. split.
  - unfold call_of_list_to_atom. eexists.
    do 6 do_step. congruence. do_step. scope_solver. apply step_refl.
  - econstructor. simpl. reflexivity.
Qed. *)

Goal generates_at_least_N_atoms [] call_of_list_to_atom 1.
Proof.
  unfold generates_at_least_N_atoms. unfold step_any_non_final.
  eexists. eexists. split.
  - unfold call_of_list_to_atom. eexists.
    do 6 do_step. congruence. do_step. scope_solver. apply step_refl.
  - split. econstructor. simpl. reflexivity.
    eexists. eexists. split. econstructor. reflexivity. auto.
Qed.

Definition infinite_atom_g (e : Exp) : Exp :=
  ELetRec
    [(1, °ELet 1
      (˝VCons (VLit 97%Z) (VCons (VVar 1) (VNil)))
      (°ESeq (°ECall (˝VLit "erlang") (˝VLit "list_to_atom") [˝VVar 0])
             (°ELet 1
                (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit 1%Z])
                (EApp (˝VFunId (1, 1)) [˝VVar 0]))))]
    (EApp (˝VFunId (0, 1)) [e])
.

Goal forall n,
  generates_at_least_N_atoms [] (infinite_atom_g (˝VLit 0%Z)) n.
Proof.
  induction n; intros.
  - unfold generates_at_least_N_atoms. auto.
  - unfold generates_at_least_N_atoms. eexists. eexists. split. 2: split.
  3: fold generates_at_least_N_atoms.