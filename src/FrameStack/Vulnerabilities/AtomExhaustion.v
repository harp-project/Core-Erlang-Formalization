(**
  This file formalises the atom exhaustion vulnerability on top of the
  labeled frame stack semantics. Atoms are never garbage collected in Erlang,
  so a program that creates too many distinct atoms crashes the runtime once
  the atom table limit is exceeded. The formalisation is described in the
  paper https://dl.acm.org/doi/10.1145/3759161.3763045.

  The file contains:
  - `mk_atom_set`, the set of atoms created in a side-effect trace;
  - `generates_at_least_n_unique_atoms` (GALNUA), an inductive
    characterisation of programs creating at least `n` new atoms;
  - `atom_exhaustion`, the trace-based definition of the vulnerability;
  - the equivalence of the two characterisations (`soundness` and
    `completeness`), and the lemmas they rely on.

  The definitions are inside the `AtomExhaustion` module; import it
  explicitly to use them unqualified.
*)

From CoreErlang.FrameStack Require Import SubstSemanticsLabeledLemmas.
From stdpp Require Import gmap sets list.
From Stdlib Require Import Lia.

Open Scope string_scope.

Module AtomExhaustion.

Import ListNotations.

(** * Atoms created in a side-effect trace *)

(** The set of atoms created in the side-effect trace `l`, i.e., the atoms
    of its `AtomCreation` entries. *)
Definition mk_atom_set (l: SideEffectList): gset string :=
  list_to_set (omap
    (fun x => match x with
              | (AtomCreation, [VLit (Atom av)]) => Some av
              | _ => None
              end) l).

(** Creating an atom adds it to the set. *)
Lemma mk_atom_set_union : forall (av: string) (l: SideEffectList),
  mk_atom_set (((AtomCreation, [VLit av]):SideEffect) :: l) =
    ({[av]} ∪ mk_atom_set l).
Proof.
  intros. unfold mk_atom_set. simpl. reflexivity.
Qed.

(** Trace entries which are not atom creations do not change the set. *)
Lemma mk_atom_set_unfit : forall (el: SideEffect) (l: SideEffectList),
  (forall (av: string), el <> (AtomCreation, [VLit av])) ->
  mk_atom_set (el :: l) = mk_atom_set l.
Proof.
  intros el l H. destruct el as [id vl].
  destruct id, vl as [|v vl].
  all: try reflexivity.
  all: destruct v as [|lit| | | | | | | |]; try reflexivity.
  all: destruct lit; try reflexivity.
  all: destruct vl; try reflexivity.
  specialize (H s). contradiction.
Qed.

(** Trace entries of other kinds than `AtomCreation` do not change the
    set. *)
Lemma mk_atom_set_unfit2 : forall (id: SideEffectId),
  id <> AtomCreation -> forall vl l,
  mk_atom_set (((id, vl):SideEffect) :: l) = mk_atom_set l.
Proof.
  intros. destruct id.
  1-2: unfold mk_atom_set; reflexivity.
  contradiction.
Qed.

(** Repeated atom creations and other side effects are ignored. *)
Example mk_atom_set_test :
  mk_atom_set [
    (AtomCreation, [VLit (Atom "e")]);
    (Input, [VLit (Atom "a")]);
    (AtomCreation, [VLit (Atom "b")]);
    (AtomCreation, [VLit (Atom "b")])] = {["e"; "b"]}.
Proof.
  reflexivity.
Qed.

(** * Programs generating new atoms *)

(** `generates_at_least_n_unique_atoms fs r s n`: the evaluation of `r` in
    `fs` creates at least `n` distinct atoms which are not in `s`. Each step
    either may be skipped (`generates_step_false`), or creates a new atom,
    which is then added to `s` (`generates_step_true_unique`). *)
Inductive generates_at_least_n_unique_atoms :
  FrameStack -> Redex -> gset string -> nat -> Prop :=
| generates_terminal fs r s:
  generates_at_least_n_unique_atoms fs r s 0

| generates_step_false fs r l fs' r' s n:
  ⟨ fs , r ⟩ -⌊ l ⌋->ₗ ⟨ fs' , r' ⟩ ->
  (generates_at_least_n_unique_atoms fs' r' s n) ->
  generates_at_least_n_unique_atoms fs r s n

| generates_step_true_unique fs r (av: string) fs' r' s n:
  ⟨ fs , r ⟩ -⌊ Some ((AtomCreation,
    [VLit (Atom av)]):SideEffect) ⌋->ₗ ⟨ fs' , r' ⟩ ->
  av ∉ s ->
  (generates_at_least_n_unique_atoms fs' r' ({[av]} ∪ s) n) ->
  generates_at_least_n_unique_atoms fs r s (S n).

(** * The atom exhaustion vulnerability *)

(** `atom_exhaustion_aux fs r avs atom_limit`: the evaluation of `r` in `fs`
    can reach a state where, together with the atoms already in `avs`, more
    than `atom_limit` atoms exist. *)
Definition atom_exhaustion_aux (fs: FrameStack) (r: Redex) (avs: gset string) (atom_limit: nat) :=
  exists fs' r' l, ⟨ fs , r ⟩ -[ l ]->ₗ* ⟨ fs' , r' ⟩ /\
    size (mk_atom_set l ∖ avs) >= atom_limit - size (avs) + 1.

(** `atom_exhaustion e atom_limit`: the evaluation of `e` creates more than
    `atom_limit` distinct atoms. *)
Definition atom_exhaustion (e: Exp) (atom_limit: nat) :=
  atom_exhaustion_aux [] e ∅ atom_limit.

(** * Properties of GALNUA *)

(** Generating `n` atoms implies generating `n - 1` atoms. *)
Lemma GALNUA_gen_one_less : forall fs r set n,
  generates_at_least_n_unique_atoms fs r set n ->
  generates_at_least_n_unique_atoms fs r set (pred n).
Proof.
  intros. induction H.
  - simpl. apply generates_terminal.
  - apply (generates_step_false _ _ _ _ _ _ _ H). assumption.
  - destruct n; simpl in *.
    + apply generates_terminal.
    + eapply generates_step_true_unique; eassumption.
Qed.

(** Generating `n` atoms implies generating any fewer atoms. *)
Lemma GALNUA_gen_many_less : forall fs r set n,
  generates_at_least_n_unique_atoms fs r set n -> forall m, m <= n ->
  generates_at_least_n_unique_atoms fs r set m.
Proof.
  intros. induction H0.
  - assumption.
  - apply GALNUA_gen_one_less in H; simpl in H.
    apply IHle. assumption.
Qed.

(** Removing an atom from the set of existing atoms preserves GALNUA. *)
Lemma GALNUA_set_relax : forall fs r set n,
  generates_at_least_n_unique_atoms fs r set n ->
  forall av, generates_at_least_n_unique_atoms fs r (set ∖ {[av]}) n.
Proof.
  intros fs r set n H. induction H; intros.
  - apply generates_terminal.
  - apply (generates_step_false _ _ _ _ _ _ _ H).
    specialize (IHgenerates_at_least_n_unique_atoms av).
    assumption.
  - eapply generates_step_true_unique; [eassumption|set_solver|].
    destruct (decide (av0 ∈ s)).
    + assert ((({[av]}) ∪ s) ∖ ({[av0]}) = ({[av]}) ∪ (s ∖ ({[av0]}))).
      { set_solver. } rewrite <- H2.
      specialize (IHgenerates_at_least_n_unique_atoms av0).
      assumption.
    + assert ((s ∖ ({[av0]})) = s). { set_solver. }
      rewrite H2. assumption.
Qed.

(** Adding a new atom to the set of existing atoms decreases the number of
    generated atoms by at most one. *)
Lemma GALNUA_set_strengthen : forall fs r avs n,
  generates_at_least_n_unique_atoms fs r avs n ->
  forall av, av ∉ avs
->
  generates_at_least_n_unique_atoms fs r ({[av]} ∪ avs) (pred n).
Proof.
  intros. generalize dependent av. induction H; intros.
  + apply generates_terminal.
  + eapply generates_step_false; try eassumption.
    apply IHgenerates_at_least_n_unique_atoms. assumption.
  + destruct (decide (av = av0)).
    - eapply generates_step_false; try eassumption. simpl.
      rewrite <- e. assumption.
    - assert (av0 ∉ {[av]} ∪ s). { set_solver. }
      destruct n. apply generates_terminal.
      eapply generates_step_true_unique. eassumption. set_solver.
      assert (({[av0]} ∪ ({[av]} ∪ s)) = ({[av]} ∪ ({[av0]} ∪ s))).
      { set_solver. } rewrite <- H4.
      apply IHgenerates_at_least_n_unique_atoms. assumption.
Qed.

(** GALNUA is preserved by evaluation: the atoms created by the evaluation
    are added to the set, and the number of atoms still to be generated
    decreases by the number of new ones. *)
Lemma GALNUA_multistep :
  forall fs r fs' r' l, ⟨ fs , r ⟩ -[ l ]->ₗ* ⟨ fs' , r' ⟩ ->
  forall avs n, generates_at_least_n_unique_atoms fs r avs n
->
  generates_at_least_n_unique_atoms fs' r'
    (avs ∪ (mk_atom_set l)) (n - (size ((mk_atom_set l) ∖ avs))).
Proof.
  intros. revert H0. revert avs n. destruct H.
  induction H; intros.
  - unfold mk_atom_set; simpl.
    assert (avs ∪ ∅ = avs). { set_solver. }
    assert (∅ ∖ avs = ∅). { set_solver. }
    rewrite H, H1, size_empty, Nat.sub_0_r.
    assumption.
  - destruct H2.
    + rewrite Nat.sub_0_l. apply generates_terminal.
    + apply (step_determinism_labeled H) in H2. destruct H2, H4.
      rewrite H4, H5 in *. specialize (IHstep_rt _ _ H3).
      destruct s; simpl option_cons in *.
      * destruct s. destruct s eqn:Hid.
        3: {
          apply side_effect_ac_value in H. destruct H. subst.
          pose proof (mk_atom_set_union x l). rewrite H.
          destruct (decide (x ∈ mk_atom_set l)).
          -- assert ({[x]} ∪ mk_atom_set l = mk_atom_set l).
             { set_solver. } rewrite H1 in *.
             assumption.
          -- destruct (decide (x ∈ s0)).
             ++ assert (s0 ∪ ({[x]} ∪ mk_atom_set l) = s0 ∪ mk_atom_set l).
                { set_solver. } rewrite H1. clear H1.
                assert (({[x]} ∪ mk_atom_set l) ∖ s0 = mk_atom_set l ∖ s0).
                { set_solver. } rewrite H1. assumption.
             ++ assert (x ∉ s0 ∪ mk_atom_set l). { set_solver. }
                pose proof (GALNUA_set_strengthen _ _ _ _ IHstep_rt x H1).
                assert (s0 ∪ ({[x]} ∪ mk_atom_set l) =
                  {[x]} ∪ (s0 ∪ mk_atom_set l)). { set_solver. }
                rewrite H4; clear H4.
                assert (({[x]} ∪ mk_atom_set l) ∖ s0 =
                  {[x]} ∪ (mk_atom_set l ∖ s0)). { set_solver. }
                rewrite H4; clear H4.
                assert ({[x]} ## (mk_atom_set l ∖ s0)). { set_solver. }
                rewrite (size_union _ _ H4), size_singleton. clear H4.
                remember (Init.Nat.pred (n - size (mk_atom_set l ∖ s0))) as sz1.
                remember (n - (1 + size (mk_atom_set l ∖ s0))) as sz2.
                clear - H2 Heqsz1 Heqsz2. assert (sz1 = sz2).
                { subst. lia. } rewrite <- H. assumption.
        }
        all: assert (s <> AtomCreation);
          [subst;discriminate|subst];
          pose proof (mk_atom_set_unfit2 _ H6 l1 l);
          rewrite H1; assumption.
      * rewrite H1. assumption.
    + apply (step_determinism_labeled H) in H2. destruct H2, H5.
      subst. simpl option_cons in *. specialize (IHstep_rt _ _ H4).
      assert (((({[av]}) ∪ s0) ∪ (mk_atom_set l)) =
        (s0 ∪ (mk_atom_set (((AtomCreation, [VLit av]):SideEffect) :: l)))).
      {
        clear - H3. pose proof (mk_atom_set_union av l).
        rewrite H. set_solver.
      }
      rewrite H1 in IHstep_rt.
      assert ((S n - size (mk_atom_set
        (((AtomCreation, [VLit av]):SideEffect) :: l) ∖ s0)) =
        (n - size (mk_atom_set l ∖ ({[av]} ∪ s0)))).
      {
        clear - H3. pose proof (mk_atom_set_union av l). rewrite H.
        destruct (decide (av ∈ mk_atom_set l)).
        - assert (({[av]} ∪ mk_atom_set l) = mk_atom_set l).
          { set_solver. } rewrite H0.
          do 2 (rewrite size_difference_alt; symmetry).
          assert (mk_atom_set l ∩ ({[av]} ∪ s0) =
            (mk_atom_set l ∩ s0) ∪ {[av]}). { set_solver. }
          rewrite H1. symmetry; rewrite size_union_alt; symmetry.
          assert ({[av]} ∖ (mk_atom_set l ∩ s0) = {[av]}).
          { set_solver. } rewrite H2, size_singleton.
          assert (size (mk_atom_set l ∩ s0) < size (mk_atom_set l)).
          { apply subset_size. set_solver. } clear - H4. lia.
        - assert ((mk_atom_set l ∖ ({[av]} ∪ s0)) = (mk_atom_set l ∖ s0)).
          { set_solver. } rewrite H0.
          do 2 (rewrite size_difference_alt; symmetry).
          assert ((({[av]} ∪ mk_atom_set l) ∩ s0) = (mk_atom_set l ∩ s0)).
          { set_solver. } rewrite H1. rewrite size_union_alt.
          assert ((mk_atom_set l ∖ {[av]}) = (mk_atom_set l)).
          { set_solver. } rewrite H2, size_singleton.
          assert (size (mk_atom_set l ∩ s0) <= size (mk_atom_set l)).
          { apply subseteq_size. set_solver. }
          clear - H4. lia.
      }
      rewrite H2. assumption.
Qed.

(** The converse of `GALNUA_multistep`: GALNUA after an evaluation implies
    GALNUA before it, increased by the number of new atoms created by the
    evaluation. *)
Lemma GALNUA_multistep_rev :
  forall fs r fs' r' l, ⟨ fs , r ⟩ -[ l ]->ₗ* ⟨ fs' , r' ⟩ ->
  forall avs n, generates_at_least_n_unique_atoms fs' r'
    (avs ∪ (mk_atom_set l)) n
->
  generates_at_least_n_unique_atoms fs r avs
    (n + (size ((mk_atom_set l) ∖ avs))).
Proof.
  intros fs r fs' r' l H. destruct H.
  induction H; intros; subst.
  - unfold mk_atom_set in *; simpl in *.
    assert (avs ∪ ∅ = avs). { set_solver. }
    assert (∅ ∖ avs = ∅). { set_solver. }
    rewrite H1, size_empty, Nat.add_0_r.
    rewrite H0 in H. assumption.
  - destruct s; simpl option_cons in *.
    + destruct s; destruct s eqn:Hid.
      3: {
        pose proof (side_effect_ac_value _ _ _ _ _ H).
        destruct H1; subst. pose proof (mk_atom_set_union x l).
        rewrite H1 in *. clear H1.
        destruct (decide (x ∈ mk_atom_set l)).
        * assert ({[x]} ∪ mk_atom_set l = mk_atom_set l).
          { set_solver. } rewrite H1 in *; clear H1.
          apply IHstep_rt in H2.
          eapply generates_step_false; try eassumption.
        * destruct (decide (x ∈ avs)).
          -- assert (avs ∪ ({[x]} ∪ mk_atom_set l) = avs ∪ mk_atom_set l).
             { set_solver. } rewrite H1 in *; clear H1.
             assert (({[x]} ∪ mk_atom_set l) ∖ avs = mk_atom_set l ∖ avs).
             { set_solver. } rewrite H1 in *; clear H1.
             apply IHstep_rt in H2.
             eapply generates_step_false; try eassumption.
          -- assert (avs ∪ ({[x]} ∪ mk_atom_set l) =
               ({[x]} ∪ avs) ∪ mk_atom_set l). { set_solver. }
             rewrite H1 in H2; clear H1. apply IHstep_rt in H2.
             assert (({[x]} ∪ mk_atom_set l) ∖ avs = 
                {[x]} ∪ (mk_atom_set l ∖ avs)). { set_solver. }
             rewrite H1; clear H1.
             assert ({[x]} ## mk_atom_set l ∖ avs). { set_solver. }
             rewrite (size_union _ _ H1), size_singleton. clear H1.
             assert (mk_atom_set l ∖ ({[x]} ∪ avs) =
               mk_atom_set l ∖ avs). { set_solver. }
             rewrite H1 in H2; clear H1.
             assert (n + (1 + size (mk_atom_set l ∖ avs)) =
               S (n + size (mk_atom_set l ∖ avs))). { lia. }
             rewrite H1; clear H1.
             eapply generates_step_true_unique; try eassumption.
      }
      all: assert (s <> AtomCreation);
        [subst;discriminate|subst];
        pose proof (mk_atom_set_unfit2 _ H1 l0 l);
        rewrite H3 in *; eapply IHstep_rt in H2;
        eapply generates_step_false; try eassumption.
    + eapply IHstep_rt in H2.
      eapply generates_step_false; eassumption.
Qed.

(** A variant of `GALNUA_multistep_rev` with the subtraction in the
    premise, mirroring `GALNUA_multistep`. *)
Corollary GALNUA_multistep_rev_alt:
  forall fs r fs' r' l, ⟨ fs , r ⟩ -[ l ]->ₗ* ⟨ fs' , r' ⟩ ->
  forall avs n, generates_at_least_n_unique_atoms fs' r'
    (avs ∪ (mk_atom_set l)) (n - (size ((mk_atom_set l) ∖ avs)))
->
  generates_at_least_n_unique_atoms fs r avs n.
Proof.
  intros. destruct H.
  destruct (decide (size (mk_atom_set l ∖ avs) <= n)).
  { assert (exists m, n = m + size (mk_atom_set l ∖ avs)).
    { clear - l0. exists (n - size (mk_atom_set l ∖ avs)). lia. }
    destruct H1. subst.
    eapply GALNUA_multistep_rev. 
    + exists x. eassumption.
    + assert (x0 + size (mk_atom_set l ∖ avs) -
        size (mk_atom_set l ∖ avs) = x0). { lia. }
      rewrite H1 in H0. assumption. }
  { assert (n - size (mk_atom_set l ∖ avs) = 0). { lia. }
    rewrite H1 in *. clear H1.
    assert (exists m, n = size (mk_atom_set l ∖ avs) - m).
    { clear - n0. exists (size (mk_atom_set l ∖ avs) - n). lia. }
    destruct H1; subst.
    apply GALNUA_gen_many_less with (n := 0 + size (mk_atom_set l ∖ avs)).
    + eapply GALNUA_multistep_rev; [exists x|]; eassumption.
    + clear - n0. lia. }
Qed.

(** * Equivalence of GALNUA and atom exhaustion *)

(** GALNUA with `n` implies an evaluation creating at least `n` new
    atoms. *)
Lemma soundness_helper1 :
  forall fs r avs n, generates_at_least_n_unique_atoms fs r avs n
->
  exists fs' r' l, ⟨ fs , r ⟩ -[ l ]->ₗ* ⟨ fs' , r' ⟩ /\
    size (mk_atom_set l ∖ avs) >= n.
Proof.
  intros fs r avs n H. induction H.
  - do 3 eexists. split.
    * eexists. apply SubstSemanticsLabeled.step_refl.
    * assert (mk_atom_set [] = ∅). reflexivity. rewrite H.
      assert (∅ ∖ s = ∅). { set_solver. }
      rewrite H0, size_empty. lia.
  - destruct IHgenerates_at_least_n_unique_atoms.
    do 4 destruct H1. destruct l.
    * do 2 eexists. exists (s0::x1). split.
      + exists (S x2). eapply SubstSemanticsLabeled.step_trans.
        eassumption. apply H1. auto.
      + destruct s0. destruct s0 eqn:Hid.
        1-2: assert (s0 <> AtomCreation);
             [subst;discriminate|subst];
             pose proof (mk_atom_set_unfit2 _ H3 l x1);
             rewrite H4; assumption.
        pose proof (side_effect_ac_value _ _ _ _ _ H).
        destruct H3; subst. rewrite mk_atom_set_union.
        clear - H2.
        assert (size (mk_atom_set x1 ∖ s) ≤
          size (({[x3]} ∪ mk_atom_set x1) ∖ s)).
        { apply subseteq_size. set_solver. } lia.
    * do 2 eexists. exists x1. split.
      + exists (S x2). eapply SubstSemanticsLabeled.step_trans.
        eassumption. apply H1. auto.
      + assumption.
  - destruct IHgenerates_at_least_n_unique_atoms.
    do 4 destruct H2. do 2 eexists.
    exists ((AtomCreation, [VLit av])::x1). split.
    + exists (S x2). eapply SubstSemanticsLabeled.step_trans.
      eassumption. apply H2. auto.
    + rewrite mk_atom_set_union.
      assert (({[av]} ∪ mk_atom_set x1) ∖ s =
        ({[av]} ∪ (mk_atom_set x1 ∖ s))). { set_solver. }
      rewrite H4. clear H4. rewrite size_union_alt, size_singleton.
      assert (mk_atom_set x1 ∖ s ∖ {[av]} = mk_atom_set x1 ∖ ({[av]} ∪ s)).
      { set_solver. } rewrite H4. clear - H3. lia.
Qed.

(** Soundness of GALNUA for `atom_exhaustion_aux`. *)
Corollary soundness_helper2 : forall atom_limit fs r avs,
  generates_at_least_n_unique_atoms fs r avs (atom_limit - size (avs) + 1) ->
  atom_exhaustion_aux fs r avs atom_limit.
Proof.
  intros.
  apply soundness_helper1 in H.
  do 5 destruct H. do 3 eexists. split.
  - eexists. eassumption.
  - assumption.
Qed.

(** Completeness of GALNUA for `atom_exhaustion_aux`. *)
Lemma completeness_helper (fs: FrameStack) (r: Redex) (avs: gset string) (atom_limit: nat):
  atom_exhaustion_aux fs r avs atom_limit
->
  generates_at_least_n_unique_atoms fs r avs (atom_limit - size (avs) + 1).
Proof.
  unfold atom_exhaustion_aux.
  intros. do 4 destruct H.
  eapply GALNUA_multistep_rev_alt.
  + eassumption.
  + remember (atom_limit - size (avs)) as s. clear Heqs.
    assert (s + 1 - size (mk_atom_set x1 ∖ avs) = 0). { lia. }
    rewrite H1. apply generates_terminal.
Qed.

(** Soundness: if `e` generates more than `atom_limit` new atoms, then it is
    vulnerable to atom exhaustion. *)
Theorem soundness (e: Exp) (atom_limit: nat):
  generates_at_least_n_unique_atoms [] e ∅ (atom_limit + 1)
->
  atom_exhaustion e atom_limit.
Proof.
  assert (atom_limit + 1 = atom_limit - size(∅:gset string) + 1).
  { rewrite size_empty. lia. } rewrite H. clear H.
  unfold atom_exhaustion. apply soundness_helper2.
Qed.

(** Completeness: if `e` is vulnerable to atom exhaustion, then it generates
    more than `atom_limit` new atoms. *)
Theorem completeness (e: Exp) (atom_limit: nat):
  atom_exhaustion e atom_limit
->
  generates_at_least_n_unique_atoms [] e ∅ (atom_limit + 1).
Proof.
  unfold atom_exhaustion.
  assert (atom_limit + 1 = atom_limit - size(∅:gset string) + 1).
  { rewrite size_empty. lia. } rewrite H. clear H.
  apply completeness_helper.
Qed.

(** * Compositional reasoning *)

(** GALNUA for `let`: if `e1` evaluates to `vs`, then `let <...> = e1 in e2`
    generates the atoms of `e1` followed by the atoms of
    `e2.[vs/...]`. *)
Lemma GALNUA_let :
  forall fs n (e1 e2 : Exp) (vs : list Val) avs atoms l,
    ⟨[], e1⟩ -[l]->ₗ* ⟨[], RValSeq vs⟩ ->
    length vs = n ->
    generates_at_least_n_unique_atoms fs e2.[list_subst vs idsubst] (avs ∪ mk_atom_set l) (atoms - size (mk_atom_set l ∖ avs)) ->
  generates_at_least_n_unique_atoms fs (ELet n e1 e2) avs atoms.
Proof.
  intros.
  eapply generates_step_false. by constructor. destruct H.
  apply frame_indep_nil_labeled with (Fs' := FLet n e2 :: fs) in H.
  simpl in H. apply ex_intro with (x := x) in H.
  eapply GALNUA_multistep_rev in H.
  2: {
    eapply generates_step_false. econstructor. assumption.
    exact H1.
  }
  assert ((atoms - size (mk_atom_set l ∖ avs) + size (mk_atom_set l ∖ avs)) >= atoms) by lia.
  eapply GALNUA_gen_many_less; eassumption.
Qed.

End AtomExhaustion.