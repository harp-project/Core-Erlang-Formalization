From CoreErlang.Concurrent Require Import BisimReductions.
From CoreErlang.FrameStack Require Import SubstSemantics Examples.

Import ListNotations.

Theorem sequential_to_node :
  forall k fs e fs' e', ⟨fs, e⟩ -[k]-> ⟨fs', e'⟩ ->
    forall O ι eth Π mb links flag,
      (eth, ι ↦ inl (fs, e, mb, links, flag) ∥ Π) -[repeat (τ, ι) k]ₙ->*
      (eth, ι ↦ inl (fs', e', mb, links, flag) ∥ Π) with O.
Proof.
  intros *. intro H. induction H; intros.
  * constructor.
  * simpl. econstructor.
    constructor. constructor. eassumption.
    by left.
    apply IHstep_rt.
Qed.

(* Everything which falls under the n_other category can be lifted to
   inter-process level *)
Theorem process_local_to_node :
  forall p p' l ι, p -⌈l⌉->* p' ->
    Forall (fun a => a = τ \/ a = ε \/ a = ASelf ι) l ->
    forall O eth Π,
      (eth, ι ↦ p ∥ Π) -[map (fun a => (a, ι)) l]ₙ->*
      (eth, ι ↦ p' ∥ Π) with O.
Proof.
  intros *. intro H. induction H; intros.
  * constructor.
  * simpl. inv H1. specialize (IHLabelStar H5 O eth Π). econstructor.
    2: exact IHLabelStar.
    clear H5 H0 IHLabelStar. destruct_or! H4; subst.
    - constructor; auto.
    - constructor; auto.
    - constructor; auto.
Qed.

(* Lemma meta_to_cons_mk_list :
  forall l l',
    meta_to_cons l = l' <-> mk_list l' = Some l.
Proof.
  split; revert l'; induction l; intros; simpl in H; subst.
  * by simpl.
  * simpl. 
Qed. *)

Lemma meta_to_cons_mk_list : forall l, mk_list (meta_to_cons l) = Some l.
Proof.
  induction l.
  by simpl.
  simpl. by rewrite IHl.
Qed.

Lemma mk_list_meta_to_cons : forall l l', mk_list l = Some l' ->
  meta_to_cons l' = l.
Proof.
  induction l; intros; inv H.
  * by simpl.
  * case_match. 2: congruence.
    inv H1. simpl. f_equal.
    by apply IHl2.
Qed.

Lemma eval_split_correct :
  forall l l' idx,
  mk_list l = Some l' ->
  idx < length l' ->
  eval_split (VLit (Z.of_nat idx)) l = RValSeq [VTuple [meta_to_cons (take idx l'); meta_to_cons (drop idx l')]].
Proof.
  intros. simpl.
  case_match.
  * apply Z.ltb_lt in H1. lia.
  * rewrite Nat2Z.id.
    clear H1. revert l l' H0 H. induction idx; intros.
    - simpl. rewrite drop_0. by erewrite mk_list_meta_to_cons.
    - simpl. destruct l; inv H. simpl in H0. lia.
      case_match. 2: congruence. inv H2. simpl in H0.
      specialize (IHidx l2 l ltac:(lia) H). case_match. 2: congruence.
      destruct p. simpl.
      by inv IHidx.
Qed.

Lemma mk_list_closed :
  forall l l' Γ,
    VAL Γ ⊢ l ->
    mk_list l = Some l' -> Forall (ValScoped Γ) l'.
Proof.
  induction l; intros; inv H0. by constructor.
  case_match; try congruence.
  inv H2. constructor. by inv H.
  apply IHl2; by destruct_scopes.
Qed.

Lemma meta_to_cons_closed :
  forall l Γ,
    Forall (ValScoped Γ) l ->
    VAL Γ ⊢ meta_to_cons l.
Proof.
  induction l; intros; inv H; simpl; by scope_solver.
Qed.

Lemma EReceive_scope :
  forall l time r Γ,
  Forall (fun '(pl, g, e) => EXP PatListScope pl + (3 + Γ) ⊢ g /\ EXP PatListScope pl + (3 + Γ) ⊢ e) l ->
  EXP 3 + Γ ⊢ time ->
  EXP 4 + Γ ⊢ r ->
  EXP Γ ⊢ EReceive l time r.
Proof.
  intros. do 6 scope_solver_step.
  1: scope_solver.
  2: lia.
  do 2 scope_solver_step. scope_solver.
  1: scope_solver.
  do 2 scope_solver_step.
  1: scope_solver.
  do 2 scope_solver_step.
  scope_solver_step.
  1: scope_solver.
  all: intros; simpl in *; rewrite app_length, map_length in H2; simpl in H2;
  assert (i < length l \/ i = length l) by lia; destruct H3.
  {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)) in H.
    apply H in H3 as H'.
    repeat rewrite map_app. repeat rewrite map_map. simpl.
    rewrite app_nth1. 2: by rewrite map_length.
    rewrite app_nth1. 2: by rewrite map_length.
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    destruct nth, p. cbn. apply H'.
  }
  {
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    subst. erewrite <- map_length. rewrite nth_middle. cbn. scope_solver.
  }
  {
    rewrite indexed_to_forall with (def := ([], ˝VNil, ˝VNil)) in H.
    apply H in H3 as H'.
    repeat rewrite map_app. repeat rewrite map_map. simpl.
    rewrite app_nth1. 2: by rewrite map_length.
    rewrite app_nth1. 2: by rewrite map_length.
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    extract_map_fun F.
    assert (° ESeq (° EPrimOp "remove_message" []) (˝VNil) = F ([], ˝VNil, ˝VNil)). {
      by subst F.
    }
    erewrite (nth_indep (map F l) _ (° ESeq (° EPrimOp "remove_message" []) (˝ VNil))).
    rewrite H4. rewrite map_nth. subst F.
    destruct nth, p. cbn.
    do 2 scope_solver_step.
    1: scope_solver.
    1: apply H'.
    by rewrite map_length.
  }
  {
    rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    setoid_rewrite map_nth with (d := ([], ˝VNil, ˝VNil)).
    subst. erewrite <- map_length. rewrite nth_middle. cbn. scope_solver.
  }
Qed.

Lemma eval_append_correct :
  forall l l',
    eval_append (meta_to_cons l) (meta_to_cons l') = RValSeq [meta_to_cons (l ++ l')].
Proof.
  induction l; simpl; intros.
  * reflexivity.
  * by rewrite IHl.
Qed.

Section seq_map_eval.

Context {l : Val}
        {l' : list Val}
        {ident : nat}
        {f : Val -> Val}
        {f_clos : Val}
        {f_clos_closed : VALCLOSED f_clos}.

Hypothesis f_simulates :
  forall v : Val, create_result (IApp f_clos) [v] [] = Some (RValSeq [f v], []).
Hypothesis l_is_proper : mk_list l = Some l'.
Hypothesis f_closed : forall v, VALCLOSED v -> VALCLOSED (f v).
Hypothesis l_closed : VALCLOSED l.

Definition map_body : Exp :=
  ECase (˝VVar 2) [
      ([PNil], ˝ttrue, ˝VNil);
      ([PCons PVar PVar], ˝ttrue, °ECons (EApp (˝VVar 3) [˝VVar 0])
                                        (EApp (˝VVar 2) [˝VVar 3;˝VVar 1])
      )
    ].

Definition map_clos : Val :=
  VClos [(ident, 2, map_body)] ident 2 map_body.

Lemma map_clos_closed :
  VALCLOSED map_clos.
Proof.
  scope_solver.
Qed.

Hint Resolve map_clos_closed : examples.

Open Scope string_scope.

Ltac do_step := econstructor; [constructor;auto with examples| simpl].

Theorem map_clos_eval :
  ⟨[], EApp (˝map_clos) [˝f_clos; ˝l]⟩ -->* RValSeq [meta_to_cons (map f l')].
Proof.
  generalize dependent l'. clear l_is_proper l'.
  induction l; intros; simpl in *; inv l_is_proper.
  * simpl.
    eexists. split. repeat constructor.
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 6 do_step.
    constructor.
  * case_match. 2: congruence. destruct l'; inv H0. clear IHv1.
    inv l_closed.
    specialize (IHv2 H4 _ eq_refl). destruct IHv2 as [clock [IHv2 IHD]].
    eexists. split.
    {
      inv IHv2. inv H1. clear H4.
      simpl. constructor. constructor; auto.
    }
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 2 do_step.
    econstructor. apply eval_step_case_not_match. reflexivity.
    do 4 do_step.
    eapply transitive_eval.
    rewrite <- app_nil_l at 1. apply frame_indep_nil.
    {
      repeat rewrite vclosed_ignores_ren; auto.
      rewrite vclosed_ignores_sub; auto.
      exact IHD.
    }
    repeat rewrite vclosed_ignores_ren; auto.
    rewrite vclosed_ignores_sub; auto.
    do 6 do_step.
    econstructor. econstructor; auto. simpl. by rewrite f_simulates.
    econstructor. constructor; auto. simpl.
    constructor.
Qed.


End seq_map_eval.

Hint Resolve map_clos_closed : examples.



Section map_pmap.

Context {l : Val}
        {l' : list Val}
        {ident : nat}
        {f : Val -> Val}
        {f_clos : Val}
        {f_clos_closed : VALCLOSED f_clos}
        {ι : PID} (* This PID will be observed *).

Hypothesis f_simulates :
  forall v : Val, create_result (IApp f_clos) [v] [] = Some (RValSeq [f v], []).
Hypothesis l_is_proper : mk_list l = Some l'.
Hypothesis f_closed : forall v, VALCLOSED v -> VALCLOSED (f v).
Hypothesis l_closed : VALCLOSED l.

Open Scope string_scope.

(* Definition map_body : Exp :=
  ECase (˝VVar 2) [
      ([PNil], ˝ttrue, ˝VNil);
      ([PCons PVar PVar], ˝ttrue, °ECons (EApp (˝VVar 3) [˝VVar 0])
                                        (EApp (˝VVar 2) [˝VVar 3;˝VVar 1])
      )
    ].

Definition map_clos : Val :=
  VClos [(ident, 2, map_body)] ident 2 map_body.

Lemma map_clos_closed :
  VALCLOSED map_clos.
Proof.
  scope_solver.
Qed.

Hint Resolve map_clos_closed : examples.

Open Scope string_scope.

Ltac do_step := econstructor; [constructor;auto with examples| simpl].

Theorem map_clos_eval :
  ⟨[], EApp (˝map_clos) [˝f_clos; ˝l]⟩ -->* RValSeq [meta_to_cons (map f l')].
Proof.
  generalize dependent l'. clear l_is_proper l'.
  induction l; intros; simpl in *; inv l_is_proper.
  * simpl.
    eexists. split. repeat constructor.
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 6 do_step.
    constructor.
  * case_match. 2: congruence. destruct l'; inv H0. clear IHv1.
    inv l_closed.
    specialize (IHv2 H4 _ eq_refl). destruct IHv2 as [clock [IHv2 IHD]].
    eexists. split.
    {
      inv IHv2. inv H1. clear H4.
      simpl. constructor. constructor; auto.
    }
    do 7 do_step.
    econstructor. econstructor; auto. cbn.
    do 2 do_step.
    econstructor. apply eval_step_case_not_match. reflexivity.
    do 4 do_step.
    eapply transitive_eval.
    rewrite <- app_nil_l at 1. apply frame_indep_nil.
    {
      repeat rewrite vclosed_ignores_ren; auto.
      rewrite vclosed_ignores_sub; auto.
      exact IHD.
    }
    repeat rewrite vclosed_ignores_ren; auto.
    rewrite vclosed_ignores_sub; auto.
    do 6 do_step.
    econstructor. econstructor; auto. simpl. by rewrite f_simulates.
    econstructor. constructor; auto. simpl.
    constructor.
Qed.
 *)
(*
  Alternative suggestion:
  1. Have a server with a number of PIDs that compute a map of some list and function
  sequentially.
  2. Prove the equivalence.
  3. Any pmap function should build up the structure of that server first (with spawns).
*)


Context (idx : nat)
        (Hidx : idx < length l').

(*
pmap(F, L) ->
  {L1, L2} = lists:split(Idx, L),
  spawn(fun(L, Addr) -> Addr ! map(F, L), [L1, self()]),
  Mapped = map(F, L2),
  receive
    L1 -> L1 ++ L2
  end
*)
Definition receive : Exp :=
(EReceive [
               ([PVar], ˝ttrue, 
                 °ECall (˝erlang) (˝send)
                   [
                    ˝VPid ι;
                    (* NOTE: the nameless approach makes it harder to guess
                       the variable used outside the given clauses in a receive
                                                               |
                                                               v
                    *)
                    °ECall (˝erlang) (˝VLit "++") [˝VVar 0; ˝VVar 4]
                   ])
             ] (˝infinity) (˝VNil)).

Definition seq_sec : Exp :=
  ELet 1 (°EApp (˝@map_clos ident) [˝f_clos; ˝VVar 2])
             receive.

Print EReceive.
Lemma receive_closed :
  EXP 1 ⊢ receive.
Proof.
  repeat constructor; simpl. 2: lia.
  destruct i. 2: lia.
  simpl. intros. do 4 scope_solver_step.
  1, 2: scope_solver.
  1-2: destruct i; intros.
  2, 4: destruct i; try lia.
  all: simpl. 1-2: scope_solver.
  all: do 3 scope_solver_step.
  1: scope_solver.
  1: scope_solver_step.
  1: scope_solver.
  all: try destruct i; intros.
  1, 3, 5, 7: simpl. 1-3:scope_solver.
  1: do 10 scope_solver_step.
  all: do 8 scope_solver_step.
  all: intros; destruct i; try destruct i; try destruct i.
  all: do 2 scope_solver_step. lia.
  all: intros; destruct i; try destruct i; try destruct i.
  all: scope_solver.
Qed.

Hint Resolve receive_closed : examples.

Definition send_body : Exp :=
  (°ECall (˝erlang) (˝send) [˝VVar 0; °EApp (˝@map_clos ident) [˝f_clos; ˝VVar 1]]).

Definition par_map : Redex :=
  ECase (ECall (˝VLit "lists") (˝VLit "split") [˝VLit (Z.of_nat idx); ˝l])
    [
      ([PTuple [PVar; PVar]], ˝ttrue,
        °ELet 1 (°ECall (˝erlang) (˝self) [])
          (°ESeq 
            (°ECall (˝erlang) (˝spawn) [
             °EFun 2 send_body;
             °ECons (˝VVar 0) (°ECons (˝VVar 1) (˝VNil))])
          (
            seq_sec
          )
        )
      )
    ].

(* Implicit assumptions with this definition:
   - Only the child communicates, there are no other messages awaiting to
     be processed by the parent process!!!
   - If the equivalence is based on the empty ether, errors are rules out!!!
*)

Context (ι_base : PID)
        (Hbase : ι_base <> ι).

Opaque eval_split.
Opaque seq_sec.
Opaque map_clos.
Theorem split_eval O :
  exists l,
    (∅, ι_base ↦ inl ([], par_map, emptyBox, ∅, false) ∥ ∅) -[l]ₙ->* 
    (∅, ι_base ↦ inl ([FParams (ICall erlang spawn) [VClos [] 0 2 send_body] [];FSeq seq_sec.[up_subst
                (meta_to_cons (take idx l') .: meta_to_cons (drop idx l') .: idsubst)].[
     VPid ι_base/] ], RValSeq [VCons (VPid ι_base) (VCons (meta_to_cons (take idx l')) VNil)], emptyBox, ∅, false) ∥ ∅) with O /\
    Forall (fun x => x.1 = τ \/ exists ι, x.1 = ASelf ι) l.
Proof.
  eexists. split.
  {
    eapply closureNodeSem_trans.
    * apply sequential_to_node.
      do 10 do_step.
      econstructor 2. econstructor. reflexivity. simpl.
      unfold eval_transform_list. simpl.
      erewrite eval_split_correct. 2-3: eassumption.
      do 9 do_step.
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_sub; auto with examples.
      constructor.
    * eapply n_trans. apply n_other with (ι := ι_base) (a := ASelf ι_base).
      2: set_solver.
      constructor.
      apply sequential_to_node.
      do 11 do_step.
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_ren; auto with examples.
      2: {
        apply meta_to_cons_closed.
        apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
        by apply Forall_take.
      }
      rewrite vclosed_ignores_sub; auto with examples.
      2: {
        apply meta_to_cons_closed.
        apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
        by apply Forall_take.
      }
      do 4 do_step.
      {
        apply meta_to_cons_closed.
        apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
        by apply Forall_take.
      }
      do 4 do_step.
      constructor.
  }
  {
    apply Forall_app. split. 2: constructor.
    1, 3: by apply Forall_repeat; left.
    right. by eexists.
  }
Qed.
Transparent eval_split.
Transparent seq_sec.


Definition map_seq_send :Exp :=
  °ECall (˝erlang) (˝send)
       [
        ˝VPid ι;
        °EApp (˝@map_clos ident) [˝f_clos; ˝l]
       ].

Lemma take_helper1 :
  VALCLOSED (meta_to_cons (take idx l')).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  by apply Forall_take.
Qed.

Lemma take_helper2 :
  VALCLOSED (meta_to_cons (map f (take idx l'))).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  apply list.Forall_forall. intros. apply elem_of_map_iff in H.
  destruct_hyps. subst.
  apply f_closed. rewrite list.Forall_forall in l_is_proper.
  apply l_is_proper. clear-H0.
  pose proof subseteq_take idx l'. set_solver.
Qed.

Lemma drop_helper1 :
  VALCLOSED (meta_to_cons (drop idx l')).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  by apply Forall_drop.
Qed.

Lemma drop_helper2 :
  VALCLOSED (meta_to_cons (map f (drop idx l'))).
Proof.
  apply meta_to_cons_closed.
  apply mk_list_closed with (Γ := 0) in l_is_proper. 2: assumption.
  apply list.Forall_forall. intros. apply elem_of_map_iff in H.
  destruct_hyps. subst.
  apply f_closed. rewrite list.Forall_forall in l_is_proper.
  apply l_is_proper. clear-H0.
  pose proof subseteq_drop idx l'. set_solver.
Qed.

Opaque receive.
(* NOTE: coercions start to tangle up here for parsing *)
Theorem map_pmap_bisim_empty_ether :
  (∅, ι_base ↦ inl ([], RExp (map_seq_send), emptyBox, ∅, false) ∥ ∅) ~
  (∅, ι_base ↦ inl ([], par_map, emptyBox, ∅, false) ∥ ∅) observing {[ι]}.
Proof.
  opose proof* (@map_clos_eval l l' ident f f_clos).
  all:try assumption. destruct H as [mapₖ [Hres HD]].
  pose proof split_eval {[ι]}. destruct H as [pmapₗ [HD2 Hₗ]].
  eapply barbedBisim_trans.
  eapply normalisation_τ_many_bisim.
  2: set_solver.
  2: {
    apply sequential_to_node.
    do 8 do_step.
    eapply frame_indep_core in HD.
    exact HD.
  }
  1: by apply Forall_repeat.
  simpl.
  eapply barbedBisim_trans.
  2: {
    apply barbedBisim_sym. eapply normalisation_τ_self_many_bisim.
    3: exact HD2.
    1: assumption.
    set_solver.
  }
  constructor.
  2,4: intros; exists source, []; eexists; simpl; split; try by constructor.
  { (* sequential process gets a signal (which can only be a send)
       In this case, the entire concurrent map has to be evaluated!
     *)
    intros. assert (ι0 = ι_base). {
      destruct A'.
      apply deconstruct_reduction in H. destruct_hyps.
      put (lookup ι0 : ProcessPool -> _) on H as H'.
      setoid_rewrite lookup_insert in H'. destruct (decide (ι0 = ι_base)).
      assumption.
      setoid_rewrite lookup_insert_ne in H'; auto. set_solver.
    }
    subst.
    assert (a = ASend ι_base ι (SMessage (meta_to_cons (map f l')))). {
      inv H.
      * put (lookup ι_base : ProcessPool -> _) on H2 as P.
        setoid_rewrite lookup_insert in P. inv P. by inv H5.
      * unfold etherPop in H2. repeat case_match; try congruence.
        set_solver.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        destruct_or! H6; inv H2; try inv H9; cbn in *; try congruence.
      * put (lookup ι_base : ProcessPool -> _) on H1 as P.
        setoid_rewrite lookup_insert in P. inv P.
        inv H2. inv H10.
    }
    subst. inv H. 2: { destruct_or! H6; congruence. } clear H1.
    put (lookup ι_base : ProcessPool -> _) on H2 as P.
    setoid_rewrite lookup_insert in P. inv P. inv H7. 
    (* prs = ∅ *)
    assert (forall p, ι_base ↦ p ∥ prs = ι_base ↦ p ∥ ∅) as X. {
      intros.
      apply map_eq. intros. put (lookup i : ProcessPool -> _) on H2 as D.
      destruct (decide (i = ι_base)).
      * subst. by setoid_rewrite lookup_insert.
      * setoid_rewrite lookup_insert_ne in D; auto.
        by setoid_rewrite lookup_insert_ne.
    }
    clear H2.
    (* To be able to use eexists, we need to pose map evaluation first! *)
    opose proof* (@map_clos_eval (meta_to_cons (take idx l')) (take idx l') ident f f_clos) as InitEval.
    all: try eassumption.
    1: apply meta_to_cons_mk_list.
    1: { apply take_helper1. }
    opose proof* (@map_clos_eval (meta_to_cons (drop idx l')) (drop idx l') ident f f_clos) as TailEval.
    all: try eassumption.
    1: apply meta_to_cons_mk_list.
    1: { apply drop_helper1. }
    destruct InitEval as [Initₖ [InitRes InitEval]].
    destruct TailEval as [Tailₖ [TailRes TailEval]].
    (**)
    do 2 eexists. split.
    {
      (* reductions *)
      eapply n_trans.
      (* spawning the new process *)
      pose proof (infinite_is_fresh [ι; ι_base]) as HF.
      eapply n_spawn with (ι := ι_base) (ι' := fresh [ι; ι_base]).
      2: { clear-HF. set_solver. }
      2: {
        admit. (* Technical - revise fresh generation on the ether + pool! that will 
                  also be future proof for general ethers *)
      }
      2: {
        admit. (* Technical *)
      }
      3: {
        constructor. reflexivity.
      }
      1: {
        simpl. reflexivity.
      }
      1: {
        simpl. reflexivity.
      }
      rewrite vclosed_ignores_sub; auto with examples.
      rewrite vclosed_ignores_sub; auto with examples.
      (* map is evaluated in the spawned process *)
      eapply closureNodeSem_trans.
      {
        apply sequential_to_node.
        do 8 do_step.
        eapply frame_indep_core in InitEval.
        exact InitEval.
      }
      simpl.
      repeat rewrite (vclosed_ignores_sub map_clos); auto with examples.
      repeat rewrite (vclosed_ignores_sub f_clos); auto with examples.
      repeat rewrite vclosed_ignores_ren; auto.
      2: { apply drop_helper1. }
      (* map is sent back to the parent *)
      eapply n_trans. eapply n_send. constructor.
      { apply take_helper2. }
      (* map arrives to the parent *)
      setoid_rewrite insert_commute.
      2: {
        pose proof (infinite_is_fresh [ι; ι_base]).
        set_solver.
      }
      eapply n_trans. apply n_arrive with (ι0 := fresh [ι; ι_base]).
      {
        unfold etherAdd, etherPop.
        setoid_rewrite lookup_empty.
        setoid_rewrite lookup_insert.
        setoid_rewrite lookup_empty.
        setoid_rewrite insert_insert.
        reflexivity.
      }
      {
        constructor.
      }
      (* parent evaluates the map *)
      eapply closureNodeSem_trans.
      {
        apply sequential_to_node.
        do 2 do_step.
        rewrite vclosed_ignores_sub.
        2: { apply drop_helper1. }
        eapply frame_indep_core in TailEval.
        eapply transitive_eval. exact TailEval.
        simpl. do_step.
        constructor.
      }
      (* parent receives the first part of the map
        This is painful :(
      *)
      eapply closureNodeSem_trans.
      {
        eapply process_local_to_node.
        {
  Transparent receive.
          unfold receive, EReceive. simpl.
          repeat rewrite vclosed_ignores_ren; try apply drop_helper2.
          eapply lsstep. constructor. constructor. cbn. reflexivity.
          cbn.
          eapply lsstep. do 2 constructor.
          eapply lsstep. do 2 constructor.
          1: {
            opose proof* (EReceive_scope ([([PVar], ˝ VLit "true",
                                  ° ECall (˝ VLit "erlang") (˝ VLit "!")
                                      [˝ VPid ι;
                                       ° ECall (˝ VLit "erlang") 
                                           (˝ VLit "++")
                                           [˝ VVar 0; ˝ meta_to_cons (map f (drop idx l'))]])]) (˝VLit "infinity"%string) (˝VNil) 0).
            2-3: scope_solver.
            {
              constructor; auto. split. scope_solver.
              do 6 scope_solver_step.
              all: intros; destruct i; try destruct i; try destruct i.
              1,3-5,7-9,11-12: scope_solver.
              1: scope_solver_step; eapply loosen_scope_val; try apply drop_helper2; lia.
              all: do 6 scope_solver_step.
            }
            inv H. inv H2. constructor; auto.
            intros. simpl in *.
            specialize (H3 0 ltac:(lia)). simpl in H3. apply H3.
          }
          eapply lsstep. do 2 constructor.
          eapply lsstep. apply p_local. econstructor. congruence. reflexivity.
          simpl.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_recv_peek_message_ok. reflexivity.
          eapply lsstep. apply p_local. constructor. reflexivity.
          simpl.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. apply eval_step_case_true. simpl.
          rewrite idsubst_is_id_val. simpl.
          repeat rewrite vclosed_ignores_ren; try apply drop_helper2.
          repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor.
          1: { apply take_helper2. }
          eapply lsstep. apply p_local. apply eval_step_case_match. reflexivity.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. apply eval_step_case_true. simpl.
          (* remove message from the mailbox *)
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_remove_message. by cbn.
          eapply lsstep. apply p_local. constructor.
          repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
          (* Reading configurations is easier from here *)
          (* evaluate send *)
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor. congruence.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. constructor.
          (* evaluate append *)
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. constructor.
          eapply lsstep. apply p_local. constructor. scope_solver.
          eapply lsstep. apply p_local. constructor. simpl.
          eapply lsstep. apply p_local. constructor. congruence.
          eapply lsstep. apply p_local. constructor.
          1: apply take_helper2.
          eapply lsstep. apply p_local. constructor. simpl.
          repeat rewrite vclosed_ignores_sub; try apply drop_helper2.
          eapply lsstep. apply p_local. constructor. apply drop_helper2.
          eapply lsstep. apply p_local. econstructor.
          { (* evaluate the meta-theoretical simulated append *)
            simpl. cbn.
            rewrite eval_append_correct.
            rewrite <- map_app, take_drop. reflexivity.
          }
          apply lsrefl.
        }
        {
          repeat constructor.
        }
      }
      (* parent sends the result *)
      eapply n_trans. apply n_send. constructor. assumption.
      (* the child process should be terminated for the equivalence *)
      setoid_rewrite insert_commute.
      2: {
        clear. pose proof (infinite_is_fresh [ι; ι_base]).
        set_solver.
      }
      eapply n_trans. apply n_other. apply p_terminate. by clear; set_solver.
      setoid_rewrite gset_to_gmap_empty.
      apply n_refl.
    }
    { (* equivalence - we need two helpers about dead processes and ether inserts *)
      rewrite X.
      eapply barbedBisim_trans.
      apply dead_process_bisim with (ι := fresh [ι;ι_base]).
      1: clear; pose proof (infinite_is_fresh [ι; ι_base]); set_solver.
      1: clear; pose proof (infinite_is_fresh [ι; ι_base]); set_solver.
      simpl. (* now the pools are equal, we have to do the same for the ethers *)
      unfold etherAdd. setoid_rewrite lookup_empty.
      setoid_rewrite lookup_insert_ne.
      2: clear; pose proof (infinite_is_fresh [ι; ι_base]); set_solver.
      setoid_rewrite lookup_empty.
      setoid_rewrite insert_commute at 2.
      2: clear; pose proof (infinite_is_fresh [ι; ι_base]); set_solver.
      remember (_ ↦ _ ∥ _ ↦ _ ∥ ∅) as P.
      setoid_rewrite <- HeqP.
      remember (insert (ι_base, ι) _ ∅) as E.
      apply ether_empty_update_bisim.
      clear-Hbase. set_solver.
      simpl. subst E. left.
      setoid_rewrite lookup_insert_ne. set_solver.
      set_solver.
    }
  }
  {
    
  }
Qed.
Transparent map_clos.

End map_pmap.
