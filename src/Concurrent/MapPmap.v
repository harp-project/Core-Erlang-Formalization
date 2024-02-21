From CoreErlang.Concurrent Require Import BarbedBisim.
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


Section map_pmap.

Context {l : Val}
        {l' : list Val}
        {i : nat}
        {f : Val -> Val}
        {f_clos : Val}
        {f_clos_closed : VALCLOSED f_clos}
        {ι : PID} (* This PID will be observed *).

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
  VClos [(i, 2, map_body)] i 2 map_body.

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

(*
pmap(F, L) ->
  {L1, L2} = halve(L),
  spawn(fun(L, Addr) -> Addr ! map(F, L), [L1, self()]),
  Mapped = map(F, L2),
  receive
    L1 -> L1 ++ L2
  end
*)
Definition par_map : Redex :=
  ECase (ECall (˝VLit "lists") (˝VLit "split") [˝VLit (Z.of_nat i); ˝VVar 2])
    [
      ([PTuple [PVar; PVar]], ˝ttrue,
        °ESeq 
          (°ECall (˝erlang) (˝spawn) [
           °EFun 2 (°ECall (˝erlang) (˝send) [˝VVar 0; °EApp (˝map_clos) [˝f_clos; ˝VVar 1]]);
           ˝VVar 0])
        (
          ELet 1 (°EApp (˝map_clos) [˝f_clos; ˝VVar 1])
             (EReceive [
               ([PVar], ˝ttrue, 
                 °ECall (˝erlang) (˝send)
                   [
                    ˝VPid ι;
                    °ECall (˝erlang) (˝VLit "++") [˝VVar 0; ˝VVar 1]
                   ])
             ] (˝infinity) (˝VNil)) (* TODO: write a receive here! *)
        )
      )
    ].

End map_pmap.
