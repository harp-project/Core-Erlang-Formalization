From CoreErlang.Eqvivalence.FsBs Require Export F1GiveNames.
From CoreErlang.Eqvivalence Require Export B3Tactics.

Import BigStep.






Import SubstSemantics.


Theorem step_one_either :
  forall Fs1 Fs2 r1 r2,
      ⟨ Fs1, r1 ⟩ --> ⟨ Fs2, r2 ⟩
  ->  (Fs1 = Fs2)
  \/  (exists F,
          Fs2 = F :: Fs1
      \/  Fs1 = F :: Fs2)
  \/  (exists F1 F2 Fs,
          Fs1 = F1 :: Fs
      /\  Fs2 = F2 :: Fs).
      (* /\  F1 <> F2). *)
Proof.
  itr.
  ivc - H;
    (try solve lft; ato);
    rgt.
  * rgt.
    exi - (FParams ident vl (e :: el)) (FParams ident (vl ++ [v]) el) xs.
    ato.
  * rgt.
    exi - (FParams ident vl (e :: el)) (FParams ident vl el) xs.
    ato.
  * lft.
    exi - (FParams ident vl []).
    rgt.
    ato.
  * lft.
    exi - (FParams ident vl []).
    rgt.
    ato.
  * lft.
    exi - (FParams IValues [] el).
    lft.
    ato.
  * lft.
    exi - (FParams ITuple [] el).
    lft.
    ato.
  * lft.
    exi - (FParams IMap [] (e2 :: flatten_list el)).
    lft.
    ato.
  * lft.
    exi - (FCallMod f el).
    lft.
    ato.
  * rgt.
    exi - (FCallMod f el) (FCallFun v el) xs.
    ato.
  * rgt.
    exi - (FCallFun m el) (FParams (ICall m f) [] el) xs.
    ato.
  * lft.
    exi - (FParams (IPrimOp f) [] el).
    lft.
    ato.
  * rgt.
    exi - (FApp1 el) (FParams (IApp v) [] el) xs.
    ato.
  * lft.
    exi - (FApp1 l).
    lft.
    ato.
  * rgt.
    do 3 eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * rgt.
    do 3 eei.
    ato.
  * rgt.
    do 3 eei.
    ato.
  * lft.
    eei.
    ato.
  * rgt.
    do 3 eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
  * lft.
    eei.
    ato.
Qed.


(* Theorem can_step :
  forall F e r k,
      ⟨ [F], RExp e ⟩ -[k]-> ⟨ [], r ⟩
  ->  exists k',
          k' < k
      ->  (forall i,
              i < k'
          ->  exists Fs r',
                  ⟨ [F], RExp e ⟩ -[i]-> ⟨ Fs ++ [F], r' ⟩)
      /\  (exists r' r'',
              ⟨ [F], RExp e ⟩ -[k']-> ⟨ [F], r' ⟩
          /\  ⟨ [F], r' ⟩ --> ⟨ [], r'' ⟩).
Proof.
  itr.
  ind - k as [| k IH].
  * ivc - H.
Restart.
  itr.
  ind - H.
  * eei.
    itr.
    lia.
  * des - IHstep_rt as [k' H1]. *)


Lemma construct_econs_result_steps :
  forall e1 e2 r,
      ((exists v1 v2,
          r = inl [VCons v1 v2]
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inl [v1]))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q1 v2,
          r = inr q1
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inr q1))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q2,
          r = inr q2
      /\  ⟨ [], e2 ⟩ -->* (to_redex (inr q2))))
  ->  ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r).
Proof.
  itr.
  des - H as [H | [H | H]].
  * des - H as [v1 [v2 [Heq [Hv1 Hv2]]]].
    sbt.
    des - Hv1 as [k1 [Hscope1 Hstep1]].
    des - Hv2 as [k2 [Hscope2 Hstep2]].
    open / Hscope1 Hscope2.
    step - Hstep2.
    step - Hstep1.
    step.
  * des - H as [v1 [v2 [Heq [Hv1 Hv2]]]].
    sbt.
    des - Hv1 as [k1 [Hscope1 Hstep1]].
    des - Hv2 as [k2 [Hscope2 Hstep2]].
    open / Hscope1 Hscope2.
    step - Hstep2.
    step - Hstep1.
    step.
  * des - H as [v2 [Heq Hv2]].
    sbt.
    des - Hv2 as [k2 [Hscope2 Hstep2]].
    open / Hscope2.
    step - Hstep2.
    step.
Qed.

Lemma destruct_econs_result_steps :
  forall e1 e2 r,
      ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r)
  ->  (exists v1 v2,
          r = inl [VCons v1 v2]
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inl [v1]))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q1 v2,
          r = inr q1
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inr q1))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q2,
          r = inr q2
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inr q2))).
Proof.
  (* itr.
  des - r as [vs | q].
  * lft.
    do 2 eei.
    
  ivc - H as [k [Hscope Hstep]].
  eapply transitive_eval in Hstep.
  ivc - Hstep.
  des - r; ivc - H2.
  ivs - H.
  eapply transitive_eval_rev in H0.
  ivs - H0.
  ivs - H1.
  des - r as [vs | q]; smp *.
  * lft.
    ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
    2: {
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H. *)
Admitted.



(* Theorem eq_fsbs :
  forall e r,
      step_any [] (RExp e) (to_redex r)
  ->  exists id1 id2,
        eval_expr [] [] "" id1 (give_names e) [] id2 (give_result r) [].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * gen - vs.
    ind ~ ind_fs_exp - e;
          itr.
    - admit.
    - (*EFUN*)
      des - H as [k [Hscope H]].
      ivc - H.
      ivc - H0.
      ivc - H1.
      2: ivc - H.
      do 2 eei.
      admit.
    - (*ECONS*)
      ivc - H.
      (*not implemented*)
      + ivc - H. 
         smp *.
        admit.
  ind - H.
  des - H as [Hscope H].
  ind - H.
  * admit.
  * *)

Import BigStep.
Definition eval_expr_simpl
    (e : Expression)
    (r : (ValueSequence + Exception))
    : Prop
    := 
    forall id1, exists id2,
        eval_expr [] [] "" id1 e [] id2 r [].


Import SubstSemantics.

Theorem value_to_value :
  forall v,
    eval_expr_simpl (give_names (˝v)) (give_result (inl [v])).
Proof.
  (* itr.
  smp.
  ind ~ ind_fs_val - v.
  * sbn. eei. cns.
  * sbn. eei. cns.
  * pse - no_pid. eei. con.
  * pse - no_reference: (give_names (˝ VVar x)).
    des - H as [H _].
    spe - H: x.
    con.
  * pse - no_reference: (give_names (˝ VFunId f)).
    des - H as [_ H].
    spe - H: f.
    con.
  * sbn *.
    rem - v1' v2' v1'' v2'' as H1 H2 H3 H4 / H1 H2 H3 H4:
          (give_vval 0 v1)
          (give_vval 0 v2)
          (give_val v1)
          (give_val v2).
    unfold eval_expr_simpl.
    itr.
    spe - IHv2: id1.
    des - IHv2 as [id2 IHv2].
    spe - IHv1: id2.
    des - IHv1 as [id3 IHv1].
    exi - id3.
    ens.
    exa - IHv2.
    exa - IHv1.
  * sbn *.
    admit.
  * admit.
  * admit. *)
Admitted.



(* Theorem if_valseq_than_value :
  forall Fs e vs,
      ⟨ Fs, e ⟩ -->* (RValSeq vs)
  ->  exists vs',
        ⟨ Fs, RValSeq vs' ⟩ -->* (RValSeq vs).
Proof.
  itr.
  ivc - H as [k [H1 H2]].
  ivs - H2.
  * exi - vs.
    open.
    step.
  * ivs - H.
    - exi - [v].
      open.
      exa - H0.
    -  *)

Theorem exi_nat_plus :
  forall n,
    exists n1 n2,
      n = n1 + n2.
Proof.
  ind - n.
  exi - 0 0.
  trv.
  des - IHn as [n1 [n2 IHn]].
  exi - (S n1) n2.
  rwr - Nat.add_succ_l.
  bwr - IHn.
Qed.

Theorem trans_middle :
  forall k Fs1 Fs3 e1 e3,
      ⟨ Fs1, e1 ⟩ -[k]-> ⟨ Fs3, e3 ⟩
  ->  exists k1 k2 Fs2 e2,
          ⟨ Fs1, e1 ⟩ -[k1]-> ⟨ Fs2, e2 ⟩
      /\  ⟨ Fs2, e2 ⟩ -[k2]-> ⟨ Fs3, e3 ⟩.
Proof.
  itr.
  induction H.
  * exi - 0 0 fs e.
    spl.
    cns.
    cns.
  * (* pse - exi_nat_plus: k.
    des - H1 as [k1 [k2 Heqk]].
    sbt. *)
    des - IHstep_rt as [k1 [k2 [Fs2 [e2 [Hstep1 Hstep2]]]]].
    exi - (S k1) k2 Fs2 e2.
    spl.
    2: asm.
    ens.
    exa - H.
    asm.
Qed.



Theorem split_econs_first :
  forall e1 e2 vs,
    ⟨ [], °(ECons e1 e2) ⟩ -->* (RValSeq vs)
  ->  exists v2,
      ⟨ [], RExp e2 ⟩ -->* (RValSeq [v2]).
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  pse - trans_middle:
        k ([] : FrameStack) ([] : FrameStack)
        (°(ECons e1 e2)) (RValSeq vs)
        Hstep.
  des - H as [k1 [k2 [Fs [e [Hstep1 Hstep2]]]]].
  ivs - Hstep1.
  * ivs - Hstep2.
    ivc - H.
    clr + H0.
    ivs - H0.
    ivs - H1.
    - ivs - H0.
      ivs - H6.
      ivs - H3.
    - ivs - H.
Admitted.
    



Lemma destruct_econs2 :
  forall e1 e2 r,
      ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r)
  ->  (exists v1 v2,
          r = inl [VCons v1 v2]
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inl [v1]))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q1 v2,
          r = inr q1
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inr q1))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q2,
          r = inr q2
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inr q2))).
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  eapply transitive_eval in Hstep.
  ivc - Hstep.
  des - r; ivc - H2.
  (* ivs - H.
  eapply transitive_eval_rev in H0.
  ivs - H0.
  ivs - H1.
  des - r as [vs | q]; smp *.
  * lft.
    ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
    2: {
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H. *)
Admitted.













Theorem eq_fsbs :
  forall e r,
      step_any [] (RExp e) (to_redex r)
  ->  eval_expr_simpl (give_names e) (give_result r).
Proof.
  ind ~ ind_fs_exp - e;
        itr - r HF.
  (* VNil*)
  (* 14:{
    app - destruct_value in HF.
    sbt.
    app - value_to_value.
  }
  3: {
    app - destruct_econs in HF.
  } *)
Admitted.






(*

Fixpoint no_reference_val
    (v : Val)
    : Prop
    :=
  match v with

  | VNil => True

  | VLit _ => True

  | VVar _ => False

  | VFunId _ => False

  | VPid _ => False

  | VCons v1 v2 => no_reference_val v1 /\ no_reference_val v2

  | VTuple vs =>
    fold_right
        (fun v acc =>
          no_reference_val v /\ acc)
        True
        vs

  | VMap vvs =>
    fold_right
        (fun '(vk, vv) acc =>
          no_reference_val vk /\ no_reference_val vv /\ acc)
        True
        vvs

  | VClos _ _ _ _ => True

  end.

Import BigStep.

Fixpoint no_reference_exp
    (e : Expression)
    : Prop
    :=
  match e with

  | ENil => True

  | ELit _ => True

  | EVar _ => False

  | EFunId _ => False

  | ECons e1 e2 => no_reference_exp e1 /\ no_reference_exp e2

  | ESeq e1 e2 => no_reference_exp e1 /\ no_reference_exp e2

  | ETuple es =>
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EValues es =>
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EPrimOp _ es =>
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EApp e es =>
    no_reference_exp e /\
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | ECall em ef es =>
    no_reference_exp em /\
    no_reference_exp ef /\
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EMap ees =>
    fold_right
        (fun '(ek, ev) acc =>
          no_reference_exp ek /\ no_reference_exp ev /\ acc)
        True
        ees

  | _ => True

  end.



Theorem eval_value_no_reference :
  forall v r,
      ⟨ [], ˝v ⟩ -->* r
  ->  no_reference_val v.
Proof.
  itr.
  ind ~ ind_fs_val - v; smp; trv.
  * admit.
  * ivc - H as [k [H1 H2]].
    ivc - H2.
    ivc - H1.
    ivc - H.
    ivc - H4.
    ivc - H3.
  * ivc - H as [k [H1 H2]].
    ivc - H2.
    ivc - H1.
    ivc - H.
    ivc - H4.
    ivc - H3.
  * 
  
    unfold is_result in H1.
    1: con.



Lemma any_cool_value :
  forall v,
      VALCLOSED v
  ->  ⟨ [], ˝v ⟩ -->* (RValSeq [v]).
Proof.
  itr.
  open.
  step.
Qed.

Lemma rt_cool_value :
  forall v,
      VALCLOSED v
  ->  ⟨ [], ˝v ⟩ -[ 1 ]-> ⟨ [], RValSeq [v] ⟩.
Proof.
  itr.
  step.
Qed.

Lemma one_cool_value :
  forall v,
      VALCLOSED v
  ->  ⟨ [], ˝v ⟩ --> ⟨ [], RValSeq [v] ⟩.
Proof.
  itr.
  step.
  asm.
Qed.

Lemma eq_cool_value :
  forall v r,
      step_any [] (˝v) (to_redex r)
  ->  (to_redex r) = RValSeq [v].
Proof.
  itr.
  ind ~ ind_fs_val - v.
  * des - H as [k [Hscope Hstep]].
    ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ass > (VALCLOSED VNil) as Hclosed; ato.
      pse - one_cool_value as Hcool_value: VNil Hclosed.
      (* pse - cool_value: VNil ([] : FrameStack) 1 Hclosed. *)
      pose proof step_determinism Hcool_value fs' e' H.
      des - H1.
      sbt.
      ivs - H0; ato.
      ivs - H1.
  * des - H as [k [Hscope Hstep]].
    ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ass > (VALCLOSED (VLit l)) as Hclosed; ato.
      pse - one_cool_value as Hcool_value: (VLit l) Hclosed.
      (* pse - cool_value: VNil ([] : FrameStack) 1 Hclosed. *)
      pose proof step_determinism Hcool_value fs' e' H.
      des - H1.
      sbt.
      ivs - H0; ato.
      ivs - H1.
  * des - H as [k [Hscope Hstep]].
    ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ass > (VALCLOSED (VPid p)) as Hclosed; ato.
      pse - one_cool_value as Hcool_value: (VPid p) Hclosed.
      (* pse - cool_value: VNil ([] : FrameStack) 1 Hclosed. *)
      pose proof step_determinism Hcool_value fs' e' H.
      des - H1.
      sbt.
      ivs - H0; ato.
      ivs - H1.
   *  des - H as [k [Hscope Hstep]].
      ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ivc - H.
      admit.
   * admit.
Admitted.




Theorem eq_fsbs :
  forall e r,
      step_any [] (RExp e) (to_redex r)
  ->  exists id,
        eval_expr [] [] "" 0 (give_names e) [] id (give_result r) [].
Proof.
  itr - e r HF.
  ind ~ ind_fs_exp - e.
  (* VNil*)
  14:{
    app - eq_cool_value in HF.
    des - r as [vs | q]; ivc - HF.
    sbn.
    exi - 0.
    cns.
  }
Admitted.
*)