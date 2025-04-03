From CoreErlang.Eqvivalence.FsBs Require Export F1GiveNames.
From CoreErlang.Eqvivalence Require Export B3Tactics.

Import SubstSemantics.










Section Determinism.



Theorem step_one_det :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃,
      ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₃, e₃ ⟩
  ->  Fs₂ = Fs₃ /\ e₂ = e₃.
Proof.
  itr.
  pose proof (step_determinism H) Fs₃ e₃ H0.
  des - H1.
  ato.
Qed.

Theorem step_one_det_implicit :
      forall {Fs₁ Fs₂ e₁ e₂},
        ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  forall {Fs₃ e₃},
        ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₃, e₃ ⟩
  ->  Fs₂ = Fs₃ /\ e₂ = e₃.
Proof.
  itr.
  pose proof (step_determinism H) Fs₃ e₃ H0.
  des - H1.
  ato.
Qed.



Theorem step_rt_det :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k,
      ⟨ Fs₁, e₁ ⟩ -[ k ]-> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[ k ]-> ⟨ Fs₃, e₃ ⟩
  ->  Fs₂ = Fs₃ /\ e₂ = e₃.
Proof.
  itr.
  pose proof (step_rt_determinism H) Fs₃ e₃ H0.
  des - H1.
  ato.
Qed.

Theorem step_rt_det_implicit :
      forall {Fs₁ Fs₂ e₁ e₂ k},
        ⟨ Fs₁, e₁ ⟩ -[ k ]-> ⟨ Fs₂, e₂ ⟩
  ->  forall {Fs₃ e₃},
        ⟨ Fs₁, e₁ ⟩ -[ k ]-> ⟨ Fs₃, e₃ ⟩
  ->  Fs₂ = Fs₃ /\ e₂ = e₃.
Proof.
  itr.
  pose proof (step_rt_determinism H) Fs₃ e₃ H0.
  des - H1.
  ato.
Qed.



End Determinism.















Section Steps.



Lemma step_any_to_rt :
  forall Fs e r,
      ⟨ Fs, e ⟩ -->* r
  ->  exists k,
        ⟨ Fs, e ⟩ -[ k ]-> ⟨ [], r ⟩.
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  eei.
  exa - Hstep.
Qed.



Lemma step_rt_to_any :
  forall Fs e r k,
      is_result r
  ->  ⟨ Fs, e ⟩ -[ k ]-> ⟨ [], r ⟩
  ->  ⟨ Fs, e ⟩ -->* r.
Proof.
  itr.
  open.
  step - H0.
Qed.



Lemma step_one_to_rt :
  forall Fs1 Fs2 e1 e2,
      ⟨ Fs1, e1 ⟩ --> ⟨ Fs2, e2 ⟩
  ->  ⟨ Fs1, e1 ⟩ -[ 1 ]-> ⟨ Fs2, e2 ⟩.
Proof.
  itr.
  ens.
  exa - H.
  step.
Qed.



Lemma step_rt_to_one :
  forall Fs1 Fs2 e1 e2,
      ⟨ Fs1, e1 ⟩ -[ 1 ]-> ⟨ Fs2, e2 ⟩
  ->  ⟨ Fs1, e1 ⟩ --> ⟨ Fs2, e2 ⟩.
Proof.
  itr.
  ivc - H.
  ivc - H4.
  asm.
Qed.



End Steps.















Section Transitive.



(* Theorem transitive_eval_notimplicit :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k₁₂ k₂₃,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H H0).
Qed. *)



Theorem step_one_add_before :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k,
      ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₂, e₂ ⟩ -[k]-> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[1 + k]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  app - step_one_to_rt in H.
  by pose proof (transitive_eval H H0).
Qed.

Theorem step_one_add_before_implicit :
      forall {Fs₁ Fs₂ e₁ e₂},
        ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  forall {Fs₃ e₃ k},
        ⟨ Fs₂, e₂ ⟩ -[k]-> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[1 + k]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  epp - step_one_add_before.
  exa - H.
  exa - H0.
Qed.



Theorem step_one_add_after :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k,
      ⟨ Fs₁, e₁ ⟩ -[k]-> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₂, e₂ ⟩ --> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k + 1]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  app - step_one_to_rt in H0.
  by pose proof (transitive_eval H H0).
Qed.

Theorem step_one_add_after_implicit :
      forall {Fs₁ Fs₂ e₁ e₂ k},
        ⟨ Fs₁, e₁ ⟩ -[k]->  ⟨ Fs₂, e₂ ⟩
  ->  forall {Fs₃ e₃},
        ⟨ Fs₂, e₂ ⟩ --> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k + 1]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  epp - step_one_add_after.
  exa - H.
  exa - H0.
Qed.






Theorem step_one_rem_before :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k,
      ⟨ Fs₁, e₁ ⟩ -[1 + k]-> ⟨ Fs₃, e₃⟩
  ->  ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₂, e₂ ⟩ -[k]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  ivc - H.
  pose proof (step_determinism H0) fs' e' H2.
  des - H.
  sbt.
  asm.
Restart.
  itr.
  app - step_one_to_rt in H0.
  epose proof transitive_eval_rev _ _ _ _ _ H0 _ _ _ H.
  asm.
Qed.

Theorem step_one_rem_before_implicit :
      forall {Fs₁ Fs₃ e₁ e₃ k},
        ⟨ Fs₁, e₁ ⟩ -[1 + k]-> ⟨ Fs₃, e₃⟩
  ->  forall {Fs₂ e₂},
        ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₂, e₂ ⟩ -[k]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  epp - step_one_rem_before.
  exa - H.
  exa - H0.
Qed.



Theorem step_one_rem_after :
  forall Fs₁ Fs₃ e₁ e₃ k,
        ⟨ Fs₁, e₁ ⟩ -[k + 1]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂,
        ⟨ Fs₁, e₁ ⟩ -[k]->  ⟨ Fs₂, e₂ ⟩.
Proof.
  itr.
  gen - Fs₁ Fs₃ e₁ e₃.
  ind - k as [| k IH];
        itr.
  * clr - H.
    exi - Fs₁ e₁.
    step.
  * ivc - H.
    spe - IH: e₃ e' Fs₃ fs' H4.
    des - IH as [Fs₂ [e₂ H]].
    exi - Fs₂ e₂.
    app - step_one_to_rt in H1.
    pose proof (transitive_eval H1 H).
    rwl - Nat.add_1_l.
    asm.
Qed.

Theorem step_one_rem_afterimplicit :
      forall {Fs₁ Fs₃ e₁ e₃ k},
        ⟨ Fs₁, e₁ ⟩ -[k + 1]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂,
        ⟨ Fs₁, e₁ ⟩ -[k]->  ⟨ Fs₂, e₂ ⟩.
Proof.
  itr.
  epp - step_one_rem_after.
  exa - H.
Qed.






Theorem step_one_break_before :
  forall Fs₁ Fs₃ e₁ e₃ k,
      ⟨ Fs₁, e₁ ⟩ -[1 + k]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂,
          ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
      /\  ⟨ Fs₂, e₂ ⟩ -[k]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  ivs - H.
  exi - fs' e'.
  spl; ato.
Qed.

Theorem step_one_break_before_implicit :
  forall {Fs₁ Fs₃ e₁ e₃ k},
      ⟨ Fs₁, e₁ ⟩ -[1 + k]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂,
          ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
      /\  ⟨ Fs₂, e₂ ⟩ -[k]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  epp - step_one_break_before.
  asm.
Qed.



Theorem step_one_break_after :
  forall Fs₁ Fs₃ e₁ e₃ k,
      ⟨ Fs₁, e₁ ⟩ -[k + 1]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂,
          ⟨ Fs₂, e₂ ⟩ --> ⟨ Fs₃, e₃ ⟩
      /\  ⟨ Fs₁, e₁ ⟩ -[k]->  ⟨ Fs₂, e₂ ⟩.
Proof.
  itr.
  epose proof step_one_rem_after _ _ _ _ _ H.
  des - H0 as [Fs₂ [e₂ H0]].
  exi - Fs₂ e₂.
  spl.
  2: asm.
  gen - Fs₁ Fs₃ e₁ e₃.
  ind - k as [| k IH];
        itr.
  * smp *.
    ivc - H0.
    app - step_rt_to_one in H.
    asm.
  * ivc - H0.
    ivc - H.
    pose proof (step_determinism H1) fs' e' H2.
    des - H.
    cwl - H H0 in *.
    spe - IH: e₃ e' Fs₃ fs' H6 H5.
    asm.
Qed.

Theorem step_one_break_after_implicit :
  forall {Fs₁ Fs₃ e₁ e₃ k},
      ⟨ Fs₁, e₁ ⟩ -[k + 1]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂,
          ⟨ Fs₂, e₂ ⟩ --> ⟨ Fs₃, e₃ ⟩
      /\  ⟨ Fs₁, e₁ ⟩ -[k]->  ⟨ Fs₂, e₂ ⟩.
Proof.
  itr.
  epp - step_one_break_after.
  asm.
Qed.









Theorem step_rt_trans :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k₁₂ k₂₃,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H H0).
Qed.

Theorem step_rt_trans_first :
  forall Fs₁ Fs₂ e₁ e₂ k₁₂,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  forall Fs₃ e₃ k₂₃,
          ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H H0).
Qed.

Theorem step_rt_trans_first_implicit :
      forall {Fs₁ Fs₂ e₁ e₂ k₁₂},
        ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  forall {Fs₃ e₃ k₂₃},
        ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->    ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H H0).
Qed.

Theorem step_rt_trans_second :
  forall Fs₂ Fs₃ e₂ e₃ k₂₃,
      ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  forall Fs₁ e₁ k₁₂,
          ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H0 H).
Qed.

Theorem step_rt_trans_second_implicit :
      forall {Fs₂ Fs₃ e₂ e₃ k₂₃},
        ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  forall {Fs₁ e₁ k₁₂},
        ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H0 H).
Qed.






Theorem step_rt_trans_rev_first :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k₁₂ k₂₃,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
  ->  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  by epose proof (transitive_eval_rev _ _ _ _ _ H) _ _ _ H0.
Qed.

Theorem step_rt_trans_rev_first_implicit :
      forall {Fs₁ Fs₂ e₁ e₂ k₁₂},
        ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  forall {Fs₃ e₃ k₂₃},
        ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
  ->    ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  by epose proof (transitive_eval_rev _ _ _ _ _ H) _ _ _ H0.
Qed.






Theorem step_rt_trans_rev_break :
  forall Fs₁ Fs₃ e₁ e₃ k,
      ⟨ Fs₁, e₁ ⟩ -[k]-> ⟨ Fs₃, e₃⟩
  ->  exists Fs₂ e₂ k₁₂ k₂₃,
          k = k₁₂ + k₂₃
      /\  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
      /\  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  intros Fs₁ Fs₃ e₁ e₃ k H.
  induction H.
  - (* Base case: k = 0 *)
    (* In this case, the multi-step relation is trivial, so we can choose Fs₂ = Fs₁, e₂ = e₁, k₁₂ = 0, and k₂₃ = 0. *)
    exists fs, e, 0, 0.
    split; [lia | split].
    + constructor. (* ⟨ Fs₁, e₁ ⟩ -[0]-> ⟨ Fs₁, e₁ ⟩ *)
    + constructor. (* ⟨ Fs₁, e₁ ⟩ -[0]-> ⟨ Fs₃, e₃ ⟩ *)
  - (* Inductive case: k > 0 *)
    (* In this case, the multi-step relation is split into a single step and a smaller multi-step relation. *)
    destruct IHstep_rt as [Fs₂ [e₂ [k₁₂ [k₂₃ [Hk [Hstep₁ Hstep₂]]]]]].
    sbt.
    exists Fs₂, e₂, (S k₁₂), k₂₃.
    split.
    + simpl. lia. (* k = S k₁₂ + k₂₃ *)
    + split.
      * econstructor; eauto. (* ⟨ Fs₁, e₁ ⟩ -[S k₁₂]-> ⟨ Fs₂, e₂ ⟩ *)
      * exact Hstep₂. (* ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩ *)
Qed.


Theorem step_rt_trans_rev_break_spec :
  forall Fs₁ Fs₃ e₁ e₃ k₁₃ k₁₂,
      ⟨ Fs₁, e₁ ⟩ -[k₁₃]-> ⟨ Fs₃, e₃⟩
  ->  k₁₂ <= k₁₃
  ->  exists Fs₂ e₂ k₂₃,
          k₁₃ = k₁₂ + k₂₃
      /\  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
      /\  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  intros Fs₁ Fs₃ e₁ e₃ k₁₃ k₁₂ H H0.
  gen - k₁₂.
  induction H; itr.
  - ivs - H0.
    exists fs, e, 0.
    split; [lia | split].
    + constructor.
    + constructor.
  - des - k₁₂ as [| k₁₂].
    * exists fs, e, (S k).
      split; [lia | split].
      + constructor.
      + ens.
        exa - H.
        exa - H0.
    * app - le_S_n in H1.
      spc - IHstep_rt: k₁₂ H1.
      des - IHstep_rt as [Fs₂ [e₂ [k₂₃ [Hk [H1 H2]]]]].
      exists Fs₂, e₂, k₂₃.
      split; [lia | split].
      2: exa - H2.
      ens.
      exa - H.
      exa - H1.
Qed.


(* Theorem step_rt_trans_rev_break_spec_core :
  forall Fs Fs₁ Fs₃ e₁ e₃ k₁₃ k₁₂,
      ⟨ Fs₁ ++ Fs, e₁ ⟩ -[k₁₃]-> ⟨ Fs₃ ++ Fs, e₃⟩
  ->  k₁₂ <= k₁₃
  ->  exists Fs₂ e₂ k₂₃,
          k₁₃ = k₁₂ + k₂₃
      /\  ⟨ Fs₁ ++ Fs, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂ ++ Fs, e₂ ⟩
      /\  ⟨ Fs₂ ++ Fs, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃ ++ Fs, e₃ ⟩.
Proof.
  itr.
  epp - step_rt_trans_rev_break_spec in H.
  2: exa - H0. *)


(* Theorem eval_transitive_second_to_first :
  forall Fs₂ Fs₃ e₂ e₃ k₂₃,
      ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  forall Fs₁ e₁ k₁₂,
          ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩.
Proof.
  itr - Fs₂ Fs₃ e₂ e₃ k₂₃ H.
  ind - H;
        itr.
        by rwr - Nat.add_0_r in H.
  by pose proof (transitive_eval_rev Fs₁ Fs₂ e₁ e₂ k₁₂ H) Fs₃ e₃ k₂₃ H0.
Qed. *)



(* Theorem step_rt_trans_rev_second :
  forall Fs₂ Fs₃ e₂ e₃ k₂₃,
      ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  exists Fs₁ e₁ k₁₂,
          ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩.
Proof.
  itr.
  gen - e₃ e₂ Fs₃ Fs₂.
  ind - k₂₃ as [| k₂₃ IH];
        itr.
  * ivc - H.
    itr.
    do 3 eei.
    rwr - Nat.add_0_r.
    itr.
    exa - H.
  * ivc - H.
    spe - IH: fs' Fs₃ e' e₃ H4.
    des - IH as [Fs₁ [e₁ [k₁₂ H]]].
    exi -
    des - IH as [Fs₂ [e₂ H]].
    exi - Fs₂ e₂.
    app - step_one_to_rt in H1.
    pose proof (transitive_eval H1 H).
    rwl - Nat.add_1_l.
    asm. *)



(* Theorem step_rt_trans_rev_second :
  forall Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k₁₂ k₂₃,
      ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
  ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩.
Proof.
  itr - Fs₁ Fs₂ Fs₃ e₁ e₂ e₃ k₁₂ k₂₃ H23 H13.
  gen - k₁₂ e₂ Fs₂.
  ind - k₂₃ as [| k₂₃ IH];
        itr.
  * ivc -  H23.
    by rwr - Nat.add_0_r in H13.
  * ivc - H23.
    rwl - Nat.add_succ_comm in H13.
    spe - IH: fs' e' H3 (S k₁₂) H13.
  
  ind - H23;
        itr.
        by rwr - Nat.add_0_r in H13.
  rwl - Nat.add_succ_comm in H13.
  spe - IHstep_rt: Fs₁ e₁ (S k₁₂) H13.
  rwl - Nat.add_1_l
        Nat.add_comm
        in IHstep_rt.
  epp - step_one_break_after in IHstep_rt.
  des - IHstep_rt as [Fs₂ [e₂ [H2 H12]]].
  
  
  
  
  
  
  rwr - Nat.add_comm in IHstep_rt.
  revert e₁.
  itr.
  gen - e₂ Fs₂.
  ind - k₁₂ as [| k₁₂ IH].
  * itr.
    gen - e₁ Fs₁.
    smp *.
  gen - k₁₂ e₁ Fs₁.
  ind - H;
        itr.
        by rwr - Nat.add_0_r in H0.
  pose proof (transitive_eval_rev Fs₁ Fs₂ e₁ e₂ k₁₂ H) Fs₃ e₃ k₂₃ H0.
Qed. *)






(* Theorem eval_transitive_one_before :
  forall Fs₁ Fs₂ e₁ e₂,
      ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
  ->  forall Fs₃ e₃  k₂₃,
          ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[1 + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  app - step_one_to_rt in H.
  by pose proof (transitive_eval H H0).
Qed.



Theorem eval_transitive_one_after :
  forall Fs₁ Fs₂ e₁ e₂ k₁₂,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  forall Fs₃ e₃,
          ⟨ Fs₂, e₂ ⟩ --> ⟨ Fs₃, e₃ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + 1]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  app - step_one_to_rt in H0.
  by pose proof (transitive_eval H H0).
Qed.



Theorem eval_transitive_one_before_reverse :
  forall Fs₁ Fs₃ e₁ e₃ k₂₃,
      ⟨ Fs₁, e₁ ⟩ -[1 + k₂₃]-> ⟨ Fs₃, e₃⟩
  ->  forall Fs₂ e₂,
          ⟨ Fs₁, e₁ ⟩ --> ⟨ Fs₂, e₂ ⟩
      ->  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  ivc - H.
  pose proof (step_determinism H0) fs' e' H2.
  des - H.
  sbt.
  asm.
Qed.



Theorem eval_transitive_one_after_reverse :
  forall Fs₁ Fs₂ e₁ e₂ k₁₂,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂ + 1]-> ⟨ Fs₂, e₂ ⟩
  ->  forall Fs₃ e₃,
          ⟨ Fs₂, e₂ ⟩ --> ⟨ Fs₃, e₃ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂⟩.
Proof.
  itr.
  app - step_one_to_rt in H0.
  by pose proof (transitive_eval H H0).
Qed. *)



(* TRANS STEPS

step1-2:  ⟨ Fs1, e1 ⟩ -[k12]-> ⟨ Fs2, e2 ⟩
step2-3:  ⟨ Fs2, e2 ⟩ -[k23]-> ⟨ Fs3, e3 ⟩
step1-3:  ⟨ Fs1, e1 ⟩ -[k13]-> ⟨ Fs3, e3 ⟩

k13 = k12 + k23
*)


(* transitive_eval:
  forall {n Fs Fs' e e'},
      ⟨ Fs, e ⟩ -[n]-> ⟨ Fs', e' ⟩
  ->  forall {n' Fs'' e''},
          ⟨ Fs', e' ⟩ -[n']-> ⟨ Fs'', e'' ⟩
      ->  ⟨ Fs, e ⟩ -[n + n']-> ⟨ Fs'', e''⟩.
*)

(*
  transitive_eval_rev:
  forall Fs Fs' e e' k1,
      ⟨ Fs, e ⟩ -[k1]-> ⟨ Fs', e' ⟩
  ->  forall Fs'' e'' k2,
          ⟨ Fs, e ⟩ -[k1 + k2]-> ⟨ Fs'', e'' ⟩
      ->  ⟨ Fs', e' ⟩ -[k2]-> ⟨ Fs'', e'' ⟩.
*)



(* Theorem eval_transitive_first_to_both :
  forall Fs₁ Fs₂ e₁ e₂ k₁₂,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  forall Fs₃ e₃ k₂₃,
          ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr.
  by pose proof (transitive_eval H H0).
Qed.



Theorem eval_transitive_first_to_second :
  forall Fs₁ Fs₂ e₁ e₂ k₁₂,
      ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
  ->  forall Fs₃ e₃ k₂₃,
          ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
      ->  ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩.
Proof.
  itr.
  by pose proof (transitive_eval_rev Fs₁ Fs₂ e₁ e₂ k₁₂ H) Fs₃ e₃ k₂₃ H0.
Qed.



Theorem eval_transitive_second_to_both :
  forall Fs₂ Fs₃ e₂ e₃ k₂₃,
      ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  forall Fs₁ e₁ k₁₂,
          ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩.
Proof.
  itr - Fs₂ Fs₃ e₂ e₃ k₂₃ H.
  ind - H;
        itr.
        bwr - Nat.add_0_r.
  rwl - Nat.add_succ_comm
        Nat.add_1_l.
  rewrite Nat.add_comm with (n := 1).
  pse - eval_transitive_one_after: Fs₁ fs e₁ e k₁₂ H1 fs' e' H.
  spe - IHstep_rt: Fs₁ e₁ (k₁₂ + 1) H2.
  asm.
Qed.



Theorem eval_transitive_second_to_first :
  forall Fs₂ Fs₃ e₂ e₃ k₂₃,
      ⟨ Fs₂, e₂ ⟩ -[k₂₃]-> ⟨ Fs₃, e₃ ⟩
  ->  forall Fs₁ e₁ k₁₂,
          ⟨ Fs₁, e₁ ⟩ -[k₁₂ + k₂₃]-> ⟨ Fs₃, e₃⟩
      ->  ⟨ Fs₁, e₁ ⟩ -[k₁₂]-> ⟨ Fs₂, e₂ ⟩.
Proof.
  itr - Fs₂ Fs₃ e₂ e₃ k₂₃ H.
  ind - H;
        itr.
        by rwr - Nat.add_0_r in H.
  by pose proof (transitive_eval_rev Fs₁ Fs₂ e₁ e₂ k₁₂ H) Fs₃ e₃ k₂₃ H0.
Qed. *)



End Transitive.















Section EvalTo.



Theorem eval_arith_notbox :
  forall s1 s2 vs r,
      eval_arith s1 s2 vs = r
  ->  r <> RBox.
Proof.
  itr.
  unfold eval_arith in H.
  des > (convert_string_to_code (s1, s2));
  des - vs;
  sbt;
  (try con);
  des - v;
  des - vs;
  sbt;
  (try con);
  try (des - vs);
  sbt;
  (try con);
  try (des - l);
  sbt;
  (try con);
  try (des - v);
  sbt;
  (try con);
  try (des - l);
  sbt;
  (try con);
  try (des - x0);
  sbt;
  (try con).
Qed.

Theorem eval_arith_notexp :
  forall s1 s2 vs r,
      eval_arith s1 s2 vs = r
  ->  forall e, r <> RExp e.
Proof.
  itr.
  unfold eval_arith in H.
  des > (convert_string_to_code (s1, s2));
  des - vs;
  sbt;
  (try con);
  des - v;
  des - vs;
  sbt;
  (try con);
  try (des - vs);
  sbt;
  (try con);
  try (des - l);
  sbt;
  (try con);
  try (des - v);
  sbt;
  (try con);
  try (des - l);
  sbt;
  (try con);
  try (des - x0);
  sbt;
  (try con).
Qed.

Theorem eval_arith_either :
  forall s1 s2 vs r,
      eval_arith s1 s2 vs = r
  ->  (exists vs, r = RValSeq vs)
  \/  (exists q, r = RExc q).
Proof.
  itr.
  des - r as [e | vs' | q |].
  * pse - eval_arith_notexp: s1 s2 vs (RExp e) H e.
    con.
  * lft.
    exi - vs'.
    rfl.
  * rgt.
    exi - q.
    rfl.
  * pse - eval_arith_notbox: s1 s2 vs (RBox) H.
    con.
Qed.



Theorem eval_logical_notbox :
  forall s1 s2 vs r,
      eval_logical s1 s2 vs = r
  ->  r <> RBox.
Proof.
  itr.
  unfold eval_logical in H.
  des > (convert_string_to_code (s1, s2));
  try (con);
  try (des - vs);
  try (des - v);
  smp - H;
  try (con);
  try (des - vs);
  try (des - v);
  smp - H;
  try (con);
  try (des - vs);
  try (des - v);
  smp - H;
  try (con);
  try (des - l);
  smp - H;
  try (con);
  try (des > (string_dec s "true"));
  try (des > (string_dec s "false"));
  smp - H;
  sbt;
  try (con);
  try (des > (Lit_beq l0 "true"));
  try (des > (Lit_beq l0 "false"));
  sbt;
  try (con).
Qed.



Theorem eval_logical_notexp :
  forall s1 s2 vs r,
      eval_logical s1 s2 vs = r
  ->  forall e, r <> RExp e.
Proof.
  itr.
  unfold eval_logical in H.
  des > (convert_string_to_code (s1, s2));
  try (con);
  try (des - vs);
  try (des - v);
  smp - H;
  try (con);
  try (des - vs);
  try (des - v);
  smp - H;
  try (con);
  try (des - vs);
  try (des - v);
  smp - H;
  try (con);
  try (des - l);
  smp - H;
  try (con);
  try (des > (string_dec s "true"));
  try (des > (string_dec s "false"));
  smp - H;
  sbt;
  try (con);
  try (des > (Lit_beq l0 "true"));
  try (des > (Lit_beq l0 "false"));
  sbt;
  try (con).
Qed.

Theorem eval_logical_either :
  forall s1 s2 vs r,
      eval_logical s1 s2 vs = r
  ->  (exists vs, r = RValSeq vs)
  \/  (exists q, r = RExc q).
Proof.
  itr.
  des - r as [e | vs' | q |].
  * pse - eval_logical_notexp: s1 s2 vs (RExp e) H e.
    con.
  * lft.
    exi - vs'.
    rfl.
  * rgt.
    exi - q.
    rfl.
  * pse - eval_logical_notbox: s1 s2 vs (RBox) H.
    con.
Qed.



(* There are no RBox and RExp in Auxiliaries *)



Theorem eval_primop_notbox:
  forall s1 vs eff eff' r,
      primop_eval s1 vs eff = Some (r, eff')
  ->  r <> RBox.
Proof.
Admitted.



Theorem eval_notbox:
  forall s1 s2 vs eff eff' r,
      eval s1 s2 vs eff = Some (r, eff')
  ->  r <> RBox.
Proof.
Admitted.



Theorem eval_primop_notexp:
  forall s1 vs eff eff' r,
      primop_eval s1 vs eff = Some (r, eff')
  ->  forall e, r <> RExp e.
Proof.
Admitted.



Theorem eval_notexp:
  forall s1 s2 vs eff eff' r,
      eval s1 s2 vs eff = Some (r, eff')
  ->  forall e, r <> RExp e.
Proof.
Admitted.



Theorem eval_either:
  forall s1 s2 vs eff eff' r,
      eval s1 s2 vs eff = Some (r, eff')
  ->  (exists vs, r = RValSeq vs)
  \/  (exists q, r = RExc q).
Proof.
Admitted.



End EvalTo.















Section StepSpecial.



Theorem step_one_framestack_to_empty :
  forall Fs e₁ e₂,
      ⟨ Fs, e₁ ⟩ --> ⟨ [], e₂ ⟩
  ->  (exists F, Fs = [F])
  \/  Fs = [].
Proof.
  itr.
  ivc - H; ato; lft; eei; ato.
Qed.



Theorem step_one_frame_nil_notbox :
  forall e₁ e₂,
      ⟨ [], e₁ ⟩ --> ⟨ [], e₂ ⟩
  ->  e₂ <> RBox.
Proof.
  itr.
  des - e₂ as [ e | vs | q |].
  * con.
  * con.
  * con.
  * ivc - H.
Qed.

Theorem step_one_frame_nil_notexc :
  forall e₁ e₂,
      ⟨ [], e₁ ⟩ --> ⟨ [], e₂ ⟩
  ->  forall q, e₂ <> RExc q.
Proof.
  itr.
  des - e₂ as [ e | vs | q0 |].
  * con.
  * con.
  * ivc - H.
  * con.
Qed.

Theorem step_one_frame_nil_either :
  forall e₁ e₂,
      ⟨ [], e₁ ⟩ --> ⟨ [], e₂ ⟩
  ->  (exists vs, e₂ = RValSeq vs)
  \/  (exists e, e₂ = RExp e).
Proof.
  itr.
  des - e₂ as [ e | vs | q |].
  * rgt.
    exi - e.
    rfl.
  * lft.
    exi - vs.
    rfl.
  * pse - step_one_frame_nil_notexc: e₁ (RExc q) H q.
    con.
  * pse - step_one_frame_nil_notbox: e₁ (RBox) H.
    con.
Qed.



Theorem step_one_frame_one_notbox :
  forall F e₁ e₂,
      ⟨ [F], e₁ ⟩ --> ⟨ [], e₂ ⟩
  ->  e₂ <> RBox.
Proof.
  itr.
  des - e₂ as [ e | vs | q |].
  * con.
  * con.
  * con.
  * ivc - H.
    - des - ident;
      ivc - H4;
      (try des - m);
      (try des - f);
      (try des - l);
      (try des - l0);
      ivc - H0.
      + sym - H1.
        pose proof eval_notbox s s0 vl [] eff' RBox H1.
        con.
      + sym - H1.
        pose proof eval_primop_notbox (String a f) vl [] eff' RBox H1.
        con.
      + des - v; ivs - H1.
        des > (params =? base.length vl); ivs - H1.
    - des - ident;
      ivc - H3;
      (try des - m);
      (try des - f);
      (try des - l);
      (try des - l0);
      ivc - H0.
      + sym - H1.
        pose proof eval_notbox s s0 (vl ++ [v]) [] eff' RBox H1.
        con.
      + sym - H1.
        pose proof eval_primop_notbox (String a f) (vl ++ [v]) [] eff' RBox H1.
        con.
      + des - v0; ivs - H1.
        des > (params =? base.length (vl ++ [v])); ivs - H1.
Qed.

(* Theorem step_one_frame_one_notexp :
  forall F e₁ e₂,
      ⟨ [F], e₁ ⟩ --> ⟨ [], e₂ ⟩
  ->  forall e, e₂ <> RExp e.
Proof.
  itr.
  des - e₂ as [ e0 | vs | q |].
  * ivc - H.
    - des - ident;
      ivc - H4;
      (try des - m);
      (try des - f);
      (try des - l);
      (try des - l0);
      ivc - H0.
      + sym - H1.
        pose proof eval_notexp s s0 vl [] eff' e0 H1.
        con.
      + sym - H1.
        pose proof eval_primop_notexp (String a f) vl [] eff' e0 H1.
        con.
      + des - v; ivs - H1.
        des > (params =? base.length vl); ivs - H1.
        admit.
Admitted. *)



(* Theorem step_rt_without_frame :
  forall F e₁ e₂ k,
      ⟨ [F], e₁ ⟩ -[k]-> ⟨ [], e₂ ⟩
  ->  exists e₃ k',
      ⟨ [], e₁ ⟩ -[k']-> ⟨ [], e₃ ⟩.
Proof.
  itr.
  ivc - H.
  pose proof step_one_add_before_implicit H0 H1.
  rwr - Nat.add_comm in H.
  pose proof (step_one_break_after_implicit H).
  des - H2 as [Fs0 [e0 [H2 H3]]].
  pse - step_one_framestack_to_empty: Fs0 e0 e₂ H2.
  des - H4.
  * des - H4 as [F0 H4].
    sbt.
Admitted. *)

(*
H : ⟨ [FCons1 e1], e2 ⟩ -[ S k ]-> ⟨ [], q2 ⟩
______________________________________(1/1)
⟨ [], e2 ⟩ -[ k ]-> ⟨ [], q2 ⟩
*)


Theorem pop_exc :
  forall F q k,
      (forall vl1 e2 vl2 e3, F <> FTry vl1 e2 vl2 e3)
  ->  ⟨ [F], RExc q ⟩ -[ S k ]-> ⟨ [], q ⟩
  ->  ⟨ [], RExc q ⟩ -[ k ]-> ⟨ [], q ⟩.
Proof.
  itr.
  ivc - H0.
  ivc - H2.
  * spe - H: vl1 e2 3 e3.
    con.
  * asm.
Qed.



End StepSpecial.















Section StepValue.



Theorem step_rt_eq_cool_value :
  forall v r k,
  ⟨ [], ˝v ⟩ -[ S k ]-> ⟨ [], r⟩
  ->  r = RValSeq [v].
Proof. (*EQ1*)
  itr.
  des - r as [e | vs | q |]; smp *.
  * ivc - H.
    ivc - H1.
    ivc - H4.
    ivc - H.
  * ivc - H.
    ivc - H4.
    ivc - H1.
    trv.
    ivc - H1.
    ivc - H.
  * ivc - H.
    ivc - H4.
    ivc - H1.
    trv.
    ivc - H1.
    ivc - H.
  * ivc - H.
    ivc - H4.
    ivc - H1.
    trv.
    ivc - H1.
    ivc - H.
Qed.



End StepValue.















Section StepCons.



Theorem step_rt_cons_stack_head :
  forall e1 e2 r,
      ⟨ [FCons1 e1], e2 ⟩ --> ⟨ [], r ⟩
  ->  exists q, r = RExc q.
Proof.
  itr.
  ivc - H.
  exi - exc.
  rfl.
Qed.



(* Theorem step_rt_cons_stack_head :
  forall e1 e2 r,
      ⟨ [FCons1 e1], e2 ⟩ --> ⟨ [], r ⟩
  ->  (exists vs, r = RValSeq vs)
  \/  (exists q, r = RExc q).
Proof.
  itr.
  ivc - H. *)



Theorem step_rt_cons_put_tail :
  forall e1 e2 r k,
      ⟨ [], °(ECons e1 e2) ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  ⟨ [FCons1 e1], RExp e2 ⟩ -[ k ]-> ⟨ [], r ⟩.
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1.
  asm.
Qed.



(* Theorem step_rt_cons_stack_head :
  forall e1 e2 q2 k,
      ⟨ [FCons1 e1], RExp e2 ⟩ -[ S k ]-> ⟨ [], RExc q2 ⟩
  ->  ⟨ [], RExp e2 ⟩ -[ k ]-> ⟨ [], RExc q2 ⟩.
Proof. (*TO1*)
  itr.
  ass > (⟨ [FCons1 e1], q2 ⟩ --> ⟨ [], q2 ⟩).
  step.
  
  intros e1 e2 q2 k H.
  remember (S k) as sk eqn:Heq.
  generalize dependent k.
  induction H; intros k' Heq.
  - (* Base case: k = 0 *)
    simpl in Heq. discriminate.
  - (* Inductive case: k > 0 *)
    destruct k'.
    + (* Case: k' = 0 *)
      simpl in Heq. inversion Heq; subst.
      inversion H0; subst.
      
      step.
      (* The frame `FCons1 e1` is popped, so the remaining evaluation is on `RExp e2`. *)
      assumption.
    + (* Case: k' > 0 *)
      simpl in Heq. inversion Heq; subst.
      inversion H; subst.
      (* Apply the inductive hypothesis to the remaining multi-step evaluation. *)
      apply IHstep_rt; reflexivity.
  ass >
    ((∀ (vl1 : nat) (e2 : Exp) (vl2 : nat) (e3 : Exp),
    FCons1 e1 ≠ FTry vl1 e2 vl2 e3)):
    con.
  pse - pop_exc: (FCons1 e1) q2 k H0. H.
  eapply frame_indep_nil in H.
  ivc - H.
  ivc - H1; clr - H6.
  ivc - H4; trv.
  ivc - H.
Qed. *)



Theorem step_rt_cons_pop_exc_tail :
  forall e1 q2 r k,
      ⟨ [FCons1 e1], RExc q2 ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  r = RExc q2.
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1; clr - H6.
  ivc - H4; trv.
  ivc - H.
Qed.



Theorem step_rt_cons_swap_valseq :
  forall e1 vs r k,
      ⟨ [FCons1 e1], RValSeq vs ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  exists v2,
          vs = [v2].
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1.
  exi - tl.
  rfl.
Qed.



Theorem step_rt_cons_swap :
  forall e1 v2 r k,
      ⟨ [FCons1 e1], RValSeq [v2] ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  ⟨ [FCons2 v2], RExp e1 ⟩ -[ k ]-> ⟨ [], r ⟩.
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1.
  asm.
Qed.



Theorem step_rt_cons_pop_exc_head :
  forall q1 v2 r k,
      ⟨ [FCons2 v2], RExc q1 ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  r = RExc q1.
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1; clr - H6.
  ivc - H4; trv.
  ivc - H.
Qed.



Theorem step_rt_cons_pop_valseq :
  forall vs v2 r k,
      ⟨ [FCons2 v2], RValSeq vs ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  exists v1,
          vs = [v1].
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1.
  exi - hd.
  rfl.
Qed.



Theorem step_rt_cons_pop :
  forall v1 v2 r k,
      ⟨ [FCons2 v2], RValSeq [v1] ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  r = RValSeq [VCons v1 v2].
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1.
  ivc - H4; trv.
  ivc - H.
Qed.




(**)
Theorem step_rt_cons0_v1 :
  forall v1 v2 r,
      ⟨ [FCons2 v2], RValSeq [v1] ⟩ -[ 1 ]-> ⟨ [], r ⟩
  ->  r = RValSeq [VCons v1 v2].
Proof.
  itr.
  ivc - H.
  ivc - H1.
  ivc - H4.
  rfl.
  (* no more step *)
  (* ivc - H0.
  ivc - H. *)
Qed.


Theorem step_rt_cons0_vs1_0 :
  forall vs v2 r,
      ⟨ [FCons2 v2], RValSeq vs ⟩ -[ 1 ]-> ⟨ [], r ⟩
  ->  exists v1,
          vs = [v1].
Proof.
  itr.
  ivc - H.
  ivc - H1.
  ivc - H4.
  exi - hd.
  rfl.
  (* no more step *)
  (* ivc - H0.
  ivc - H. *)
Qed.


Theorem step_rt_cons0_vs1_1 :
  forall vs v2 r,
      ⟨ [FCons2 v2], RValSeq vs ⟩ -[ 1 ]-> ⟨ [], r ⟩
  ->  exists v1,
          r = RValSeq [VCons v1 v2].
Proof.
  itr.
  pose proof step_rt_cons0_vs1_0 _ _ _ H.
  des - H0 as [v1 Heq]; sbt.
  exi - v1.
  bpp - step_rt_cons0_v1 in H.
Qed.

Theorem step_rt_cons0_q1 :
  forall q1 v2 r,
      ⟨ [FCons2 v2], RExc q1 ⟩ -[ 1 ]-> ⟨ [], r ⟩
  ->  r = RExc q1.
Proof.
  itr.
  ivc - H.
  ivc - H1.
  ivc - H4.
  rfl.
  (* no more step *)
  (* ivc - H0.
  ivc - H. *)
Qed.

Theorem step_rt_cons0_r1 :
  forall r1 v2 r,
      ⟨ [FCons2 v2], (to_redex r1) ⟩ -[ 1 ]-> ⟨ [], r ⟩
  ->  (exists v1, r = RValSeq [VCons v1 v2])
  \/  (exists q1, r = RExc q1).
Proof.
  itr.
  des - r1.
  * lft.
    app - step_rt_cons0_vs1_1 in H.
    asm.
  * rgt.
    app - step_rt_cons0_q1 in H.
    exi - e.
    asm.
Qed.



Theorem step_rt_cons1_r1_0 :
  forall e1 r1 v2 k r,
      ⟨ [], RExp e1 ⟩ -[ k ]-> ⟨ [], (to_redex r1) ⟩
  ->  ⟨ [FCons2 v2], RExp e1 ⟩ -[ k + 1 ]-> ⟨ [], r ⟩
  ->  (exists v1, r = RValSeq [VCons v1 v2])
  \/  (exists q1, r = RExc q1).
Proof.
  itr.
  epp - frame_indep_core in H.
  epose proof (step_rt_trans_rev_first_implicit H H0).
  smp - H1.
  epp - step_rt_cons0_r1.
  exa - H1.
Qed.



Theorem step_rt_cons1_r1_1 :
  forall v2 e1 r k,
      ⟨ [FCons2 v2], RExp e1 ⟩ -[ k ]-> ⟨ [], (to_redex r) ⟩
  ->  exists r1 k',
      ⟨ [], RExp e1 ⟩ -[ k' ]-> ⟨ [], (to_redex r1) ⟩.
Proof.
  itr.
  ren - e: e1.
  ind ~ ind_fs_exp - e.
  14: { (*VNIL*)
    exists (inl [VNil]), 1.
    smp.
    step.
  }
  14: { (*VLit*)
    exists (inl [VLit l]), 1.
    smp.
    step.
  }
  14: { (*VPid*)
    exists (inl [VPid p]), 1.
    smp.
    step.
  }
  14: { (*VVar x*)
    exists (inl [VVar x]), 1.
    smp.
    step.
    (*Scope*)
    admit.
  }
  14: { (*VFunId f*)
    exists (inl [VFunId f]), 1.
    smp.
    step.
    (*Scope*)
    admit.
  }
  14: { (*VCons*)
    exists (inl [VCons v₁ v₂]), 1.
    smp.
    step.
    (*Scope*)
    all: admit.
  }
  14: { (*VClos*)
    exists (inl [VClos os id n e]), 1.
    smp.
    step.
    (*Scope*)
    all: admit.
  }
  14: { (*VTuple*)
    exists (inl [VTuple vs]), 1.
    smp.
    step.
    (*Scope*)
    admit.
  }
  14: { (*VMap*)
    exists (inl [VMap vvs]), 1.
    smp.
    step.
    (*Scope*)
    all: admit.
  }
  2: { (*EFun*)
    exists (inl [VClos [] 0 n e]), 1.
    smp.
    step.
  }
  (* 2: { (*ECons*)
    exists (inl [VClos [] 0 n e]), 1.
    smp.
    step.
  }
  ivc - H. 
  gen - r e1 v2.
  ind - k as [| k IH];
        itr.
  * smp *.
    ivc - H.
  * ivc - H. 
  epp - frame_indep_core in H.
  epose proof (step_rt_trans_rev_first_implicit H H0).
  smp - H1.
  epp - step_rt_cons0_r1.
  exa - H1. *)
Admitted.


Theorem step_any_with_less_frames :
  forall F e r,
      ⟨ [F], RExp e ⟩ -->* r
  ->  exists r',
      ⟨ [], RExp e ⟩ -->* r'.
Proof.
  itr.
  gen - r F.
  ind ~ ind_fs_exp - e;
        itr.
  14: { (*VNil*)
    exi - (RValSeq [VNil]).
    open.
    step.
  }
  14: { (*VLit*)
    exi - (RValSeq [VLit l]).
    open.
    step.
  }
  14: { (*VPid p*)
    exi - (RValSeq [VPid p]).
    open.
    step.
  }
  14: { (*VVar x*)
    exi - (RValSeq [VVar x]).
    open.
    adm.
    step.
    adm.
    (*scope*)
  }
  14: { (*VFunId f*)
    exi - (RValSeq [VFunId f]).
    open.
    adm.
    step.
    adm.
    (*scope*)
  }
  14: { (*VCons v₁ v₂*)
    clr - IHe IHe0.
    des - H as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VCons v₁ v₂]).
    open.
    step.
  }
  14: { (*VVClos os id n e*)
    clr - H IHe.
    des - H0 as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VClos os id n e]).
    open.
    step.
  }
  14: { (*VTuple vs*)
    clr - H.
    des - H0 as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VTuple vs]).
    open.
    step.
  }
  14: { (*VMap vvs*)
    clr - H.
    des - H0 as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VMap vvs]).
    open.
    step.
  }
  2: { (*EFun n e*)
    clr - IHe.
    des - H as [k [_ H]].
    ivc - H.
    ivc - H0.
    exi - (RValSeq [VClos [] 0 n e]).
    open.
    adm.
    step.
    (*scope*)
  }
  2: { (*ECons e1 e2*)
    des - H as [k [Hscope H]].
    ivc - H.
    ivc - H0.
    spe - IHe2: F.
    admit.
  }
Admitted.


Theorem step_any_with_less_frames2 :
  forall F e,
      (exists r,
        ⟨ [F], RExp e ⟩ -->* r)
  ->  (exists r,
        ⟨ [], RExp e ⟩ -->* r).
Proof.
  itr.
  gen - F.
  ind ~ ind_fs_exp - e;
        itr.
  14: { (*VNil*)
    exi - (RValSeq [VNil]).
    open.
    step.
  }
  14: { (*VLit*)
    exi - (RValSeq [VLit l]).
    open.
    step.
  }
  14: { (*VPid p*)
    exi - (RValSeq [VPid p]).
    open.
    step.
  }
  14: { (*VVar x*)
    exi - (RValSeq [VVar x]).
    open.
    adm.
    step.
    adm.
    (*scope*)
  }
  14: { (*VFunId f*)
    exi - (RValSeq [VFunId f]).
    open.
    adm.
    step.
    adm.
    (*scope*)
  }
  14: { (*VCons v₁ v₂*)
    clr - IHe IHe0.
    des - H as [r H].
    des - H as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VCons v₁ v₂]).
    open.
    step.
  }
  14: { (*VVClos os id n e*)
    clr - H IHe.
    des - H0 as [r H0].
    des - H0 as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VClos os id n e]).
    open.
    step.
  }
  14: { (*VTuple vs*)
    clr - H.
    des - H0 as [r H0].
    des - H0 as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VTuple vs]).
    open.
    step.
  }
  14: { (*VMap vvs*)
    clr - H.
    des - H0 as [r H0].
    des - H0 as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VMap vvs]).
    open.
    step.
  }
  2: { (*EFun n e*)
    clr - IHe.
    des - H as [r H].
    des - H as [k [_ H]].
    ivc - H.
    ivc - H0.
    exi - (RValSeq [VClos [] 0 n e]).
    open.
    adm.
    step.
    (*scope*)
  }
  2: { (*ECons e1 e2*)
    des - H as [r H].
    des - H as [k [Hscope H]].
    ivc - H.
    ivc - H0.
    spe - IHe2: F.
    admit.
  }
Admitted.


Theorem step_any_with_less_frames3 :
  forall e1 Fs e,
      (exists r,
        ⟨ FCons1 e1 :: Fs, RExp e ⟩ -->* r)
  ->  (exists r,
        ⟨ [], RExp e ⟩ -->* r).
Proof.
  itr.
  gen - Fs.
  ind ~ ind_fs_exp - e;
        itr.
  14: { (*VNil*)
    exi - (RValSeq [VNil]).
    open.
    step.
  }
  14: { (*VLit*)
    exi - (RValSeq [VLit l]).
    open.
    step.
  }
  14: { (*VPid p*)
    exi - (RValSeq [VPid p]).
    open.
    step.
  }
  14: { (*VVar x*)
    exi - (RValSeq [VVar x]).
    open.
    adm.
    step.
    adm.
    (*scope*)
  }
  14: { (*VFunId f*)
    exi - (RValSeq [VFunId f]).
    open.
    adm.
    step.
    adm.
    (*scope*)
  }
  14: { (*VCons v₁ v₂*)
    clr - IHe IHe0.
    des - H as [r H].
    des - H as [k [_ H]].
    ivc - H.
    ivc - H0.
    clr - H1.
    ivc - H3.
    exi - (RValSeq [VCons v₁ v₂]).
    open.
    step.
  }
  2: { (*EFun n e*)
    clr - IHe.
    des - H as [r H].
    des - H as [k [_ H]].
    ivc - H.
    ivc - H0.
    exi - (RValSeq [VClos [] 0 n e]).
    open.
    adm.
    step.
    (*scope*)
  }
  2: { (*ECons e1 e2*)
    des - H as [r H].
    des - H as [k [Hscope H]].
    ivc - H.
    ivc - H0.
    (* spe - IHe2: .
    admit. *)
    admit.
  }
Admitted.


Theorem step_any_with_less_frames4 :
  forall F e r k,
      ⟨ [F], RExp e ⟩ -[ k ]-> ⟨ [], r ⟩
  ->  exists r1 r2 k1 k2,
      k = k1 + 1 + k2
  /\  ⟨ [F], RExp e ⟩ -[ k1 ]-> ⟨ [F], r1 ⟩
  /\  ⟨ [F], r1 ⟩ --> ⟨ [], r2 ⟩
  /\  ⟨ [], r2 ⟩ -[ k2 ]->  ⟨ [], r ⟩.
Proof.
  itr.
  ind ~ ind_fs_exp - e;
        itr.
  14: {
    ivc - H.
    ivc - H1.
    * exi - (RExp (˝ VNil)) r 0 0.
      smp.
      spl; ato.
      spl; ato.
      step.
      spl; ato.
      step.
    * admit.
  }
Admitted.
  
  (* epose proof step_rt_trans_rev_break [F] [] (RExp e) r k H. *)



End StepCons.















(* Section StepAnyRules.







Lemma step_any_eq_cool_value :
  forall v r,
  ⟨ [], ˝v ⟩ -->* (to_redex r)
  ->  r = inl [v].
Proof. (*EQ1*)
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma step_rt_eq_cool_value0 :
  forall v r k,
  ⟨ [], ˝v ⟩ -[ k ]-> ⟨ [], to_redex r⟩
  ->  r = inl [v].
Proof. (*EQ1*)
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H.
    ivc - H1.
    ivc - H0.
    trv.
    ivc - H0.
    ivc - H.
  * ivc - H.
    ivc - H1.
    ivc - H0.
    trv.
    ivc - H0.
    ivc - H.
Qed.



Lemma step_rt_eq_cool_value :
  forall v r k,
  ⟨ [], ˝v ⟩ -[ S k ]-> ⟨ [], r⟩
  ->  r = RValSeq [v].
Proof. (*EQ1*)
  itr.
  des - r as [e | vs | q |]; smp *.
  * ivc - H.
    ivc - H1.
    ivc - H4.
    ivc - H.
  * ivc - H.
    ivc - H4.
    ivc - H1.
    trv.
    ivc - H1.
    ivc - H.
  * ivc - H.
    ivc - H4.
    ivc - H1.
    trv.
    ivc - H1.
    ivc - H.
  * ivc - H.
    ivc - H4.
    ivc - H1.
    trv.
    ivc - H1.
    ivc - H.
Qed.


(* Lemma tmpp :
  ⟨ [], RExp (°(ECons (°EValues []) (°EValues []))) ⟩ -->* RValSeq [].
Proof.
  open.
  do_step.
  do_step.
  do_step.
  -
Admitted. *)


Theorem is_result_with_frame_than_without :
  forall F Fs e r k,
      ⟨ F :: Fs, RExp e ⟩ -[ k ]-> ⟨ [], r ⟩
  ->  exists r' k',
        ⟨ Fs, RExp e ⟩ -[ k' ]-> ⟨ [], r' ⟩.
Proof.
  ind ~ ind_fs_exp - e;
        itr.
  * admit.
  * ivc - H.
    ivc - H0.
  * 
Admitted.


Theorem is_result_with_frame_than_without :
  forall Fs e r k,
      ⟨ Fs, RExp e ⟩ -[ k ]-> ⟨ [], r ⟩
  ->  exists r' k',
        ⟨ [], RExp e ⟩ -[ k' ]-> ⟨ [], r' ⟩.
Proof.
  ind - Fs as [| F Fs IH].
  * itr.
    exi - r k.
    asm.
  * ind ~ ind_fs_exp - e;
          itr.
    - admit.
    - admit.
    - 
Admitted.
  


Theorem step_rt_result :
  forall e,
    exists k r,
      ⟨ [], RExp e ⟩ -[ k ]-> ⟨ [], r ⟩.
Proof.
  ind ~ ind_fs_exp - e;
        itr.
  * admit.
  * do 2 eei; step.
  * des - IHe1 as [k1 [r1 H1]].
    des - IHe2 as [k2 [r2 H2]].
    do 2 eei; step.
    step - H2.
   (*  
    - exi - (RExp (° EFun n e)).
      step.
    - exi - (RValSeq [VClos [] 0 n e]).
      step.
      
    step.
  ind - k.
  * exi - e.
    step.
  * des - IHk as [r IHk].*)
Admitted.
  






















(* CONS *)


Lemma step_rt_to_eval_heat_cons :
  forall e1 e2 r k,
      ⟨ [], °(ECons e1 e2) ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  ⟨ [FCons1 e1], RExp e2 ⟩ -[ k ]-> ⟨ [], r ⟩.
Proof. (*TO1*)
  itr.
  ivc - H.
  ivc - H1.
  asm.
Qed.








Lemma step_rt_either :
  forall e r k,
      ⟨ [], RExp e ⟩ -[ S k ]-> ⟨ [], r ⟩
  ->  (exists vs,  r = RValSeq vs)
  \/  (exists q,   r = RExc q).
Proof.
  ind ~ ind_fs_exp - e;
        itr.
  * adm.
  * adm.
  * app - step_rt_to_eval_heat_cons in H.
    
  ivc - H.
    ivc - H4.
    adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * (*VNil*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VNil].
    trv.
  * (*VLit*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VLit l].
    trv.
  * (*VPid*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VPid p].
    trv.
  * (*VVar*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VVar x].
    trv.
  * (*VFunId*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VFunId f].
    trv.
  * (*VCons*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VCons v₁ v₂].
    trv.
  * (*VClos*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VClos os id n e].
    trv.
  * (*VTuple*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VTuple vs].
    trv.
  * (*VMap*)
    app - step_rt_eq_cool_value in H.
    lft.
    exi - [VMap vvs].
    trv.
Admitted.



Lemma step_any_either :
  forall Fs e r,
      ⟨ Fs, RExp e ⟩ -->* (to_redex r)
  ->  (exists vs,  r = inl vs)
  \/  (exists q,   r = inr q).
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  ind ~ ind_fs_exp - e.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * (*VNil*)
    app - step_rt_eq_cool_value in Hstep.
    ivc - Hstep.
    - exi -  
    adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
  * adm.
Admitted.







Lemma step_any_eq_cool_value :
  forall v r,
  ⟨ [], ˝v ⟩ -->* (to_redex r)
  ->  r = inl [v].
Proof. (*EQ1*)
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.






(* CONS *)


Lemma step_any_to_eval_heat_cons :
  forall e1 e2 r,
      ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r)
  ->  ⟨ [FCons1 e1], RExp e2 ⟩ -->* (to_redex r).
Proof. (*TO1*)
  itr.
  ivc - H as [k [Hscope Hstep]].
  des - r as [vs | q]; smp *.
  * ivs - Hstep.
    ivs - H.
    open.
    step - H0.
  * ivs - Hstep.
    ivs - H.
    open.
    step - H0.
Qed.



Lemma step_any_from_eval_heat_cons :
  forall e1 e2 r,
      ⟨ [FCons1 e1], RExp e2 ⟩ -->* (to_redex r)
  ->  ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r).
Proof. (*FROM1*)
  itr.
  ivc - H as [k [Hscope Hstep]].
  open.
  step - Hstep.
Qed.






Lemma step_any_eq_cons_tail :
  forall e1 e2 r r',
      ⟨ [FCons1 e1], RExp e2 ⟩ -->* (to_redex r)
  ->  ⟨ [], RExp e2 ⟩ -->* (to_redex r').
Proof. (*FROM1*)
  itr.
  ivc - H as [k [Hscope Hstep]].
  open.
  step - Hstep.
Qed.



Lemma step_any_eq_eval_cool_cons_2 :
  forall v1 v2 r,
  ⟨ [FCons2 v2], RValSeq [v1] ⟩ -->* (to_redex r)
  ->  r = inl [VCons v1 v2].
Proof. (*EQ1*)
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma step_any_eq2_eval_cool_cons_2 :
  forall v1 v2 vs,
  ⟨ [FCons2 v2], RValSeq vs ⟩ -->* (RValSeq [VCons v1 v2])
  ->  vs = [v1].
Proof. (*EQ2*)
  itr.
  ivc - H as [k [Hscope Hstep]].
  ivc - Hstep.
  ivc - H.
  ivc - H0.
  trv.
  ivs - H.
Qed.






Lemma step_any_eval_heat_cons_rev :
  forall e1 e2 r,
      ⟨ [FCons1 e1], RExp e2 ⟩ -->* (to_redex r)
  ->  ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r).
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  open.
  step - Hstep.
Qed.



End StepAnyRules.





Lemma destruct_vnil :
  forall r,
      ⟨ [], ˝VNil ⟩ -->* (to_redex r)
  ->  r = inl [VNil].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vlit :
  forall l r,
      ⟨ [], ˝(VLit l) ⟩ -->* (to_redex r)
  ->  r = inl [VLit l].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vvar :
  forall x r,
      ⟨ [], ˝(VVar x) ⟩ -->* (to_redex r)
  ->  False.
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H3.
    ivc - H1.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vfunid :
  forall f r,
      ⟨ [], ˝(VFunId f) ⟩ -->* (to_redex r)
  ->  False.
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H3.
    ivc - H1.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vcons :
  forall v1 v2 r,
      ⟨ [], ˝(VCons v1 v2) ⟩ -->* (to_redex r)
  ->  r = inl [VCons v1 v2].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vtuple :
  forall vl r,
      ⟨ [], ˝(VTuple vl) ⟩ -->* (to_redex r)
  ->  r = inl [VTuple vl].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vmap :
  forall vvl r,
      ⟨ [], ˝(VMap vvl) ⟩ -->* (to_redex r)
  ->  r = inl [VMap vvl].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vclos :
  forall os id xs e r,
      ⟨ [], ˝(VClos os id xs e) ⟩ -->* (to_redex r)
  ->  r = inl [VClos os id xs e].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.


Axiom no_pid :
  forall v,
    v <> VPid.

Axiom no_reference :
  forall e,
  (forall x, e <> give_names (˝VVar x))
  /\
  (forall f, e <> give_names (˝VFunId f)).



Theorem destruct_value :
  forall v r,
      ⟨ [], ˝v ⟩ -->* (to_redex r)
  ->  r = inl [v].
Proof.
  itr.
  des - v.
  bpp - destruct_vnil.
  bpp - destruct_vlit.
  pse - no_pid. con.
  bpp - destruct_vcons.
  bpp - destruct_vtuple.
  bpp - destruct_vmap.
  app - destruct_vvar in H. ivs - H.
  app - destruct_vfunid in H. ivs - H.
  bpp - destruct_vclos.
Qed. *)