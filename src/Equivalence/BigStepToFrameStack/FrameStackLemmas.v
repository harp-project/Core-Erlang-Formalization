From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.

Require Import stdpp.list.



  Theorem framestack_ident :
    forall ident el vl vl' r x eff Fs,
      create_result ident (vl ++ x :: vl') [] = Some (r , eff)
      -> list_biforall (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v]) el vl'
      -> exists k, ⟨ FParams ident vl el :: Fs, RValSeq [x] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    intros.
    generalize dependent r. generalize dependent vl'. revert vl. revert x.
    induction el; intros.
    {
      inv H0.
      exists 1. econstructor. econstructor. by symmetry.
      constructor.
    }
    {
      inv H0.
      destruct H3 as [khd [Hhd Dhd]].
      replace (vl ++ x :: hd' :: tl') with ((vl ++ [x]) ++ hd' :: tl') in H.
      2: {
        rewrite <- app_assoc.
        by rewrite <- app_cons_swap.
      }
      specialize (IHel _ _ _ H5 _ H). destruct IHel as [kIH DIH].
      eexists. econstructor. constructor.
      eapply transitive_eval.
      eapply frame_indep_core in Dhd. exact Dhd.
      simpl. exact DIH.
    }
  Qed.

  Theorem framestack_ident_rev :
    forall el ident vl e k r,
     ⟨ [FParams ident vl el], RExp e ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
     -> exists v vl' eff, 
          create_result ident (vl ++ v :: vl') [] = Some (RValSeq r, eff) /\ 
          list_biforall (λ (e0 : Exp) (v : Val), ⟨ [], RExp e0 ⟩ -->* RValSeq [v]) (e :: el) (v :: vl').
  Proof.
    induction el; intros.
    * Search step_rt.
      pose proof term_eval.
      pose proof terminates_in_k_eq_terminates_in_k_sem.
      unfold terminates_in_k_sem in H1.
      assert (is_result r).
      {
        constructor.
        admit. (*scope *)
      }
      pose proof conj H2 H.
      apply ex_intro with (x := RValSeq r) in H3.
      apply H1 in H3.
      apply H0 in H3. 2:
      {
        admit. (* scope *)
      }
      destruct H3 as [v [k0 [Hres [Hv Hk]]]].
      inv Hres.
      {
        pose proof transitive_eval_rev. (* H Hv *) (* inv H*)
        admit.
      }
      admit.
    * admit.
  Admitted.