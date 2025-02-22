From CoreErlang.Eqvivalence.BsFs Require Export BX4Helpers.

Import BigStep.










  Ltac spl_ato := repeat (try split; auto).




Section EraserSubstRemove_EraserLemmas.



  Lemma eraser_max :
    forall k ks,
      apply_eraser ks k <= length ks.
  Proof.
    itr.
    ind - ks as [| k₁ ks IH]:
          sli.
    smp.
    des > (k =ᵏ k₁);
          sli.
  Qed.



  Lemma eraser_destruct :
    forall k ks,
        apply_eraser ks k < length ks
    \/  apply_eraser ks k = length ks.
  Proof.
    itr.
    pse - eraser_max: k ks.
    lia.
  Qed.









  Lemma eraser_split :
    forall k ks,
        apply_eraser ks k < length ks
    ->  exists ks₁ ks₂,
            ks = ks₁ ++ [k] ++ ks₂
        /\  apply_eraser ks k = length ks₁.
  Proof.
    itr - k ks Hlt.
    ind - ks as [| k₁ ks IH]:
          smp *;
          lia.
    smp - Hlt.
    des > (k =ᵏ k₁) as Hkey.
    * clr - IH Hlt.
      exi - ([] : list Key) ks.
      smp.
      rwr - Hkey.
      rwr - var_funid_eqb_eq in Hkey.
      cwl - Hkey / k₁.
      ato.
    * app - PeanoNat.lt_S_n in Hlt.
      spc - IH: Hlt.
      des - IH as [ks₁ [ks₂ [Hks Heq]]].
      exi - (k₁ :: ks₁) ks₂.
      smp.
      cwr - Hkey Heq Hks / ks.
      ato.
  Qed.



  Lemma eraser_cut :
    forall k ks1 ks2,
        apply_eraser (ks1 ++ ks2) k = length ks1
    ->  apply_eraser ks1 k = length ks1.
  Proof.
    itr.
    smp *.
    ind - ks1 as [| k1 ks1 IHks1]
          :> smp *.
    des > (k =ᵏ k1) as Hkey:
          con.
    app - Nat.succ_inj in H.
    spc - IHks1: H.
    bwr - IHks1.
  Qed.



  Lemma eraser_add :
    forall k ks1 ks2,
        apply_eraser ks1 k = base.length ks1
    ->  apply_eraser (ks1 ++ [k] ++ ks2) k = base.length ks1.
  Proof.
    itr.
    smp *.
    ind - ks1 as [| k1 ks1 IHks1];
          smp *.
          1: bwr - var_funid_eqb_refl.
    des > (k =ᵏ k1) as Hkey:
          con.
    app - Nat.succ_inj in H.
    spc - IHks1: H.
    bwr - IHks1.
  Qed.



  Lemma eraser_exact :
    forall k ks,
        apply_eraser (k :: ks) k = 0.
  Proof.
    itr.
    smp.
    bwr - var_funid_eqb_refl.
  Qed.









  Lemma eraser_skip_notin_all :
    forall k ks,
        apply_eraser ks k = length ks
    ->  ¬ In k ks.
  Proof.
    itr.
    ind - ks as [| k1 ks IHks]:
          smp *; lia.
    smp - H.
    des > (k =ᵏ k1) as Hkey:
          con.
    app - Nat.succ_inj in H.
    spc - IHks: H.
    rwr - var_funid_eqb_neq in Hkey.
    ufl - not.
    itr.
    rwr - cons_app in H.
    app - in_app_or in H.
    des - H;
          ato.
    smp - H.
    des - H;
          ato.
  Qed.



  Lemma eraser_skip_notin_app :
    forall k ks1 ks2 n,
        apply_eraser (ks1 ++ ks2) k = length ks1 + n
    ->  ¬ In k ks1.
  Proof.
    itr.
    ind - ks1 as [| k1 ks1 IH]:
          smp *; lia.
    smp - H.
    des > (k =ᵏ k1) as Hkey:
          con.
    app - Nat.succ_inj in H.
    spc - IH: H.
    rwr - var_funid_eqb_neq in Hkey.
    ufl - not.
    itr.
    rwr - cons_app in H.
    app - in_app_or in H.
    des - H;
          ato.
    smp - H.
    des - H;
          ato.
  Qed.



  Lemma eraser_notin_skip_app :
    forall k ks1 ks2,
        ¬ In k ks1
    ->  apply_eraser (ks1 ++ ks2) k = length ks1 + apply_eraser ks2 k.
  Proof.
    itr.
    ind - ks1 as [| k1 ks1 IHks1]
          :> smp.
    rwr - cons_app in H.
    apply not_in_app in H.
    des - H.
    spc - IHks1: H0.
    smp - H.
    ufl - not in H.
    des > (k =ᵏ k1) as Hkey.
    2: bwr - IHks1.
    rwr - var_funid_eqb_eq in Hkey.
    des - H;
          ato.
  Qed.



  Lemma eraser_notin_skip_all :
    forall k ks,
        ¬ In k ks
    ->  apply_eraser ks k = length ks.
  Proof.
    itr.
    psc - eraser_notin_skip_app:
          k ks ([] : list Key) H.
    smp - H0.
    rwr - app_nil_r
          Nat.add_0_r
          in H0;
          trv.
  Qed.






  Lemma eraser_notin_skip_all_eq :
    forall k ks,
        apply_eraser ks k = length ks
    <-> ¬ In k ks.
  Proof.
    itr.
    spl.
    app - eraser_skip_notin_all.
    app - eraser_notin_skip_all.
  Qed.



  Lemma eraser_notin_skip_app_eq :
    forall k ks1 ks2,
        apply_eraser (ks1 ++ ks2) k = length ks1 + apply_eraser ks2 k
    <-> ¬ In k ks1.
  Proof.
    itr.
    spl.
    app - eraser_skip_notin_app.
    app - eraser_notin_skip_app.
  Qed.












  Theorem eraser_either :
    forall k ks,
         (exists ks1 ks2,
            ks = ks1 ++ [k] ++ ks2
        /\  apply_eraser ks k = length ks1
        /\  apply_eraser ks k < length ks
        /\  ¬ In k ks1)
    \/     (apply_eraser ks k = length ks
        /\  ¬ In k ks).
  Proof.
    itr.
    pse - eraser_destruct: k ks.
    des - H.
    * lft.
      pse - eraser_split: k ks H.
      des - H0 as [ks1 [ks2 [Hks Hlen]]].
      exi - ks1 ks2.
      spl_ato.
      sbt.
      clr - H.
      rwl - (eraser_notin_skip_app_eq k ks1 ([k] ++ ks2))
            cons_app
            in *.
      bwr - eraser_exact
            Nat.add_0_r.
   * rgt.
     spl_ato.
     bwl - eraser_notin_skip_all_eq.
  Qed.






  Theorem eraser_app_either :
    forall k ks1 ks2,
         (exists ks11 ks12,
            ks1 = ks11 ++ [k] ++ ks12
        /\  apply_eraser (ks1 ++ ks2) k = length ks11
        /\  apply_eraser (ks1 ++ ks2) k < length ks1
        /\  In k ks1
        /\  ¬ In k ks11)
    \/   (exists ks21 ks22,
            ks2 = ks21 ++ [k] ++ ks22
        /\  apply_eraser (ks1 ++ ks2) k = length (ks1 ++ ks21)
        /\  apply_eraser (ks1 ++ ks2) k < length (ks1 ++ ks2)
        /\  In k ks2
        /\  ¬ In k (ks1 ++ ks21))
    \/     (apply_eraser (ks1 ++ ks2) k = length (ks1 ++ ks2)
        /\  ¬ In k (ks1 ++ ks2)).
  Proof.
    itr.
    pse - eraser_either: k (ks1 ++ ks2).
    des - H as [H | H].
    * des - H as [ks1' [ks2' [Hks [Heq [Hlt Hnotin]]]]].
      psc - length_lt_split_middle_app: Key ks1 ks2 ks1' ks2' k Hks.
      des - H as [H | H].
      - lft.
        ren - ks11 ks12:
              ks1' ks2'.
        des - H as [ks [Hks1 _]].
        exi - ks11 ks.
        spl_ato;
              clr + Heq Hks1.
        + cwr - Heq
                Hks1.
          do 2 rwr - length_app.
          sli.
        + cwr - Hks1.
          do 2 rwr - in_app_iff.
          rgt; lft.
          amp.
      - rgt; lft.
        ren - ks21 ks22:
              ks1' ks2'.
        des - H as [ks [Hks1 Hks2]].
        exi - ks ks22.
        sbt.
        spl_ato.
        do 2 rwr - in_app_iff.
        rgt; lft.
        amp.
    * rgt; rgt.
      des - H as [Heq Hnotin].
      ato.
  Qed.



End EraserSubstRemove_EraserLemmas.















Section EraserSubstRemove_EnvironmentLemmas.



  Lemma length_env_keys_eq_vals :
    forall Γ,
      length Γ.keys = length Γ.vals.
  Proof.
    itr.
    ufl - get_keys
          get_vals.
    bwl - length_map_fst
          length_map_snd.
  Qed.



  Lemma env_get_keys_app_split_middle :
    forall Γ ks1 k ks2,
        Γ.keys = ks1 ++ [k] ++ ks2
    ->  exists Γ1 Γ2 v,
            Γ = Γ1 ++ [(k, v)] ++ Γ2
        /\  Γ1.keys = ks1
        /\  Γ2.keys = ks2.
   Proof.
    itr.
    ufl - get_keys
          get_vals.
    pse - list_app_fst_split_middle_both: Key Value Γ ks1 ks2 k H.
    des - H0 as [Γ1 [Γ2 [v [HΓ [Hvs [Hks1 [Hks2 [Hlen1 Hlen2]]]]]]]].
    exi - Γ1 Γ2 v.
    ato.
  Qed.






  Lemma env_rem_keys_comm :
    forall Γ ks1 ks2,
      Γ //ᵏ ks1 //ᵏ ks2
    = Γ //ᵏ ks2 //ᵏ ks1.
  Proof.
    itr.
    ind - Γ as [| [k v] Γ IHΓ]:
          do 3 rwr - env_rem_keys_nil_l.
    rwr - cons_app.
    do 4 rwr - env_rem_keys_app_l.
    cwr - IHΓ.
    feq.
    pse - env_rem_keys_single as Hsingle1: k v ks1.
    pse - env_rem_keys_single as Hsingle2: k v ks2.
    des - Hsingle1 as [Hsingle1 | Hempty1];
    des - Hsingle2 as [Hsingle2 | Hempty2].
    * bwr - Hsingle1
            Hsingle2
            Hsingle1.
    * bwr - Hsingle1
            Hempty2
            env_rem_keys_nil_l.
    * bwr - Hsingle2
            Hempty1
            env_rem_keys_nil_l.
    * bwr - Hempty1
            Hempty2
            env_rem_keys_nil_l
            env_rem_keys_nil_l.
  Qed.



  Lemma env_rem_keys_double :
    forall Γ ks,
      Γ //ᵏ ks //ᵏ ks
    = Γ //ᵏ ks.
  Proof.
    itr.
    ind - Γ as [| [k v] Γ IH]:
          do 2 rwr - env_rem_keys_nil_l;
          ato.
    rwr - cons_app.
    do 2 rwr - env_rem_keys_app_l.
    cwr - IH.
    feq.
    ind - ks as [| k1 ks IH]:
          do 2 rwr - env_rem_keys_nil_r;
          ato.
    rwr - cons_app.
    do 2 rwr - env_rem_keys_app_r.
    rwr - env_rem_keys_comm.
    rewrite env_rem_keys_comm with (Γ := [(k, v)]).
    rewrite env_rem_keys_comm with (Γ := [(k, v)] //ᵏ [k1]).
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k1 =ᵏ k) as Hkey.
    * smp.
      do 2 rwr - env_rem_keys_nil_l.
      ato.
    * smp.
      rwr - app_nil_r.
      ufl - env_rem_key_one.
      smp.
      cwr - Hkey.
      ato.
  Qed.






  Lemma notin_env_implies_notin_env_rem_keys :
    forall Γ k ks,
        ¬ In k Γ.keys
    ->  ¬ In k (Γ //ᵏ ks).keys.
  Proof.
    itr.
    ind - Γ as [| [k1 v1] Γ IH]:
          bwr - env_rem_keys_nil_l.
    ufl - get_keys in *.
    rwr - cons_app in *.
    rwr - env_rem_keys_app_l.
    rwr - map_app in *.
    apply not_in_app in H.
    des - H as [Hhead Htail].
    spc - IH: Htail.
    pse - env_rem_keys_single: k1 v1 ks.
    des - H as [Hsingle | Hempty].
    * epose proof app_not_in
          k (map fst [(k1, v1)]) (map fst Γ //ᵏ ks)
          Hhead IH
          as Hgoal;
          clr - Hhead IH. 
      by cwr - Hsingle in *.
    * by cwr - Hempty in *.
  Qed.



  Lemma env_rem_keys_sinle_notin_eq :
    forall k v ks,
        ¬ In k ks
    ->  [(k, v)] //ᵏ ks 
      = [(k, v)].
  Proof.
    itr.
    ind - ks as [| k1 ks IH]; ato.
    rwr + cons_app in H.
    rwr - env_rem_keys_app_r.
    apply not_in_app in H.
    des - H as [Hhead Htail].
    spc - IH: Htail.
    cwr - IH.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k1 =ᵏ k) as Hkey; ato.
    rwr - var_funid_eqb_eq in Hkey.
    smp - Hhead.
    des - Hhead.
    ato.
  Qed.









  Theorem eraser_env_def_and_rem_either :
    forall k ks Γ,
           (apply_eraser (ks ++ Γ.keys) k
            = apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
        /\  apply_eraser (ks ++ Γ.keys) k
            < length ks
        /\  apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
            < length ks)
    \/   (exists Γ1 Γ2 v,
            Γ = Γ1 ++ [(k, v)] ++ Γ2
        /\  apply_eraser (ks ++ Γ.keys) k
            = length (ks ++ Γ1.keys)
        /\  apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
            = length (ks ++ (Γ1 //ᵏ ks).keys)
        /\  ¬ In k ks)
    \/     (apply_eraser (ks ++ Γ.keys) k
            = length (ks ++ Γ.keys)
        /\    apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
            = length (ks ++ (Γ //ᵏ ks).keys)).
  Proof.
    itr.
    pse - eraser_app_either: k ks Γ.keys.
    des - H as [H | [H | H]].
    * lft.
      des - H as [ks1 [ks2 [Hks [Heq [Hlt [_ Hnotin]]]]]].
      spl_ato;
            clr - Hlt.
      - cwr - Heq.
        rem - ks3 as Hks3 / Hks3 Γ:
              (Γ //ᵏ ks).keys.
        cwr - Hks / ks.
        repeat rwl - app_assoc.
        rwr - eraser_notin_skip_app; ato.
        rwl - cons_app.
        bwr - eraser_exact.
      - clr - Heq.
        rem - ks3 as Hks3 / Hks3 Γ:
              (Γ //ᵏ ks).keys.
        cwr - Hks / ks.
        repeat rwl - app_assoc.
        rwr - eraser_notin_skip_app; ato.
        do 2 rwl - cons_app.
        rwr - eraser_exact
              Nat.add_0_r
              length_app.
        sli.
    * rgt; lft.
      des - H as [ks1 [ks2 [Hks [Heq [Hlt [Hisin Hnotin]]]]]].
      pse - env_get_keys_app_split_middle: Γ ks1 k ks2 Hks.
      des - H as [Γ1 [Γ2 [v [HΓ [Hks1 _]]]]].
      exi - Γ1 Γ2 v.
      spl_ato.
      - clr + Hks1 Heq.
        bwr - Hks1.
      - clr + Hks1 HΓ Hnotin.
        cwl - Hks1 / ks1.
        apply not_in_app in Hnotin.
        des - Hnotin as [Hnotin_ks Hnotin_Γ].
        app - (notin_env_implies_notin_env_rem_keys Γ1 k ks) in Hnotin_Γ.
        epose proof app_not_in
            k ks (Γ1 //ᵏ ks).keys
            Hnotin_ks Hnotin_Γ
            as Hnotin;
            clr - Hnotin_Γ.
        cwr - HΓ.
        ufl - get_keys in *.
        repeat rwr -
              env_rem_keys_app_l
              map_app.
        rwr - app_assoc.
        rwr - eraser_notin_skip_app;
              ato;
              clr - Hnotin.
        rwr - env_rem_keys_sinle_notin_eq;
              ato;
              clr - Hnotin_ks.
        rwr - map_single.
        rwl - cons_app.
        simpl fst.
        bwr - eraser_exact
              Nat.add_0_r
              length_app
              length_app.
      - clr + Hnotin.
        apply not_in_app in Hnotin.
        des - Hnotin as [Hnotin _].
        exa - Hnotin.
    * rgt; rgt.
      des - H as [Heq Hnotin].
      spl_ato.
      clr - Heq.
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin_ks Hnotin_Γ].
      app - (notin_env_implies_notin_env_rem_keys Γ k ks) in Hnotin_Γ.
      Search In not app.
      epose proof app_not_in
            k ks (Γ //ᵏ ks).keys
            Hnotin_ks Hnotin_Γ
            as Hnotin;
            clr - Hnotin_ks Hnotin_Γ.
      bwr - eraser_notin_skip_all.
  Qed.



End EraserSubstRemove_EnvironmentLemmas.















Section EraserSubstRemove_SubstLemmas.

  Import SubstSemanticsLemmas.



  (* NOT USING *)
  Lemma upn_app :
    forall m1 m2 x ξ,
      upn m1 (upn m2 ξ) x
    = upn (m1 + m2) ξ x.
  Proof.
    itr.
    gen - x.
    ind - m1 as [| m1 IH]:
          itr;
          smp.
    itr.
    smp.
    des - x:
          smp.
    smp.
    spe - IH: x.
    ufl - Manipulation.shift.
    bwr - IH.
  Qed.



  Lemma upn_from_inr_subst:
    forall m x ξ n,
        ξ x = inr n
    ->  upn m ξ (x + m) = inr (n + m).
  Proof.
    itr.
    itr.
    rwr - Nat.add_comm.
    rewrite Nat.add_comm with (n := n).
    ind - m as [| m IH]:
          smp.
    smp.
    ufl - Manipulation.shift.
    bwr - IH.
  Qed.



  (* NOT USING *)
  Lemma upn_subst_skip_all :
    forall m x,
      m = x
  ->  upn m idsubst x = inr m.
  Proof.
    itr.
    ivc - H.
    ass > (idsubst 0 = inr 0): ato.
    psc - upn_from_inr_subst: x 0 idsubst 0 H.
    smp - H0.
    trv.
  Qed.









  Lemma list_subst_skip_all :
    forall vs x,
      length vs = x
  ->  list_subst vs idsubst x = inr 0.
  Proof.
    itr.
    ufl - idsubst.
    ivc - H.
    ind - vs as [| v vs IH]; trv.
  Qed.



  Lemma list_subst_skip_app :
    forall vs1 v vs2 x,
      length vs1 = x
  ->  list_subst (vs1 ++ [v] ++ vs2) idsubst x = inl v.
  Proof.
    itr.
    ufl - idsubst.
    ivc - H.
    ind - vs1 as [| v1 vs1 IH]; trv.
  Qed.






  Lemma upn_list_subst_skip_all :
    forall m vs x,
      m + length vs = x
  ->  upn m (list_subst vs idsubst) x = inr m.
  Proof.
    itr.
    ass > (length vs = x - m): lia.
    app - list_subst_skip_all in H0.
    pse - upn_from_inr_subst: m (x - m) (list_subst vs idsubst) 0 H0.
    smp - H1.
    erewrite Nat.sub_add in H1.
          2: lia.
    exa - H1.
  Qed.



  Lemma upn_list_subst_skip_app :
    forall m vs1 v vs2 x,
      m + length vs1 = x
  ->  upn m (list_subst (vs1 ++ [v] ++ vs2) idsubst) x
    = inl (renameVal (fun n => n + m) v).
  Proof.
    itr.
    ass > (length vs1 = x - m): lia.
    pse - list_subst_skip_app: vs1 v vs2 (x - m) H0.
    pse - upn_inl_eq_2: m (x - m) v
          (list_subst (vs1 ++ [v] ++ vs2) idsubst)
          H1.
    erewrite Nat.sub_add in H2.
          2: lia.
    exa - H2.
  Qed.



End EraserSubstRemove_SubstLemmas.















Section EraserSubstRemove_EraserSubstLemmas.



  Theorem eraser_subst_env_rem_keys_eq :
    forall ks Γ k,
        upn (length ks)
            (list_subst (map erase_val
              (Γ //ᵏ ks).vals)
              idsubst)
            (apply_eraser
              (ks ++ (Γ //ᵏ ks).keys)
              k)
      = upn (length ks)
            (list_subst
              (map erase_val
                Γ.vals)
                idsubst)
            (apply_eraser
              (ks ++ Γ.keys)
              k).
  Proof.
    itr.
    pse - eraser_env_def_and_rem_either: k ks Γ.
    des - H as [H | [H | H]].
    * des - H as [Heq [Hle1 Hle2]].
      eapply upn_Var in Hle1.
      eapply upn_Var in Hle2.
      cwr - Hle1 Hle2.
      bwr - Heq.
    * des - H as [Γ1 [Γ2 [v [HΓ [Heq1 [Heq2 HnotIn]]]]]].
      cwr - HΓ in *.
      rwr - length_app
            length_env_keys_eq_vals
            in Heq1 Heq2.
      rwl - length_map_erase_val
            in Heq1 Heq2.
      sym - Heq1 Heq2.
      ufl - get_keys
            get_vals
            in *.
      repeat rwr - env_rem_keys_app_l in *.
      repeat rwr - map_app in *.
      erewrite env_rem_keys_sinle_notin_eq in *; ato.
      clr - HnotIn.
      repeat rwr - map_single in *.
      simpl fst in *.
      simpl snd in *.
      psc - upn_list_subst_skip_app as Hskip1:
            (base.length ks)
            (map erase_val (map snd Γ1))
            (erase_val v)
            (map erase_val (map snd Γ2))
            (apply_eraser (ks ++ map fst Γ1 ++ [k] ++ map fst Γ2) k)
            Heq1.
      psc - upn_list_subst_skip_app as Hskip2:
            (base.length ks)
            (map erase_val (map snd Γ1 //ᵏ ks))
            (erase_val v)
            (map erase_val (map snd Γ2 //ᵏ ks))
            (apply_eraser (ks ++ map fst Γ1 //ᵏ ks ++ [k] ++ map fst Γ2 //ᵏ ks)
              k)
            Heq2.
      setoid_rewrite Hskip1.
      setoid_rewrite Hskip2.
      rfl.
    * des - H as [Heq1 Heq2].
      rwr - length_app
            length_env_keys_eq_vals
            in Heq1 Heq2.
      rwl - length_map_erase_val
            in Heq1 Heq2.
      sym - Heq1 Heq2.
      psc - upn_list_subst_skip_all as Hskip1:
            (base.length ks) (map erase_val Γ.vals)
            (apply_eraser (ks ++ Γ.keys) k)
            Heq1.
      psc - upn_list_subst_skip_all as Hskip2:
            (base.length ks) (map erase_val (Γ //ᵏ ks).vals)
            (apply_eraser (ks ++ (Γ //ᵏ ks).keys) k)
            Heq2.
      bwr - Hskip1 Hskip2.
   Qed.






  Theorem eraser_subst_env_rem_keys_app_eq1 :
    forall ks1 ks2 Γ k,
        upn (length ks1)
       (upn (length ks2)
            (list_subst (map erase_val
              (Γ //ᵏ ks2).vals)
              idsubst))
            (apply_eraser
              (ks1 ++ ks2 ++ (Γ //ᵏ ks2).keys)
              k)
      = upn (length ks1)
       (upn (length ks2)
            (list_subst
              (map erase_val
                Γ.vals)
                idsubst))
            (apply_eraser
              (ks1 ++ ks2 ++ Γ.keys)
              k).
  Proof.
    itr.
    do 2 rwr - upn_app.
    rwl - length_app.
    do 2 rwr - app_assoc.
    rwl - (eraser_subst_env_rem_keys_eq (ks1 ++ ks2) (Γ //ᵏ ks2) k).
    rwl - (eraser_subst_env_rem_keys_eq (ks1 ++ ks2) Γ k).
    do 2 rwr - env_rem_keys_app_r.
    bwr - env_rem_keys_double.
  Qed.






  Theorem eraser_subst_env_rem_keys_app_eq :
    forall ks1 ks2 Γ k,
        upn (length (ks1 ++ ks2))
            (list_subst (map erase_val
              (Γ //ᵏ ks2).vals)
              idsubst)
            (apply_eraser
              (ks1 ++ ks2 ++ (Γ //ᵏ ks2).keys)
              k)
      = upn (length (ks1 ++ ks2))
            (list_subst
              (map erase_val
                Γ.vals)
                idsubst)
            (apply_eraser
              (ks1 ++ ks2 ++ Γ.keys)
              k).
  Proof.
    itr.
    do 2 rwr - app_assoc.
    rwl - (eraser_subst_env_rem_keys_eq (ks1 ++ ks2) (Γ //ᵏ ks2) k).
    rwl - (eraser_subst_env_rem_keys_eq (ks1 ++ ks2) Γ k).
    do 2 rwr - env_rem_keys_app_r.
    bwr - env_rem_keys_double.
  Qed.


(*

(erase_exp ((map inl xs ++ ks) ++ (Γ //ᵏ ks).keys) e).[upn 
                                                       (base.length xs)
                                                       (upn 
                                                       (base.length ks)
                                                       (list_subst
                                                       (map erase_val
                                                       (Γ //ᵏ ks).vals) idsubst))] =
(erase_exp ((map inl xs ++ ks) ++ Γ.keys) e).[upn (base.length xs)
                                                (upn (base.length ks)
                                                   (list_subst
                                                      (map erase_val Γ.vals) idsubst))]
*)
  (* Theorem eraser_subst_skip_app :
    forall k ks1 ks2 ξ,
      upn
        (length (ks1 ++ ks2))
        ξ
        (apply_eraser (ks1 ++ ks2) k)
    = upn
        (length ks2)
        ξ
        (apply_eraser ks2 k).
  Proof.
    itr.
    pse - eraser_app_either: k ks1 ks2.
    des - H as [H | [H | H]].
    * des - H as [ks11 [ks12 [Hks1 [Heq [Hlt [Hisin Hnotin]]]]]].
      sbt.
      do 2 rwl - app_assoc in *.
      cwr - Heq.
      erewrite upn_Var.
            2: do 2 rwr - length_app; sli.
      
      
      
    pse - eraser_destruct: k (ks1 ++ ks2).
    des - H.
    * pse - upn_Var.
      erewrite upn_Var;
            ato.
      
            
             (apply_eraser (ks1 ++ ks2) k).
    ass > ((apply_eraser (ks1 ++ ks2) k < length ks1 \/ length ks1 <= (apply_eraser (ks1 ++ ks2) k): lia.
    ass >
      (apply_eraser (ks1 ++ ks2) k < length ks1
      \/ length ks1 <= apply_eraser (ks1 ++ ks2) k):
      lia.
      
      eraser_exp (ks1 + ks2) e.[upn (length (ks1 ++ ks2))] *)
  
  (* Theorem eraser_subst_add :
    forall k ks1 ks2 ξ,
      upn
        (length (ks1 ++ ks2))
        ξ
        (apply_eraser (ks1 ++ ks2) k)
    = upn
        (length ks2)
        ξ
        (apply_eraser ks2 k). *)

  Lemma upn_add1 :
    forall m ξ1 ξ2 x1 x2,
        upn m ξ1 x1
      = upn m ξ2 x2
    ->  upn (1 + m) ξ1 (1 + x1)
      = upn (1 + m) ξ2 (1 + x2).
  Proof.
    itr.
    smp.
    ufl - Manipulation.shift.
    bwr - H.
  Qed.

  Lemma upn_add :
    forall n m ξ1 ξ2 x1 x2,
        upn m ξ1 x1
      = upn m ξ2 x2
    ->  upn (n + m) ξ1 (n + x1)
      = upn (n + m) ξ2 (n + x2).
  Proof.
    itr.
    ind - n as [| n IH]:
          smp.
    smp.
    ufl - Manipulation.shift.
    bwr - IH.
  Qed.

(* 
    des > (upn m idsubst x).
    ind - x as [| x IH].
    * smp.
    ufl - Manipulation.shift.
    des > (upn m ξ x ).

  Lemma upn_add :
    forall n m x ξ,
      upn m ξ x
    = upn (n + m) ξ (n + x).
  Proof.
    itr.
    ind - n as [| n IH]:
          smp.
    itr.
    do 2 rwr - Nat.add_succ_comm.
    do 2 rwr - Nat.add_succ_r.
    smp.
    ufl - Manipulation.shift.
    rwl - IH.
    Search (_ + S _). *)

  Theorem eraser_subst_add :
    forall k ks1 ks2 ks3 ks3' ξ,
        upn (length ks2) ξ (apply_eraser (ks2 ++ ks3) k)
      = upn (length ks2) ξ (apply_eraser (ks2 ++ ks3') k)
    ->  upn (length (ks1 ++ ks2)) ξ (apply_eraser (ks1 ++ ks2 ++ ks3) k)
      = upn (length (ks1 ++ ks2)) ξ (apply_eraser (ks1 ++ ks2 ++ ks3') k).
   Proof.
    itr.
    Check upn_from_inr_subst.
    (*
    #1 eraser_app_either ks1 (ks2 ++ ks3)
    
      + Option 1: is in ks1
        - ks1 = ks11 ++ [k] ks12
        - skip_app (to [k])
        - exact
        - both equal :)
      
      + Option 2-3: not int ks1
        - not In k ks1
        
    
    *)
    
      upn
        (length (ks1 ++ ks2))
        ξ
        (apply_eraser (ks1 ++ ks2) k)
    = upn
        (length ks2)
        ξ
        (apply_eraser ks2 k).



  Theorem exp_eraser_subst_env_rem_keys_eq :
    forall e ks Γ,
      (erase_exp
       (ks ᵏ++ (Γ //ᵏ ks).keys)
        e)
      .[upn (length ks)
       (list_subst
         (map erase_val (Γ //ᵏ ks).vals)
          idsubst)]
    = (erase_exp
       (ks ᵏ++ Γ.keys)
        e)
      .[upn (length ks)
       (list_subst
         (map erase_val Γ.vals)
          idsubst)].
  Proof.
    itr - e.
    ufl - eraser_add_keys.
    ind ~ ind_bs_exp - e;
          itr;
          ato;
          smp.
    (* EVar/EFunId *)
    2-3:    bwr - eraser_subst_env_rem_keys_eq.
    (* ECons/ESeq *)
    3 ,10:  bwr - IHe1 IHe2.
    (**)
    2: {
      ufl - eraser_add_vars
            eraser_add_keys.
      do 2 rwr - app_assoc.
      do 2 feq.
      spe - IHe: ks Γ.
      bwr - IHe1 IHe2.
      do 2 feq. 
      rwr - 
    2: {
      smp.
      bwr - eraser_subst_env_rem_keys_eq.
    }
    2: {
      bwr - eraser_subst_env_rem_keys_eq.



End EraserSubstRemove_EraserSubstLemmas.