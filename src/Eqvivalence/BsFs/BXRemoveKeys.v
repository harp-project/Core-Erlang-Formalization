From CoreErlang.Eqvivalence.BsFs Require Export B4Helpers.

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



(*   Lemma eraser_split_with_in :
    forall k ks,
        In k ks
    ->  exists ks₁ ks₂,
            ks = ks₁ ++ [k] ++ ks₂
        /\  apply_eraser ks k = length ks₁.
  Proof.
    itr - k ks Hin.
    ind - ks as [| k₁ ks IH]:
          smp *;
          lia.
    smp - Hin.
    des - Hin as [Hin | Hin].
    * clr - IH.
      cwr - Hin / k₁.
      exi - ([] : list Key) ks.
      smp.
      rwr - var_funid_eqb_refl.
      ato.
    * spc - IH: Hin.
      des - IH as [ks₁ [ks₂ [Hks Heq]]].
      exi - (k₁ :: ks₁) ks₂.
      cwr - Hks / ks.
      smp.
      spl_ato.
      des > (k =ᵏ k₁) as Hkey.
      rwl - app_assoc.
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
  Qed. *)



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





(*   Theorem shift_inj :
    forall ξ1 ξ2 n1 n2,
        shift ξ1 n1 = shift ξ2 n2
    ->  ξ1 n1 = ξ2 n2.
  Proof.
    itr.
    ufl - shift in H.
    des > (ξ1 n1);
          des > (ξ2 n2);
          ivc - H;
          feq.
    (* bpp - renameVal_inj_S in H1. *)
  Admitted. *)


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



(*   Lemma upn_rem :
    forall n m ξ1 ξ2 x1 x2,
        upn (n + m) ξ1 (n + x1)
      = upn (n + m) ξ2 (n + x2)
    ->  upn m ξ1 x1
      = upn m ξ2 x2.
  Proof.
    itr.
    ind - n as [| n IH]:
          smp.
    smp *.
    app - shift_inj in H.
    spc - IH: H.
    trv.
  Qed. *)



  (* Lemma upn_rem_eq :
    forall n m ξ x,
        upn (n + m) ξ (n + x)
      = upn m ξ x.
  Proof.
    itr.
    ind - n as [| n IH]:
          smp.
    smp.
    rwl - IH.
    ufl - shift.
    ass > (upn (n + m) ξ (n + x) = upn (n + m) ξ (n + x)): rfl.
    app - upn_rem in H.
    erewrite (upn_rem n m ξ ξ x x).
    ind - n as [| n IH]:
          smp.
    smp *.
    app - shift_inj in H.
    spc - IH: H.
    trv.
  Qed. *)



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



  Lemma upn_fun_app :
    forall m1 m2 ξ,
      upn m1 (upn m2 ξ)
    = upn (m1 + m2) ξ.
  Proof.
    itr.
    eapply functional_extensionality.
    itr.
    app - upn_app.
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



  Lemma upn_rem_var_reduction :
    forall n m ξ x,
        match upn (n + m) ξ (n + x) with
        | inl exp => exp
        | inr num => VVar num
        end
      = match upn m ξ x with
        | inl exp => (renameVal (fun x => x + n) exp)
        | inr num => VVar (n + num)
        end.
  Proof.
    itr.
    rwl - upn_app.
    rwr- Nat.add_comm.
    rem - x1 as Hx:
          (upn m ξ x).
    sym - Hx.
    des - x1.
    * app - (upn_inl_eq_2 n) in Hx.
      bwr - Hx.
    * app - (upn_from_inr_subst n) in Hx.
      cwr - Hx.
      bwr - Nat.add_comm.
  Qed.



  Lemma upn_rem_fid_reduction :
    forall n m ξ x a,
        match upn (n + m) ξ (n + x) with
        | inl exp => exp
        | inr num => VFunId (num, a)
        end
      = match upn m ξ x with
        | inl exp => (renameVal (fun x => x + n) exp)
        | inr num => VFunId ((n + num), a)
        end.
  Proof.
    itr.
    rwl - upn_app.
    rwr- Nat.add_comm.
    rem - x1 as Hx:
          (upn m ξ x).
    sym - Hx.
    des - x1.
    * app - (upn_inl_eq_2 n) in Hx.
      bwr - Hx.
    * app - (upn_from_inr_subst n) in Hx.
      cwr - Hx.
      bwr - Nat.add_comm.
  Qed.



  Lemma upn_rem_var_reduction_fun :
    forall n m ξ x f1 f2,
        match upn (n + m) ξ (n + x) with
        | inl exp => f1 exp
        | inr num => VVar (f2 num)
        end
      = match upn m ξ x with
        | inl exp => f1 (renameVal (fun x => x + n) exp)
        | inr num => VVar (f2 (n + num))
        end.
  Proof.
    itr.
    rwl - upn_app.
    rwr- Nat.add_comm.
    rem - x1 as Hx:
          (upn m ξ x).
    sym - Hx.
    des - x1.
    * app - (upn_inl_eq_2 n) in Hx.
      bwr - Hx.
    * app - (upn_from_inr_subst n) in Hx.
      rwr - Hx.
      bwr - Nat.add_comm.
  Qed.



  Lemma upn_rem_fid_reduction_fun :
    forall n m ξ x a f1 f2,
        match upn (n + m) ξ (n + x) with
        | inl exp => f1 exp
        | inr num => VFunId (f2 num, a)
        end
      = match upn m ξ x with
        | inl exp => f1 (renameVal (fun x => x + n) exp)
        | inr num => VFunId (f2 (n + num), a)
        end.
  Proof.
    itr.
    rwl - upn_app.
    rwr- Nat.add_comm.
    rem - x1 as Hx:
          (upn m ξ x).
    sym - Hx.
    des - x1.
    * app - (upn_inl_eq_2 n) in Hx.
      bwr - Hx.
    * app - (upn_from_inr_subst n) in Hx.
      cwr - Hx.
      bwr - Nat.add_comm.
  Qed.



  Lemma upn_rem_var_reduction_full :
    forall n ξ x,
        match upn n ξ (n + x) with
        | inl exp => exp
        | inr num => VVar num
        end
      = match ξ x with
        | inl exp => (renameVal (fun x => x + n) exp)
        | inr num => VVar (n + num)
        end.
  Proof.
    itr.
    pse - Nat.add_0_r: n.
    rem - tmp1: (n + x).
    rem - tmp2: (upn n ξ tmp1).
    cwl - H in Heqtmp2.
    sbt.
    ass > (upn 0 ξ x = ξ x): trv.
    cwl - H.
    app - upn_rem_var_reduction.
  Qed.



  Lemma upn_rem_fid_reduction_full :
    forall n ξ x a,
        match upn n ξ (n + x) with
        | inl exp => exp
        | inr num => VFunId (num, a)
        end
      = match ξ x with
        | inl exp => (renameVal (fun x => x + n) exp)
        | inr num => VFunId ((n + num), a)
        end.
  Proof.
    itr.
    pse - Nat.add_0_r: n.
    rem - tmp1: (n + x).
    rem - tmp2: (upn n ξ tmp1).
    cwl - H in Heqtmp2.
    sbt.
    ass > (upn 0 ξ x = ξ x): trv.
    cwl - H.
    app - upn_rem_fid_reduction.
  Qed.




  Lemma upn_rem_var_reduction_full_fun :
    forall n ξ x f1 f2,
        match upn n ξ (n + x) with
        | inl exp => f1 exp
        | inr num => VVar (f2 num)
        end
      = match ξ x with
        | inl exp => f1 (renameVal (fun x => x + n) exp)
        | inr num => VVar (f2 (n + num))
        end.
  Proof.
    itr.
    pse - Nat.add_0_r: n.
    rem - tmp1: (n + x).
    rem - tmp2: (upn n ξ tmp1).
    cwl - H in Heqtmp2.
    sbt.
    ass > (upn 0 ξ x = ξ x): trv.
    cwl - H.
    app - upn_rem_var_reduction_fun.
  Qed.



  Lemma upn_rem_fid_reduction_full_fun :
    forall n ξ x a f1 f2,
        match upn n ξ (n + x) with
        | inl exp => f1 exp
        | inr num => VFunId (f2 num, a)
        end
      = match ξ x with
        | inl exp => f1 (renameVal (fun x => x + n) exp)
        | inr num => VFunId (f2 (n + num), a)
        end.
  Proof.
    itr.
    pse - Nat.add_0_r: n.
    rem - tmp1: (n + x).
    rem - tmp2: (upn n ξ tmp1).
    cwl - H in Heqtmp2.
    sbt.
    ass > (upn 0 ξ x = ξ x): trv.
    cwl - H.
    app - upn_rem_fid_reduction_fun.
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



(*   Theorem eraser_subst_env_rem_keys_fun_eq :
    forall ks Γ,
        (fun k =>
        upn (length ks)
            (list_subst (map erase_val
              (Γ //ᵏ ks).vals)
              idsubst)
            (apply_eraser
              (ks ++ (Γ //ᵏ ks).keys)
              k))
      = (fun k =>
        upn (length ks)
            (list_subst
              (map erase_val
                Γ.vals)
                idsubst)
            (apply_eraser
              (ks ++ Γ.keys)
              k)).
  Proof.
    itr.
    apply functional_extensionality.
    itr - k.
    app - eraser_subst_env_rem_keys_eq.
  Qed. *)






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


  (* Theorem eraser_subst_env_rem_keys_app_eq_fun :
    forall ks1 ks2 Γ,
        (fun k =>
          upn (length (ks1 ++ ks2))
              (list_subst (map erase_val
                (Γ //ᵏ ks2).vals)
                idsubst)
              (apply_eraser
                (ks1 ++ ks2 ++ (Γ //ᵏ ks2).keys)
                k))
      = (fun k =>
          upn (length (ks1 ++ ks2))
              (list_subst
                (map erase_val
                  Γ.vals)
                  idsubst)
              (apply_eraser
                (ks1 ++ ks2 ++ Γ.keys)
                k)).
  Proof.
    itr.
    apply functional_extensionality.
    itr - k.
    app - eraser_subst_env_rem_keys_app_eq.
  Qed.


  Theorem eraser_subst_env_rem_keys_app_eq_fun2 :
    forall ks1 ks2 Γ,
        (fun k =>
          upn (length (ks1 ++ ks2))
              (list_subst (map erase_val
                (Γ //ᵏ ks2).vals)
                idsubst)
              (apply_eraser
                (ks1 ++ ks2 ++ (Γ //ᵏ ks2).keys)
                k))
      = (fun k =>
          upn (length (ks1 ++ ks2))
              (list_subst
                (map erase_val
                  Γ.vals)
                  idsubst)
              (apply_eraser
                (ks1 ++ ks2 ++ Γ.keys)
                k)).
  Proof.
    itr.
    apply functional_extensionality.
    itr - k.
    app - eraser_subst_env_rem_keys_app_eq.
  Qed. *)


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

  (* Lemma upn_add1 :
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
  Qed. *)

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

(* Require Import Coq.Logic.Classical. *)
(* Require Import Coq.Logic.Classical_Prop.
Lemma forall_or_not_implies_or_forall :
  forall (A : Type) (P Q : A -> Prop),
    (forall x, P x \/ Q x) -> (forall x, P x) \/ (forall x, Q x).
Proof.
  intros A P Q H.
  (* We will use classical logic to derive a contradiction *)
  apply NNPP.
  unfold not.
  intros Hcontra.
  (* Assume neither (forall x, P x) nor (forall x, Q x) holds *)
  assert (H1 : ~ (forall x, P x)).
  { intro HforallP. apply Hcontra. left. assumption. }
  assert (H2 : ~ (forall x, Q x)).
  { intro HforallQ. apply Hcontra. right. assumption. }
  (* Use classical logic to derive the existence of counterexamples *)
  Check not_all_not_ex.
  apply not_all_not_ex in H1.
  apply not_all_not_ex in H2.
  destruct H1 as [x1 HnotP].
  destruct H2 as [x2 HnotQ].
  (* Use the original hypothesis to derive a contradiction *)
  specialize (H x1) as [HPx1 | HQx1].
  - contradiction.
  - specialize (H x2) as [HPx2 | HQx2].
    + contradiction.
    + contradiction.
Qed. *)












  Theorem eraser_subst_add :
    forall k ks1 ks2 ks3 m ξ1 ξ2,
        upn m ξ1 (apply_eraser ks2 k)
      = upn m ξ2 (apply_eraser ks3 k)
    ->  upn (length ks1) (upn m ξ1) (apply_eraser (ks1 ++ ks2) k)
      = upn (length ks1) (upn m ξ2) (apply_eraser (ks1 ++ ks3) k).
  Proof.
    itr.
    psc - upn_add as Hadd:
          (length ks1) m ξ1 ξ2
          (apply_eraser ks2 k)
          (apply_eraser ks3 k)
          H.
    do 2 rwl - upn_app in Hadd.
    (* ass > (In k ks1 \/ not (In k ks1)):
          app - classic.
    des - H as [H | H]. *)
    pse - eraser_app_either as H2: k ks1 ks2.
    pse - eraser_app_either as H3: k ks1 ks3.
    des - H2 as [H2 | [H2 | H2]];
    des - H3 as [H3 | [H3 | H3]].
    * clr - Hadd.
      des - H2 as [ks11 [ks12 [Hks1 [_ [_ [_ Hnotin]]]]]].
      des - H3 as [_ [_ [_ [_ [_ [_ _]]]]]].
      cwr - Hks1 / ks1.
      do 4 rwl - app_assoc in *.
      rwr - eraser_notin_skip_app;
            ato.
      rwr - (eraser_notin_skip_app k ks11);
            ato.
      clr - Hnotin.
      do 3 rwl - cons_app.
      do 2 rwr - eraser_exact.
      rwr - Nat.add_0_r.
      rwr - upn_Var.
            2: rwr - length_app; smp; lia.
      rwr - upn_Var.
            2: rwr - length_app; smp; lia.
      rfl.
    * des - H2 as [_ [_ [_ [_ [_ [Hisin _]]]]]].
      des - H3 as [ks4 [_ [_ [_ [_ [_ Hnotin]]]]]].
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      con.
    * des - H2 as [_ [_ [_ [_ [_ [Hisin _]]]]]].
      des - H3 as [_ Hnotin].
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      con.
    * des - H2 as [ks4 [_ [_ [_ [_ [_ Hnotin]]]]]].
      des - H3 as [_ [_ [_ [_ [_ [Hisin _]]]]]].
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      con.
    * des - H2 as [ks4 [_ [_ [_ [_ [_ Hnotin]]]]]].
      clr - H3.
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      clr - ks4.
      do 2 rwl - eraser_notin_skip_app in Hadd;
            ato.
    * des - H2 as [ks4 [_ [_ [_ [_ [_ Hnotin]]]]]].
      clr - H3.
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      clr - ks4.
      do 2 rwl - eraser_notin_skip_app in Hadd;
            ato.
    * des - H2 as [_ Hnotin].
      des - H3 as [_ [_ [_ [_ [_ [Hisin _]]]]]].
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      con.
    * des - H2 as [_ Hnotin].
      clr - H3.
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      do 2 rwl - eraser_notin_skip_app in Hadd;
            ato.
    * des - H2 as [_ Hnotin].
      clr - H3.
      apply not_in_app in Hnotin.
      des - Hnotin as [Hnotin _].
      do 2 rwl - eraser_notin_skip_app in Hadd;
            ato.
  Qed.



  (* Theorem eraser_subst_fun_add :
    forall k ks1 ks2 ks3 m ξ1 ξ2,
        (fun k => upn m ξ1 (fun  ks2 k))
      = (fun k => upn m ξ2 (apply_eraser ks2 k))
    ->  upn (length ks1) (upn m ξ1) (apply_eraser (ks1 ++ ks2) k)
      = upn (length ks1) (upn m ξ2) (apply_eraser (ks1 ++ ks3) k).
  Proof.  *)
  
  (*
  
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
  *)


(*   Import SubstSemanticsLemmas.


  Theorem shift_sur :
    forall ξ1 ξ2 n1 n2,
      ξ1 n1 = ξ2 n2 ->
      shift ξ1 n1 = shift ξ2 n2.
  Proof.
    intros ξ1 ξ2 n1 n2 H.
    ufl - shift.
    bwr - H.
  Qed.
  Theorem match_shift_sur :
    forall ξ1 ξ2 n1 n2,
        match ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = match ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end
    ->  match shift ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = match shift ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr.
    ufl - shift.
    rem - x1 x2 as Hx1 Hx2:
          (ξ1 n1)
          (ξ2 n2).
    des - x1;
    des - x2;
          ivc - H;
          trv.
  Qed.


  Lemma vval_eq :
    forall v₁ v₂,
        v₁ = v₂
    <-> ˝ v₁ = ˝ v₂.
  Proof.
    itr.
    spl; itr.
    * feq; asm.
    * bvs - H.
  Qed.

  Theorem vval_match_shift_sur :
    forall ξ1 ξ2 n1 n2,
        ˝ match ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = ˝ match ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end
    ->  ˝ match shift ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = ˝ match shift ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr.
    rwl - vval_eq in *.
    bpp - match_shift_sur.
  Qed. *)

  (*
  IHe :
  (erase_exp (ks1 ++ ks ++ ks2) e).[upn (base.length ks1) (upn (base.length ks) ξ1)] =
  (erase_exp (ks1 ++ ks ++ ks3) e).[upn (base.length ks1) (upn (base.length ks) ξ2)]
______________________________________(1/1)
(erase_exp (ks ++ ks1 ++ ks2) e).[upn (base.length ks) (upn (base.length ks1) ξ1)] =
(erase_exp (ks ++ ks1 ++ ks3) e).[upn (base.length ks) (upn (base.length ks1) ξ2)]
  *)

(*

H1 :
  match
    upn (base.length ks0 + base.length ks1 + base.length ks2) ξ1
      (apply_eraser (ks0 ++ ks1 ++ ks2 ++ ks3) (inl x))
  with
  | inl exp => exp
  | inr num => VVar num
  end =
  match
    upn (base.length ks0 + base.length ks1 + base.length ks2) ξ2
      (apply_eraser (ks0 ++ ks1 ++ ks2 ++ ks4) (inl x))
  with
  | inl exp => exp
  | inr num => VVar num
  end
______________________________________(1/1)
match
  upn (base.length ks0 + base.length ks2 + base.length ks1) ξ1
    (apply_eraser (ks0 ++ ks2 ++ ks1 ++ ks3) (inl x))
with
| inl exp => exp
| inr num => VVar num
end =
match
  upn (base.length ks0 + base.length ks2 + base.length ks1) ξ2
    (apply_eraser (ks0 ++ ks2 ++ ks1 ++ ks4) (inl x))
with
| inl exp => exp
| inr num => VVar num
end
*)






  Theorem match_eraser_subst_upn_var_comm :
    forall k ks0 ks1 ks2 ks3 ks4 ξ1 ξ2,
        match
          upn (base.length ks0 + base.length ks1 + base.length ks2) ξ1
            (apply_eraser (ks0 ++ ks1 ++ ks2 ++ ks3) k)
        with
        | inl exp => exp
        | inr num => VVar num
        end
      = match
          upn (base.length ks0 + base.length ks1 + base.length ks2) ξ2
            (apply_eraser (ks0 ++ ks1 ++ ks2 ++ ks4) k)
        with
        | inl exp => exp
        | inr num => VVar num
        end
   ->   match
          upn (base.length ks0 + base.length ks2 + base.length ks1) ξ1
            (apply_eraser (ks0 ++ ks2 ++ ks1 ++ ks3) k)
        with
        | inl exp => exp
        | inr num => VVar num
        end
      = match
          upn (base.length ks0 + base.length ks2 + base.length ks1) ξ2
            (apply_eraser (ks0 ++ ks2 ++ ks1 ++ ks4) k)
        with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr -  k ks0 ks1 ks2 ks3 ks4 ξ1 ξ2 Hmatch.
    pse - eraser_app_either: k ks0 (ks1 ++ ks2 ++ ks3).
    des - H as [H | [H | H]].
    * (* is in ks0 *)
      clr - Hmatch.
      des - H as [ks01 [ks02 [Hks0 [_ [_ [_ Hnotin]]]]]].
      cwr - Hks0 / ks0.
      do 4 rwl - app_assoc in *.
      rwr - eraser_notin_skip_app;
            ato.
      rwr - (eraser_notin_skip_app k ks01);
            ato.
      clr - Hnotin.
      do 3 rwl - cons_app.
      do 2 rwr - eraser_exact.
      rwr - Nat.add_0_r.
      rwr - upn_Var.
            2: rwr - length_app; smp; lia.
      rwr - upn_Var.
            2: rwr - length_app; smp; lia.
      rfl.
    * (* not in ks0 *)
      des - H as [ks [_ [_ [_ [_ [_ Hnotin0]]]]]].
      apply not_in_app in Hnotin0.
      des - Hnotin0 as [Hnotin0 _].
      rwr - eraser_notin_skip_app in *;
            ato.
      rwr - (eraser_notin_skip_app k ks0) in *;
            ato.
      clr - Hnotin0 ks.
      rwl - Nat.add_assoc in *.
      do 2 rewrite upn_rem_var_reduction in *.
      rem - n0 as Hn0 / Hn0 ks0:
            (base.length ks0).
      pse - eraser_app_either: k ks2 (ks1 ++ ks3).
      des - H as [H | [H | H]].
      - (* is in ks2 *)
        des - H as [ks21 [ks22 [Hks2 [_ [_ [_ Hnotin]]]]]].
        cwr - Hks2 / ks2.
        do 4 rwl - app_assoc in *.
        rwr - eraser_notin_skip_app;
              ato.
        rwr - (eraser_notin_skip_app k ks21);
              ato.
        clr - Hnotin.
        do 3 rwl - cons_app.
        do 2 rwr - eraser_exact.
        rwr - Nat.add_0_r.
        rwr - upn_Var.
              2: rwr - length_app; smp; lia.
        rwr - upn_Var.
              2: rwr - length_app; smp; lia.
        rfl.
      - (* not in ks2 *)
        des - H as [ks [_ [_ [_ [_ [Hisin13 Hnotin2]]]]]].
        apply not_in_app in Hnotin2.
        des - Hnotin2 as [Hnotin2 _].
        rwr - eraser_notin_skip_app;
              ato.
        rwr - (eraser_notin_skip_app k ks2);
              ato.
        clr - ks.
        do 2 rewrite upn_rem_var_reduction_fun.
        pse - eraser_app_either: k ks1 (ks2 ++ ks3).
        des - H as [H | [H | H]].
        + (* is in ks1 *)
          clr - Hisin13 Hnotin2.
          des - H as [ks11 [ks12 [Hks1 [_ [_ [_ Hnotin]]]]]].
          cwr - Hks1 / ks1.
          do 4 rwl - app_assoc in *.
          rwr - eraser_notin_skip_app;
                ato.
          rwr - (eraser_notin_skip_app k ks11);
                ato.
          clr - Hnotin.
          do 3 rwl - cons_app.
          do 2 rwr - eraser_exact.
          rwr - Nat.add_0_r.
          rwr - upn_Var.
                2: rwr - length_app; smp; lia.
          rwr - upn_Var.
                2: rwr - length_app; smp; lia.
          rfl.
        + (* not in ks1  *)
          des - H as [ks [_ [_ [_ [_ [Hisin23 Hnotin1]]]]]].
          apply not_in_app in Hnotin1.
          des - Hnotin1 as [Hnotin1 _].
          apply in_app_or in Hisin13, Hisin23.
          des - Hisin13 as [Hisin1 | _];
          des - Hisin23 as [Hisin2 | _];
                try con.
          pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
          clr - Hnotin2.
          rwr - eraser_notin_skip_app;
                ato.
          rwr - (eraser_notin_skip_app k ks1);
                ato.
          clr - Hnotin1 ks.
          do 2 rwr - app_assoc in Hmatch.
          rwr - eraser_notin_skip_app in Hmatch;
                ato.
          rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
                ato.
          clr - Hnotin12.
          rwl - length_app in Hmatch.
          do 2 rewrite upn_rem_var_reduction_full_fun in *.
          rwr - length_app in Hmatch.
          pse - rename_comp.
          des - H as [_ [_ HrenameVal_comp]].
          ass >
            ( (fun x => x + (length ks1 + length ks2) + n0)
            = (fun x => x + length ks1 + length ks2 + n0))
            as Hcomp:
            apply functional_extensionality;
            itr;
            rwr - Nat.add_assoc.
          des > (ξ1 (apply_eraser ks3 k));
          des > (ξ2 (apply_eraser ks4 k)).
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** clr - Hcomp HrenameVal_comp.
             do 2 rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
        + (* not in (ks1 ++ ks2 ++ ks3 *)
          clr - Hisin13.
          des - H as [_ Hnotin123].
          apply not_in_app in Hnotin123.
          des - Hnotin123 as [Hnotin1 _].
          pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
          clr - Hnotin2.
          rwr - eraser_notin_skip_app;
                ato.
          rwr - (eraser_notin_skip_app k ks1);
                ato.
          clr - Hnotin1.
          do 2 rwr - app_assoc in Hmatch.
          rwr - eraser_notin_skip_app in Hmatch;
                ato.
          rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
                ato.
          clr - Hnotin12.
          rwl - length_app in Hmatch.
          do 2 rewrite upn_rem_var_reduction_full_fun in *.
          rwr - length_app in Hmatch.
          pse - rename_comp.
          des - H as [_ [_ HrenameVal_comp]].
          ass >
            ( (fun x => x + (length ks1 + length ks2) + n0)
            = (fun x => x + length ks1 + length ks2 + n0))
            as Hcomp:
            apply functional_extensionality;
            itr;
            rwr - Nat.add_assoc.
          des > (ξ1 (apply_eraser ks3 k));
          des > (ξ2 (apply_eraser ks4 k)).
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** clr - Hcomp HrenameVal_comp.
             do 2 rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
      - (* not in (ks2 ++ ks1 ++ ks3 *)
        des - H as [_ Hnotin213].
        apply not_in_app in Hnotin213.
        des - Hnotin213 as [Hnotin2 Hnotin13].
        apply not_in_app in Hnotin13.
        des - Hnotin13 as [Hnotin1 _].
        pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
        pose proof app_not_in k ks2 ks1 Hnotin2 Hnotin1 as Hnotin21.
        clr - Hnotin1 Hnotin2.
        rwl - length_app in *.
        repeat rwr - app_assoc in *.
        rwr - (eraser_notin_skip_app k (ks2 ++ ks1));
              ato.
        rwr - (eraser_notin_skip_app k (ks2 ++ ks1));
              ato.
        clr - Hnotin21.
        rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
              ato.
        rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
              ato.
        clr - Hnotin12.
        do 2 rewrite upn_rem_var_reduction_full_fun in *.
        rwr - length_app in *.
        pse - rename_comp.
        des - H as [_ [_ HrenameVal_comp]].
        ass >
          ( (fun x => x + (length ks1 + length ks2) + n0)
          = (fun x => x + (length ks2 + length ks1) + n0))
          as Hcomp:
          apply functional_extensionality;
          itr;
          rewrite Nat.add_comm with (n := length ks2).
        des > (ξ1 (apply_eraser ks3 k));
        des > (ξ2 (apply_eraser ks4 k)).
        + repeat rwr - HrenameVal_comp in *.
          clr - HrenameVal_comp.
          unfold compose in *.
          cwr - Hcomp in Hmatch.
          exa - Hmatch.
        + repeat rwr - HrenameVal_comp in *.
          clr - HrenameVal_comp.
          unfold compose in *.
          rewrite Nat.add_comm with (n := length ks2).
          exa - Hmatch.
        + repeat rwr - HrenameVal_comp in *.
          clr - HrenameVal_comp.
          unfold compose in *.
          rewrite Nat.add_comm with (n := length ks2).
          exa - Hmatch.
        + clr - Hcomp HrenameVal_comp.
          rewrite Nat.add_comm with (n := length ks2).
          exa - Hmatch.
    * (* not in (ks0 ++ ks1 ++ ks2 ++ ks3 *)
      des - H as [_ Hnotin0123].
      apply not_in_app in Hnotin0123.
      des - Hnotin0123 as [Hnotin0 Hnotin123].
      apply not_in_app in Hnotin123.
      des - Hnotin123 as [Hnotin1 Hnotin23].
      apply not_in_app in Hnotin23.
      des - Hnotin23 as [Hnotin2 _].
      pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
      pose proof app_not_in k ks2 ks1 Hnotin2 Hnotin1 as Hnotin21.
      clr - Hnotin1 Hnotin2.
      pose proof app_not_in k ks0 (ks1 ++ ks2) Hnotin0 Hnotin12 as Hnotin012.
      pose proof app_not_in k ks0 (ks2 ++ ks1) Hnotin0 Hnotin21 as Hnotin021.
      clr - Hnotin0 Hnotin12 Hnotin21.
      do 2 rwl - length_app in *.
      repeat rwr - app_assoc in *.
      rwr - eraser_notin_skip_app; ato.
      rwr - eraser_notin_skip_app; ato.
      rwr - eraser_notin_skip_app in Hmatch; ato.
      rwr - eraser_notin_skip_app in Hmatch; ato.
      clr - Hnotin012 Hnotin021.
      do 2 rewrite upn_rem_var_reduction_full_fun in *.
      rem - n1 n2 as Hn1 Hn2:
        (base.length ((ks0 ++ ks1) ++ ks2))
        (base.length ((ks0 ++ ks2) ++ ks1)).
      ass > (n1 = n2) as Heqn:
            sbt;
            do 4 rwr - length_app;
            lia.
      cwl - Heqn / Hn1 Hn2 ks0 ks1 ks2 n2.
      ren - n: n1.
      exa - Hmatch.
  Qed.











  Theorem match_eraser_subst_upn_fid_comm :
    forall k ks0 ks1 ks2 ks3 ks4 ξ1 ξ2 a,
        match
          upn (base.length ks0 + base.length ks1 + base.length ks2) ξ1
            (apply_eraser (ks0 ++ ks1 ++ ks2 ++ ks3) k)
        with
        | inl exp => exp
        | inr num => VFunId (num, a)
        end
      = match
          upn (base.length ks0 + base.length ks1 + base.length ks2) ξ2
            (apply_eraser (ks0 ++ ks1 ++ ks2 ++ ks4) k)
        with
        | inl exp => exp
        | inr num => VFunId (num, a)
        end
   ->   match
          upn (base.length ks0 + base.length ks2 + base.length ks1) ξ1
            (apply_eraser (ks0 ++ ks2 ++ ks1 ++ ks3) k)
        with
        | inl exp => exp
        | inr num => VFunId (num, a)
        end
      = match
          upn (base.length ks0 + base.length ks2 + base.length ks1) ξ2
            (apply_eraser (ks0 ++ ks2 ++ ks1 ++ ks4) k)
        with
        | inl exp => exp
        | inr num => VFunId (num, a)
        end.
  Proof.
    itr -  k ks0 ks1 ks2 ks3 ks4 ξ1 ξ2 a Hmatch.
    pse - eraser_app_either: k ks0 (ks1 ++ ks2 ++ ks3).
    des - H as [H | [H | H]].
    * (* is in ks0 *)
      clr - Hmatch.
      des - H as [ks01 [ks02 [Hks0 [_ [_ [_ Hnotin]]]]]].
      cwr - Hks0 / ks0.
      do 4 rwl - app_assoc in *.
      rwr - eraser_notin_skip_app;
            ato.
      rwr - (eraser_notin_skip_app k ks01);
            ato.
      clr - Hnotin.
      do 3 rwl - cons_app.
      do 2 rwr - eraser_exact.
      rwr - Nat.add_0_r.
      rwr - upn_Var.
            2: rwr - length_app; smp; lia.
      rwr - upn_Var.
            2: rwr - length_app; smp; lia.
      rfl.
    * (* not in ks0 *)
      des - H as [ks [_ [_ [_ [_ [_ Hnotin0]]]]]].
      apply not_in_app in Hnotin0.
      des - Hnotin0 as [Hnotin0 _].
      rwr - eraser_notin_skip_app in *;
            ato.
      rwr - (eraser_notin_skip_app k ks0) in *;
            ato.
      clr - Hnotin0 ks.
      rwl - Nat.add_assoc in *.
      do 2 rewrite upn_rem_fid_reduction in *.
      rem - n0 as Hn0 / Hn0 ks0:
            (base.length ks0).
      pse - eraser_app_either: k ks2 (ks1 ++ ks3).
      des - H as [H | [H | H]].
      - (* is in ks2 *)
        des - H as [ks21 [ks22 [Hks2 [_ [_ [_ Hnotin]]]]]].
        cwr - Hks2 / ks2.
        do 4 rwl - app_assoc in *.
        rwr - eraser_notin_skip_app;
              ato.
        rwr - (eraser_notin_skip_app k ks21);
              ato.
        clr - Hnotin.
        do 3 rwl - cons_app.
        do 2 rwr - eraser_exact.
        rwr - Nat.add_0_r.
        rwr - upn_Var.
              2: rwr - length_app; smp; lia.
        rwr - upn_Var.
              2: rwr - length_app; smp; lia.
        rfl.
      - (* not in ks2 *)
        des - H as [ks [_ [_ [_ [_ [Hisin13 Hnotin2]]]]]].
        apply not_in_app in Hnotin2.
        des - Hnotin2 as [Hnotin2 _].
        rwr - eraser_notin_skip_app;
              ato.
        rwr - (eraser_notin_skip_app k ks2);
              ato.
        clr - ks.
        do 2 rewrite upn_rem_fid_reduction_fun.
        pse - eraser_app_either: k ks1 (ks2 ++ ks3).
        des - H as [H | [H | H]].
        + (* is in ks1 *)
          clr - Hisin13 Hnotin2.
          des - H as [ks11 [ks12 [Hks1 [_ [_ [_ Hnotin]]]]]].
          cwr - Hks1 / ks1.
          do 4 rwl - app_assoc in *.
          rwr - eraser_notin_skip_app;
                ato.
          rwr - (eraser_notin_skip_app k ks11);
                ato.
          clr - Hnotin.
          do 3 rwl - cons_app.
          do 2 rwr - eraser_exact.
          rwr - Nat.add_0_r.
          rwr - upn_Var.
                2: rwr - length_app; smp; lia.
          rwr - upn_Var.
                2: rwr - length_app; smp; lia.
          rfl.
        + (* not in ks1  *)
          des - H as [ks [_ [_ [_ [_ [Hisin23 Hnotin1]]]]]].
          apply not_in_app in Hnotin1.
          des - Hnotin1 as [Hnotin1 _].
          apply in_app_or in Hisin13, Hisin23.
          des - Hisin13 as [Hisin1 | _];
          des - Hisin23 as [Hisin2 | _];
                try con.
          pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
          clr - Hnotin2.
          rwr - eraser_notin_skip_app;
                ato.
          rwr - (eraser_notin_skip_app k ks1);
                ato.
          clr - Hnotin1 ks.
          do 2 rwr - app_assoc in Hmatch.
          rwr - eraser_notin_skip_app in Hmatch;
                ato.
          rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
                ato.
          clr - Hnotin12.
          rwl - length_app in Hmatch.
          do 2 rewrite upn_rem_fid_reduction_full_fun in *.
          rwr - length_app in Hmatch.
          pse - rename_comp.
          des - H as [_ [_ HrenameVal_comp]].
          ass >
            ( (fun x => x + (length ks1 + length ks2) + n0)
            = (fun x => x + length ks1 + length ks2 + n0))
            as Hcomp:
            apply functional_extensionality;
            itr;
            rwr - Nat.add_assoc.
          des > (ξ1 (apply_eraser ks3 k));
          des > (ξ2 (apply_eraser ks4 k)).
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** clr - Hcomp HrenameVal_comp.
             do 2 rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
        + (* not in (ks1 ++ ks2 ++ ks3 *)
          clr - Hisin13.
          des - H as [_ Hnotin123].
          apply not_in_app in Hnotin123.
          des - Hnotin123 as [Hnotin1 _].
          pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
          clr - Hnotin2.
          rwr - eraser_notin_skip_app;
                ato.
          rwr - (eraser_notin_skip_app k ks1);
                ato.
          clr - Hnotin1.
          do 2 rwr - app_assoc in Hmatch.
          rwr - eraser_notin_skip_app in Hmatch;
                ato.
          rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
                ato.
          clr - Hnotin12.
          rwl - length_app in Hmatch.
          do 2 rewrite upn_rem_fid_reduction_full_fun in *.
          rwr - length_app in Hmatch.
          pse - rename_comp.
          des - H as [_ [_ HrenameVal_comp]].
          ass >
            ( (fun x => x + (length ks1 + length ks2) + n0)
            = (fun x => x + length ks1 + length ks2 + n0))
            as Hcomp:
            apply functional_extensionality;
            itr;
            rwr - Nat.add_assoc.
          des > (ξ1 (apply_eraser ks3 k));
          des > (ξ2 (apply_eraser ks4 k)).
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** repeat rwr - HrenameVal_comp in *.
             clr - HrenameVal_comp.
             unfold compose in *.
             cwr - Hcomp in Hmatch.
             rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
          ** clr - Hcomp HrenameVal_comp.
             do 2 rewrite Nat.add_assoc with (n := length ks2).
             rewrite Nat.add_comm with (n := length ks2).
             repeat rwr - Nat.add_assoc in *.
             exa - Hmatch.
      - (* not in (ks2 ++ ks1 ++ ks3 *)
        des - H as [_ Hnotin213].
        apply not_in_app in Hnotin213.
        des - Hnotin213 as [Hnotin2 Hnotin13].
        apply not_in_app in Hnotin13.
        des - Hnotin13 as [Hnotin1 _].
        pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
        pose proof app_not_in k ks2 ks1 Hnotin2 Hnotin1 as Hnotin21.
        clr - Hnotin1 Hnotin2.
        rwl - length_app in *.
        repeat rwr - app_assoc in *.
        rwr - (eraser_notin_skip_app k (ks2 ++ ks1));
              ato.
        rwr - (eraser_notin_skip_app k (ks2 ++ ks1));
              ato.
        clr - Hnotin21.
        rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
              ato.
        rwr - (eraser_notin_skip_app k (ks1 ++ ks2)) in Hmatch;
              ato.
        clr - Hnotin12.
        do 2 rewrite upn_rem_fid_reduction_full_fun in *.
        rwr - length_app in *.
        pse - rename_comp.
        des - H as [_ [_ HrenameVal_comp]].
        ass >
          ( (fun x => x + (length ks1 + length ks2) + n0)
          = (fun x => x + (length ks2 + length ks1) + n0))
          as Hcomp:
          apply functional_extensionality;
          itr;
          rewrite Nat.add_comm with (n := length ks2).
        des > (ξ1 (apply_eraser ks3 k));
        des > (ξ2 (apply_eraser ks4 k)).
        + repeat rwr - HrenameVal_comp in *.
          clr - HrenameVal_comp.
          unfold compose in *.
          cwr - Hcomp in Hmatch.
          exa - Hmatch.
        + repeat rwr - HrenameVal_comp in *.
          clr - HrenameVal_comp.
          unfold compose in *.
          rewrite Nat.add_comm with (n := length ks2).
          exa - Hmatch.
        + repeat rwr - HrenameVal_comp in *.
          clr - HrenameVal_comp.
          unfold compose in *.
          rewrite Nat.add_comm with (n := length ks2).
          exa - Hmatch.
        + clr - Hcomp HrenameVal_comp.
          rewrite Nat.add_comm with (n := length ks2).
          exa - Hmatch.
    * (* not in (ks0 ++ ks1 ++ ks2 ++ ks3 *)
      des - H as [_ Hnotin0123].
      apply not_in_app in Hnotin0123.
      des - Hnotin0123 as [Hnotin0 Hnotin123].
      apply not_in_app in Hnotin123.
      des - Hnotin123 as [Hnotin1 Hnotin23].
      apply not_in_app in Hnotin23.
      des - Hnotin23 as [Hnotin2 _].
      pose proof app_not_in k ks1 ks2 Hnotin1 Hnotin2 as Hnotin12.
      pose proof app_not_in k ks2 ks1 Hnotin2 Hnotin1 as Hnotin21.
      clr - Hnotin1 Hnotin2.
      pose proof app_not_in k ks0 (ks1 ++ ks2) Hnotin0 Hnotin12 as Hnotin012.
      pose proof app_not_in k ks0 (ks2 ++ ks1) Hnotin0 Hnotin21 as Hnotin021.
      clr - Hnotin0 Hnotin12 Hnotin21.
      do 2 rwl - length_app in *.
      repeat rwr - app_assoc in *.
      rwr - eraser_notin_skip_app; ato.
      rwr - eraser_notin_skip_app; ato.
      rwr - eraser_notin_skip_app in Hmatch; ato.
      rwr - eraser_notin_skip_app in Hmatch; ato.
      clr - Hnotin012 Hnotin021.
      do 2 rewrite upn_rem_fid_reduction_full_fun in *.
      rem - n1 n2 as Hn1 Hn2:
        (base.length ((ks0 ++ ks1) ++ ks2))
        (base.length ((ks0 ++ ks2) ++ ks1)).
      ass > (n1 = n2) as Heqn:
            sbt;
            do 4 rwr - length_app;
            lia.
      cwl - Heqn / Hn1 Hn2 ks0 ks1 ks2 n2.
      ren - n: n1.
      exa - Hmatch.
  Qed.


































































  Theorem exp_eraser_subst_upn_comm :
    forall e ks0 ks1 ks2 ks3 ks4 ξ1 ξ2,
        (erase_exp (ks0 ++ ks1 ++ ks2 ++ ks3) e)
          .[upn (base.length ks0)
           (upn (base.length ks1)
           (upn (base.length ks2) ξ1))]
      = (erase_exp (ks0 ++ ks1 ++ ks2 ++ ks4) e)
          .[upn (base.length ks0)
           (upn (base.length ks1)
           (upn (base.length ks2) ξ2))]
    ->  (erase_exp (ks0 ++ ks2 ++ ks1 ++ ks3) e)
          .[upn (base.length ks0)
           (upn (base.length ks2)
           (upn (base.length ks1) ξ1))]
      = (erase_exp (ks0 ++ ks2 ++ ks1 ++ ks4) e)
          .[upn (base.length ks0)
           (upn (base.length ks2)
           (upn (base.length ks1) ξ2))].
  Proof.
    itr.
    do 4 rwr - upn_fun_app in *.
    gen - ξ2 ξ1 ks4 ks3 ks2 ks1 ks0.
    ind ~ ind_bs_exp - e;
          itr;
          ato;
          smp.
    (* EVar/EFunId *)
    2: {
      smp - H.
      ivc - H.
      rem - k as Hk / Hk x:
            (inl x : Key).
      feq.
      bpp - match_eraser_subst_upn_var_comm.
    }
    2: {
      smp - H.
      ivc - H.
      rem - k as Hk / Hk:
            (inr f : Key).
      feq.
      bpp - match_eraser_subst_upn_fid_comm.
    }
    (* EFun *)
    2: {
      ivc - H.
      ufl - eraser_add_vars
                 eraser_add_keys
                 in *.
      rwr - (length_map_inl Var FunctionIdentifier) in *.
      rem - ks as Hks / Hks xs:
            (map inl xs : list Key).
      do 2 feq.
      do 2 rwr - upn_fun_app in *.
      do 2 rwr - Nat.add_assoc in *.
      spe - IHe:  (ks ++ ks0) ks1 ks2 ks3 ks4 ξ1 ξ2.
      rwr - length_app in IHe.
      do 4 rwl - app_assoc in IHe.
      spc - IHe: H1.
      by setoid_rewrite IHe.
    }
    (* ELet *)
    8: {
      ivc - H.
      ufl - eraser_add_vars
                 eraser_add_keys
                 in *.
      rwr - (length_map_inl Var FunctionIdentifier) in *.
      rem - ks as Hks / Hks xs₁:
            (map inl xs₁ : list Key).
      do 2 feq.
      * clr - IHe2 H2.
        spe - IHe1:  ks0 ks1 ks2 ks3 ks4 ξ1 ξ2.
        spc - IHe1: H1.
        by setoid_rewrite IHe1.
      * clr - IHe1 H1.
        do 2 rwr - upn_fun_app in *.
        do 2 rwr - Nat.add_assoc in *.
        spe - IHe2:  (ks ++ ks0) ks1 ks2 ks3 ks4 ξ1 ξ2.
        rwr - length_app in IHe2.
        do 4 rwl - app_assoc in IHe2.
        spc - IHe2: H2.
        by setoid_rewrite IHe2.
    }
  Admitted.














  Theorem exp_eraser_subst_add :
    forall e ks1 ks2 ks3 ξ1 ξ2,
      (*   upn (length ks2) ξ1
      = upn (length ks2) ξ2 *)
        (erase_exp ks2 e).[ξ1]
      = (erase_exp ks3 e).[ξ2]
    ->  (erase_exp (ks1 ++ ks2) e).[upn (length ks1) ξ1]
      = (erase_exp (ks1 ++ ks3) e).[upn (length ks1) ξ2].
  Proof.
    itr - e.
    ind ~ ind_bs_exp - e;
          itr;
          ato;
          smp.
    4: {
      smp - H.
      ivc - H.
      ufl - eraser_add_vars
            eraser_add_keys
            in *.
      rwr - (length_map_inl Var FunctionIdentifier) in *.
      rem - ks as Hks / Hks xs:
            (map inl xs : list Key).
      spc - IHe: ks1 (ks ++ ks2) (ks ++ ks3)
            (upn (base.length ks) ξ1)
            (upn (base.length ks) ξ2)
            H1.
      do 2 feq.
      psc - exp_eraser_subst_upn_comm as Heq:
            e ([] : list Key) ks1 ks ks2 ks3 ξ1 ξ2 IHe.
      smp - Heq.
      exa - Heq.
    }
    2: {
      smp - H.
      rem - k as Hk / Hk x:
            (inl x : Key).
      ivc - H as [Hmatch].
      feq.
      pse - eraser_app_either: k ks1 ks2.
      des - H as [H | [H | H]].
      - clr - Hmatch.
        des - H as [ks11 [ks12 [Hks1 [_ [_ [_ Hnotin]]]]]].
        cwr - Hks1 / ks1.
        smp *.
        repeat rwl - app_assoc.
        rwr - eraser_notin_skip_app; ato.
        rwr - (eraser_notin_skip_app k ks11); ato.
        rwr - cons_app.
        repeat rwl - app_assoc.
        do 3 rwl - cons_app.
        do 2 rwr - eraser_exact.
        rwr - Nat.add_0_r.
        rwr - upn_Var.
              2: rwr - length_app; smp; lia.
        rwr - upn_Var.
              2: rwr - length_app; smp; lia.
        rfl.
      - des - H as [ks [_ [_ [_ [_ [_ Hnotin]]]]]].
        apply not_in_app in Hnotin.
        des - Hnotin as [Hnotin _].
        rwr - eraser_notin_skip_app; ato.
        rwr - eraser_notin_skip_app; ato.
        (* Check upn_rem_var_reduction_full.
        rem - (ξ1 (apply_eraser ks2 k)) as x *)
        do 2 rewrite upn_rem_var_reduction_full in *.
        admit. (* 
    rem - x1 x2 as Hx1 Hx2:
      (ξ1 (apply_eraser ks2 (inl x)))
      (ξ2 (apply_eraser ks3 (inl x))).
    des - x1;
    des - x2.
    * ivs - H.
      admit.
    * ivs - H.
      sym - Hx1 Hx2.
      app - (upn_inl_eq_2 (base.length ks1)) in Hx1.
      app - (upn_from_inr_subst (base.length ks1)) in Hx2.
      rwl - Hx1. *)
  Admitted.














  Theorem exp_eraser_subst_add2 :
    forall e ks1 ks2 ks Γ,
      (*   upn (length ks2) ξ1
      = upn (length ks2) ξ2 *)
        (erase_exp (ks2 ++ ks ++ Γ.keys) e)
          .[upn (length (ks2 ++ ks))
                (list_subst (map erase_val Γ.vals) idsubst)]
      = (erase_exp (ks2 ++ ks ++ (Γ //ᵏ ks).keys) e)
          .[upn (length (ks2 ++ ks))
                (list_subst (map erase_val (Γ //ᵏ ks).vals) idsubst)]
    ->  (erase_exp (ks1 ++ ks2 ++ ks ++ Γ.keys) e)
          .[upn (length ks1)
           (upn (length (ks2 ++ ks))
                (list_subst (map erase_val Γ.vals) idsubst))]
      = (erase_exp (ks1 ++ ks2 ++ ks ++ (Γ //ᵏ ks).keys) e)
          .[upn (length ks1)
           (upn (length (ks2 ++ ks))
                (list_subst (map erase_val (Γ //ᵏ ks).vals) idsubst))].
  Proof.
    itr - e.
    ind ~ ind_bs_exp - e;
          itr;
          ato;
          smp.
    4: {
      smp - H.
      ivc - H.
      do 2 feq.
      ufl - eraser_add_vars
            eraser_add_keys
            in *.
      rwr - (length_map_inl Var FunctionIdentifier) in *.
      rem - ks0 as Hks / Hks xs:
            (map inl xs : list Key).
      spc - IHe: ks1 (ks0 ++ ks2) ks Γ.
      repeat rwl - app_assoc in *.
      do 2 rwr - upn_fun_app in H1.
      rwl - length_app in H1.
      spc - IHe: H1.
      Check exp_eraser_subst_upn_comm.
      (* Reorder app; nil_l, upn (length []) .. and is solveable*)
      (* add upn ks2 ++ ks to substs *)
      pse - exp_eraser_subst_upn_comm as Heq:
            e ([] : list Key) ks1 ks0
            (ks2 ++ ks ++ Γ.keys) (ks2 ++ ks ++ (Γ //ᵏ ks).keys)
            (list_subst (map erase_val Γ.vals) idsubst) 
            (list_subst (map erase_val (Γ //ᵏ ks).vals) idsubst).
      smp - Heq.
      admit.
     
    }
    2: {
      smp *.
      ivc - H.
      feq.
      rem - k as Hk / Hk x:
            (inl x : Key).
      (*
      Step New version of eraser_subst_env_rem_keys_eq this
      with app ks0 with not in rem_keys
      *)
      admit.
      }
  Admitted.
  
(*
Hx1 : inl v = ξ1 (apply_eraser ks2 (inl x))
n : nat
Hx2 : inr n = ξ2 (apply_eraser ks3 (inl x))
H : ˝ v = ˝ VVar n
*)
  (* Lemma subst_nat_var_eq :
    forall n x
    .
  
  Theorem exp_eraser_subst_add :
    forall e ks1 ks2 ks3 m ξ1 ξ2,
      (*   upn (length ks2) ξ1
      = upn (length ks2) ξ2 *)
        (erase_exp ks2 e).[upn m ξ1]
      = (erase_exp ks3 e).[upn m ξ2]
    ->  (erase_exp (ks1 ++ ks2) e).[upn (length ks1) (upn m ξ1)]
      = (erase_exp (ks1 ++ ks3) e).[upn (length ks1) (upn m ξ2)].
  Proof.
    itr - e.
    ind ~ ind_bs_exp - e;
          itr;
          ato;
          smp.
    (* EVar/EFunId *)
    2: {    smp - H.
            ass > ((apply_eraser (ks1 ++ ks2) (inl x)) < length ks1 \/ length ks1 <= (apply_eraser (ks1 ++ ks2) (inl x))): lia.
            des - H0.
            * erewrite upn_Var; ato.
              admit.
            * 
      
     app - vval_match_shift_sur in H. - (eraser_subst_add (inl x) ks1) in H.
    (* ECons/ESeq *)
    3 ,10:  bwr - IHe1 IHe2.
    (**)
    2: {  *)
    
    
    (* 
    
        upn m ξ1 (apply_eraser ks2 k)
      = upn m ξ2 (apply_eraser ks3 k)
    ->  upn (length ks1) (upn m ξ1) (apply_eraser (ks1 ++ ks2) k)
      = upn (length ks1) (upn m ξ2) (apply_eraser (ks1 ++ ks3) k).
      
       *)
      
      
      
      
      
      
      (* des - H3 as [_ Hnotin].
      Search not In app.
    * des - H as [ks11 [ks12 [Hks1 [Heq [Hlt [Hisin Hnotin]]]]]].
      sbt.
      do 2 rwl - app_assoc in *.
      cwr - Heq in *.
      erewrite upn_Var in *.
            2: do 2 rwr - length_app; sli.
   Check eraser_skip_notin_app.

  Theorem eraser_subst_add :
    forall k ks1 ks2 ks3 ks3' ξ1 ξ2,
        upn (length ks2) ξ1 (apply_eraser (ks2 ++ ks3) k)
      = upn (length ks2) ξ2 (apply_eraser (ks2 ++ ks3') k)
    ->  upn (length (ks1 ++ ks2)) ξ1 (apply_eraser (ks1 ++ ks2 ++ ks3) k)
      = upn (length (ks1 ++ ks2)) ξ2 (apply_eraser (ks1 ++ ks2 ++ ks3') k).
   Proof.
    itr.
    pse - upn_add: (length ks1) (length ks2) ξ1 ξ2 (apply_eraser (ks2 ++ ks3) k)
     (apply_eraser (ks2 ++ ks3') k).
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
        (apply_eraser ks2 k). *)



















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
    (* EFun *)
    2: {
      (* pse - eraser_subst_env_rem_keys_fun_eq: ks Γ. *)
      do 2 feq.
      ufl - eraser_add_vars
            eraser_add_keys
            in *.
      rwr - (length_map_inl Var FunctionIdentifier) in *.
      rem - ks0 as Hks / Hks xs:
            (map inl xs : list Key).
      spe - IHe: ks Γ.
      pse - exp_eraser_subst_add2: e ks0 ([] : list Key) ks Γ.
      smp - H.
      sym - IHe.
      spc - H: IHe.
      sym - H.
      exa - H.
    }
  Admitted.






End EraserSubstRemove_EraserSubstLemmas.