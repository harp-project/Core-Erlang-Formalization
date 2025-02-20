From CoreErlang.Eqvivalence.BsFs Require Export BX4Helpers.

Import BigStep.




Section ApplyEraserLemmas.



  Lemma apply_eraser_max :
    forall k ks,
      apply_eraser ks k <= length ks.
  Proof.
    itr.
    ind - ks as [| k1 ks IHks]:
          sli.
    smp.
    des > (k =ᵏ k1);
          sli.
  Qed.



  Lemma apply_eraser_destruct :
    forall k ks,
        apply_eraser ks k < length ks
    \/  apply_eraser ks k = length ks.
  Proof.
    itr.
    pse - apply_eraser_max: k ks.
    lia.
  Qed.



  Lemma apply_eraser_split :
    forall k ks,
        apply_eraser ks k < length ks
    ->  exists ks1 ks2,
            ks = ks1 ++ [k] ++ ks2
        /\  apply_eraser ks k = length ks1.
  Proof.
    itr.
    ind - ks as [| k1 ks IHks]:
          smp *; lia.
    smp - H.
    des > (k =ᵏ k1) as Hkey.
    * exi - ([] : list Key) ks.
      smp.
      rwr - Hkey.
      rwr - var_funid_eqb_eq in Hkey.
      cwl - Hkey / k1.
      ato.
    * app - PeanoNat.lt_S_n in H.
      spc - IHks: H.
      des - IHks as [ks1 [ks2 [Hks Hlen]]].
      exi - (k1 :: ks1) ks2.
      spl.  1: bwr - Hks.
      smp.
      bwr - Hkey Hlen.
  Qed.



  Lemma apply_eraser_cut :
    forall k ks1 ks2,
        apply_eraser (ks1 ++ ks2) k = base.length ks1
    ->  apply_eraser ks1 k = base.length ks1.
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



  Lemma apply_eraser_add :
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



  Lemma apply_eraser_In :
    forall k ks,
        apply_eraser ks k = length ks
    ->  not (In k ks).
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



  Lemma apply_eraser_In_app :
    forall k ks1 ks2,
        apply_eraser (ks1 ++ ks2) k = length ks1
    ->  not (In k ks1).
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



  Lemma apply_eraser_skip :
    forall k ks1 ks2,
        not (In k ks1)
    ->  apply_eraser (ks1 ++ ks2) k
      = length ks1 + apply_eraser ks2 k.
  Proof.
    itr.
    ind - ks1 as [| k1 ks1 IHks1]
          :> smp.
    Search In.
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



  Lemma apply_eraser_skip_all :
    forall k ks,
        not (In k ks)
    ->  apply_eraser ks k
      = length ks.
  Proof.
    itr.
    psc - apply_eraser_skip: k ks ([] : list Key) H.
    smp - H0.
    rwr - app_nil_r
          Nat.add_0_r
          in H0;
          trv.
  Qed.

(*
apply_eraser_In eq <->
*)

  Lemma apply_eraser_either :
    forall x k ks,
        x = (apply_eraser ks k)
    ->  (exists ks1 ks2,
            ks = ks1 ++ [k] ++ ks2
        /\  x = length ks1
        /\  not (In k ks1)
        /\  x < length ks)
    \/      (not (In k ks)
        /\  x = length ks).
  Proof.
    itr.
    sbt.
    pse - apply_eraser_destruct: k ks.
    des - H.
    * lft.
      pse - apply_eraser_split: k ks H.
      des - H0 as [ks1 [ks2 [Hks Hlen]]].
      exi - ks1 ks2.
      do 3 (spl; ato).
      sbt.
      clr - H.
      app - apply_eraser_In.
      bse - apply_eraser_cut: k ks1 ([k] ++ ks2) Hlen.
   * rgt.
     spl; ato.
     bpp - apply_eraser_In.
  Qed.



  Lemma apply_eraser_either_app :
    forall x k ks1 ks2,
        x = (apply_eraser (ks1 ++ ks2) k)
    ->  (exists ks11 ks12,
            ks1 = ks11 ++ [k] ++ ks12
        /\  x = length ks11
        /\  In k ks1
        /\  not (In k ks11)
        /\  x < length ks1)
    \/  (exists ks21 ks22,
            ks2 = ks21 ++ [k] ++ ks22
        /\  x = length (ks1 ++ ks21)
        /\  In k ks2
        /\  not (In k (ks1 ++ ks21))
        /\  x < length (ks1 ++ ks2))
    \/      (not (In k (ks1 ++ ks2))
        /\  x = length (ks1 ++ ks2)).
  Proof.
    itr.
    pse - apply_eraser_either: x k (ks1 ++ ks2) H.
    des - H0.
    2: {
      des - H0 as [HIn Hlen].
      rgt; rgt; ato.
    }
    des - H0 as [ks1' [ks2' [Hks [Hlen [HIn Hle]]]]].
    pse - length_lt_split_middle_app: Key ks1 ks2 ks1' ks2' k Hks.
    des - H0.
    * lft.
      des - H0 as [ks [Hks1 Hks2]].
      sbt.
      exi - ks1' ks.
      do 4 (try spl); ato.
      1: {
        rwr - in_app_iff.
        rgt.
        rwr - in_app_iff.
        lft.
        smp.
        ato.
      }
      do 2 rwl - app_assoc.
      rwr - apply_eraser_skip; ato.
      smp.
      rwr - var_funid_eqb_refl.
      rwr - Nat.add_0_r.
      rewrite length_app.
      sli.
    * rgt; lft.
      des - H0 as [ks [Hks1 Hks2]].
      sbt.
      exi - ks ks2'.
      do 4 (try spl); ato.
      rwr - in_app_iff.
      rgt.
      rwr - in_app_iff.
      lft.
      smp.
      ato.
  Qed.


End ApplyEraserLemmas.









Module EnvironmentCount.



  (* Fixpoint env_rem_key_in_count
      (k : Key)
      (Γ : Environment)
      : nat
      :=
    match Γ with
    | [] => 0
    | (k', v') :: Γ' =>
      (if k =ᵏ k'
        then 1
        else 0)
      + env_rem_key_in_count k Γ'
    end.





  Fixpoint env_rem_keys_in_count
      (ks : list Key)
      (Γ : Environment)
      : nat
      :=
    match ks with
    | [] => 0
    | k' :: ks' =>
      env_rem_key_in_count k' Γ
      + env_rem_keys_in_count ks' Γ
    end. *)

  (* Fixpoint key_in_count
      (k : Key)
      (ks : list Key)
      : nat
      :=
    match ks with
    | [] => 0
    | k' :: ks' =>
      (if k =ᵏ k'
        then 1
        else 0)
      + key_in_count k ks'
    end.



  Fixpoint keys_in_count_base
      (ks ksNotIn ksIn: list Key)
      : nat
      :=
    match ks with
    | [] => 0
    | k' :: ks' =>
      (if (Nat.eqb (key_in_count k' ksNotIn) 0)
        then key_in_count k' ksIn
        else 0)
      + keys_in_count_base ks' (k' :: ksNotIn) ksIn
    end.



  Definition keys_in_count
      (ks ksIn: list Key)
      : nat
      :=
    keys_in_count_base ks [] ksIn.



  Notation "k 'inᵏ' Γ " := (key_in_count k Γ.keys)
    (at level 1,
    format "k  inᵏ  Γ").

  Notation "ks 'inᵏˢ' Γ " := (keys_in_count ks Γ.keys)
    (at level 1,
    format "ks  inᵏˢ  Γ"). *)


End EnvironmentCount.

Export EnvironmentCount.









Section EnvironmentLemmas.



  Lemma env_rem_key_commutative :
    forall Γ k1 k2,
      Γ /ᵏ k1 /ᵏ k2
    = Γ /ᵏ k2 /ᵏ k1.
  Proof.
    itr.
    ind - Γ as [| [k v] Γ IHΓ]:
          smp.
    rwr - cons_app.
    do 4 rwr - env_rem_key_app.
    cwr - IHΓ.
    feq.
    smp.
    do 2 rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k1 =ᵏ k) as Hkey1;
    des > (k2 =ᵏ k) as Hkey2;
          smp;
          ato;
          rwr - app_nil_r;
          ufl - env_rem_key_one;
          smp.
    * bwr - Hkey1.
    * bwr - Hkey2.
    * bwr - Hkey1 Hkey2.
  Qed.



  Lemma env_rem_keys_commutative :
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



(*   Lemma env_rem_key_in_count_app :
    forall k Γ1 Γ2,
      k inᵏ (Γ1 ++ Γ2)
    = k inᵏ Γ1 + k inᵏ Γ2.
  Proof.
    itr.
    ind - Γ1 as [| [k1 v1] Γ1 IH]: sli.
  Qed.



  Lemma env_rem_keys_in_count_app :
    forall ks Γ1 Γ2,
      ks inᵏˢ (Γ1 ++ Γ2)
    = ks inᵏˢ Γ1 + ks inᵏˢ Γ2.
  Proof.
    itr.
    ind - ks as [| k ks IH]:
          smp.
    smp.
    (* ufl - keys_in_count in *.
    smp. *)
    rwr - env_rem_key_in_count_app IH.
    rem - n1 n2 ns1 ns2 as Hn1 Hn2 Hns1 Hns2
        / IH Hn1 Hn2 Hns1 Hns2 Γ1 Γ2 k ks:
          (k inᵏ Γ1)
          (k inᵏ Γ2)
          (ks inᵏˢ Γ1)
          (ks inᵏˢ Γ2).
    do 2 rwr - Nat.add_assoc.
    feq.
    do 2 rwl - Nat.add_assoc.
    feq.
    bwr - Nat.add_comm.
  Qed.



  Lemma env_rem_key_length_difference :
    forall Γ k,
      length (Γ /ᵏ k) + (k  inᵏ  Γ) = length Γ.
  Proof.
    itr.
    ind - Γ as [| [k1 v1] Γ IH]: sli.
    rwr - cons_app.
    rwr - env_rem_key_app.
    do 2 rwr - length_app.
    rwr - env_rem_key_in_count_app.
    rwl - Nat.add_assoc.
    rewrite Nat.add_comm with (m := k inᵏ Γ).
    rewrite Nat.add_assoc with (p := k inᵏ [(k1, v1)]).
    rewrite Nat.add_comm with (m := k inᵏ [(k1, v1)]).
    cwr - IH.
    rwr - Nat.add_assoc.
    feq.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k1); ato.
  Qed.



  Lemma env_rem_keys_length_difference :
    forall Γ ks,
      length (Γ //ᵏ ks) + (ks  inᵏˢ  Γ) = length Γ.
  Proof.
    itr.
    ind - ks as [| k1 ks IH]:
          sli.
    smp.
    rwl - IH.
    pse - env_rem_key_length_difference: (Γ //ᵏ ks) k1.
    rwl - H.
    rwl - Nat.add_assoc.
    rwr - Nat.add_comm.
    rewrite Nat.add_comm with (n := base.length Γ //ᵏ ks /ᵏ k1).
    do 2 feq.
  Admitted. *)


  Lemma env_rem_key_not_In_neq1 :
    forall Γ k k',
        k <> k'
    ->  not (In k (Γ /ᵏ k').keys)
    ->  not (In k Γ.keys).
  Proof.
    itr.
    ufl - get_keys in *.
    ind - Γ as [| [k1 v1] Γ IH]: sli.
    smp.
    ufl - not.
    itr.
    des - H1.
    * sbt.
      rwr - cons_app in H0.
      rwr - env_rem_key_app in H0.
      rwr - map_app in H0.
      rwr - in_app_iff in H0.
      smp - H0.
      rwr - app_nil_r in H0.
      ufl - env_rem_key_one in H0.
      apply not_eq_sym in H.
      rwl - var_funid_eqb_neq in H.
      smp - H0.
      rwr - H in H0.
      smp - H0.
      des - H0.
      lft; lft; rfl.
    * ufl - not in IH.
      app - IH; ato.
      itr.
      clr - IH.
      rwr - cons_app in H0.
      rwr - env_rem_key_app in H0.
      rwr - map_app in H0.
      rwr - in_app_iff in H0.
      smp - H0.
      rwr - app_nil_r in H0.
      ufl - env_rem_key_one in H0.
      smp - H0.
      des > (k' =ᵏ k1) as Hkey.
      - smp - H0.
        des - H0.
        rgt; ato.
      - smp - H0.
        des - H0.
        rgt; ato.
  Qed.
    



  Lemma env_rem_key_not_In_neq2 :
    forall Γ k k',
        k <> k'
    ->  not (In k Γ.keys)
    ->  not (In k (Γ /ᵏ k').keys).
  Proof.
    itr.
    ufl - get_keys in *.
    ind - Γ as [| [k1 v1] Γ IH]: sli.
    smp.
    ufl - not.
    itr.
    rwr - cons_app in H0.
    rwr - map_app in H0.
    rwr - in_app_iff in H0.
    smp - H0.
    rwr - map_app in H1.
    rwr - in_app_iff in H1.
    ufl - env_rem_key_one in H1.
    smp - H1.
    des > (k' =ᵏ k1) as Hkey.
    * smp - H1.
      des - H1; ato.
      ufl - not in IH.
      app - IH; ato.
    * smp - H1.
      des - H1; ato.
      ufl - not in IH.
      app - IH; ato.
  Qed.



  Lemma env_rem_key_not_In :
    forall Γ k,
      not (In k (Γ /ᵏ k).keys).
  Proof. 
    itr.
    ind - Γ as [| [k1 v1] Γ IHΓ]:
          sli.
    rwr - cons_app.
    rwr - env_rem_key_app.
    ufl - get_keys in *.
    rwr - map_app.
    rwr - in_app_iff.
    ufl - not.
    itr.
    des - H; ato.
    smp - H.
    rwr - app_nil_r in H.
    ufl - env_rem_key_one in H.
    smp - H.
    des > (k =ᵏ k1) as Hkey; ato.
    rwr - var_funid_eqb_neq in Hkey.
    smp - H.
    des - H; ato.
  Qed.



  Lemma env_rem_keys_not_In :
    forall Γ k ks,
        In k ks
    ->  not (In k (Γ //ᵏ ks).keys).
  Proof. 
    itr.
    ind - ks as [| k1 ks IHks]:
          ivs - H.
    Search In.
    rwr - cons_app in H.
    app - in_app_or in H.
    smp.
    smp - H.
    rem - x as Hx:
          (k1 =ᵏ k).
    sym - Hx.
    des - x.
    * rwr - var_funid_eqb_eq in Hx.
      sbt.
      app - env_rem_key_not_In.
    * rwr - var_funid_eqb_neq in Hx.
      des - H; ato.
      des - H; ato.
      spc - IHks: H.
      apply not_eq_sym in Hx.
      bpp - env_rem_key_not_In_neq2.
  Qed.


(*
HnotIn : ¬ In k ks
______________________________________(1/1)
apply_eraser (ks ++ (Γ1 ++ [(k, v)] ++ Γ2).keys) k = base.length (ks ++ Γ1.keys)
∧ apply_eraser (ks ++ (Γ1 //ᵏ ks ++ [(k, v)] //ᵏ ks ++ Γ2 //ᵏ ks).keys) k =
  base.length (ks ++ (Γ1 //ᵏ ks).keys)
*)

  Lemma env_rem_keys_single_notIn :
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
    
    

(*
(Γ //ᵏ ks).keys = ks1 ++ [k] ++ ks2
*)

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

(*¬ In k Γ.keys*)

  Lemma notIn_env_then_notIn_env_rem_keys :
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



  Lemma env_get_keys_split_middle_both :
    forall Γ ks1 k ks2,
        Γ.keys = ks1 ++ [k] ++ ks2
    ->  exists Γ1 Γ2 v,
            Γ = Γ1 ++ [(k, v)] ++ Γ2
        /\  Γ.vals = Γ1.vals ++ [v] ++ Γ2.vals
        /\  Γ1.keys = ks1
        /\  Γ2.keys = ks2
        /\  length Γ1.keys = length Γ1.vals
        /\  length Γ2.keys = length Γ2.vals.
  Proof.
    itr.
    ufl - get_keys
          get_vals.
    pse - list_app_fst_split_middle_both: Key Value Γ ks1 ks2 k H.
    des - H0 as [Γ1 [Γ2 [v [HΓ [Hvs [Hks1 [Hks2 [Hlen1 Hlen2]]]]]]]].
    exi - Γ1 Γ2 v.
    do 4 (try spl); ato.
    rwr - length_map_snd in Hlen1 Hlen2.
    rwl - Hks1 in Hlen1.
    rwl - Hks2 in Hlen2.
    sym - Hlen1 Hlen2.
    ato.
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
(* 
  Lemma env_get_keys_split_base :
    forall Γ ks1 ks2,
        Γ.keys = ks1 ++ ks2
    ->  exists Γ1 Γ2,
            Γ = Γ1 ++ Γ2
        /\  length Γ1 = length ks1
        /\  length Γ2 = length ks2.
  Proof.
    itr.
    exi - (take (length ks1) Γ)
          (drop (length ks1) Γ).
    epose proof take_drop (base.length ks1) Γ as Htake_drop.
    rwr - Htake_drop.
    spl; ato.
    ufl - get_keys in *.
    ass > (length Γ = length ks1 + length ks2) as Hlen:
          rwr - length_map_fst
                H
                length_app.
    epose proof length_firstn (base.length ks1) Γ as Hlen_take.
    epose proof length_skipn (base.length ks1) Γ as Hlen_drop.
    rwr - Hlen in Hlen_take Hlen_drop.
    erewrite Nat.min_l in Hlen_take.
          2: lia.
    rwr - Nat.add_comm
          Nat.add_sub
          in Hlen_drop.
    spl; ato.
  Qed.



  Lemma env_get_vals_split_base :
    forall Γ vs1 vs2,
        Γ.vals = vs1 ++ vs2
    ->  exists Γ1 Γ2,
            Γ = Γ1 ++ Γ2
        /\  length Γ1 = length vs1
        /\  length Γ2 = length vs2.
  Proof.
    itr.
    exi - (take (length vs1) Γ)
          (drop (length vs1) Γ).
    epose proof take_drop (base.length vs1) Γ as Htake_drop.
    rwr - Htake_drop.
    spl; ato.
    ufl - get_vals in *.
    ass > (length Γ = length vs1 + length vs2) as Hlen:
          rwr - length_map_snd
                H
                length_app.
    epose proof length_firstn (base.length vs1) Γ as Hlen_take.
    epose proof length_skipn (base.length vs1) Γ as Hlen_drop.
    rwr - Hlen in Hlen_take Hlen_drop.
    erewrite Nat.min_l in Hlen_take.
          2: lia.
    rwr - Nat.add_comm
          Nat.add_sub
          in Hlen_drop.
    spl; ato.
  Qed.



  Lemma env_get_keys_split :
    forall Γ ks1 ks2,
        Γ.keys = ks1 ++ ks2
    ->  exists Γ1 Γ2,
            Γ = Γ1 ++ Γ2
        /\  ks1 = Γ1.keys
        /\  ks2 = Γ2.keys.
   Proof.
    itr.
    pse - env_get_keys_split_base: Γ ks1 ks2 H.
    des - H0 as [Γ1 [Γ2 [Heq [Hlen1 Hlen2]]]].
    exi - Γ1 Γ2.
    spl; ato.
    ufl - get_keys in *.
    ass > (length Γ = length Γ1 + length Γ2) as Hlen:
          rwr - Heq
                length_app.
    rwr - length_map_fst in *.
    do 2 rwr - length_map_fst in Hlen.
    Search fst app.
    exi - (take (length ks1) Γ)
          (drop (length ks1) Γ).
    epose proof take_drop (base.length ks1) Γ.
    rwr - H0.
    spl; ato.
    ufl - get_keys in *.
    Search firstn.
    spl. 
    
    rwl - H0.
    Search take.

  Lemma env_get_keys_middle :
    forall Γ ks1 k ks2,
        Γ.keys = ks1 ++ [k] ++ ks2
    ->  exists Γ1 Γ2 v,
            Γ = Γ1 ++ [(k, v)] ++ Γ2
        /\  ks1 = Γ1.keys
        /\  ks2 = Γ2.keys.
  Proof.
    itr.
    Print drop.
    exi - (take (length ks1) Γ)
          (drop (1 + length ks1) Γ)
          (nth (length ks1) (map snd Γ) (VNil)).
    spl.
    * Search firstn.
      epose proof take_drop (base.length ks1) Γ. *)
    

(*   Lemma apply_eraser_env :
    forall x k ks Γ k',
        In k' ks
    ->  x = apply_eraser (ks ++ (Γ /ᵏ k').keys) k
    ->  x = 1.
  Proof.
    itr.
    pse - apply_eraser_either_app: x k ks (Γ /ᵏ k').keys H0.
    
  Admitted. *)
  Lemma apply_eraser_env_rem_keys_either :
    forall x k ks Γ,
          x = apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
    ->    (exists ks1 ks2,
              ks = ks1 ++ [k] ++ ks2
          /\  x = length ks1
          /\  apply_eraser ks1 k = length ks1
          /\  apply_eraser ks k = length ks1
          /\  apply_eraser (ks ++ Γ.keys) k = length ks1
          /\  x < length ks
          /\  apply_eraser (ks ++ Γ.keys) k < length ks
          /\  In k ks
          /\  not (In k ks1)
          /\  not (In k (Γ //ᵏ ks).keys))
      \/
          x = 1
      \/  x = 1.
  Proof.
    itr.
    pse - apply_eraser_either_app: x k ks (Γ //ᵏ ks).keys H.
    sbt.
    des - H0 as [H | [H | H]].
    * lft.
      des - H as [ks1 [ks2 [Hks [Heq [His_In [Hnot_In Hlen]]]]]].
      pse - env_rem_keys_not_In as Hnot_in2: Γ k ks His_In.
      rwr - Hks in Heq.
      do 2 rwl - app_assoc in Heq.
      pose proof apply_eraser_cut _ _ _ Heq as Heq1.
      pse - apply_eraser_add as Heq2: k ks1 ks2 Heq1.
      rwl - Hks in Heq2.
      pse - apply_eraser_add as Heq3: k ks1 (ks2 ++ Γ.keys) Heq1.
      do 2 rwr - app_assoc in Heq3.
      rewrite <- app_assoc with (n := ks2) in Heq3.
      rwl - Hks in Heq3.
      ass > (apply_eraser (ks ++ Γ.keys) k < length ks) as Hlen1.
      rwr - Heq3 Hks.
      rwr - length_app.
      sli.
      exi - ks1 ks2.
      sbt.
      do 5 (try spl); ato.
      do 2 rwl - app_assoc.
      ato.
    * rgt; lft.
      des - H as [ks1 [ks2 [Hks [Heq [His_In [Hnot_In Hlen]]]]]].
      admit.
    * 
      (*
        exists ks1 ks2,
            ks = ks1 ++ [k] ++ ks2
        /\  x = length ks1
        /\  apply_eraser ks1 l = length ks1
        /\  apply_eraser ks l = length ks1
        /\  apply_eraser (ks ++ Γ.keys) l = length ks1
        /\  x < length ks
        /\  apply_eraser (ks ++ Γ.keys) l < length ks
        /\  In k ks
        /\  not (In k ks1)
        /\  not (In k (Γ //ᵏ ks).keys)
      
      *)
  Admitted.

(*
Hx : x = apply_eraser (ks ++ (Γ //ᵏ ks).keys) k

      Hle1 : apply_eraser (ks ++ (Γ //ᵏ ks).keys) k < base.length ks
      Hle2 : apply_eraser (ks ++ Γ.keys) k < base.length ks
      Heq1 : apply_eraser (ks ++ (Γ //ᵏ ks).keys) k = base.length ks1
      Heq4 : apply_eraser (ks ++ Γ.keys) k = base.length ks1
*)


(*!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!*)
  Lemma apply_eraser_env_rem_either :
    forall k ks Γ,
             (apply_eraser (ks ++ Γ.keys) k
            = apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
        /\    apply_eraser (ks ++ Γ.keys) k
              < length ks
        /\    apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
              < length ks)
    \/       (exists Γ1 Γ2 v,
                    Γ = Γ1 ++ [(k, v)] ++ Γ2
              /\    apply_eraser (ks ++ Γ.keys) k
                  = length (ks ++ Γ1.keys)
              /\    apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
                  = length (ks ++ (Γ1 //ᵏ ks).keys)
              /\  ¬ In k ks)
    \/       (apply_eraser (ks ++ Γ.keys) k
            = length (ks ++ Γ.keys)
        /\    apply_eraser (ks ++ (Γ //ᵏ ks).keys) k
            = length (ks ++ (Γ //ᵏ ks).keys)).
  Proof.
    itr.
    rem - x as Hx:
          (apply_eraser (ks ++ Γ.keys) k).
    pse - apply_eraser_either_app: x k ks Γ.keys Hx.
    des - H as [H | [H | H]].
    * lft.
      des - H as [ks1 [ks2 [Hks [Heq [_ [_ _]]]]]].
      rwr - Hx Hks in Heq.
      do 2 rwl - app_assoc in Heq.
      pse - apply_eraser_cut as Hmin: k ks1 ([k] ++ ks2 ++ Γ.keys) Heq.
      pse - apply_eraser_add as Heq_rem: k ks1 (ks2 ++ (Γ //ᵏ ks).keys) Hmin.
      cwr - Hx Hks in *.
      repeat rwl - app_assoc in *. 
      cwr - Heq Heq_rem.
      do 2 rwr - length_app.
      smp.
      repeat (try spl);
            app - Nat.lt_add_pos_r;
            lia.
    * rgt; lft.
      des - H as [ks1 [ks2 [Hks [Heq [_ [_ _]]]]]].
      pse - env_get_keys_app_split_middle: Γ ks1 k ks2 Hks.
      des - H as [Γ1 [Γ2 [v [HΓ [Hks1 _]]]]].
      exi - Γ1 Γ2 v.
      spl; ato.
      cwr - Hx in *.
      cwr - Hks in Heq.
      pse - apply_eraser_In_app as HnotIn: k (ks ++ ks1) ([k] ++ ks2).
      rwl - app_assoc in HnotIn.
      spc - HnotIn: Heq.
      epose proof not_in_app ks ks1 k HnotIn as HnotIn_app.
      des - HnotIn_app as [Hnot_ks HnotIn_Γ1].
      cwl - Hks1 in *.
      cwr - HΓ.
      do 2 rwr - env_rem_keys_app_l.
      ufl - get_keys in *.
      repeat rwr - map_app.
      erewrite env_rem_keys_single_notIn; ato.
      psc -  notIn_env_then_notIn_env_rem_keys as HnotIn_Γ1rem:
             Γ1 k ks HnotIn_Γ1.
      epose proof app_not_in
              k ks (Γ1 //ᵏ ks).keys Hnot_ks HnotIn_Γ1rem
              as HnotIn_rem;
              clr - HnotIn_Γ1rem.
      do 2 (try spl); ato.
      - clr - Hnot_ks HnotIn_rem.
        psc - apply_eraser_skip:
              k (ks ++ map fst Γ1)
              (map fst [(k, v)] ++ map fst Γ2)
              HnotIn.
        repeat rwl - app_assoc in H.
        setoid_rewrite H.
        smp.
        rwr - var_funid_eqb_refl.
        bwr - Nat.add_0_r.
     -  clr - Hnot_ks HnotIn.
        psc - apply_eraser_skip:
              k (ks ++ map fst Γ1 //ᵏ ks)
              (map fst [(k, v)] ++ map fst Γ2 //ᵏ ks)
              HnotIn_rem.
        repeat rwl - app_assoc in H.
        setoid_rewrite H.
        smp.
        rwr - var_funid_eqb_refl.
        bwr - Nat.add_0_r.
    * rgt; rgt.
      des - H as [_ Heq].
      cwr - Hx / x.
      spl; ato.
      pse - apply_eraser_In as HnotIn: k (ks ++ Γ.keys) Heq.
      clr - Heq.
      apply not_in_app in HnotIn.
      des - HnotIn as [HnotIn_ks HnotIn_Γ].
      psc - notIn_env_then_notIn_env_rem_keys as HnotIn_Γrem:
            Γ k ks HnotIn_Γ.
      epose proof app_not_in
          k ks (Γ //ᵏ ks).keys
          HnotIn_ks HnotIn_Γrem
          as HnotIn;
          clr - HnotIn_ks HnotIn_Γrem.
      psc - apply_eraser_skip_all as Heq2:
          k (ks ++ (Γ //ᵏ ks).keys) HnotIn.
      exa - Heq2.
  Qed.



End EnvironmentLemmas.


(*

  upn (length ks)
      (list_subst
        ((Γ //ᵏ ks).vals)
        idsubst)
      (apply_eraser
        (ks ++ (Γ //ᵏ ks).keys)
        x)
= upn (length ks)
      (list_subst
        (Γ.vals)
        idsubst)
      (apply_eraser
        (ks ++ Γ.keys)
        x)

!3 OPTION :
* In x ks
* not (In x ks) /\ In x (Γ //ᵏ ks) /\ In x Γ
* not (In x ks) /\ not In x (Γ //ᵏ ks) /\ not (In x Γ)


#1:
*  ks = ks1 ++ [x] ++ ks2
*  apply_eraser_cut
*  (apply_eraser
        (ks ++ (Γ //ᵏ ks).keys)
        x)
 = (apply_eraser
        (ks ++ Γ.keys)
        x)
 = X
* X < length ks
* upn_lesser (upn_Var) ( x < m -> upn m ξ x = inr x)
* Both equal :)

#2:
* vs = vs1 ++ [v] ++ vs2
* ? 


#3
* ? m + length vs = x -> upn m (list_subst vs idsubst) = inr m ?
* if this true, than its true 

*)

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



  Lemma inr_upn_from_subst:
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



  (*Not Using*)
  Lemma upn_subst_skip_all :
    forall m x,
      m = x
  ->  upn m idsubst x = inr m.
  Proof.
    itr.
    ivc - H.
    ass > (idsubst 0 = inr 0): ato.
    psc - inr_upn_from_subst: x 0 idsubst 0 H.
    smp - H0.
    trv.
  Qed.



(*
length ks + length Γ.vals = x
length ks + length Γ.vals = x
*)

  (*!!!!*)
  Lemma upn_list_subst_skip_all :
    forall m vs x,
      m + length vs = x
  ->  upn m (list_subst vs idsubst) x = inr m.
  Proof.
    itr.
    ass > (length vs = x - m): lia.
    app - list_subst_skip_all in H0.
    pse - inr_upn_from_subst: m (x - m) (list_subst vs idsubst) 0 H0.
    smp - H1.
    erewrite Nat.sub_add in H1.
          2: lia.
    exa - H1.
  Qed.


  (*!!!!*)
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



  Theorem eraser_subst_rem_keys :
    forall ks Γ k,
        upn (length ks)
          (list_subst
            (map erase_val (Γ //ᵏ ks).vals)
            idsubst)
          (apply_eraser
            (ks ++ (Γ //ᵏ ks).keys)
            k)
        = upn (length ks)
          (list_subst
            (map erase_val Γ.vals)
            idsubst)
          (apply_eraser
            (ks ++ Γ.keys)
            k).
  Proof.
    itr.
    pse - apply_eraser_env_rem_either: k ks Γ.
    des - H as [H | [H | H]].
    * des - H as [Heq [Hle1 Hle2]].
      eapply upn_Var in Hle1.
      eapply upn_Var in Hle2.
      cwr - Hle1 Hle2.
      bwr - Heq.
    * des - H as [Γ1 [Γ2 [v [HΓ [Heq1 [Heq2 HnotIn]]]]]].
      cwr - HΓ in *.
      (*list_fst_eq*)
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
      erewrite env_rem_keys_single_notIn in *; ato.
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
    