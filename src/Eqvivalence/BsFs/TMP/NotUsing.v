From CoreErlang.Eqvivalence.BsFs Require Export BX4Helpers.










(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_SUBST_REMOVE ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import SubstSemantics.






Section EraseSubstRemove_UprennLemmas.



   Theorem uprenn_inj :
    forall n n1 n2,
        (uprenn n S) n1 = (uprenn n S) n2
    ->  n1 = n2.
  Proof.
    itr - n.
    ind - n as [| n IHn];
          itr;
          ivc - H;
          trv.
    des - n1 as [| n1];
          des - n2 as [| n2];
          ivc - H1;
          trv.
    spc - IHn: n1 n2 H0.
    bvs - IHn.
  Qed.






  Lemma uprenn_app :
    forall n1 n2,
      uprenn n1 (uprenn n2 S)
    = uprenn (n1 + n2) S.
  Proof.
    itr.
    ind - n1 as [| n1 IHn1]
          :- smp
          |> smp.
    feq.
    exa - IHn1.
  Qed.



  Lemma uprenn_app_ext :
    forall n1 n2 (os : Ext),
      map
        (fun '(id, n, e) =>
          (id,
          n,
          rename (uprenn (n1 + n) (upren (uprenn n2 S))) e))
        os
    = map
        (fun '(id, n, e) =>
          (id,
          n,
          rename (uprenn (n1 + n2 + 1 + n) S) e))
        os.
  Proof.
    itr.
    app - map_ext.
    itr.
    des - a as [[id n] e].
    do 2 feq.
    rwr - upren_S.
    rwl - Nat.add_1_r.
    rewrite <- Nat.add_assoc with (n := n1 + n2).
    rewrite Nat.add_comm with (n := 1) (m := n).
    rewrite <- Nat.add_assoc with (p := n + 1).
    rewrite Nat.add_comm with (n := n2).
    do 2 rwr - Nat.add_assoc.
    app - uprenn_app.
  Qed.



  Lemma uprenn_app_ext_noid :
    forall n1 n2 (os : ExtNoId),
      map
        (fun '(n, e) =>
          (n,
          rename (uprenn (n1 + n) (uprenn n2 S)) e))
        os
    = map
      (fun '(n, e) =>
        (n,
        rename (uprenn (n1 + n2 + n) S) e))
      os.
  Proof.
    itr.
    app - map_ext.
    itr.
    des - a as [n e].
    do 2 feq.
    rwl - Nat.add_assoc.
    rewrite Nat.add_comm with (n := n2).
    rwr - Nat.add_assoc.
    app - uprenn_app.
  Qed.



  Lemma uprenn_app_case :
    forall n us,
      map
        (fun '(ps, ᵍe, ᵇe) =>
          (ps,
          rename (uprenn (PatListScope ps) (uprenn n S)) ᵍe,
          rename (uprenn (PatListScope ps) (uprenn n S)) ᵇe))
        us
    = map
      (fun '(ps, ᵍe, ᵇe) =>
        (ps,
        rename (uprenn (PatListScope ps + n) S) ᵍe,
        rename (uprenn (PatListScope ps + n) S) ᵇe))
      us.
  Proof.
    itr.
    app - map_ext.
    itr.
    des - a as [[ps ᵍe] ᵇe].
    do 2 feq.
    1: feq.
    1-2: app - uprenn_app.
  Qed.



End EraseSubstRemove_UprennLemmas.









Section EraseSubstRemove_ExpValLemmas.


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

  Lemma eexp_eq :
    forall e₁ e₂,
        e₁ = e₂
    <-> ° e₁ = ° e₂.
  Proof.
    itr.
    spl; itr.
    * feq; asm.
    * bvs - H.
  Qed.



  Lemma rename_vval :
    forall n v,
        ˝ renameVal (uprenn n S) v = rename (uprenn n S) (˝ v).
  Proof.
    trv.
  Qed.

  Lemma rename_eexp :
    forall n e,
        ° renameNonVal (uprenn n S) e = rename (uprenn n S) (° e).
  Proof.
    trv.
  Qed.



  Lemma rename_vval_eq :
    forall n v₁ v₂,
        renameVal (uprenn n S) v₁ = renameVal (uprenn n S) v₂
    <-> rename (uprenn n S) (˝ v₁) = rename (uprenn n S) (˝ v₂).
  Proof.
    itr.
    spl; itr.
    * smp; feq; asm.
    * smp - H; ivs - H; rfl.
  Qed.

  Lemma rename_eexp_eq :
    forall n e₁ e₂,
        renameNonVal (uprenn n S) e₁ = renameNonVal (uprenn n S) e₂
    <-> rename (uprenn n S) (° e₁) = rename (uprenn n S) (° e₂).
  Proof.
    itr.
    spl; itr.
    * smp; feq; asm.
    * smp - H; ivs - H; rfl.
  Qed.



End EraseSubstRemove_ExpValLemmas.









Section EraseSubstRemove_RenamingInjectiveTheorems.



  Lemma renameVal_inj_helper_single :
    forall n v₁ v₂,
        (forall e n,
            rename (uprenn n S) (˝ v₁)
          = rename (uprenn n S) e
        ->  ˝ v₁ = e)
    ->  renameVal (uprenn n S) v₁
      = renameVal (uprenn n S) v₂
    ->  v₁ = v₂.
  Proof.
    itr - n v₁ v₂ IHv Hv.
    spe - IHv: (˝ v₂).
    smp - IHv.
    rwr - vval_eq in Hv.
    spc - IHv : n Hv.
    bwr - vval_eq.
  Qed.



  Lemma renameVal_inj_helper_list :
    forall n vs₁ vs₂,
        Forall
          (fun v₁ =>
            forall e n,
                rename (uprenn n S) (˝ v₁)
              = rename (uprenn n S) e
            ->  ˝ v₁ = e)
          vs₁
    ->  map (fun v => renameVal (uprenn n S) v) vs₁
      = map (fun v => renameVal (uprenn n S) v) vs₂
    ->  vs₁ = vs₂.
  Proof.
    itr - n vs₁ vs₂ HForall Hvs.
    revert vs₂ Hvs.
    ind - vs₁ as [| v₁ vs₁ IHvs];
          itr;
          destruct vs₂ as [| v₂ vs₂];
          (con + ivs - Hvs);
          ivs - HForall.
    feq.
    * bpp - renameVal_inj_helper_single in H0.
    * bpp - IHvs.
  Qed.



  Lemma renameVal_inj_helper_map :
    forall n vvs₁ vvs₂,
        Forall
          (fun vv₁ =>
              (forall e n,
                  rename (uprenn n S) (˝ vv₁.1)
                = rename (uprenn n S) e
              ->  ˝ vv₁.1 = e)
            /\
              (forall e n,
                  rename (uprenn n S) (˝ vv₁.2)
                = rename (uprenn n S) e
              ->  ˝ vv₁.2 = e))
          vvs₁
    ->  map (fun '(ᵏv, ᵛv) => (renameVal (uprenn n S) ᵏv,
                               renameVal (uprenn n S) ᵛv))
            vvs₁
      = map (fun '(ᵏv, ᵛv) => (renameVal (uprenn n S) ᵏv,
                               renameVal (uprenn n S) ᵛv))
             vvs₂
    ->  vvs₁ = vvs₂.
  Proof.
    itr - n vvs₁ vvs₂ HForall Hvvs.
    revert vvs₂ Hvvs.
    ind - vvs₁ as [| [ᵏv₁ ᵛv₁] vvs₁ IHvvs];
          itr;
          destruct vvs₂ as [| [ᵏv₂ ᵛv₂] vvs₂];
          (con + ivs - Hvvs);
          ivs - HForall;
          des - H4;
          smp *.
    do 2 feq.
    * bpp - renameVal_inj_helper_single in H0.
    * bpp - renameVal_inj_helper_single in H1.
    * bpp - IHvvs.
  Qed.






  Lemma rename_inj_helper_single :
    forall n e₁ e₂,
        (forall e n,
            rename (uprenn n S) e₁ = rename (uprenn n S) e
        ->  e₁ = e)
    ->  rename (uprenn n S) e₁ = rename (uprenn n S) e₂
    ->  e₁ = e₂.
  Proof.
    itr - n e₁ e₂ IHe He.
    bpe - IHe: e₂ n He.
  Qed.



  Lemma rename_inj_helper_list :
    forall n es₁ es₂,
        Forall
          (fun e₁ =>
            forall e n,
                rename (uprenn n S) e₁
              = rename (uprenn n S) e
            ->  e₁ = e)
          es₁
    ->  map (fun e => rename (uprenn n S) e) es₁
      = map (fun e => rename (uprenn n S) e) es₂
    ->  es₁ = es₂.
  Proof.
    itr - n es₁ es₂ HForall Hes.
    revert es₂ Hes.
    ind - es₁ as [| e₁ es₁ IHes];
          itr;
          destruct es₂ as [| e₂ es₂];
          (con + ivs - Hes);
          ivs - HForall.
    feq.
    * bpp - rename_inj_helper_single in H0.
    * bpp - IHes.
  Qed.



  Lemma rename_inj_helper_map :
    forall n ees₁ ees₂,
        Forall
          (fun ee₁ =>
              (forall e n,
                  rename (uprenn n S) ee₁.1
                = rename (uprenn n S) e
              ->  ee₁.1 = e)
            /\
              (forall e n,
                  rename (uprenn n S) ee₁.2
                = rename (uprenn n S) e
              ->  ee₁.2 = e))
          ees₁
    ->  map (fun '(ᵏe, ᵛe) => (rename (uprenn n S) ᵏe,
                               rename (uprenn n S) ᵛe))
            ees₁
      = map (fun '(ᵏe, ᵛe) => (rename (uprenn n S) ᵏe,
                               rename (uprenn n S) ᵛe))
             ees₂
    ->  ees₁ = ees₂.
  Proof.
    itr - n ees₁ ees₂ HForall Hees.
    revert ees₂ Hees.
    ind - ees₁ as [| [ᵏe₁ ᵛe₁] ees₁ IHees];
          itr;
          destruct ees₂ as [| [ᵏe₂ ᵛe₂] ees₂];
          (con + ivs - Hees);
          ivs - HForall;
          des - H4;
          smp *.
    do 2 feq.
    * bpp - rename_inj_helper_single in H0.
    * bpp - rename_inj_helper_single in H1.
    * bpp - IHees.
  Qed.



  Lemma rename_inj_helper_ext :
    forall n (os₁ os₂ : Ext),
        Forall
          (fun idne₁ =>
            forall e n,
                rename (uprenn n S) idne₁.2
              = rename (uprenn n S) e
            ->  idne₁.2 = e)
          os₁
    ->  map (fun '(id, n', e) => (id, n', rename (uprenn (n + n') S) e)) os₁
      = map (fun '(id, n', e) => (id, n', rename (uprenn (n + n') S) e)) os₂
    ->  os₁ = os₂.
  Proof.
    itr - n os₁ os₂ HForall Hos.
    revert os₂ Hos.
    ind - os₁ as [| [[id₁ n₁] e₁] os₁ IHos];
          itr;
          destruct os₂ as [| [[id₂ n₂] e₂] os₂];
          (con + ivs - Hos);
          ivs - HForall.
    do 2 feq.
    * clr + H1 H2.
      smp - H1.
      bpe - H1: e₂ (n + n₂) H2.
    * bpp - IHos.
  Qed.



  Lemma rename_inj_helper_ext_noid :
    forall n os₁ os₂,
        Forall
          (fun ne₁ =>
            forall e n,
                rename (uprenn n S) ne₁.2
              = rename (uprenn n S) e
            ->  ne₁.2 = e)
          os₁
    ->  map (fun '(n', e) => (n', rename (uprenn (n + n') S) e)) os₁
      = map (fun '(n', e) => (n', rename (uprenn (n + n') S) e)) os₂
    ->  os₁ = os₂.
  Proof.
    itr - n os₁ os₂ HForall Hos.
    revert os₂ Hos.
    ind - os₁ as [| [n₁ e₁] os₁ IHos];
          itr;
          destruct os₂ as [| [n₂ e₂] os₂];
          (con + ivs - Hos);
          ivs - HForall.
    do 2 feq.
    * clr + H1 H3.
      smp - H3.
      bpe - H3: e₂ (n + n₂) H1.
    * bpp - IHos.
  Qed.



  Lemma rename_inj_helper_case :
    forall n us₁ us₂,
        Forall
          (fun psee₁ =>
              (forall e n,
                  rename (uprenn n S) psee₁.1.2
                = rename (uprenn n S) e
              ->  psee₁.1.2 = e)
            /\
              (forall e n,
                  rename (uprenn n S) psee₁.2
                = rename (uprenn n S) e
              ->  psee₁.2 = e))
          us₁
    ->  map
          (fun '(ps, ᵍe, ᵇe) =>
            (ps,
            rename (uprenn (PatListScope ps + n) S) ᵍe,
            rename (uprenn (PatListScope ps + n) S) ᵇe))
          us₁
      = map
          (fun '(ps, ᵍe, ᵇe) =>
            (ps,
            rename (uprenn (PatListScope ps + n) S) ᵍe,
            rename (uprenn (PatListScope ps + n) S) ᵇe))
          us₂
    ->  us₁ = us₂.
  Proof.
    itr - n us₁ us₂ HForall Hus.
    revert us₂ Hus.
    ind - us₁ as [| [[ps₁ ᵍe₁] ᵇe₁] us₁ IHus];
          itr;
          destruct us₂ as [| [[ps₂ ᵍe₂] ᵇe₂] us₂];
          (con + ivs - Hus);
          ivs - HForall;
          des - H4.
    do 3 feq.
    * clr + H1 H.
      smp - H.
      bpe - H: ᵍe₂ (PatListScope ps₂ + n) H1.
    * clr + H2 H0.
      smp - H0.
      bpe - H0: ᵇe₂ (PatListScope ps₂ + n) H2.
    * bpp - IHus.
  Qed.









  Theorem rename_inj : 
    forall n e1 e2,
        rename (uprenn n S) e1 = rename (uprenn n S) e2
    -> e1 = e2.
  Proof.
    itr - n e1 e2 HR.
    gen - n e2.
    ind ~ ind_fs_exp - e1;
          itr; des - e2; des - e;
          try (smp - HR; ivs - HR; ato);
          try (des - f; ivs - HR);
          try (des - n0; ivs - HR);
          try (des - n1; ivs - HR);
          clr - HR;
          auto.
    (* ### VAL ### *)
    (* VVar *)
    17-18:     by do 2 feq;
                  app - uprenn_inj in H0.
    (* VFunId *)
    17-18:     by do 3 feq;
                  app - uprenn_inj in H2.
    (* VCons *)
    17:        by do 2 feq;
                  app - renameVal_inj_helper_single in H0;
                  app - renameVal_inj_helper_single in H1.
    (* VTuple *)
    19:        by do 3 feq;
                  app - renameVal_inj_helper_list in H1.
    (* VMap *)
    19:        by do 3 feq;
                  app - renameVal_inj_helper_map in H1.
    (* VClos *)
    17-18:     by do 2 feq;
                  ivs - H1;
                  app - length_eq_map in H1;
                  rwl - H1 in *;
                  try (rwr - uprenn_app in H4);
                  try (do 2 rwr - uprenn_app_ext in H2);
                  app - rename_inj_helper_ext in H2;
                  app - rename_inj_helper_single in H4.
    (* ### EXP ### *)
    (* EFun *)
    2-3:       by do 2 feq;
                  rwr - uprenn_app in H1;
                  app - rename_inj_helper_single in H1.
    (* ECons/ESeq *)
    2, 11:     by do 2 feq;
                  app - rename_inj_helper_single in H0;
                  app - rename_inj_helper_single in H1.
    (* ELet *)
    9:         by do 2 feq;
                  rwr - uprenn_app in H2;
                  app - rename_inj_helper_single in H1;
                  app - rename_inj_helper_single in H2.
    (* ETry *)
    11:        by do 2 feq;
                  rwr - uprenn_app in H2 H4;
                  app - rename_inj_helper_single in H0;
                  app - rename_inj_helper_single in H2;
                  app - rename_inj_helper_single in H4.
    (* ETuple *)
    1-2, 5-6:  by do 2 feq;
                  app - rename_inj_helper_list in H1.
    (* EMap *)
    6:         by do 3 feq;
                  app - rename_inj_helper_map in H1.
    (* EApp *)
    3:         by do 2 feq;
                  app - rename_inj_helper_single in H1;
                  app - rename_inj_helper_list in H2.
    (* ECall *)
    1-2:       by do 2 feq;
                  (rwr - rename_vval in H5 +
                   rwr - rename_eexp in H5);
                  app - rename_inj_helper_single in H4;
                  app - rename_inj_helper_single in H5;
                  app - rename_inj_helper_list in H6.
    (* ELetRec *)
    2:         by do 2 feq;
                  ivs - H1;
                  app - length_eq_map in H1;
                  rwl - H1 in *;
                  rwr - uprenn_app in H2;
                  do 2 rwr - uprenn_app_ext_noid in H3;
                  app - rename_inj_helper_ext_noid in H3;
                  app - rename_inj_helper_single in H2.
    1:         by do 2 feq;
                  do 2 rwr - uprenn_app_case in H2;
                  app - rename_inj_helper_single in H1;
                  app - rename_inj_helper_case in H2.
  Qed.









  Theorem renameVal_inj : 
    forall n v1 v2,
        renameVal (uprenn n S) v1 = renameVal (uprenn n S) v2
    -> v1 = v2.
  Proof.
    itr.
    rwr - rename_vval_eq in H.
    app - rename_inj in H.
    rwl - vval_eq in H;
          trv.
  Qed.



  Theorem renameNonVal_inj : 
    forall n e1 e2,
        renameNonVal (uprenn n S) e1 = renameNonVal (uprenn n S) e2
    -> e1 = e2.
  Proof.
    itr.
    rwr - rename_eexp_eq in H.
    app - rename_inj in H.
    rwl - eexp_eq in H;
          trv.
  Qed.





  Theorem rename_inj_S : 
    forall e1 e2,
        rename S e1 = rename S e2
    -> e1 = e2.
  Proof.
    itr.
    pse - rename_inj: 0 e1 e2.
    smp *.
    bse - H0: H.
  Qed.



  Theorem renameVal_inj_S : 
    forall v1 v2,
        renameVal S v1 = renameVal S v2
    -> v1 = v2.
  Proof.
    itr.
    pse - renameVal_inj: 0 v1 v2.
    smp *.
    bse - H0: H.
  Qed.



  Theorem renameNonVal_inj_S : 
    forall e1 e2,
        renameNonVal S e1 = renameNonVal S e2
    -> e1 = e2.
  Proof.
    itr.
    pse - renameNonVal_inj: 0 e1 e2.
    smp *.
    bse - H0: H.
  Qed.



End EraseSubstRemove_RenamingInjectiveTheorems.









Section EraseSubstRemove_ShiftInjectiveTheorems.



  Theorem shift_injective :
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
    bpp - renameVal_inj_S in H1.
  Qed.



  Theorem shift_surjective :
    forall ξ1 ξ2 n1 n2,
      ξ1 n1 = ξ2 n2 ->
      shift ξ1 n1 = shift ξ2 n2.
  Proof.
    intros ξ1 ξ2 n1 n2 H.
    ufl - shift.
    bwr - H.
  Qed.



  Theorem shift_bijective :
    forall ξ1 ξ2 n1 n2,
        shift ξ1 n1 = shift ξ2 n2
    <-> ξ1 n1 = ξ2 n2.
  Proof.
    itr.
    spl.
    bpp - shift_injective.
    bpp - shift_surjective.
  Qed.






  Theorem match_shift_injective :
    forall ξ1 ξ2 n1 n2,
        match shift ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = match shift ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end
    ->  match ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = match ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr.
    rem - x1 x2 as Hx1 Hx2:
          (shift ξ1 n1)
          (shift ξ2 n2).
    des - x1;
    des - x2;
          ivc - H.
    1, 4: cwr - Hx2 in Hx1;
          app - shift_injective in Hx1;
          bwr - Hx1.
    1, 2: rem - y1 y2 as Hy1 Hy2:
                (ξ1 n1)
                (ξ2 n2);
          des - y1;
                des - y2;
                ufl - shift in *;
                rwl - Hy1 in Hx1;
                rwl - Hy2 in Hx2;
                try con;
          ivc - Hx1 Hx2;
          des - v;
                smp *; 
                try des - n;
                con.
  Qed.



  Theorem match_shift_surjective :
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



  Theorem match_shift_bijective :
    forall ξ1 ξ2 n1 n2,
        match shift ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = match shift ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end
    <-> match ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = match ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr.
    spl.
    app - match_shift_injective.
    app - match_shift_surjective.
  Qed.






  Theorem vval_match_shift_injective :
    forall ξ1 ξ2 n1 n2,
        ˝ match shift ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = ˝ match shift ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end
    ->  ˝ match ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = ˝ match ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr.
    rwl - vval_eq in *.
    bpp - match_shift_injective.
  Qed.



  Theorem vval_match_shift_surjective :
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
    bpp - match_shift_surjective.
  Qed.



  Theorem vval_match_shift_bijective :
    forall ξ1 ξ2 n1 n2,
        ˝ match shift ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = ˝ match shift ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end
    <-> ˝ match ξ1 n1 with
        | inl exp => exp
        | inr num => VVar num
        end
      = ˝ match ξ2 n2 with
        | inl exp => exp
        | inr num => VVar num
        end.
  Proof.
    itr.
    spl.
    app - vval_match_shift_injective.
    app - vval_match_shift_surjective.
  Qed.



End EraseSubstRemove_ShiftInjectiveTheorems.









Section EraseSubstRemove_NotUsing.



  Definition injective
      {A B}
      (f : A -> B)
      :=
    forall x1 x2,
        f x1 = f x2
     -> x1 = x2.



  Theorem map_injective :
    forall (A B : Type) (f : A -> B) (l1 l2 : list A),
        injective f
    ->  map f l1 = map f l2
    ->  l1 = l2.
  Proof.
    itr - A B f l1 l2 H_inj H_map.
    revert l2 H_map.
    ind - l1 as [| x1 l1 IHl];
          itr;
          des - l2 as [| x2 l2]
                :- smp - H_map; con
                |> smp - H_map;
                   ivs - H_map;
                   feq;
                   ato.
  Qed.



  Lemma vval_inj :
    forall v₁ v₂,
        VVal v₁ = VVal v₂
    ->  v₁ = v₂.
  Proof.
    itr.
    bvs - H.
  Qed.

  Lemma eexp_inj :
    forall e₁ e₂,
        EExp e₁ = EExp e₂
    ->  e₁ = e₂.
  Proof.
    itr.
    bvs - H.
  Qed.



  Lemma map_rename_vval_eq :
    forall vs₁ vs₂,
          map (fun v => renameVal S v) vs₁
        = map (fun v => renameVal S v) vs₂
    <->   map (fun v => rename S (˝v)) vs₁
        = map (fun v => rename S (˝v)) vs₂.
  Proof.
    itr.
    spl; itr.
    * smp.
      rewrite <- map_map with (l := vs₁).
      rewrite <- map_map with (l := vs₂).
      feq. asm.
    * smp - H.
      rewrite <- map_map with (l := vs₁) in H.
      rewrite <- map_map with (l := vs₂) in H.
      by epose proof map_injective Val Exp VVal
            (map (renameVal S) vs₁) (map (renameVal S) vs₂) vval_inj H.
  Qed.



  Lemma map_rename_eexp_eq :
    forall es₁ es₂,
          map (fun e => renameNonVal S e) es₁
        = map (fun e => renameNonVal S e) es₂
    <->   map (fun e => rename S (°e)) es₁
        = map (fun e => rename S (°e)) es₂.
  Proof.
    itr.
    spl; itr.
    * smp.
      rewrite <- map_map with (l := es₁).
      rewrite <- map_map with (l := es₂).
      feq. asm.
    * smp - H.
      rewrite <- map_map with (l := es₁) in H.
      rewrite <- map_map with (l := es₂) in H.
      by epose proof map_injective NonVal Exp EExp
            (map (renameNonVal S) es₁) (map (renameNonVal S) es₂) eexp_inj H.
  Qed.






  Theorem shift_val_not_num :
    forall ξ n,
        (exists v, ξ n = inl v)
    ->  (exists v, shift ξ n = inl v).
  Proof.
    itr.
    des - H as [v H].
    exi - (renameVal S v).
    ufl - shift.
    bwr - H.
  Qed.



End EraseSubstRemove_NotUsing.




(*
upn (base.length ks' + 1) (list_subst (map erase_val (Γ /ᵏ k).vals) ξ)
      (apply_eraser (ks' ᵏ++ (k :: (Γ /ᵏ k).keys ᵏ++ σ)) (inl x))
*)

Section EraseSubstRemove_EraseLemmas.



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



(*   Lemma apply_eraser_skip :
    forall k ks ks1 ks2,
        ks = ks1 ++ [k] ++ ks2
    ->  apply_eraser ks k = base.length ks1
    ->  apply_eraser ks k = apply_eraser (ks1 ++ [k]) k.
  Proof.
    itr.
    cwr - H / ks.
    smp *.
    ind - ks1 as [| k1 ks1 IHks1];
          smp *.
    * pse - var_funid_eqb_refl: k.
      cwr - H in *.
      trv.
    * des > (k =ᵏ k1) as Hkey:
          con.
      app - Nat.succ_inj in H0.
      spc - IHks1: H0.
      bwr - IHks1.
  Qed. *)



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



(*   Lemma apply_eraser_either :
    forall x k ks,
        x = (apply_eraser ks k)
    ->  (x < length ks
        ->  exists ks1 ks2,
                ks = ks1 ++ [k] ++ ks2
            /\  x = length ks1
            /\  not (In k ks1))
     /\ (x = length ks
        -> not (In k ks)).
  Proof.
    itr.
    spl; itr; sbt.
    * ind - ks as [| k1 ks IHks].
      - smp *. lia.
      - smp *.
        des > (k =ᵏ k1) as Hkey.
        + rwr - var_funid_eqb_eq in Hkey.
          cwl - Hkey / k1.
          exi - ([] : list Key) ks.
          smp.
          ato.
        + rwr - var_funid_eqb_neq in Hkey.
          app - PeanoNat.lt_S_n in H0.
          spc - IHks: H0.
          des - IHks as [ks1 [ks2 [Hks [Hlen HIn]]]].
          exi - (k1 :: ks1) ks2.
          spl.  1: bwr - Hks.
          spl.  1:  rwr - Hlen; sli.
          clr + HIn Hkey.
          rwr - cons_app.
          apply app_not_in.
          2: exa - HIn.
          ufl - not.
          smp; itr.
          des - H; ato.
    * ind - ks as [| k1 ks IHks]:
            ato.
      smp *.
      des > (k =ᵏ k1) as Hkey:
            con.
      rwr - var_funid_eqb_neq in Hkey.
      app - Nat.succ_inj in H0.
      spc - IHks: H0.
      ufl - not.
      itr.
      des - H; ato.
  Qed. *)


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



End EraseSubstRemove_EraseLemmas.









Section EraseSubstRemove_SubstLemmas.



  Lemma subst_destruct :
    forall x (ξ : Substitution),
        (exists v, ξ x = inl v)
    \/  (exists n, ξ x = inr n).
  Proof.
    itr.
    des > (ξ x).
    * lft.
      exi - v.
      trv.
    * rgt.
      exi - n.
      trv.
  Qed.

(*
upn_inl_eq_1:
  ∀ (n x : nat) (v : Val) (ξ : Substitution),
    upn n ξ x = inl v → ξ (x - n) = inl (renameVal (λ m : nat, m - n) v)
upn_inl_eq_2:
  ∀ (n x : nat) (v : Val) (ξ : nat → Val + nat),
    ξ x = inl v → upn n ξ (x + n) = inl (renameVal (λ m : nat, m + n) v)
up_subst_S: ∀ (n : nat) (ρ : Substitution), upn n (up_subst ρ) = upn (S n) ρ
up_get_inr:
  ∀ (ξ : nat → Val + nat) (x y : nat), ξ x = inr y → up_subst ξ (S x) = inr (S y)
up_get_inl:
  ∀ (ξ : nat → Val + nat) (x : nat) (y : Val),
    ξ x = inl y → up_subst ξ (S x) = inl (renameVal S y)
upn_Var
     : ∀ (Γ : nat) (ξ : Substitution) (v : nat), v < Γ → upn Γ ξ v = inr v
*)

Search uprenn.

(*   Lemma uprenn_S :
    forall m,
      (fun n => n + m)
    = match m with
      | 0 => id
      | S m' => uprenn m S
      end.
  Proof.
    itr.
    ind - m.
    * unfold id.
      apply functional_extensionality.
      ato.
    * 
    * smp. *)
(* #DEFINED
  Lemma upn_inl_eq_1 :
    forall n x ξ,
        upn n ξ x = inl v
    ->  ξ (x - n) = inl (renameVal (λ m : nat, m - n) v).
*)

(* Lemma subst_from_up_inl :
  forall x v ξ y,
      up_subst (v .: ξ) (S x) = y
  ->  ξ x = y.
Proof.
  itr.
  smp *.
  ufl - shift in H.

up_get_inr:
  ∀ (ξ : nat → Val + nat) (x y : nat), ξ x = inr y → up_subst ξ (S x) = inr (S y) *)


  Lemma upn_lesser :
    forall m x ξ,
        x < m
    ->  upn m ξ x = inr x.
  Proof.
    itr.
    bpp - upn_Var.
  Qed.

(*
upn m (v .: list_subst vs2 ξ1) m = upn m (v .: ξ2) m
*)

  (* Lemma upn_skip :
    forall m v ξ,
      upn m (v .: ξ) m = inl v.
  Proof.
    itr.
    ind - m as [| m IHm]:
          smp.
    smp *.
    ufl - shift.
    rwr - IHm.
    des > (ξ 0). *)


  Lemma upn_destruct :
    forall m (ξ : Substitution) x,
        (m <= x /\ exists v,  upn m ξ x = inl v)
    \/  (m <= x /\ exists n, upn m ξ x = inr n)
    \/  (x < m  /\ upn m ξ x = inr x).
  Proof.
    itr.
    ass > (m <= x \/ x < m):
          lia.
    des - H.
    * pse - subst_destruct: x (upn m ξ).
      des - H0;
            ato.
    * do 2 rgt.
      spl; trv.
      bpp - upn_lesser.
  Qed.



  Lemma inl_upn_to_subst :
    forall m x ξ v,
        upn m ξ x = inl v
    ->  ξ (x - m) = inl (renameVal (fun n => n - m) v).
  Proof.
    itr.
    bpp - upn_inl_eq_1.
  Qed.

  Lemma inl_upn_from_subst :
    forall m x ξ v,
        ξ x = inl v
    ->  upn m ξ (x + m) = inl (renameVal (fun n => n + m) v).
  Proof.
    itr.
    bpp - upn_inl_eq_2.
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
    ufl - shift.
    bwr - IH.
  Qed.

(* #DEFINED
  Lemma upn_inl_eq_2 :
    forall n x ξ,
        ξ x = inl v
    ->  upn n ξ (x + n) = inl (renameVal (λ m : nat, m + n) v).
*)







  Lemma list_subst_split :
    forall x vs ξ,
        x < length vs
    ->  exists vs1 v vs2,
            list_subst vs ξ x = inl v
        /\  vs = vs1 ++ [v] ++ vs2
        /\  x = length vs1.
  Proof.
    itr.
    gen - x.
    ind - vs as [| v1 vs IHvs]:
          smp *;
          lia.
    itr.
    smp *.
    des - x;
          smp - H.
    * exi - ([] : list Val) v1 vs.
      ato.
    * app - PeanoNat.lt_S_n in H.
      spc - IHvs: x H.
      des - IHvs as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
      exi - (v1 :: vs1) v vs2.
      sbt.
      spl; ato.
  Qed.



  Lemma list_subst_cut :
    forall vs1 v vs2 ξ1 ξ2,
      list_subst (vs1 ++ [v] ++ vs2) ξ1 (length vs1)
    = list_subst (vs1 ++ [v]) ξ2 (length vs1).
  Proof.
    itr.
    rwr - app_assoc.
    rwl - list_subst_app.
    ind - vs1 as [| v1 vs1 IHvs1]
          :- smp.
  Qed.



  Lemma list_subst_skip :
    forall x vs ξ,
        x < length vs
    ->  exists vs1 vs2,
            vs = vs1 ++ vs2
        /\  list_subst vs  ξ x
          = list_subst vs2 ξ 0.
  Proof.
    itr.
    gen - x.
    ind - vs as [| v1 vs IHvs]:
          smp *;
          lia.
    itr.
    smp *.
    des - x;
          smp + H.
    * exi - ([] : list Val) (v1 :: vs).
      ato.
    * app - PeanoNat.lt_S_n in H.
      spc - IHvs: x H.
      des - IHvs as [vs1 [vs2 [Hvs Hlen]]].
      exi - (v1 :: vs1) vs2.
      sbt.
      spl; ato.
  Qed.



  Lemma list_subst_skip_full :
    forall x vs ξ,
        length vs <= x
    ->  list_subst vs  ξ x
      = ξ (x - length vs).
  Proof.
    itr.
    gen - x.
    ind - vs as [| v1 vs IHvs];
          itr;
          smp.
    bwr - Nat.sub_0_r.
    des - x;
          smp + H.
    lia.
    app - le_S_n in H.
    bpe - IHvs: x H.
  Qed.



  Lemma list_subst_either :
    forall x vs ξ,
        (exists vs1 v vs2,
            x < length vs
        /\  list_subst vs ξ x = inl v
        /\  vs = vs1 ++ [v] ++ vs2
        /\  x = length vs1)
    \/  (exists v,
            length vs <= x
        /\  list_subst vs ξ x = inl v)
    \/  (exists n,
            length vs <= x
        /\  list_subst vs ξ x = inr n).
  Proof.
    itr.
    ass > (x < length vs \/ length vs <= x):
          lia.
    des - H.
    * lft.
      pse - list_subst_split: x vs ξ H.
      des - H0 as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
      exi - vs1 v vs2.
      ato.
    * rgt.
      pse - subst_destruct: x (list_subst vs ξ).
      des - H0 as [[v H0] | [n H0]].
      - lft.
        exi - v.
        ato.
      - rgt.
        exi - n.
        ato.
  Qed.




(* TO BASICS *)
  Lemma add_sub_refl :
    forall n m, n = n + m - m.
  Proof.
    itr.
    ind - m.
    bwr - Nat.sub_0_r
          Nat.add_0_r.
    rwl - Nat.sub_succ
          Nat.add_succ_r
          in IHm.
    trv.
  Qed.

  Lemma sub_add_refl :
    forall n m,
        m <= n
    ->  n = n - m + m.
  Proof.
    itr.
    ind - m.
    bwr - Nat.sub_0_r
          Nat.add_0_r.
    rwl - Nat.sub_succ in IHm.
    rwl - Nat.add_succ_comm.
    Search (S _ - _).
    erewrite <- Nat.sub_succ_l; ato.
    app - IHm.
    lia.
  Qed.

  Lemma add_sub_eq :
    forall n m p,
        p <= n
    ->  n = m + p
    <-> n - p = m.
  Proof.
    itr.
    spl; itr.
    * rwr - H0.
      sym.
      app - add_sub_refl.
    * rwl - H0.
      bpp - sub_add_refl.
  Qed.
  (* Lemma list_subst_subst_inl_from :
    forall vs ξ x v,
      list_subst vs ξ x = inl v
  
    forall m x ξ v,
        upn m ξ x = inl v
    ->  ξ (x - m) = inl (renameVal (fun n => n - m) v).
  Proof.
    itr.
    bpp - upn_inl_eq_1.
  Qed. *)

  (* Lemma inl_list_to_subst_lesser :
    forall vs x ξ v,
        x < length vs
    ->  list_subst vs ξ x = inl v
    ->  
    forall m x ξ v,
        upn m ξ x = inl v
    ->  ξ (x - m) = inl (renameVal (fun n => n - m) v).
  Proof.
    itr.
    bpp - upn_inl_eq_1.
  Qed. *)
  Lemma list_to_subst:
    forall vs x ξ,
        length vs <= x
    ->  list_subst vs ξ x = ξ (x - length vs).
  Proof.
    itr.
    bpp - list_subst_skip_full.
  Qed.

  Lemma list_from_subst:
    forall vs x ξ,
        length vs <= x
    ->  ξ x = list_subst vs ξ (x + length vs).
  Proof.
    itr.
    pse - add_sub_refl: x (length vs).
    rem - tmp as Htmp:
      (list_subst vs ξ (x + base.length vs)).
    cwr - H0 Htmp.
    ass > (base.length vs ≤ x + base.length vs): lia.
    rem - y as Hy:
      (x + base.length vs).
    sym.
    bpp - list_to_subst.
  Qed.


  Lemma inl_upn_to_list :
    forall m vs x ξ v,
        upn m (list_subst vs ξ) x = inl v
    ->  (list_subst vs ξ) (x - m) = inl (renameVal (fun n => n - m) v).
  Proof.
    itr.
    bpp - inl_upn_to_subst.
  Qed.

  Lemma inl_upn_from_list :
    forall m vs x ξ v,
        (list_subst vs ξ) x = inl v
    ->  upn m (list_subst vs ξ) (x + m) = inl (renameVal (fun n => n + m) v).
  Proof.
    itr.
    bpp - inl_upn_from_subst.
  Qed.

  Lemma inr_upn_from_list:
    forall m vs x ξ n,
        (list_subst vs ξ) x = inr n
    ->  upn m (list_subst vs ξ) (x + m) = inr (n + m).
  Proof.
    itr.
    bpp - inr_upn_from_subst.
  Qed.

  Lemma inr_upnlist_from_subst:
    forall m vs x ξ n,
        length vs <= x
    ->  ξ x = inr n
    ->  upn m (list_subst vs ξ) (x + length vs + m) = inr (n + m).
  Proof.
    itr.
    pse - list_from_subst: vs x ξ H.
    cwr - H1 in H0.
    bpp - inr_upn_from_list.
  Qed.







  Lemma upn_list_subst_split :
    forall m x vs ξ,
        m <= x
    ->  x < length vs + m
    ->  exists vs1 v vs2,
            upn m (list_subst vs ξ) x = inl (renameVal (fun n => n + m) v)
        /\  vs = vs1 ++ [v] ++ vs2
        /\  x = length vs1 + m.
  Proof.
    itr.
    ass > (x - m < length vs): lia.
    psc - list_subst_split: (x - m) vs ξ H1.
    des - H2 as [vs1 [v [vs2 [Hsubst [Hvs Hlen]]]]].
    pse - inl_upn_from_list: m vs (x - m) ξ v Hsubst.
    pse - sub_add_refl: x m H.
    cwl - H2 in H1.
    rwl - add_sub_eq in Hlen; ato.
    exi - vs1 v vs2.
    ato.
  Qed.



  (* Lemma upn_list_subst_cut :
    forall m vs1 v vs2 ξ1 ξ2,
      upn m (list_subst (vs1 ++ [v] ++ vs2) ξ1) (length vs1 + m)
    = upn m (list_subst (vs1 ++ [v]) ξ2) (length vs1 + m).
  Proof.
    itr.
    rwr - app_assoc.
    rwl - list_subst_app.
    ind - vs1 as [| v1 vs1 IHvs1].
    * smp.
      
  Qed. *)

(*
H : base.length vs + m ≤ x
______________________________________(1/1)
upn m (list_subst vs ξ) x = ξ (x - base.length vs)
*)
  (* Lemma upn_list_subst_skip :
    forall m x vs ξ (ξ1 : Substitution) x1,
       length vs + m ≤ x
    -> upn m (list_subst vs ξ) x = ξ1 x1.
  Proof.
    itr.
    ass > (length vs <= x - m): lia.
    pse - list_to_subst: vs (x - m) ξ H0.
    pse - list_from_subst: vs (x - m) ξ H0.
    des > (ξ1 x1).
    * pse - inl_upn_from_list. *)

  Lemma upn_list_subst_either :
    forall m x vs ξ,
        (x < m /\ upn m (list_subst vs ξ) x = inr x)
    \/  (m <= x
         /\ x < length vs + m
         /\ (exists vs1 v vs2,
            upn m (list_subst vs ξ) x = inl (renameVal (fun n => n + m) v)
        /\  vs = vs1 ++ [v] ++ vs2
        /\  x = length vs1 + m))
    \/  (length vs + m <= x).
  Proof.
    itr.
    ass > (x < m
          \/ (m <= x /\ x < length vs + m)
          \/ length vs + m <= x):
          lia.
    des - H as [H | [[H1 H2] | H]].
    * lft.
      spl; ato.
      bpp - upn_lesser.
    * rgt; lft.
      do 2 (try spl; ato).
      bpp - upn_list_subst_split.
    * rgt; rgt.
      ato.
  Qed.



Section EraseSubstRemove_EraseSubstLemmas.


Check apply_eraser_either.
Check list_subst_either.
Check upn_list_subst_either.
(*
∀ (x : nat) (k : Key) (ks : Eraser),
         x = apply_eraser ks k
         → (∃ ks1 ks2 : list Key,
              ks = ks1 ++ [k] ++ ks2
              ∧ x = base.length ks1 ∧ ¬ In k ks1 ∧ x < base.length ks)
           ∨ ¬ In k ks ∧ x = base.length ks


∀ (x : nat) (vs : list Val) (ξ : Substitution),
         (∃ (vs1 : list Val) (v : Val) (vs2 : list Val),
            x < base.length vs
            ∧ list_subst vs ξ x = inl v
              ∧ vs = vs1 ++ [v] ++ vs2 ∧ x = base.length vs1)
         ∨ (∃ v : Val, base.length vs ≤ x ∧ list_subst vs ξ x = inl v)
           ∨ ∃ n : nat, base.length vs ≤ x ∧ list_subst vs ξ x = inr n


∀ (m x : nat) (vs : list Val) (ξ : Substitution),
         x < m ∧ upn m (list_subst vs ξ) x = inr x
         ∨ m ≤ x
           ∧ x < base.length vs + m
             ∧ (∃ (vs1 : list Val) (v : Val) (vs2 : list Val),
                  upn m (list_subst vs ξ) x = inl (renameVal (λ n : nat, n + m) v)
                  ∧ vs = vs1 ++ [v] ++ vs2 ∧ x = base.length vs1 + m)
           ∨ base.length vs + m ≤ x
*)

(*
(list_subst (vs1' ++ Γ.vals ++ vs2') idsubst)
(apply_eraser (ks1' ++ Γ.keys ++ ks2') k)


upn (length ks0')
(list_subst (vs1' ++ Γ.vals ++ vs2') idsubst)
(apply_eraser (ks0' ++ ks1' ++ Γ.keys ++ ks2') k)



upn (length ks0')
(list_subst (vs1' ++ [k1, v1].vals ++ vs2') idsubst)
(apply_eraser (ks0' ++ ks1' ++ [k1, v1].keys ++ ks2') k)



upn (length ks0')
(list_subst (vs1' ++ [k1, v1].vals ++ vs2') idsubst)
(apply_eraser (ks0' ++ ks1' ++ [k1, v1].keys ++ ks2') k)
= 
upn (length ks0')
(list_subst (vs1' ++ ([k1, v1] - k).vals ++ vs2') idsubst)
(apply_eraser (ks0' ++ ks1' ++ ([k1, v1] - k).keys ++ ks2') k)
*)
Import BigStep.


Lemma eraser_subst_env_remove_key_one :
  forall k1 v1 k x,
    upn (length [k])
        (list_subst
          ((map erase_val ([(k1, v1)] /ᵏ k).vals))
          idsubst)
        (apply_eraser
          ([k] ++ ([(k1, v1)] /ᵏ k).keys)
          x)
  = upn (length [k])
        (list_subst
          ((map erase_val [(k1, v1)].vals))
          idsubst)
        (apply_eraser
          ([k] ++ [(k1, v1)].keys)
          x).
Proof.
  itr.
  smp.
  rwr - app_nil_r.
  ufl - env_rem_key_one.
  smp.
  des > (x =ᵏ k) as Heq_k.
  * rwr - var_funid_eqb_eq in Heq_k.
    cwl - Heq_k / k.
    bmp.
  * smp.
    des > (k =ᵏ k1) as Heq_k1.
    - ufl - get_vals.
      smp.
      rwr - var_funid_eqb_eq in Heq_k1.
      rwr - var_funid_eqb_neq in Heq_k.
      rwr - Heq_k1 in Heq_k.
      rwl - var_funid_eqb_neq in Heq_k.
      rwr - Heq_k.
      bbn.
    - bmp.
Qed.



Lemma eraser_subst_env_remove_key :
  forall Γ k x,
    upn (length [k])
        (list_subst
          ((map erase_val (Γ /ᵏ k).vals))
          idsubst)
        (apply_eraser
          ([k] ++ (Γ /ᵏ k).keys)
          x)
  = upn (length [k])
        (list_subst
          ((map erase_val Γ.vals))
          idsubst)
        (apply_eraser
          ([k] ++ Γ.keys)
          x).
Proof.
  itr.
  rem - Ks1 Ks2 as HKs1 HKs2:
    ([k] ++ (Γ /ᵏ k).keys)
    ([k] ++ Γ.keys).
  rem - X1 X2 as HX1 HX2:
    (apply_eraser Ks1 x)
    (apply_eraser Ks2 x).
  pse - apply_eraser_either as Heither2: X2 x Ks2 HX2.
  des - Heither2 as [HIn_true | HIn_false].
  (* 2: { des 
  smp.
  smp.
  rwr - var_funid_eqb_refl.
  des > (k =ᵏ k1) as Heq_k.
  * ufl - get_vals.
    bmp.
  * bmp.
Qed. *)
  Admitted.




(* Lemma eraser_subst_env_remove_one :
  forall k1 v1 k ks0' ks1' ks2' vs1' vs2',
    upn (length ks0')
        (list_subst
          (vs1' ++ (map erase_val ([(k1, v1)] /ᵏ k).vals) ++ vs2')
          idsubst)
        (apply_eraser
          (ks0' ++ ks1' ++ ([(k1, v1)] /ᵏ k).keys ++ ks2')
          k)
  = upn (length ks0')
        (list_subst
          (vs1' ++ (map erase_val [(k1, v1)].vals) ++ vs2')
          idsubst)
        (apply_eraser
          (ks0' ++ ks1' ++ [(k1, v1)].keys ++ ks2')
          k).
Proof.
  itr.
  rem - Ks1 Ks2 as HKs1 HKs2:
    (ks0' ++ ks1' ++ ([(k1, v1)] /ᵏ k).keys ++ ks2')
    (ks0' ++ ks1' ++ [(k1, v1)].keys ++ ks2')
  rem  - x1 x2 as Hx1 Hx2:
    (apply_eraser (ks0' ++ ks1' ++ ([(k1, v1)] /ᵏ k).keys ++ ks2') k)
    (apply_eraser (ks0' ++ ks1' ++ [(k1, v1)].keys ++ ks2') k).
  pse - apply_eraser_either. x1 k 
  smp.
  rwr - app_nil_r.
  ufl - env_rem_key_one.
  smp.
  des > (k =ᵏ k1) as Heq_k.
  * rwr - var_funid_eqb_eq in Heq_k.
    cwl - Heq_k / k1.
    smp.
    des - k as [x' | f']
          :- smp.
    des > ((x =? x')%string)
            :- smp.
  * rwr - var_funid_eqb_neq in Heq_k.
    smp.
    des - k as [x' | f'];
          des - k₁ as [x₁ | f₁]
                :- smp. *)




(*
itr.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁) as Heq_k.
    * rwr - var_funid_eqb_eq in Heq_k.
      cwl - Heq_k / k₁.
      smp.
      des - k as [x' | f']
            :- smp.
      des > ((x =? x')%string)
              :- smp.
    * rwr - var_funid_eqb_neq in Heq_k.
      smp.
      des - k as [x' | f'];
            des - k₁ as [x₁ | f₁]
                  :- smp.
*)
    



(*itr.
    revert k ks' σ ξ.
    ind - Γ as [| [k₁ v₁] Γ IHΓ]
          :> itr; smp.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁).
    * smp.
    
    * smp.
    ind - ks as [| k' ks' IHks].
    * do 2  rwr -
            eraser_add_keys_nil_l.
      simpl base.length.
      rwr - Nat.add_0_l.
      app - evar_add_keys_erase_subst_rem_key_single.
    * rwr - cons_app.
      do 2  rwr -
            eraser_add_keys_app_l.
      smp.
      des - k' as [x' | f'].
      - des > ((x =? x')%string)
              :- smp.
        smp + IHks.
        rwr - app_nil_r in *.
        bpp - vval_match_shift_surjective.
      - smp + IHks.
        rwr - app_nil_r in *.
        bpp - vval_match_shift_surjective.*)




  (* Lemma eraser_list_subst_either :
    length ks < length vs
  
    forall x vs ξ,
        (exists vs1 v vs2,
            x < length vs
        /\  list_subst vs ξ x = inl v
        /\  vs = vs1 ++ [v] ++ vs2
        /\  x = length vs1)
    \/  (exists v,
            length vs <= x
        /\  list_subst vs ξ x = inl v)
    \/  (exists n,
            length vs <= x
        /\  list_subst vs ξ x = inr n). *)

End EraseSubstRemove_EraseSubstLemmas.



















































(*   Lemma upn_inr_eq_2 :
    forall ξ x y n,
        ξ x = inr y
    ->  upn n ξ (x + n) = inr (y + n).
  Proof.
    itr.
    rwr - Nat.add_comm.
    rewrite Nat.add_comm with (n := y).
    ind - n as [| n IHn]:
          smp.
    smp.
    ufl - shift.
    bwr - IHn.
  Qed.

(*
upn_inl_eq_1:
  ∀ (n x : nat) (v : Val) (ξ : Substitution),
    upn n ξ x = inl v → ξ (x - n) = inl (renameVal (λ m : nat, m - n) v)
upn_inl_eq_2:
  ∀ (n x : nat) (v : Val) (ξ : nat → Val + nat),
    ξ x = inl v → upn n ξ (x + n) = inl (renameVal (λ m : nat, m + n) v)
up_subst_S: ∀ (n : nat) (ρ : Substitution), upn n (up_subst ρ) = upn (S n) ρ
*)

  Lemma upn_subst_destruct :
    forall n (ξ : Substitution) m,
        (m <= n /\ exists v,  upn m ξ n = inl v)
    \/  (m <= n /\ exists n', upn m ξ n = inr n')
    \/  (n < m  /\ upn m ξ n = inr n).
  Proof.
    itr.
    ass > (m <= n \/ n < m):
          lia.
    des - H.
    * pse - subst_destruct: n (upn m ξ).
      des - H0;
            ato.
    * do 2 rgt.
      spl; trv.
      bpp - upn_Var.
  Qed.



  Lemma list_subst_idsubst_split :
    forall n vs v,
        list_subst vs idsubst n = inl v
    ->  exists vs1 vs2,
            vs = vs1 ++ [v] ++ vs2
        /\  n = length vs1.
  Proof.
    itr.
    gen - n.
    ind - vs as [| v1 vs IHvs];
          itr;
          smp - H.
    * ufl - idsubst in H.
      con.
    * des - n;
            smp - H.
      - ivs - H.
        exi - ([] : list Val) vs.
        ato.
      - spc - IHvs: n H.
        des - IHvs as [vs1 [vs2 [Hvs Hlen]]].
        exi - (v1 :: vs1) vs2.
        sbt.
        spl; ato.
  Qed.



(*   Lemma list_subst_split :
    forall n vs ξ v,
        n < length vs
    ->  list_subst vs ξ n = inl v
    ->  exists vs1 vs2,
            vs = vs1 ++ [v] ++ vs2
        /\  n = length vs1.
  Proof.
    itr.
    gen - n.
    ind - vs as [| v1 vs IHvs]:
          smp *;
          lia.
    itr.
    smp *.
    des - n;
          smp - H0.
    * ivs - H0.
      exi - ([] : list Val) vs.
      ato.
    * app - PeanoNat.lt_S_n in H.
      spc - IHvs: n H H0.
      des - IHvs as [vs1 [vs2 [Hvs Hlen]]].
      exi - (v1 :: vs1) vs2.
      sbt.
      spl; ato.
  Qed. *)



  Lemma list_subst_split :
    forall n vs ξ,
        n < length vs
    ->  exists vs1 v vs2,
            list_subst vs ξ n = inl v
        /\  vs = vs1 ++ [v] ++ vs2
        /\  n = length vs1.
  Proof.
    itr.
    gen - n.
    ind - vs as [| v1 vs IHvs]:
          smp *;
          lia.
    itr.
    smp *.
    des - n;
          smp - H.
    * exi - ([] : list Val) v1 vs.
      ato.
    * app - PeanoNat.lt_S_n in H.
      spc - IHvs: n H.
      des - IHvs as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
      exi - (v1 :: vs1) v vs2.
      sbt.
      spl; ato.
  Qed.



  Lemma list_subst_cut :
    forall vs1 v vs2 ξ1 ξ2,
      list_subst (vs1 ++ [v] ++ vs2) ξ1 (length vs1)
    = list_subst (vs1 ++ [v]) ξ2 (length vs1).
  Proof.
    itr.
    rwr - app_assoc.
    rwl - list_subst_app.
    ind - vs1 as [| v1 vs1 IHvs1]
          :- smp.
  Qed.



  Lemma list_subst_skip :
    forall n vs ξ,
        n < length vs
    ->  exists vs1 vs2,
            vs = vs1 ++ vs2
        /\  list_subst vs  ξ n
          = list_subst vs2 ξ 0.
  Proof.
    itr.
    gen - n.
    ind - vs as [| v1 vs IHvs]:
          smp *;
          lia.
    itr.
    smp *.
    des - n;
          smp + H.
    * exi - ([] : list Val) (v1 :: vs).
      ato.
    * app - PeanoNat.lt_S_n in H.
      spc - IHvs: n H.
      des - IHvs as [vs1 [vs2 [Hvs Hlen]]].
      exi - (v1 :: vs1) vs2.
      sbt.
      spl; ato.
  Qed.



  Lemma list_subst_skip_full :
    forall n vs ξ,
        length vs <= n
    ->  list_subst vs  ξ n
      = ξ (n - length vs).
  Proof.
    itr.
    gen - n.
    ind - vs as [| v1 vs IHvs];
          itr;
          smp.
    bwr - Nat.sub_0_r.
    des - n;
          smp + H.
    lia.
    app - le_S_n in H.
    bpe - IHvs: n H.
  Qed.



  Lemma list_subst_destruct :
    forall n vs ξ,
        (exists vs1 v vs2,
            n < length vs
        /\  list_subst vs ξ n = inl v
        /\  vs = vs1 ++ [v] ++ vs2
        /\  n = length vs1)
    \/  (exists v,
            length vs <= n
        /\  list_subst vs ξ n = inl v)
    \/  (exists n',
            length vs <= n
        /\  list_subst vs ξ n = inr n').
  Proof.
    itr.
    ass > (n < length vs \/ length vs <= n):
          lia.
    des - H.
    * lft.
      pse - list_subst_split: n vs ξ H.
      des - H0 as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
      exi - vs1 v vs2.
      ato.
    * rgt.
      pse - subst_destruct: n (list_subst vs ξ).
      des - H0 as [[v H0] | [n' H0]].
      - lft.
        exi - v.
        ato.
      - rgt.
        exi - n'.
        ato.
  Qed.

(*
upn_inl_eq_1:
  ∀ (n x : nat) (v : Val) (ξ : Substitution),
    upn n ξ x = inl v → ξ (x - n) = inl (renameVal (λ m : nat, m - n) v)
upn_inl_eq_2:
  ∀ (n x : nat) (v : Val) (ξ : nat → Val + nat),
    ξ x = inl v → upn n ξ (x + n) = inl (renameVal (λ m : nat, m + n) v)
up_subst_S: ∀ (n : nat) (ρ : Substitution), upn n (up_subst ρ) = upn (S n) ρ
up_get_inr:
  ∀ (ξ : nat → Val + nat) (x y : nat), ξ x = inr y → up_subst ξ (S x) = inr (S y)
up_get_inl:
  ∀ (ξ : nat → Val + nat) (x : nat) (y : Val),
    ξ x = inl y → up_subst ξ (S x) = inl (renameVal S y)
upn_Var
     : ∀ (Γ : nat) (ξ : Substitution) (v : nat), v < Γ → upn Γ ξ v = inr v
*)

  Lemma upn_inr_eq_2 :
    forall ξ x y n,
        ξ x = inr y
    ->  upn n ξ (x + n) = inr (y + n).
  Proof.
    itr.
    rwr - Nat.add_comm.
    rewrite Nat.add_comm with (n := y).
    ind - n as [| n IHn]:
          smp.
    smp.
    ufl - shift.
    bwr - IHn.
  Qed.

  (* Lemma upn_get_inl :
    forall ξ x y n,
        ξ x = inl y
    ->  0 < n
    ->  upn n ξ (n + x) = inl (renameVal (uprenn n S) y).
  Proof.
    itr.
    ind - n as [| n IHn]:
          lia.
    des - n.
    1: bpp - up_get_inl in H.
    app - up_get_inl in IHn.
    smp *.
    ufl - shift in *.
    des > (up_subst (upn n ξ) (S (n + x))).
    2: con.
    do 1 feq.
    ivc - IHn.
    app - renameVal_inj_S in H1.
    sbt.
    Search upren.
    ufl - upren.
    Search (renameVal S _ ).
    rwr - upren_uprenn.
    Search (renameVal S _ = renameVal S _).
    rwr - H1.
    ivc - H1.
    
      smp *.
    smp.
    ufl - shift.
    rwr - IHn.
  Qed. *)

Lemma upn_subst_destruct_inr :
  forall n ξ x y,
      upn n ξ x = inr y
  ->        ((x < n
        /\  x = y)
    \/      (n <= x
        /\  (exists z,
                ξ x = inr z
            /\  y = n + z))
    \/      (n <= x
        /\  (exists z,
                ξ x = inl z))).
  Proof.
    itr.
    ass > (x < n \/ n <= x) as Hlia: lia.
    des - Hlia as [Hlt | Hle].
    * lft.
      spl; ato.
      psc - upn_Var: n ξ x Hlt.
      cwr - H0 in H.
      rwr - right_eq in H; trv.
    * rgt.
      pse - subst_destruct: x ξ.
      des - H0.
      - rgt.
        des - H0 as [z Hsubst].
        spl; ato.
        exi - z.
        ato.
      - lft.
        des - H0 as [z Hsubst].
        spl; ato.
        exi - z.
        pse - upn_get_inr: ξ x z n Hsubst.
        pse - upn_inl_eq_1: n x. y ξ H.
        ato.
      spl; ato.
      
      gen - x n' ξ.
      ind - n as [| n IHn]; 
            itr.
      - smp *.
        exi - n'.
        ato.
      - rwl - up_subst_S in H.
        ass > (n <= x) as Hle': lia.
        spe - IHn: (up_subst ξ) n' x H Hle'.
        des - IHn as [n'' [H2 Hn]].
        sbt.
        exi - (n'' - 1).
        spl.
        1: {
        
         2: { Search (S _ + _ = _). rwr - Nat.add_succ_comm. feq.
        destruct n''. exfalso.
        app - up_get_inr.
        app - up_get_inr.
Search upn.
  Lemma upn_list_subst_succ_inr1 :
    forall n vs ξ x n'
    upn n (list_subst vs ξ) = inr n'
    -> (x < n /\ x = n'
       \/ (m + length vs <= x) /\ upn n ξ (x - length vs) = inr n')

  Lemma upn_list_subst_split :
    forall m n vs ξ,
        m <= n
    ->  n < m + length vs
    ->  exists vs1 v vs2,
            upn m (list_subst vs ξ) n = inl v
        /\  vs = vs1 ++ [v] ++ vs2
        /\  n = m + length vs1.
  Proof.
    itr.
    gen - n m.
    ind - vs as [| v1 vs IHvs]:
          smp *;
          lia.
    itr.
    smp *.
    des - n;
          smp - H.
    * ivc - H.
      exi - ([] : list Val) v1 vs.
      ato.
    * des - m.
      - smp *.
        app - PeanoNat.lt_S_n in H0.
        pse - list_subst_split: n vs ξ H0.
        des - H1 as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
        exi - (v1 :: vs1) v vs2.
        sbt.
        smp.
        do 2 (spl; ato).
      - app - le_S_n in H.
  Restart.
    itr.
    gen - m.
    ind - n as [| n IHn];
          itr.
    * ivc - H.
      smp - H0.
      pse - list_subst_split: 0 vs ξ H0.
      des - H as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
      exi - vs1 v vs2.
      sbt.
      smp *.
      ato.
   *  des - m.
      - smp *.
        pse - list_subst_split: (S n) vs ξ H0.
        des - H1 as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
        exi - vs1 v vs2.
        sbt.
        smp.
        ato.
      - rwr - Nat.add_succ_l in H0.
        app - PeanoNat.lt_S_n in H0.
        app - le_S_n in H.
        spc - IHn: m H H0.
        des - IHn as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
        exi - vs1 v vs2.
        do 2 (try spl; ato).
        2: rwr - Nat.add_succ_l; bpp - eq_S.
  Restart.
    itr - m n vs ξ Hle Hlt.
    pse - upn_subst_destruct as Hupn: n (list_subst vs ξ) m.
    des - Hupn as [Hupn | [Hupn | Hupn]].
    3: des - Hupn as [H _]; lia.
    2: { des - Hupn as [_ [n' Hinr]].
        ind - m as [| m IHm].
        * smp *.
          pse - list_subst_split: n vs ξ Hlt.
          des - H as [vs1 [v [vs2 [Hsubst [Hvs Hlen]]]]].
          con.
        * smp - Hinr.
          Search up_subst. 
  Restart.
    itr - m n vs ξ Hle Hlt.
    pse - list_subst_destruct: (n - m) vs ξ.
    des - H as [H | [H | H]].
    2-3:  des - H as [n' [Hle' Hsubst]]; lia.
    des - H as [vs1 [v [vs2 [Hle' [Hsubst [Hvs Hlen]]]]]].
    pse - upn_subst_destruct as Hupn: n (list_subst vs ξ) m.
    des - Hupn as [Hupn | [Hupn | Hupn]].
    3: des - Hupn; lia.
    2: { 
      des - Hupn as [_ [n' Hinr]].
      des - m.
      smp *. rwr - Nat.sub_0_r in Hsubst. con.
      admit.
    }
    des - Hupn as [_ [v' Hinl]].
      
      
        lia.
    
    
    des - H as [vs1 [v [vs2 [Hsubst [Hvs Hlen]]]]].
        pse - upn_inl_eq_1: m n v (list_subst vs ξ) Hsubt.
        Search (S _ - S _).
        rwl - Nat.sub_succ in H.
        smp.
        ufl - shift.
        rwr - Hsubt.
        sbt.
        smp *.
        
      spe - IHn: vs
        app - PeanoNat.lt_S_n in H0.
      ass > (m + S (base.length vs) = S (m + base.length vs)): lia.
      cwr - H1 in H0.
      app - PeanoNat.lt_S_n in H0.
      spc - IHvs: n H.
      des - IHvs as [vs1 [v [vs2 [Hsubt [Hvs Hlen]]]]].
      exi - (v1 :: vs1) v vs2.
      sbt.
      spl; ato.
  Qed.

(*
upn_inl_eq_1:
  ∀ (n x : nat) (v : Val) (ξ : Substitution),
    upn n ξ x = inl v → ξ (x - n) = inl (renameVal (λ m : nat, m - n) v)
upn_inl_eq_2:
  ∀ (n x : nat) (v : Val) (ξ : nat → Val + nat),
    ξ x = inl v → upn n ξ (x + n) = inl (renameVal (λ m : nat, m + n) v)
up_subst_S: ∀ (n : nat) (ρ : Substitution), upn n (up_subst ρ) = upn (S n) ρ
up_get_inr:
  ∀ (ξ : nat → Val + nat) (x y : nat), ξ x = inr y → up_subst ξ (S x) = inr (S y)
up_get_inl:
  ∀ (ξ : nat → Val + nat) (x : nat) (y : Val),
    ξ x = inl y → up_subst ξ (S x) = inl (renameVal S y)
*)



  Lemma list_subst_either :
    forall x i vs ξ,
        x = (list_subst (map erase_val vs) ξ) n
    ->  (exists v,
          inr v)
        (i < length vs
        ->  exists vs1 vs2,
                vs = vs1 ++ [v] ++ ks2
            /\  x = length ks1
            /\  not (In k ks1))
     /\ (x = length ks
        -> not (In k ks)).
  Proof.


  Admitted.
  (* Lemma tmpttt :
    forall x k n ks vs ξ,
      x = upn n (list_subst (map erase_val vs) ξ) (apply_eraser ks k)
    ->    (exists v, x = inl v)
       \/ (exists n, x = inr n /\ ). *)

End EraseSubstRemove_SubstLemmas. *)


Section EraseSubstRemove_VarTheorems.



  Theorem evar_erase_subst_rem_key_single :
    forall x k₁ v₁ k,
      (erase_exp
        ([k] ᵏ++ ([(k₁, v₁)] /ᵏ k).keys)
        (EVar x))
      .[upn 1
        (list_subst
          (map erase_val ([(k₁, v₁)] /ᵏ k).vals)
          idsubst)]
    = (erase_exp
        ([k] ᵏ++ [(k₁, v₁)].keys)
        (EVar x))
      .[upn 1
        (list_subst
          (map erase_val [(k₁, v₁)].vals)
          idsubst)].
  Proof.
    itr.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁) as Heq_k.
    * rwr - var_funid_eqb_eq in Heq_k.
      cwl - Heq_k / k₁.
      smp.
      des - k as [x' | f']
            :- smp.
      des > ((x =? x')%string)
              :- smp.
    * rwr - var_funid_eqb_neq in Heq_k.
      smp.
      des - k as [x' | f'];
            des - k₁ as [x₁ | f₁]
                  :- smp.
  Qed.



  Theorem evar_add_keys_erase_subst_rem_key_single :
    forall x k₁ v₁ k σ ξ,
      (erase_exp
        ([k] ᵏ++ ([(k₁, v₁)] /ᵏ k).keys ᵏ++ σ)
        (EVar x))
      .[upn 1
        (list_subst
          (map erase_val ([(k₁, v₁)] /ᵏ k).vals)
          ξ)]
    = (erase_exp
        ([k] ᵏ++ [(k₁, v₁)].keys ᵏ++ σ)
        (EVar x))
      .[upn 1
        (list_subst
          (map erase_val [(k₁, v₁)].vals)
          ξ)].
  Proof.
    itr.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁) as Heq_k.
    * rwr - var_funid_eqb_eq in Heq_k.
      cwl - Heq_k / k₁.
      smp.
      des - k as [x' | f']
            :- smp.
      des > ((x =? x')%string)
              :- smp.
    * rwr - var_funid_eqb_neq in Heq_k.
      smp.
      des - k as [x' | f'];
            des - k₁ as [x₁ | f₁]
                  :- smp.
  Qed.



  Theorem evar_add_keys2_erase_subst_rem_key_single :
    forall x k₁ v₁ k ks' σ ξ,
      (erase_exp
        (ks' ᵏ++ [k] ᵏ++ ([(k₁, v₁)] /ᵏ k).keys ᵏ++ σ)
        (EVar x))
      .[upn (length ks' +1)
        (list_subst
          (map erase_val ([(k₁, v₁)] /ᵏ k).vals)
          ξ)]
    = (erase_exp
        (ks' ᵏ++ [k] ᵏ++ [(k₁, v₁)].keys ᵏ++ σ)
        (EVar x))
      .[upn (length ks' + 1)
        (list_subst
          (map erase_val [(k₁, v₁)].vals)
          ξ)].
  Proof.
    itr.
    ind - ks' as [| k' ks' IHks].
    * do 2  rwr -
            eraser_add_keys_nil_l.
      simpl base.length.
      rwr - Nat.add_0_l.
      app - evar_add_keys_erase_subst_rem_key_single.
    * rwr - cons_app.
      do 2  rwr -
            eraser_add_keys_app_l.
      smp.
      des - k' as [x' | f'].
      - des > ((x =? x')%string)
              :- smp.
        smp + IHks.
        rwr - app_nil_r in *.
        bpp - vval_match_shift_surjective.
      - smp + IHks.
        rwr - app_nil_r in *.
        bpp - vval_match_shift_surjective.
  Qed.



  Theorem evar_add_keys2_erase_subst_rem_key :
    forall x Γ k ks' σ ξ,
      (erase_exp
        (ks' ᵏ++ [k] ᵏ++ (Γ /ᵏ k).keys ᵏ++ σ)
        (EVar x))
      .[upn (length ks' +1)
        (list_subst
          (map erase_val (Γ /ᵏ k).vals)
          ξ)]
    = (erase_exp
        (ks' ᵏ++ [k] ᵏ++ Γ.keys ᵏ++ σ)
        (EVar x))
      .[upn (length ks' + 1)
        (list_subst
          (map erase_val Γ.vals)
          ξ)].
  Proof.
    itr.
    revert k ks' σ ξ.
    ind - Γ as [| [k₁ v₁] Γ IHΓ]
          :> itr; smp.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁).
    * smp.
    (* 
    * smp.
    ind - ks as [| k' ks' IHks].
    * do 2  rwr -
            eraser_add_keys_nil_l.
      simpl base.length.
      rwr - Nat.add_0_l.
      app - evar_add_keys_erase_subst_rem_key_single.
    * rwr - cons_app.
      do 2  rwr -
            eraser_add_keys_app_l.
      smp.
      des - k' as [x' | f'].
      - des > ((x =? x')%string)
              :- smp.
        smp + IHks.
        rwr - app_nil_r in *.
        bpp - vval_match_shift_surjective.
      - smp + IHks.
        rwr - app_nil_r in *.
        bpp - vval_match_shift_surjective. *)
  Admitted.



  Theorem evar_add_keys_erase_subst_rem_key :
    forall Γ k x σ ξ,
      (erase_exp
        ([k]  ᵏ++ (Γ /ᵏ k).keys ᵏ++ σ)
        (EVar x))
      .[upn (base.length [k])
        (list_subst
          (map erase_val (Γ /ᵏ k).vals)
          ξ)]
    = (erase_exp
        ([k]  ᵏ++ Γ.keys ᵏ++ σ)
        (EVar x))
      .[upn (base.length [k])
        (list_subst
          (map erase_val Γ.vals)
          ξ)].
  Proof.
    itr - Γ.
    ind - Γ as [| [k₁ v₁] Γ IHΓ]
          :- itr; smp
          |> itr.
    rewrite cons_app with (x := (k₁, v₁)).
    rwr - env_rem_key_app.
    do 2  rwr -
          get_keys_app
          get_vals_app.
    rwr - eraser_add_keys_app_l.
    do 2  rwr -
          map_app.
    do 2  rwl -
          list_subst_app.
    (* app - evar_add_keys_erase_subst_rem_key_single. *)
  Admitted.



  Theorem evar_erase_subst_rem_key :
    forall Γ k x,
      (erase_exp
        ([k]  ᵏ++ (Γ /ᵏ k).keys)
        (EVar x))
      .[upn (base.length [k])
        (list_subst
          (map erase_val (Γ /ᵏ k).vals)
          idsubst)]
    = (erase_exp
        ([k]  ᵏ++ Γ.keys)
        (EVar x))
      .[upn (base.length [k])
        (list_subst
          (map erase_val Γ.vals)
          idsubst)].
  Proof.
    itr.
    ind - Γ as [| [k₁ v₁] Γ IHΓ]
          :- smp.
    rewrite cons_app with (x := (k₁, v₁)).
    rwr - env_rem_key_app.
    rwr - get_keys_app
          get_vals_app.
    (* rwr - eraser_add_keys_app_l.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp. *)
  Admitted.



End EraseSubstRemove_VarTheorems.









Section EraseSubstRemove_FunIdTheorems.

Import BigStep.

  Theorem efunid_add_keys_erase_subst_rem_key_single :
    forall k₁ v₁ k f σ ξ,
      (erase_exp
        ([k]  ᵏ++ ([(k₁, v₁)] /ᵏ k).keys ᵏ++ σ)
        (EFunId f))
      .[upn (base.length [k])
        (list_subst
          (map erase_val ([(k₁, v₁)] /ᵏ k).vals)
          ξ)]
    = (erase_exp
        ([k]  ᵏ++ [(k₁, v₁)].keys ᵏ++ σ)
        (EFunId f))
      .[upn (base.length [k])
        (list_subst
          (map erase_val [(k₁, v₁)].vals)
          ξ)].
  Proof.
    itr.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁) as Heq_k.
    * rwr - var_funid_eqb_eq in Heq_k.
      cwl - Heq_k / k₁.
      smp.
      des - k as [x' | f']
            :- smp.
      des > (funid_eqb f f')
              :- smp.
    * rwr - var_funid_eqb_neq in Heq_k.
      smp.
      des - k as [x' | f'];
            des - k₁ as [x₁ | f₁]
                  :- smp.
  Qed.



  Theorem efunid_erase_subst_rem_key_single :
    forall k₁ v₁ k f,
      (erase_exp
        ([k]  ᵏ++ ([(k₁, v₁)] /ᵏ k).keys)
        (EFunId f))
      .[upn (base.length [k])
        (list_subst
          (map erase_val ([(k₁, v₁)] /ᵏ k).vals)
          idsubst)]
    = (erase_exp
        ([k]  ᵏ++ [(k₁, v₁)].keys)
        (EFunId f))
      .[upn (base.length [k])
        (list_subst
          (map erase_val [(k₁, v₁)].vals)
          idsubst)].
  Proof.
    itr.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁) as Heq_k.
    * rwr - var_funid_eqb_eq in Heq_k.
      cwl - Heq_k / k₁.
      smp.
      des - k as [x' | f']
            :- smp.
      des > (funid_eqb f f')
              :- smp.
    * rwr - var_funid_eqb_neq in Heq_k.
      smp.
      des - k as [x' | f'];
            des - k₁ as [x₁ | f₁]
                  :- smp.
  Qed.



End EraseSubstRemove_FunIdTheorems.









Section EraseSubstRemove_ExpTheorems.



  Theorem erase_subst_rem_key_single :
    forall k₁ v₁ k e,
      (erase_exp
        ([k]  ᵏ++ ([(k₁, v₁)] /ᵏ k).keys)
        e)
      .[upn (base.length [k])
        (list_subst
          (map erase_val ([(k₁, v₁)] /ᵏ k).vals)
          idsubst)]
    = (erase_exp
        ([k]  ᵏ++ [(k₁, v₁)].keys)
        e)
      .[upn (base.length [k])
        (list_subst
          (map erase_val [(k₁, v₁)].vals)
          idsubst)].
  Proof.
    itr.
    ind ~ ind_bs_exp - e
          :- smp
          |> smp.
    (* #1 EVar/EFunid *)
    2: app - evar_erase_subst_rem_key_single.
    2: app - efunid_erase_subst_rem_key_single.
    (* #2 ECons/ESeq *)
    3: do 2 feq; asm.
    9: do 2 feq; asm.
    (* #2 EFun/ELetRec *)
    2: { do 2 feq.
    smp.
    rwr - app_nil_r.
    ufl - env_rem_key_one.
    smp.
    des > (k =ᵏ k₁).
    * smp.
  Admitted.



End EraseSubstRemove_ExpTheorems.