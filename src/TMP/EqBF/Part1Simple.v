From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: VALTOEXP /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - bval_to_bexp_ext [Fold]
* Main
  - bval_to_bexp
*)






Section ValToExp_Help.



  Definition bval_to_bexp_ext
    (f : Environment -> Expression -> Expression)
    (env : Environment)
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    : list (FunctionIdentifier * (list Var * Expression))
    :=
  map
    (fun '(n, fid, (vl, e)) =>
      (fid,
        (vl,
        (f (rem_vars vl env) e))))
    ext.



End ValToExp_Help.






Section ValToExp_Main.



  Fixpoint bval_to_bexp
    (f : Environment -> Expression -> Expression)
    (v : Value)
    : Expression
    :=
  let
    bval_to_bexp_ext'
      (f : Environment -> Expression -> Expression)
      (env : Environment)
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      : list (FunctionIdentifier * (list Var * Expression))
      :=
    map
      (fun '(n, fid, (vl, e)) =>
        (fid,
          (vl,
          (f (rem_vars vl env) e))))
      ext
  in
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
      (bval_to_bexp f hd)
      (bval_to_bexp f tl)

  | VTuple l => ETuple
      (map (bval_to_bexp f) l)

  | VMap l => EMap
      (map
        (prod_map 
          (bval_to_bexp f)
          (bval_to_bexp f))
        l)

  | VClos env ext id vl e fid =>
      match ext, fid with
      | [], _ => EFun
          vl
          (f (rem_vars vl env) e)

      (* This is None in option version *)
      | _, None => EFun
          vl
          (f (rem_vars vl env) e)

      | _, Some fid' => ELetRec
          (bval_to_bexp_ext'
            f
            (rem_nfifes ext env)
            ext)
          (EFunId fid')
      end
  end.



End ValToExp_Main.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SUBSTITUTE ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - subst_env
*)






Section Substitue.



  Fixpoint subst_env
    (fuel : nat)
    (env : Environment)
    (e : Expression)
    : Expression
    :=
  match fuel with
  (* This is None in option version *)
  | O => e
  | S fuel' =>
    match e with
    | ENil => e
    | ELit l => e

    | EValues el => EValues
        (map (subst_env fuel' env) el)

    | EFun vl e => EFun
      vl
      (subst_env fuel' env e)

    | ECons hd tl => ECons
        (subst_env fuel' env hd)
        (subst_env fuel' env tl)

    | ETuple l => ETuple
        (map (subst_env fuel' env) l)

    | ECall m f l => ECall
        (subst_env fuel' env m)
        (subst_env fuel' env f)
        (map (subst_env fuel' env) l)

    | EPrimOp f l => EPrimOp
      f
      (map (subst_env fuel' env) l)

    | EApp exp l => EApp
        (subst_env fuel' env exp)
        (map (subst_env fuel' env) l)

    | ECase e l => ECase
        (subst_env fuel' env e)
        (map
          (fun '(pl, g, b) =>
            (pl,
            (subst_env fuel' env g),
            (subst_env fuel' env b)))
          l)

    | ELet l e1 e2 => ELet
        l
        (subst_env fuel' env e1)
        (subst_env fuel' (rem_vars l env) e2)

    | ESeq e1 e2 => ESeq
        (subst_env fuel' env e1)
        (subst_env fuel' env e2)

    | ELetRec l e => ELetRec
        (map
          (fun '(fid, (vl, b)) =>
            (fid,
            (vl,
            (subst_env fuel' (rem_both l vl env) b))))
          l)
        (subst_env fuel' (rem_fids l env) e)

    | EMap l => EMap
        (map
          (prod_map
            (subst_env fuel' env)
            (subst_env fuel' env))
          l)

    | ETry e1 vl1 e2 vl2 e3 => ETry
        (subst_env fuel' env e1)
        vl1
        (subst_env fuel' env e2)
        vl2
        (subst_env fuel' env e3)

    | EVar var =>
        match (get_value env (inl var)) with
        | Some [v] => bval_to_bexp (subst_env fuel') v
        | Some vs => EValues
            (map (bval_to_bexp (subst_env fuel')) vs)
        | _ => e
        end

    | EFunId fid =>
        match (get_value env (inr fid)) with
        | Some [v] => bval_to_bexp (subst_env fuel') v
        | Some vs => EValues
            (map (bval_to_bexp (subst_env fuel')) vs)
        | _ => e
        end
    end
  end.



End Substitue.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SUBSTITUTELEMMAS /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - subst_env_empty
*)






Section SubstituteLemmas.



  Theorem subst_env_empty :
    forall n e,
      subst_env n [] e = e.
  Proof.
    intros.
    generalize dependent n.
    induction e using derived_Expression_ind.
    * (* Values *)
      rename H into HForall.
      induction el as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      invc HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * destruct n; by cbn.
    * destruct n; by cbn.
    * destruct n; by cbn.
    * destruct n; by cbn.
    * (* Fun *)
      destruct n; cbn.
      - reflexivity.
      - specialize (IHe n).
        rewrite IHe.
        reflexivity.
    * (* Cons *)
      destruct n; cbn.
      - reflexivity.
      - specialize (IHe1 n).
        specialize (IHe2 n).
        rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    * (* Tuple *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      invc HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* Call *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      2: rewrite IHe1; by rewrite IHe2.
      1-2: reflexivity.
      rewrite IHe1.
      rewrite IHe2.
      invc HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* PrimOp *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      invc HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He.
      clear He.
      cbn in IHel.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* App *)
      rename e into e'.
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      2: by rewrite IHe.
      1-2: reflexivity.
      invc HForall.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn in IHel.
      inv IHel.
      clear H0.
      rename H1 into Hel.
      rewrite IHe.
      rewrite IHe.
      rewrite He.
      rewrite Hel.
      rewrite Hel.
      reflexivity.
    * (* Case *)
      rename e into e'.
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      2: by rewrite IHe.
      1-2: reflexivity.
      invc HForall.
      destruct e as [e e2].
      destruct e as [p e1].
      destruct H1.
      cbn in *.
      rename H into He1.
      rename H0 into He2.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall IHe.
      cbn in IHel.
      injection IHel; intros Hel He.
      clear IHel.
      rewrite He.
      rewrite Hel.
      rewrite He1.
      rewrite He2.
      reflexivity.
    * (* Let *)
      destruct n; cbn.
      - reflexivity.
      - rewrite rem_vars_empty.
        rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    * (* Seq *)
      destruct n; cbn.
      - reflexivity.
      - rewrite IHe1.
        rewrite IHe2.
        reflexivity.
    * (* LetRec *)
      rename e into e'.
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n.
      2: cbn; by rewrite IHe.
      1-2: reflexivity.
      invc HForall.
      destruct e as [f e].
      destruct e as [l e].
      cbn in H1.
      rename H1 into He.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn in IHel.
      injection IHel; intros Hefid Hel.
      clear IHel.
      simpl.
      rewrite rem_fids_empty.
      rewrite IHe.
      rewrite rem_both_empty.
      rewrite He.
      cbn.
      do 2 f_equal.
      rewrite <- Hel at 2.
      apply map_ext.
      intros [fid [vl b]].
      do 2 f_equal.
      rewrite rem_vars_fold.
      rewrite rem_fids_fold.
      rewrite rem_vars_empty.
      rewrite rem_fids_empty.
      rewrite rem_both_empty.
      reflexivity.
    * (* Map *)
      rename H into HForall.
      induction l as [| e el IHel]; intros; destruct n; cbn.
      1-3: reflexivity.
      invc HForall.
      destruct e as [e1 e2].
      destruct H1.
      rename H into He1.
      rename H0 into He2.
      rename H2 into HForall.
      specialize (IHel HForall (S n)).
      clear HForall.
      cbn.
      f_equal.
      rewrite He1.
      rewrite He2.
      clear He1 He2.
      cbn in *.
      injection IHel; intros Hel.
      clear IHel.
      rewrite Hel.
      reflexivity.
    * (* Try *)
      destruct n; cbn.
      - reflexivity.
      - rewrite IHe1.
        rewrite IHe2.
        rewrite IHe3.
        reflexivity.
  Qed.



End SubstituteLemmas.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: CONVERT //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - bexp_to_fexp_subst
  - bvs_to_fvs
  - bexc_to_fexc
  - bres_to_fres
*)






Section Convert.



  Definition bexp_to_fexp_subst
    f
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  bexp_to_fexp
    f
    (subst_env
      (measure_env_exp
        env
        e)
      env
      e).



  Definition bvs_to_fvs
    f
    (vs : ValueSequence)
    : ValSeq
    :=
  map
    (bval_to_fval f)
    vs.



  Definition bexc_to_fexc
    f
    (exc : Exception)
    : CoreErlang.Syntax.Exception
    :=
  match exc with
  | (excc, v1, v2) =>
      match
        (bval_to_fval f v1),
        (bval_to_fval f v2)
      with
      | v1', v2' =>
          match excc with
          | Error => (CoreErlang.Syntax.Error, v1', v2')
          | Throw => (CoreErlang.Syntax.Throw, v1', v2')
          | Exit => (CoreErlang.Syntax.Exit, v1', v2')
          end
      end
  end.



  Definition bres_to_fres
    f
    (res : (ValueSequence + Exception))
    : Redex
    :=
  match res with
  | inl vs =>
      match (bvs_to_fvs f vs) with
      | vs' => RValSeq vs'
      end
  | inr exc => 
      match (bexc_to_fexc f exc) with
      | exc' => RExc exc'
      end
  end.



End Convert.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MeasureLemmas2 ///////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Value
  - measure_val_reduction
* Expression
  - measure_exp_reduction
* Mapper
  - measure_val_reduction_list
  - measure_val_reduction_map
* Minimum
  - measure_val_reduction_min
  - measure_val_reduction_list_min
  - measure_val_reduction_map_min
  - measure_exp_reduction_min
* Specials
  - measure_reduction_vcons1
  - measure_reduction_vcons2
  - measure_reduction_vtuple
  - measure_reduction_vmap
*)






Section MeasureLemmas_Value.



  Theorem measure_val_reduction :
    forall v n1 n2,
      measure_val v <= n1
    ->
      measure_val v <= n2
    ->
      bval_to_bexp (subst_env n1) v
    =
      bval_to_bexp (subst_env n2) v.
  Proof.
    intros v n1 n2 Hn1 Hn2.
    induction v using derived_Value_ind.
    * by cbn.
    * by cbn.
    * (* Cons *)
      remember
        (BigStep.Syntax.VCons v1 v2)
        as vcons
        eqn:Heq_vcons.
      assert (measure_val v1 ≤ measure_val vcons) as Hv1.
      rewrite Heq_vcons; slia.
      assert (measure_val v2 ≤ measure_val vcons) as Hv2.
      rewrite Heq_vcons; slia.
      assert (measure_val v1 ≤ n1) as Hv1n1.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv1.
        - exact Hn1.
      }
      assert (measure_val v1 ≤ n2) as Hv1n2.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv1.
        - exact Hn2.
      }
      assert (measure_val v2 ≤ n1) as Hv2n1.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv2.
        - exact Hn1.
      }
      assert (measure_val v2 ≤ n2) as Hv2n2.
      {
        apply Nat.le_trans with (m := measure_val vcons).
        - exact Hv2.
        - exact Hn2.
      }
      clear Hv1 Hv2 Hn1 Hn2.
      specialize (IHv1 Hv1n1 Hv1n2).
      specialize (IHv2 Hv2n1 Hv2n2).
      inv Heq_vcons.
      clear H Hv1n1 Hv1n2 Hv2n1 Hv2n2.
      cbn.
      rewrite IHv1.
      rewrite IHv2.
      reflexivity.
    * (* Clos *)
      (*
      simpl in *.
      destruct ext.
      - f_equal.
      *)
      rename H into HForall.
      induction ref as [| x env IHenv].
      - cbn.
        destruct ext; destruct funid.
        1-2, 4: rewrite rem_vars_empty; by do 2 rewrite subst_env_empty.
        rewrite rem_nfifes_empty.
        f_equal.
        unfold bval_to_bexp_ext.
        apply map_ext.
        intros [fid [vl e]].
        rewrite rem_vars_empty.
        do 2 rewrite subst_env_empty.
        reflexivity.
      - invc HForall.
        rename H1 into Hx.
        rename H2 into HForall.
        specialize (IHenv HForall).
        clear HForall.
        remember
          (VClos env ext id params body funid)
          as v_env
          eqn:Heq_v_env.
        remember
          (VClos (x :: env) ext id params body funid)
          as v_xenv
          eqn:Heq_v_xenv.
        assert (measure_val v_env ≤ measure_val v_xenv) as Henv.
        {
          rewrite Heq_v_env.
          rewrite Heq_v_xenv.
          simpl.
          unfold measure_env.
          slia.
        }
        assert (measure_val x.2 ≤ n1) as Hxn1.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - rewrite Heq_v_xenv. destruct x. simpl. unfold measure_env. slia.
          - exact Hn1.
        }
        assert (measure_val v_env ≤ n1) as Henvn1.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - exact Henv.
          - exact Hn1.
        }
        assert (measure_val x.2 ≤ n2) as Hxn2.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - rewrite Heq_v_xenv. destruct x. simpl. unfold measure_env. slia.
          - exact Hn2.
        }
        assert (measure_val v_env ≤ n2) as Henvn2.
        {
          apply Nat.le_trans with (m := measure_val v_xenv).
          - exact Henv.
          - exact Hn2.
        }
        specialize (Hx Hxn1 Hxn2).
        specialize (IHenv Henvn1 Henvn2).
        clear Hxn1 Hxn2 Henvn1 Henvn2 Henv.
        inv Heq_v_env.
        clear H Hn2 Hn1.
        simpl in *.
        destruct ext; destruct funid.
        + f_equal.
          inv IHenv.
          rename H0 into Henv.
          destruct x.
          simpl in *.
          admit.
        + admit.
        + admit.
        + admit.
    * (* Tuple *)
      induction l as [| v vl IHvl].
      - by cbn.
      - inv H.
        rename H2 into Hv.
        rename H3 into HForall.
        remember
          (BigStep.Syntax.VTuple vl)
          as vtuple_vl
          eqn:Heq_vtuple_vl.
        remember
          (BigStep.Syntax.VTuple (v :: vl))
          as vtuple_vvl
          eqn:Heq_vtuple_vvl.
        assert (measure_val vtuple_vl ≤ measure_val vtuple_vvl) as Hvl.
        {
          rewrite Heq_vtuple_vl.
          rewrite Heq_vtuple_vvl.
          simpl.
          unfold measure_list.
          simpl.
          slia.
        }
        assert (measure_val v ≤ n1) as Hvn1.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - inv Heq_vtuple_vvl. cbn. lia.
          - exact Hn1.
        }
        assert (measure_val vtuple_vl ≤ n1) as Hvln1.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - exact Hvl.
          - exact Hn1.
        }
        assert (measure_val v ≤ n2) as Hvn2.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - inv Heq_vtuple_vvl. cbn. lia.
          - exact Hn2.
        }
        assert (measure_val vtuple_vl ≤ n2) as Hvln2.
        {
          apply Nat.le_trans with (m := measure_val vtuple_vvl).
          - exact Hvl.
          - exact Hn2.
        }
        clear Hn1 Hn2.
        specialize (Hv Hvn1 Hvn2).
        specialize (IHvl HForall Hvln1 Hvln2).
        invc Heq_vtuple_vl.
        clear H Hvn1 Hvln1 Hvn2 Hvln2 Hvl HForall.
        simpl in *.
        injection IHvl as Hmap_vl.
        rewrite Hmap_vl.
        rewrite Hv.
        reflexivity.
    * (* Map *)
      induction l as [| (v1, v2) vl IHvl].
      - by cbn.
      - inv H.
        rename H2 into Hv.
        rename H3 into HForall.
        simpl in Hv.
        destruct Hv as [Hv1 Hv2].
        remember
          (BigStep.Syntax.VMap vl)
          as vmap_vl
          eqn:Heq_vmap_vl.
        remember
          (BigStep.Syntax.VMap ((v1, v2) :: vl))
          as vmap_vvl
          eqn:Heq_vmap_vvl.
        assert (measure_val vmap_vl ≤ measure_val vmap_vvl) as Hvl.
        {
          rewrite Heq_vmap_vl.
          rewrite Heq_vmap_vvl.
          simpl.
          unfold measure_list.
          unfold measure_map.
          slia.
        }
        assert (measure_val v1 ≤ n1) as Hv1n1.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn1.
        }
        assert (measure_val v2 ≤ n1) as Hv2n1.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn1.
        }
        assert (measure_val vmap_vl ≤ n1) as Hvln1.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - exact Hvl.
          - exact Hn1.
        }
        assert (measure_val v1 ≤ n2) as Hv1n2.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn2.
        }
        assert (measure_val v2 ≤ n2) as Hv2n2.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - inv Heq_vmap_vvl. cbn. lia.
          - exact Hn2.
        }
        assert (measure_val vmap_vl ≤ n2) as Hvln2.
        {
          apply Nat.le_trans with (m := measure_val vmap_vvl).
          - exact Hvl.
          - exact Hn2.
        }
        clear Hn1 Hn2.
        specialize (Hv1 Hv1n1 Hv1n2).
        specialize (Hv2 Hv2n1 Hv2n2).
        specialize (IHvl HForall Hvln1 Hvln2).
        invc Heq_vmap_vl.
        clear H Hv1n1 Hv2n1 Hvln1 Hv1n2 Hv2n2 Hvln2 Hvl HForall.
        simpl in *.
        injection IHvl as Hvl.
        rewrite Hv1.
        rewrite Hv2.
        rewrite Hvl.
        reflexivity.
  Admitted.



End MeasureLemmas_Value.






Section MeasureLemmas_Expression.



Theorem measure_env_exp_reduction :
    forall env e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env e
    =   subst_env n2 env e.
  Proof.
  Admitted.



End MeasureLemmas_Expression.






Section MeasureLemmas_Mappers.



  Theorem measure_val_reduction_list :
    forall vl n1 n2,
      list_sum (map measure_val vl) <= n1
    ->
      list_sum (map measure_val vl) <= n2
    ->
      map (bval_to_bexp (subst_env n1)) vl
    =
      map (bval_to_bexp (subst_env n2)) vl.
  Proof.
    intros vl n1 n2 Hn1 Hn2.
    induction vl.
    * by cbn.
    * rename a into v.
      assert (measure_val v
        <= list_sum (map measure_val (v :: vl))) as Hv.
      slia.
      assert (list_sum (map measure_val vl)
        <= list_sum (map measure_val (v :: vl))) as Hvl.
      slia.
      assert (measure_val v <= n1) as Hvn1.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hv.
          - exact Hn1.
      }
      assert (list_sum (map measure_val vl) <= n1) as Hvln1.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hvl.
          - exact Hn1.
      }
      assert (measure_val v <= n2) as Hvn2.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hv.
          - exact Hn2.
      }
      assert (list_sum (map measure_val vl) <= n2) as Hvln2.
      {
        apply Nat.le_trans with (m := list_sum (map measure_val (v :: vl))).
          - exact Hvl.
          - exact Hn2.
      }
      clear Hv Hvl Hn1 Hn2.
      specialize (IHvl Hvln1 Hvln2).
      pose proof measure_val_reduction
        v n1 n2 Hvn1 Hvn2 as Hv.
      clear Hvn1 Hvln1 Hvn2 Hvln2.
      cbn.
      rewrite IHvl.
      rewrite Hv.
      reflexivity.
  Qed.



  Theorem measure_val_reduction_map :
    forall vl n1 n2,
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl) <= n1
    ->
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl) <= n2
    ->
      map
        (prod_map
          (bval_to_bexp (subst_env n1))
          (bval_to_bexp (subst_env n1)))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env n2))
          (bval_to_bexp (subst_env n2)))
        vl.
  Proof.
    intros vl n1 n2 Hvvl_n1 Hvvl_n2.
    induction vl.
    * by cbn.
    * (* + rename/remember *)
      rename a into v.
      remember
        (measure_val v.1)
        as measure_v1
        eqn: Heq_v1.
      remember
        (measure_val v.2)
        as measure_v2
        eqn: Heq_v2.
      remember
        (measure_val v.1 + measure_val v.2)
        as measure_v
        eqn: Heq_v.
      remember
        (list_sum (map (λ '(x, y), measure_val x + measure_val y) vl))
        as measure_vl
        eqn: Heq_vl.
      remember
        (list_sum (map (λ '(x, y), measure_val x + measure_val y) (v :: vl)))
        as measure_vvl
        eqn: Heq_vvl.
      (* + assert triv *)
      assert (measure_v1 <= measure_v) as Hv1_v by slia.
      assert (measure_v2 <= measure_v) as Hv2_v by slia.
      assert (measure_v <= measure_vvl) as Hv_vvl.
      rewrite Heq_v; rewrite Heq_vvl; destruct v; slia.
      assert (measure_vl <= measure_vvl) as Hvl_vvl.
      rewrite Heq_vl; rewrite Heq_vvl; slia.
      (* + assert trans *)
      assert (measure_v1 <= n1) as Hv1_n1.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hv1_v.
          + exact Hv_vvl.
        - exact Hvvl_n1.
      }
      assert (measure_v2 <= n1) as Hv2_n1.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hv2_v.
          + exact Hv_vvl.
        - exact Hvvl_n1.
      }
      assert (measure_vl <= n1) as Hvl_n1.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - exact Hvl_vvl.
        - exact Hvvl_n1.
      }
      assert (measure_v1 <= n2) as Hv1_n2.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hv1_v.
          + exact Hv_vvl.
        - exact Hvvl_n2.
      }
      assert (measure_v2 <= n2) as Hv2_n2.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - apply Nat.le_trans with (m := measure_v).
          + exact Hv2_v.
          + exact Hv_vvl.
        - exact Hvvl_n2.
      }
      assert (measure_vl <= n2) as Hvl_n2.
      {
        apply Nat.le_trans with (m := measure_vvl).
        - exact Hvl_vvl.
        - exact Hvvl_n2.
      }
      rewrite Heq_v1 in *.
      rewrite Heq_v2 in *.
      clear Heq_v1 Heq_v2 Hv1_v Hv2_v Hv_vvl Hvl_vvl Hvvl_n1 Hvvl_n2.
      (* + specialize/pose proof *)
      pose proof measure_val_reduction
        v.1 n1 n2 Hv1_n1 Hv1_n2 as Hv1.
      pose proof measure_val_reduction
        v.2 n1 n2 Hv2_n1 Hv2_n2 as Hv2.
        specialize (IHvl Hvl_n1 Hvl_n2) as Hvl.
      clear - Hv1 Hv2 Hvl.
      (* rewrite *)
      destruct v as [x y].
      cbn in *.
      rewrite Hv1.
      rewrite Hv2.
      rewrite Hvl.
      reflexivity.
  Qed.



End MeasureLemmas_Mappers.






Section MeasureLemmas_Min.



  Theorem measure_val_reduction_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    intros v n Hn.
    assert (measure_val v <= measure_val v) as Hv.
    lia.
    by pose proof measure_val_reduction
      v n (measure_val v) Hn Hv.
  Qed.



    Theorem measure_val_reduction_list_min :
    forall vl n,
      list_sum (map measure_val vl) <= n
    ->
      map (bval_to_bexp (subst_env n)) vl
    =
      map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
    Proof.
      intros vl n Hn.
      assert (list_sum (map measure_val vl) <= measure_val (VTuple vl))
        as Hvl by slia.
      by pose proof measure_val_reduction_list
        vl n (measure_val (VTuple vl)) Hn Hvl.
    Qed.



  Theorem measure_val_reduction_map_min :
    forall vl n,
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl) <= n
    ->
      map
        (prod_map
          (bval_to_bexp (subst_env n))
          (bval_to_bexp (subst_env n)))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vl))))
          (bval_to_bexp (subst_env (measure_val (VMap vl)))))
        vl.
  Proof.
      intros vl n Hn.
      assert
        (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= measure_val (VMap vl))
        as Hvl by slia.
      by pose proof measure_val_reduction_map
        vl n (measure_val (VMap vl)) Hn Hvl.
    Qed.



  Theorem measure_env_exp_reduction_min :
    forall env e n,
        measure_env_exp env e <= n
    ->  subst_env n env e
    =   subst_env (measure_env_exp env e) env e.
  Proof.
    intros env e n Hn.
    assert (measure_env_exp env e <= measure_env_exp env e) as Hv.
    lia.
    by pose proof measure_env_exp_reduction
      env e n (measure_env_exp env e) Hn Hv.
  Qed.



End MeasureLemmas_Min.





Section MeasureLemmas_Specials.



  Theorem measure_reduction_vcons1 :
    forall v1 v2,
        bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v1
    =   bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    intros.
    assert (measure_val v1 <= measure_val (VCons v1 v2)) as Hv by slia.
    by pose proof measure_val_reduction_min
      v1 (measure_val (VCons v1 v2)) Hv.
  Qed.



  Theorem measure_reduction_vcons2 :
    forall v1 v2,
        bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v2
    =   bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    intros.
    assert (measure_val v2 <= measure_val (VCons v1 v2)) as Hv by slia.
    by pose proof measure_val_reduction_min
      v2 (measure_val (VCons v1 v2)) Hv.
  Qed.



  Theorem measure_reduction_vtuple :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    =
      map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
    Proof.
      intros.
      assert (list_sum (map measure_val vl) <= measure_val (VTuple (v :: vl)))
        as Hvl by slia.
      by pose proof measure_val_reduction_list_min
        vl (measure_val (VTuple (v :: vl))) Hvl.
    Qed.



  Theorem measure_reduction_vmap :
    forall v1 v2 vl,
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))))
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl))))))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vl))))
          (bval_to_bexp (subst_env (measure_val (VMap vl)))))
        vl.
  Proof.
      intros.
      assert
        (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= (measure_val (VMap ((v1, v2) :: vl))))
        as Hvl by slia.
      by pose proof measure_val_reduction_map_min
        vl (measure_val (VMap ((v1, v2) :: vl))) Hvl.
    Qed.



End MeasureLemmas_Specials.