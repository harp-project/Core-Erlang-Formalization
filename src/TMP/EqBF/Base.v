From CoreErlang.TMP Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.

Import BigStep.



(** STRUCTURE:
* Induction
* WellFormedMapDefinitions
* WellFormedMapLemmas
* EnvironmentDefinitions
* EnvironmentLemmas
* FrameStackIdentLemmas
* ScopingLemmas
* MeasureDefinitions
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: INDUCTION ////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(** STRUCTURE:
* Induction_Value
  - ind_val
* Induction_Expression
  - ind_exp
*)



(** NOTES:
* Maybe place this in BigStep/Induction
*)



(** DOCUMENTATION:
* These are derived versions of the inductions from BigStep/Induction,
  which are no longer in need for logical propositions as parameters (Q R w Z)
* They are created for special inductions on Value and Expression types
*)









Section Induction_Value.



  Variables
    (P : Value -> Prop).



  Hypotheses
    (HNil : P VNil)

    (HLit :
      forall l,
        P (VLit l))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (VCons hd tl))

    (HClos :
      forall ref ext id params body funid,
          Forall (fun x => P (snd x)) ref
      ->  P (VClos ref ext id params body funid))

    (HTuple :
      forall l,
          Forall P l
      ->  P (VTuple l))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (VMap l)).



  (** DOCUMENTATION:
  * FULL NAME:
    - Induction on BigStep Value
  * OLD NAME:
    - derived_Value_ind, value_ind, val_ind
  * USING:
    - Project:
      + Lemmas: Value_ind2
  * USED AT:
    - MeasureLemmas:
      + mred_val [Might Deprecate]
    - ConverterLemmas:
      + bval_to_fval_add_vars
    - EqvivalenceReductionLemmas:
      + bs_to_fs_equivalence_reduction
  * HISTORY:
    - First created for 'bs_to_fs_equivalence_reduction',
      because the regular induction on value wasn't enought
  *)
  Theorem ind_val :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd x))); intuition.
  Defined.



End Induction_Value.






Section Induction_Expression.



  Variables
    (P : Expression -> Prop).



  Hypotheses
    (HValues :
      forall el,
          Forall P el
      ->  P (EValues el))

    (HNil : P ENil)

    (HLit :
      forall l,
          P (ELit l))

    (HVar :
      forall v,
          P (EVar v))

    (HFunId :
      forall f,
        P (EFunId f))

    (HFun :
      forall vl e,
          P e
      ->  P (EFun vl e))

    (HCons :
      forall hd tl,
          P hd
      ->  P tl
      ->  P (ECons hd tl))

    (HTuple :
      forall l,
          Forall P l
      ->  P (ETuple l))

    (HCall :
      forall m f l,
          P m
      ->  P f
      ->  Forall P l
      ->  P (ECall m f l))

    (HPrimOp :
      forall f l,
          Forall P l
      ->  P (EPrimOp f l))

    (HApp :
      forall exp l,
          P exp
      ->  Forall P l
      ->  P (EApp exp l))

    (HCase :
      forall e l,
          P e
      ->  Forall (fun x => P (snd (fst x)) /\ P (snd x)) l
      ->  P (ECase e l))

    (HLet :
      forall l e1 e2,
          P e1
      ->  P e2
      ->  P (ELet l e1 e2))

    (HSeq :
      forall e1 e2,
          P e1
      ->  P e2
      ->  P (ESeq e1 e2))

    (HLetRec :
      forall l e,
          P e
      ->  Forall (fun x => P (snd (snd x))) l
      ->  P (ELetRec l e))

    (HMap :
      forall l,
          Forall (fun x => P (fst x) /\ P (snd x)) l
      ->  P (EMap l))

    (HTry :
      forall e1 vl1 e2 vl2 e3,
          P e1
      ->  P e2
      ->  P e3
      ->  P (ETry e1 vl1 e2 vl2 e3)).


  (** DOCUMENTATION:
  * FULL NAME:
    - Induction on BigStep Expression
  * OLD NAME:
    - derived_Expression_ind, expression_ind, val_exp
  * USING:
    - Project:
      + Lemmas: Expression_ind2
  * USED AT:
    - SubstitueLemmas:
      + subst_env_empty [Not Using]
    - MeasureLemmas:
      + mexp_val
    - ConverterLemmas:
      + bexp_to_fexp_add_vars_comm
      + bexp_to_fexp_add_vars
  * HISTORY:
    - First created for 'subst_env_empty',
      because the regular induction on expression wasn't enought
    - Later I found out, that I doesn't need 'subst_env_empty',
      but creating ind_exp wasn't useless, becasuse later I need it,
      in different necessary theorems
  *)
  Theorem ind_exp :
    forall e, P e.
  Proof.
    induction e using Expression_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd (fst x)) /\ P (snd x)))
      (Z := Forall (fun x => P (snd (snd x)))); intuition.
  Defined.



End Induction_Expression.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: WELLFORMEDMAP ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(** STRUCTURE:
* WellFormedMap
  - wfm_bs_val
  - fs_wfm
*)



(** NOTES:
* Later change lists to maps in Syntax
*)



(** DOCUMENTATION:
* Unfortunately both in the BigStep & FrameStack syntax maps are defined
  by lists, which create some problems
* I first noticed this, when trying to prove something
  at 'bs_to_fs_equivalence_reduction', and I could prove something,
  because of the lack of hypthesis, which would automaticly come from the Map,
  if they were realy would be implemented with maps
* But changing lists to maps in Syntax would take too much time,
  so temporaly I created these extra predicates, which tell if the Map
  represeting list are indeed correctly represeting a map.
* These currently put in every theorem, which need them
* Later the Syntax need a refactor!!!
*)









Section WellFormedMap.



  (** DOCUMENTATION: [NOT USING]
  * FULL NAME:
    - Well Formed Map in BigStep
  * OLD NAME:
    - well_formed_map_bigstep, well_formed_map_bs
  * USING:
    - Built in:
      + Definition:
        * zip [stdpp.base]
    - Project:
      + Definition:
        * make_value_map [CoreErlang.BigStep.Helpers]
        * PBoth [CoreErlang.Basics]
  * USED AT:
    /
  * HOW IT WORKS
    - For VCons, VClos, VTuple, VMap its chechk recursively every Value type
    - if v : Value is a 'VMap l', than its also checks,
      if the 'l' list, which suposed to representing a map
      is indeed does it corretly
    - this is done by make_value_map, if the new list and the old one equals,
      then the list is an well formed map
  * HISTORY:
    - Currently not used, but create a BigStep pair for the FrameStack one
    - Noticed, that unlike the FrameStack on it's not defined recursively,
      and missing Cons, Tuple, Clos
  * SUGESSTION:
    - Modify make_value_map
      + Parameters: instead two lists use one pair typed list
      + Returns: instead a list pair use a pair typed list
    - Refactor Syntax so in 'VMap l' the  'l' is represented by a map
  *)
  Fixpoint wfm_bs_val
    (v : Value)
    : Prop
    :=
  match v with
  | VCons hd tl =>
      wfm_bs_val hd
      /\
      wfm_bs_val tl

  | VTuple l =>
      foldr
        (fun v acc =>
          wfm_bs_val v /\ acc)
        True
        l

  | VClos env _ _ _ _ _ =>
      foldr
        (fun kv acc =>
          wfm_bs_val (snd kv) /\ acc)
        True
        env

  | VMap l =>
      (l =
      let (kl , vl) :=
        (make_value_map
          (fst (split l))
          (snd (split l)))
      in zip kl vl)
      /\
      foldr
        (fun v acc =>
          PBoth wfm_bs_val v /\ acc)
        True
        l

  | _ => True
  end.



  (** DOCUMENTATION:
  * FULL NAME:
    - FrameStack Value is a Well For
  * OLD NAME:
    - well_formed_map_framestack, well_formed_map_fs
  * USING:
    - Project:
      + Definition:
        * make_make_val_map [CoreErlang.Maps]
        * PBoth [CoreErlang.Basics]
  * USED AT:
    - WellFormedMapDefinitions:
      + fs_wfm_valseq
      + fs_wfm_exception
    - WellFormedMapLemmas:
      + fs_wfm_vcons
      + fs_wfm_vtuple
      + fs_wfm_vmap
    - EqvivalenceReductionLemmas:
      + bs_to_fs_equivalence_reduction
    - Eqvivalence:
      + bigstep_to_framestack_equivalence
  * HOW IT WORKS
    - For VCons, VClos, VTuple, VMap its chechk recursively every Value type
    - if v : Value is a 'VMap l', than its also checks,
      if the 'l' list, which suposed to representing a map
      is indeed does it corretly
    - this is done by make_val_map, if the new list and the old one equals,
      then the list is an well formed map
  * HISTORY:
    - Created when noticed in 'bs_to_fs_equivalence_reduction's VMap branch,
      the list_biforall can't be proved, because l in not a map, only a list,
      so as a hot fix, I created a extra predicate for the theorem,
      which states, that l has all the qualities as a regular map
  * SUGESSTION:
    - Refactor Syntax so in 'VMap l' the  'l' is represented by a map
  *)
  Fixpoint fs_wfm_val
    (v : Val)
    : Prop
    :=
  match v with
  | Syntax.VCons hd tl =>
      fs_wfm_val hd
      /\
      fs_wfm_val tl

  | Syntax.VTuple l =>
      foldr
        (fun v acc =>
          fs_wfm_val v /\ acc)
        True 
        l

  | Syntax.VMap l =>
      l = make_val_map l
      /\
      foldr
        (fun v acc =>
          PBoth fs_wfm_val v /\ acc)
        True
        l

  | _ => True
  end.



  Definition fs_wfm_valseq
    (vs : ValSeq)
    : Prop
    :=
  foldr (fun v acc => fs_wfm_val v /\ acc) True vs.



  Definition fs_wfm_exception
    (exc : CoreErlang.Syntax.Exception)
    : Prop
    :=
  match exc with
  | (excc, v1, v2) => fs_wfm_val v1 /\ fs_wfm_val v2
  end.



  Definition fs_wfm_result
    (res : Redex)
    : Prop
    :=
  match res with
  | RValSeq vs => fs_wfm_valseq vs
  | RExc exc => fs_wfm_exception exc
  | _ => True
  end.



End WellFormedMap.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: WELLFORMEDMAPLEMMASS /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






(**
* Help
  - map_insert_unfold
  - make_value_map_length
  - make_value_map_cons
  - map_insert_length_ge [NotUsing]
  - map_insert_length_le
  - make_val_map_length
  - make_val_map_cons
* Main
  - fs_wfm_vcons
  - fs_wfm_vtuple
  - fs_wfm_vmap
  - fs_wfm_val_to_result
  - fs_wfm_valseq_to_result
  - fs_wfm_exception_to_result
  - fs_wfm_val_to_forall
*)



(**
NOTES:  Later change lists to maps in Syntax
*)






Section WellFormedMapLemmas_Help.



  Lemma map_insert_unfold :
    forall k v kl vl,
      map_insert k v kl vl
    = match kl with
      | [] => match vl with
              | [] => ([k], [v])
              | _ :: _ => ([], [])
              end
      | k' :: ks =>
          match vl with
          | [] => ([], [])
          | v' :: vs =>
              if Value_ltb k k'
              then (k :: k' :: ks, v :: v' :: vs)
              else
               if Value_eqb k k'
               then (k' :: ks, v' :: vs)
               else (k' :: (map_insert k v ks vs).1, v' :: (map_insert k v ks vs).2)
          end
      end.
  Proof.
    (* #1 Destruct Trivial: intro/destruct/trivial *)
    itr.
    des - kl; des - vl :- trv.
  Qed.



  Lemma make_value_map_length :
    forall kvl vvl,
        Datatypes.length kvl = Datatypes.length vvl
    ->  Datatypes.length (make_value_map kvl vvl).1
      = Datatypes.length (make_value_map kvl vvl).2.
  Proof.
    (* #1 Destruct Lists: intro/destruct/inversion
        + simpl/congruence + subst/clear *)
    itr - kvl vvl Hlength.
    des - kvl as [| kv kvl];des - vvl as [| vv vvl]
       :- smp - Hlength; con + smp.
    ivc - Hlength as Hlength: H0.
    (* #2 Unfold Map_Insert: refold/rewrite *)
    rfl - make_value_map.
    rwr - map_insert_unfold.
    (* #3 Destruct Elements: destruct + trivial/simpl *)
    des > ((make_value_map kvl vvl).1); des > ((make_value_map kvl vvl).2).
    1-3: trv.
    des > (Value_ltb kv v); des > (Value_eqb kv v).
    1-3: smp; trv.
  Admitted.



  Lemma make_value_map_cons :
    forall kv kvl vv vvl mkvl mvvl,
        Datatypes.length kvl = Datatypes.length vvl
    ->  make_value_map (kv :: kvl) (vv :: vvl) = (mkvl, mvvl)
    ->  mkvl <> [] /\ mvvl <> [].
  Proof.
    (* #1 Unfold Map_Insert: intro/simpl/rewrite *)
    itr - kv kvl vv vvl mkvl mvvl Hlength Hmake.
    smp - Hmake.
    rwr - map_insert_unfold in Hmake.
    (* #2 Pose Length: pose + clear *)
    psc - make_value_map_length as Hlength_make: kvl vvl Hlength.
    (* #3 Destruct Maps: destruct
        + simpl/symmetry/apply/rewrite/inversion/subst/split/auto *)
    des > ((make_value_map kvl vvl).1).
    {
      smp - Hlength_make.
      sym - Hlength_make.
      app - length_zero_iff_nil as Hempty in Hlength_make.
      rwr - Hempty in *.
      ivs - Hmake.
      spl; ato.
    }
    des > ((make_value_map kvl vvl).2): ivs - Hlength_make.
    (* #4 Destuct Key Eq: destruct + inversion/subst/split/auto *)
    des > (Value_ltb kv v); des > (Value_eqb kv v); ivs - Hmake; spl; ato.
  Qed.



  Import SubstSemantics.



(** NOTES [NotUsing]
* FULL NAME:
  - Map Insert Length Greater or Equal
* OLD NAME:
  - map_insert_length1
* FUNCTION:
  - States that the length of a list with a 'map_insert'
    is greater than or equal to the length of the list
  - Meaning inserting in the list with 'map_insert'
    not necessary increases it's length
* USING:
  - library: le_n_S
  - project: map_insert
* USED AT:
  - /
* HISTORY:
  - First attempt to create a lemma which can be used to create a congruence
    at 'make_val_map_length'
* Proof:
  - induction ms; destruct each (k ? key); by le_n_S
  - Same as: map_insert_length_le
*)
  Theorem map_insert_length_ge :
    forall k v vl,
      length vl <= length (map_insert k v vl).
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (key, var) vl IHvl]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + simpl/lia *)
    des > (k <ᵥ key): sli.
    des > (k =ᵥ key): sli.
    bpp - le_n_S.
  Restart.
    intros.
    induction vl as [| (key, var) vl IHvl].
    * (* Case: vl is empty *)
      slia.
    * (* Inductive case: vl is (key, var) :: vl *)
      fold map_insert in *.
      simpl.
      destruct (k <ᵥ key).
      - (* Case: k <ᵥ key *)
        clear IHvl.
        slia.
      - destruct (k =ᵥ key).
        + (* Case: k =ᵥ key *)
          clear IHvl.
          slia.
        + (* Case: k >ᵥ key *)
          by apply le_n_S.
  Qed.



(** NOTES
* FULL NAME:
  - Map Insert Length Lesser or Equal
* OLD NAME:
  - map_insert_length2
* FUNCTION:
  - States that the length of a list with a 'map_insert'
    is lesser than or equal to the length of the list with an extra element
  - Meaning inserting in the list with 'map_insert'
    not necessary increases it's length
* USING:
  - library: le_n_S
  - project: map_insert
* USED AT:
  - make_val_map_length
* HISTORY:
  - First attempt to create a lemma which can be used to create a congruence
    at 'make_val_map_length'
* Proof:
  - induction ms; destruct each (k ? key); by le_n_S
  - Same as: map_insert_length_ge
*)
  Theorem map_insert_length_le :
    forall k k' v v' vl,
      length (map_insert k v vl) <= length ((k', v') :: vl).
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (key, var) vl IHvl]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + simpl/lia *)
    des > (k <ᵥ key): sli.
    des > (k =ᵥ key): sli.
    bpp - le_n_S.
  Restart.
    intros.
    induction vl as [| (key, var) vl IHvl].
    * (* Case: vl is empty *)
      slia.
    * (* Inductive case: vl is (key, var) :: vl *)
      fold map_insert in *.
      simpl.
      destruct (k <ᵥ key).
      - (* Case: k <ᵥ key *)
        clear IHvl.
        slia.
      - destruct (k =ᵥ key).
        + (* Case: k =ᵥ key *)
          clear IHvl.
          slia.
        + (* Case: k >ᵥ key *)
          by apply le_n_S.
  Qed.



  Theorem make_val_map_length :
    forall vl,
      length (make_val_map vl) <= length vl.
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr.
    ind - vl as [| (k, v) vl Hvl_cons]: sli |> smp.
    (* #2 Destruct Key: destruct/apply + apply/simpl *)
    des > (make_val_map vl) as [| (k', v') vl']: app - le_n_S |> smp.
    des > (k <ᵥ k'): smp *; app - le_n_S.
    des > (k =ᵥ k'): smp *; app - le_S |> smp.
    app - le_n_S.
    (* #3 Transivity: pose/apply/exact *)
    pse - map_insert_length_le as Hvl_insert: k k' v v' vl'.
    epp - Nat.le_trans.
    * exa - Hvl_insert.
    * exa - Hvl_cons.
  Restart.
    induction vl as [| (k, v) vl IHvl].
    * (* Base case: vl is empty *)
      slia.
    * (* Inductive case: vl = (k, v) :: vl'*)
      simpl.
      destruct (make_val_map vl) as [| (k', v') vl'].
      - (* Case: make_val_map vl = [] *)
        by apply le_n_S.
      - (* Case: make_val_map vl = (k', v') :: vl' *)
        simpl.
        destruct (k <ᵥ k').
        + (* Case: k <ᵥ k' *)
          simpl in *.
          apply le_n_S.
          apply IHvl.
        + destruct (k =ᵥ k').
          ** (* Case: k =ᵥ k' *)
             simpl in *.
             apply le_S.
             apply IHvl.
          ** (* Case: k >ᵥ k' *)
             simpl.
             apply le_n_S.
             pose proof map_insert_length_le k k' v v' vl' as Hinsert.
             eapply Nat.le_trans.
             -- apply Hinsert.
             -- apply IHvl.
  Qed.



  Theorem make_val_map_cons :
    forall v1 v2 vl,
        (v1, v2) :: vl = make_val_map ((v1, v2) :: vl)
    ->  vl = make_val_map vl.
  Proof.
    (* #1 Destruct Make: intro/inversion/unfold/destruct + inversion *)
    itr - v1 v2 vl Hcons.
    ivc - Hcons as Hcons: H0.
    ufl - Maps.map_insert in Hcons.
    des > (make_val_map vl) as [| (v1', v2') vl'] Hmake: ivr - Hcons.
    (* #2 Destruct Key: destruct + inversion *)
    des > (v1 <ᵥ v1'): ivr - Hcons.
    des > (v1 =ᵥ v1') as Heq; ivc - Hcons.
    * (* #2.1 Insert Key Equals: pose/rewrite/simpl/lia *)
      pse - make_val_map_length as Hlen: vl'.
      cwr - Hmake in Hlen.
      smp - Hlen.
      sli.
    * (* #2.1 Insert Key Bigger: rewrite/congruence*)
      rwr - Val_eqb_refl in Heq.
      con.
  Restart.
    intros v1 v2 vl H.
    ivc - H as H: H1.
    unfold Maps.map_insert in H.
    destruct (make_val_map vl) as [| (v1', v2') vl'] eqn:Hmake.
    - (* Case: make_val_map vl = [] *)
      clear Hmake.
      by inv H.
    - (* Case: make_val_map vl = (v1', v2') :: vl' *)
      destruct (v1 <ᵥ v1') eqn:Hlt.
      + (* Case: v1 <ᵥ v1' *)
        clear Hmake Hlt.
        by inv H.
      + destruct (v1 =ᵥ v1') eqn:Heq.
        * (* Case: v1 =ᵥ k' *)
          clear Hlt Heq.
          inv H.
          pose proof make_val_map_length vl' as Hlength.
          rewrite Hmake in Hlength.
          simpl in Hlength.
          lia.
        * (* Case: v1 >ᵥ v1' *)
          clear Hmake Hlt.
          inv H.
          rewrite Val_eqb_refl in Heq.
          congruence.
  Qed.



End WellFormedMapLemmas_Help.






Section WellFormedMapLemmas_Main.



  Import SubstSemantics.



  Theorem fs_wfm_vcons :
    forall v1 v2,
        Forall fs_wfm_val [VCons v1 v2]
    ->  Forall fs_wfm_val [v1]
    /\  Forall fs_wfm_val [v2].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v1 v2 HForall.
    ivc - HForall as Hv1v2: H1 / H2.
    (* #2 Destruct & Split: destruct/split/auto *)
    des - Hv1v2 as [Hv1 Hv2].
    spl; ato.
  Restart.
    intros v1 v2 HForall.
    inv HForall.
    clear H2.
    destruct H1.
    ren - Hv1 Hv2: H H0.
    split.
    * apply Forall_cons.
      - exact Hv1.
      - apply Forall_nil.
    * apply Forall_cons.
      - unfold fs_wfm_val.
        exact Hv2.
      - apply Forall_nil.
  Qed.



  Theorem fs_wfm_vtuple :
    forall v vl,
        Forall fs_wfm_val [VTuple (v :: vl)]
    ->  Forall fs_wfm_val [v]
    /\  Forall fs_wfm_val [VTuple vl].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v vl HForall.
    ivc - HForall as Hvvl: H1 / H2.
    (* #2 Destruct & Split: destruct/split/auto *)
    des - Hvvl as [Hv Hvl].
    spl; ato.
  Restart.
    intros v vl Hvvl.
    inv Hvvl.
    clear H2.
    destruct H1.
    ren - Hv Hvl: H H0.
    split.
    * apply Forall_cons.
      - exact Hv.
      - apply Forall_nil.
    * apply Forall_cons.
      - unfold fs_wfm_val.
        exact Hvl.
      - apply Forall_nil.
  Qed.



  Theorem fs_wfm_vmap :
    forall v1 v2 vl,
        Forall fs_wfm_val [VMap ((v1, v2) :: vl)]
    ->  Forall fs_wfm_val [v1]
    /\  Forall fs_wfm_val [v2]
    /\  Forall fs_wfm_val [VMap vl].
  Proof.
    (* #1 Destruct Foralls: intro/inversion *)
    itr - v1 v2 vl HForall.
    ivc - HForall as Hv1v2vl: H1 / H2.
    (* #2 Destruct & Split: destruct/split/constructor/auto *)
    des - Hv1v2vl as [Hmake [[Hv1 Hv2] Hvl]].
    do 4 (spl + cns; ato).
    (* #3 Prove Eqvivalence by Lemma: clear/pose *)
    clr - Hv1 Hv2 Hvl.
    bse - make_val_map_cons: v1 v2 vl Hmake.
  Restart.
    intros v1 v2 vl Hv1v2vl.
    inv Hv1v2vl.
    clear H2.
    destruct H1 as [Hmake H].
    ivc - H as Hvl: H1.
    ivc - H0 as Hv1 Hv2: H H1.
    smp - Hv1 Hv2.
    split.
    - clear Hmake Hvl Hv2.
      apply Forall_cons.
      + exact Hv1.
      + apply Forall_nil.
    - clear Hv1.
      split.
      + clear Hmake Hvl.
        apply Forall_cons. 
        * exact Hv2.
        * apply Forall_nil.
      + clear Hv2.
        apply Forall_cons.
        * unfold fs_wfm_val.
          split. 2: { exact Hvl. }
          clear Hvl.
          by pose proof make_val_map_cons v1 v2 vl Hmake.
       * apply Forall_nil.
  Qed.



  Lemma fs_wfm_val_to_result :
    forall v,
      fs_wfm_val v
  ->  fs_wfm_result (RValSeq [v]).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma fs_wfm_valseq_to_result :
    forall vs,
      fs_wfm_valseq vs
  ->  fs_wfm_result (RValSeq vs).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma fs_wfm_exception_to_result :
    forall exc,
      fs_wfm_exception exc
  ->  fs_wfm_result (RExc exc).
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



  Lemma fs_wfm_val_to_forall :
    forall v,
      fs_wfm_val v
  ->  Forall fs_wfm_val [v].
  Proof.
    (* #1 Auto: intro/cbn/auto *)
    itr; abn.
  Qed.



End WellFormedMapLemmas_Main.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ENVIRONMENTDEFINITIONS ///////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Import BigStep.



(**
* Help
  - rem_keys
* Main
  - rem_vars
  - rem_fids
  - rem_fid
  - rem_both
  - rem_nfifes
*)



(**
NOTES:  Maybe place this in BigStep/Environment
*)






Section EnvironmentDefinitions_Help.



  Definition rem_keys
    (keys : list (Var + FunctionIdentifier))
    (env : Environment)
    : Environment
    :=
    filter
      (fun '(k, v) =>
        negb (existsb
          (fun x => (var_funid_eqb x k))
          keys))
      env.



End EnvironmentDefinitions_Help.






Section EnvironmentDefinitions_Main.



  Definition rem_vars
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inl vars) env.



  Definition rem_fids
    (fids : list FunctionIdentifier)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr fids) env.



  Definition rem_exp_ext_fids
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map fst ext) env.



  Definition rem_val_ext_fids
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map (snd ∘ fst) ext) env.



  Definition rem_exp_ext_both
    (vars : list Var)
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_exp_ext_fids ext (rem_vars vars env).



  Definition rem_val_ext_both
    (vars : list Var)
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_val_ext_fids ext (rem_vars vars env).



(*
  Definition rem_val_ext_fids
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map (snd ∘ fst) ext) env.



  Definition rem_exp_ext
    (ext : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map fst ext) ().



  Definition rem_val_ext_fids
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map (snd ∘ fst) ext) env.











  Definition rem_fid
    (fid : FunctionIdentifier)
    (env : Environment)
    : Environment
    :=
  rem_keys [(inr fid)] env.



  Definition rem_fids
    (fids : list (FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr (map fst fids)) env.



  Definition rem_both
    (fids : list (FunctionIdentifier * FunctionExpression))
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_fids fids (rem_vars vars env).



  Definition rem_nfifes
    (nfifes : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr (map snd (map fst nfifes))) env.
*)


End EnvironmentDefinitions_Main.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ENVIRONMENTLEMMAS ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - Get
    + get_value_cons
  - Remove [NotUsing]
    + rem_keys_empty_env [NotUsing]
    + rem_vars_empty [NotUsing]
    + rem_fids_empty [NotUsing]
    + rem_both_empty [NotUsing]
    + rem_nfifes_empty [NotUsing]
    + rem_both_empty_map [NotUsing]
    + rem_keys_empty_keys
* Main
  - Get
    + can_get_value_than_in
    + get_value_singleton
    + get_value_singleton_length
  - Remove
    + rem_keys_cons_env
*)



(**
NOTES:  Maybe place this in BigStep/Environment
*)






Section EnvironmentLemmas_Help.



  Section EnvironmentLemmas_Help_Get.

    Lemma get_value_cons :
      forall env key k var v,
          get_value ((k, v) :: env) key = Some [var]
      ->  get_value [(k, v)] key = Some [var] 
      \/  get_value env key = Some [var].
    Proof.
      (* #1 Destruct Key Equality: intro/simpl/destruct/auto *)
      itr - env key k var v Hcons.
      smp *.
      des > (var_funid_eqb key k) as Heqb_key; ato.
    Restart.
      intros env key k var v Hcons.
      unfold get_value in Hcons.
      remember
        (var_funid_eqb key k)
        as _key_eqb.
      symmetry in Heq_key_eqb.
      destruct _key_eqb.
      * left.
        clear env.
        inv Hcons.
        unfold var_funid_eqb in Heq_key_eqb.
        destruct key.
        - destruct k.
          + cbn.
            rewrite Heq_key_eqb.
            reflexivity.
          + congruence.
        - destruct k.
          + congruence.
          + cbn.
            rewrite Heq_key_eqb.
            reflexivity.
      * right.
        exact Hcons.
    Qed.

  End EnvironmentLemmas_Help_Get.



  Section EnvironmentLemmas_Help_Remove.



  Lemma filter_unfold :
    forall A (f : A -> bool) al,
      filter f al
    = match al with
      | [] => []
      | a :: al' => if f a then a :: filter f al' else filter f al'
      end.
  Proof.
    itr.
    des - al; trv.
  Qed.



  Lemma filter_comm :
    forall A (f g : A -> bool) al,
      filter f (filter g al)
    = filter g (filter f al).
  Proof.
    (* #1 Induction: intro/induction + simpl *)
    itr.
    ind - al as [| a al IHal] :> smp.
    (* #2 Pose Unfold Filter: pose*)
    pse - filter_unfold as Hfg: A f (a :: filter g al);
    pse - filter_unfold as Hgf: A g (a :: filter f al).
    (* #3 Destruct & Rewrite: destruct/rewrite *)
    des > (f a) as Hf;
    des > (g a) as Hg :>
      try rwr - Hfg Hf;
      try rwr - Hgf Hg;
      rwr - IHal.
  Qed.



  Lemma rem_keys_comm :
    forall keys1 keys2 env,
      rem_keys keys1 (rem_keys keys2 env)
    = rem_keys keys2 (rem_keys keys1 env).
  Proof.
    (* #1 By Filter Comm: intro/unfold/rewrite *)
    itr.
    ufl - rem_keys.
    bwr - filter_comm.
  Qed.



(*
    Lemma rem_keys_empty_env :
      forall keys,
        rem_keys keys [] = [].
    Proof.
      (* #1 Induction on Keys: intro/unfold/induction/auto *)
      itr.
      ufl - rem_keys.
      ind - keys; ato.
    Restart.
      intros.
      unfold rem_keys.
      (* induction keys.
      * by cbn.
      * cbn.
        by rewrite IHkeys. *)
      induction keys; by cbn.
    Qed.

    Lemma rem_vars_empty :
      forall vars,
        rem_vars vars [] = [].
    Proof.
      (* #1 Unfold & Rewrite: intro/unfold/rewrite *)
      itr.
      ufl - rem_vars.
      bwr - rem_keys_empty_env.
    Restart.
      intros.
      unfold rem_vars.
      by rewrite rem_keys_empty_env.
    Qed.

    Lemma rem_fids_empty :
      forall fids,
        rem_fids fids [] = [].
    Proof.
      (* #1 Unfold & Rewrite: intro/unfold/rewrite *)
      itr.
      ufl - rem_fids.
      bwr - rem_keys_empty_env.
    Restart.
      intros.
      unfold rem_fids.
      by rewrite rem_keys_empty_env.
    Qed.

    Lemma rem_both_empty :
      forall fids vars,
        rem_both fids vars [] = [].
    Proof.
      (* #1 Unfold & Rewrite: intro/unfold/rewrite *)
      itr.
      ufl - rem_both.
      bwr - rem_vars_empty rem_fids_empty.
    Restart.
      intros.
      unfold rem_both.
      rewrite rem_vars_empty.
      rewrite rem_fids_empty.
      reflexivity.
    Qed.

    Lemma rem_nfifes_empty :
      forall ext,
        rem_nfifes ext [] = [].
    Proof.
      (* #1 Unfold & Rewrite: intro/unfold/rewrite *)
      itr.
      ufl - rem_nfifes.
      bwr - rem_keys_empty_env.
    Restart.
      intros.
      unfold rem_nfifes.
      by rewrite rem_keys_empty_env.
    Qed.

    Lemma rem_both_empty_map :
      forall (f : Environment -> Expression -> Expression) el,
        map
          (fun  '(fid, (vl, b)) =>
            (fid, (vl, f (rem_both el vl []) b)))
          el
      = map
          (fun '(fid, (vl, b)) =>
            (fid, (vl, f [] b)))
          el.
    Proof.
      (* #1 Apply & Rewrite: intro/apply/rewrite *)
      itr.
      app - map_ext.
      intros [fid [vl b]].
      bwr - rem_both_empty.
    Restart.
      intros.
      apply map_ext.
      intros [fid [vl b]].
      by rewrite rem_both_empty.
    Qed.

    Lemma rem_keys_empty_keys :
      forall env,
        rem_keys [] env = env.
    Proof.
      (* #1 Induction on Environment: induction + simpl*)
      ind - env as [| [k v] env IHenv] :> smp.
      (* #2 Rewrite by Induction: rewrite *)
      bwr - IHenv.
    Qed.
*)
  End EnvironmentLemmas_Help_Remove.



End EnvironmentLemmas_Help.






Section EnvironmentLemmas_Main.



  Section EnvironmentLemmas_Main_Get.

    Theorem get_value_in :
      forall env key var,
          get_value env key = Some [var]
      ->  In (key , var) env.
    Proof.
      (* #1 Induction on Environment: intro/induction + intro/inversion *)
      itr - env.
      ind - env as [| [k v] env IHenv] :> itr - key var Hget :- ivc - Hget.
      (* #2 Destruct Get_Value: apply/destruct *)
      app - get_value_cons in Hget.
      des - Hget as [Hget | Hget].
      * (* #3.1 Destruct Key Equality: clear/simpl/destruct + congruence *)
        clr - IHenv.
        smp *.
        des > (var_funid_eqb key k) as Hkey :- con.
        (* #4.1 Rewrite Var & FunId: left/inversion/apply/rewrite *)
        lft.
        ivc - Hget.
        app - var_funid_eqb_eq in Hkey.
        bwr - Hkey.
      * (* #3.2 Pose In_Cons: specialize/pose *)
        spc - IHenv: key var Hget.
        by pose proof in_cons (k, v) (key, var) env IHenv.
    Restart.
      intros env.
      induction env; intros key var Hget_value.
      * inv Hget_value.
      * destruct a as [k v].
        apply get_value_cons in Hget_value.
        destruct Hget_value.
        - clear IHenv.
          rename H into Hget_value.
          unfold get_value in Hget_value.
          remember
            (var_funid_eqb key k)
            as key_eqb
            eqn:Heq_key_eqb.
          symmetry in Heq_key_eqb.
          destruct key_eqb.
          + inv Hget_value.
            apply var_funid_eqb_eq in Heq_key_eqb.
            rewrite <- Heq_key_eqb.
            clear Heq_key_eqb k.
            constructor.
            clear env.
            reflexivity.
          + clear Heq_key_eqb.
            congruence.
        - rename H into Hget_value.
          specialize (IHenv key var Hget_value).
          pose proof in_cons (k, v) (key, var) env IHenv.
          clear IHenv Hget_value.
          assumption.
    Qed.

    Lemma get_value_singleton :
      forall env key vs,
          get_value env key = Some vs
      ->  exists value, vs = [value].
    Proof.
      (* #1 Induction on Environment: intro/induction + intro/simpl/congruence*)
      itr - env key vs.
      ind - env as [| [k v] env IHenv] :> itr - Hget; smp - Hget :- con.
      (* #2 Destruct Key Equality: destruct + apply *)
      des > (var_funid_eqb key k) as Hkey :- app - IHenv.
      (* #3 Exists Value: exists/inversion *)
      exi - v.
      bvs - Hget.
    Restart.
      intros env key vs.
       induction env as [| [k v] env IHenv]; intros Hget; cbn in Hget.
       * congruence.
       * destruct (var_funid_eqb key k) eqn:Heqb.
         - exists v.
           by inv Hget.
         - by apply IHenv.
    Qed.

    Lemma get_value_singleton_length :
      forall env key l,
          get_value env key = Some l
      ->  length l = 1.
    Proof.
      (* #1 Pose by Previous: intro/pose/inversion *)
      itr - env key vs Hget.
      pse - get_value_singleton as Hsingl: env key vs Hget.
      bvs - Hsingl.
    Restart.
      intros env key vs Hget.
      pose proof get_value_singelton env key vs Hget as Hsingelton.
      bvs - Hsingelton.
    Qed.

  End EnvironmentLemmas_Main_Get.



  Section EnvironmentLemmas_Main_Remove.

    Lemma rem_keys_cons_env :
      forall keys k v env env',
          env' = rem_keys keys ((k, v) :: env)
      ->  env' = rem_keys keys env
      \/  env' = (k, v) :: rem_keys keys env.
    Proof.
      (* #1 Simplify: intro/simple *)
      itr - keys k v env env' Hcons.
      smp *.
      (* #2 Destruct Exists: destruct/right/left *)
      des >
        (negb
          (existsb (λ x : Var + FunctionIdentifier, var_funid_eqb x k) keys)).
      * by rgt.
      * by lft.
    Qed.

  End EnvironmentLemmas_Main_Remove.



End EnvironmentLemmas_Main.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SCOPINGLEMMAS ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Import SubstSemantics.



(**
* ScopingLemmas
  - scope_vl_succ
  - scope_vl_succ_id
  - scope_cons
*)



(**
NOTES:  Maybe place this in CoreFrameStack/Scoping! or into FrameStack
*)






Section ScopingLemmas_Help.



  Theorem scope_vl_succ :
    forall A i vl (f : A -> Val),
          (i < length vl
      ->  VALCLOSED (nth i (map f vl) VNil))
    ->    (S i < S (length vl)
      ->  VALCLOSED (nth i (map f vl) VNil)).
  Proof.
    (* #1 Pose: intro/pose/destruct/ *)
    itr - A i vl f Hvl Hsucc_lt.
    pse - Nat.succ_lt_mono as Hmono_succ_lt: i (base.length vl).
    des - Hmono_succ_lt as [_ Hfrom_succ_lt].
    (* #2 Apply: apply *)
    app - Hfrom_succ_lt in Hsucc_lt as Hlt; clr - Hfrom_succ_lt.
    bpp - Hvl in Hlt.
  Restart.
    intros A i vl f Hvl.
    intros Hsucc_lt.
    pose proof Nat.succ_lt_mono 
      as Hmono_succ_lt.
    specialize (Hmono_succ_lt i (base.length vl)).
    destruct Hmono_succ_lt
      as [Hto_succ_lt Hfrom_succ_lt].
    clear Hto_succ_lt.
    apply Hfrom_succ_lt
      in Hsucc_lt 
      as Hlt.
    clear Hfrom_succ_lt Hsucc_lt.
    apply Hvl in Hlt.
    clear Hvl.
    rename Hlt into Hvl.
    exact Hvl.
  Qed.



  Theorem scope_vl_succ_id :
    forall i vl,
          (i < length vl
      ->  VALCLOSED (nth i vl VNil))
    ->    (S i < S (length vl)
      ->  VALCLOSED (nth i vl VNil)).
  Proof.
    (* #1 Assert: intro/assert/remember + apply *)
    itr - i vl Hvl.
    ass > (map id vl = vl) as Hid: apply Basics.map_id.
    rem - n as Hn: (base.length vl).
    (* #2 Rewrite: rewrite *)
    cwl + Hid in Hvl.
    cwr - Hn in *.
    (* #3 Pose by Previus: pose *)
    by pose proof scope_vl_succ Val i vl id Hvl.
  Restart.
    intros i vl Hvl.
    assert (map id vl = vl).
    {
      apply Basics.map_id.
    }
    remember
      (base.length vl)
      as _n.
    rewrite <- H.
    rewrite <- H in Hvl.
    rewrite Heq_n in *.
    clear Heq_n _n H.
    pose proof scope_vl_succ Val i vl id Hvl.
    assumption.
  Qed.



End ScopingLemmas_Help.






Section ScopingLemmas_Main.



  Theorem scope_cons :
    forall v1 v2,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VCons v1 v2]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 Hv1 Hv2.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    des_for - Hv1 Hv2: H3 H1.
    (* #2 Finish: pose *)
    ato.
  Qed.



  Theorem scope_tuple :
    forall v vl,
        is_result (RValSeq [v])
    ->  is_result (RValSeq [VTuple vl])
    ->  is_result (RValSeq [VTuple (v :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v vl Hv Hvl.
    ivc - Hv as Hv: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv Hvl: H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    (* #4 Simplify: intro/simpl *)
    itr - i Hl.
    smp *.
    (* #5 Destruct: destruct + exact *)
    des - i: exa - Hv.
    (* #6 Inversion: inversion *)
    ivc - Hvl as Hvl: H1 / v Hv.
    (* #7 Finish: pose *)
    bse - scope_vl_succ_id: i vl (Hvl i) Hl.
  Qed.



  Theorem scope_map :
    forall v1 v2 vl,
        is_result (RValSeq [v1])
    ->  is_result (RValSeq [v2])
    ->  is_result (RValSeq [VMap vl])
    ->  is_result (RValSeq [VMap ((v1, v2) :: vl)]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - v1 v2 vl Hv1 Hv2 Hvl.
    ivc - Hv1 as Hv1: H0.
    ivc - Hv2 as Hv2: H0.
    ivc - Hvl as Hvl: H0.
    des_for - Hv1 Hv2 Hvl: H5 H3 H1.
    (* #3 Constructor: constructor *)
    do 3 cns.
    * (* #4.1 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.1 Destruct: clear/destruct + exact *)
      clr - Hv2 v2.
      des - i: exa - Hv1.
      (* #6.1 Inversion: inversion *)
      ivc - Hvl as Hvl: H0 / H2 v1 Hv1.
      (* #7.1 Finish: pose *)
      by pose proof scope_vl_succ (Val * Val) i vl fst (Hvl i) Hl.
    * (* #4.2 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.2 Destruct: clear/destruct + exact *)
      clr - Hv1 v1.
      des - i: exa - Hv2.
      (* #6.2 Inversion: inversion *)
      ivc - Hvl as Hvl: H2 / H0 v2 Hv2.
      (* #7.2 Finish: pose *)
      by pose proof scope_vl_succ (Val * Val) i vl snd (Hvl i) Hl.
  Qed.



End ScopingLemmas_Main.






(* Section ScopingLemmas_Tactics. *)



Ltac scope_solver_triv :=
  constructor;
  solve [scope_solver].



Ltac scope_solver_by H1 :=
  solve [exact H1].



Ltac scope_solver_cons v1 v2 Hresult_v1 Hresult_v2 :=
  pose proof scope_cons v1 v2 Hresult_v1 Hresult_v2;
  solve [auto].



Ltac scope_solver_tuple v vl Hresult_v Hresult_vl :=
  pose proof scope_tuple v vl Hresult_v Hresult_vl;
  solve [auto].



Ltac scope_solver_map v1 v2 vl Hresult_v1 Hresult_v2 Hresult_vl :=
  pose proof scope_map v1 v2 vl Hresult_v1 Hresult_v2 Hresult_vl;
  solve [auto].






Tactic Notation "framestack_scope"
  :=
  eexists;
  split;
  [ scope_solver_triv
  | idtac ].



Tactic Notation "framestack_scope"
  "-"   ident(I1)
  :=
  eexists;
  split;
  [ scope_solver_by I1
  | clear I1].



Tactic Notation "framestack_scope"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  eexists;
  split;
  [ (scope_solver_cons I1 I2 I3 I4
  + scope_solver_tuple I1 I2 I3 I4)
  | clear I3 I4].



Tactic Notation "framestack_scope"
  "-"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5) ident(I6)
  :=
  eexists;
  split;
  [ scope_solver_map I1 I2 I3 I4 I5 I6
  | clear I4 I5 I6].



(* End ScopingLemmas_Tactics. *)














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: FRAMESTACKLEMMAS /////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* FrameStackLemmas
  - framestack_ident
  - framestack_ident_rev [Admitted]
*)



(**
Note: Maybe place this into CoreErlang.FrameStack/SubstSemanticsLemmas
*)


Section FrameStackLemmas.



  Theorem framestack_ident :
    forall ident el r vl v' vl' eff Fs,
        create_result ident (vl' ++ v' :: vl) [] = Some (r , eff)
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' el :: Fs, RValSeq [v'] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - r vl v' vl' eff Fs Hcreate Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
      (* #3.1 Exact: symmetry/exact *)
      sym.
      exa - Hcreate.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      cwr - Hrewrite in Hcreate.
      spc - Hfs_vl: r vl v (vl' ++ [v']) eff Fs Hcreate Hbiforall.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 Constructor: exists/constructor *)
      eei.
      (* #5.2 Do Step: fs_transitive/exact *)
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
  Restart.
    intros ident el.
    induction el; intros r vl v' vl' eff Fs Hcreate Hbiforall.
    * inv Hbiforall.
      exists 1.
      econstructor.
      econstructor.
      by symmetry.
      constructor.
    * inv Hbiforall.
      rename H3 into Hbiforall.
      destruct H1 as [khd [Hhd Dhd]].
      replace
        (vl' ++ v' :: hd' :: tl') with
        ((vl' ++ [v']) ++ hd' :: tl') 
        in Hcreate.
      2:
      {
        rewrite <- app_assoc.
        by rewrite <- app_cons_swap.
      }
      specialize (IHel r tl' hd' (vl' ++ [v']) eff Fs Hcreate Hbiforall).
      destruct IHel as [kIH DIH].
      eexists.
      econstructor.
      constructor.
      eapply transitive_eval.
      eapply frame_indep_core in Dhd. 
      exact Dhd.
      simpl.
      exact DIH.
  Qed.


  (* For tuple exception *)
  Theorem framestack_ident_partial :
    forall ident el e' el' vl v' vl' Fs,
        list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ident vl' (el ++ e' :: el') :: Fs, RValSeq [v'] ⟩ -[ k ]->
          ⟨ FParams ident (vl' ++ v' :: vl) el' :: Fs, RExp e' ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - e' el' vl v' vl' Fs Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      spc - Hfs_vl: e' el' vl v (vl' ++ [v']) Fs Hbiforall.
      cwl - Hrewrite in Hfs_vl.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 Constructor: exists/constructor *)
      eei.
      (* #5.2 Do Step: fs_transitive/exact *)
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
  Qed.



  (*Not Using*)
  Theorem framestack_ident_tuple :
    forall el r vl v' vl' Fs,
        r = RValSeq [Syntax.VTuple (vl' ++ v' :: vl)]
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  exists k,
          ⟨ FParams ITuple vl' el :: Fs, RValSeq [v'] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - el.
    ind - el as [| e el Hfs_vl];
      itr - r vl v' vl' Fs Hresult Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
      (* #3.1 Simplify: simpl *)
      bmp.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      cwr - Hrewrite.
      specialize (Hfs_vl
        (RValSeq [VTuple ((vl' ++ [v']) ++ v :: vl)])
        vl v (vl' ++ [v']) Fs eq_refl Hbiforall);
        clr - Hbiforall.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      (* #4.2 Constructor: exists/constructor *)
      eei.
      (* #5.2 Do Step: fs_transitive/exact *)
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
    Qed.



  (*Not Using*)
  Theorem framestack_ident_map :
    forall el r vl v' vl' Fs,
        vl = make_val_map vl
    ->  r = RValSeq [Syntax.VMap
          (make_val_map
            (deflatten_list ((flatten_list vl') ++ v' :: (flatten_list vl))))]
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e.1 ⟩ -->* RValSeq [v.1]
                  /\  ⟨ [] , RExp e.2 ⟩ -->* RValSeq [v.2])
          el
          vl
    ->  exists k,
          ⟨ FParams IMap (flatten_list vl') (flatten_list el) :: Fs,
              RValSeq [v'] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction *)
    itr - el.
    ind - el as [| e el Hfs_vl];
      itr - r vl v' vl' Fs Heq_map Hresult Hbiforall; ivc - Hbiforall.
    * (* #2.1 Constructor: exists/constructor *)
      eei.
      do 2 ens.
      (* #3.1 Simplify: simpl *)
      bmp.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      des - Hfs_v as [Hfs_v1 Hfs_v2].
      des - e as [e1 e2].
      des - v as [v1 v2].
      smp - Hfs_v1 Hfs_v2.
      admit.
    Admitted.



  (*NotUsing*) (* Depricate*)
  Theorem framestack_ident_rt :
    forall ident el r vl v' vl' eff,
        create_result ident (vl' ++ v' :: vl) [] = Some (r , eff)
    ->  list_biforall
          (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v])
          el
          vl
    ->  is_result r
    ->  ⟨ [FParams ident vl' el], RValSeq [v'] ⟩ -->* r.
  Proof.
    (* #1 Induction: intro/generalize/revert/induction/inversion *)
    itr - ident el.
    ind - el as [| e el Hfs_vl];
      itr - r vl v' vl' eff Hcreate Hbiforall Hresult; ivc - Hbiforall.
    * (* #2.1 Scope: exists/split/scope_solver *)
      framestack_scope - Hresult.
      (* #3.1 Step: constructor/symmetry/exact *)
      do 2 ens.
      sym.
      exa - Hcreate.
    * (* #2.2 Specialize: rename/assert/rewrite/specialize *)
      ren - v vl Hfs_v Hbiforall: hd' tl' H1 H3.
      ass > ((vl' ++ v' :: v :: vl) = ((vl' ++ [v']) ++ v :: vl))
        as Hrewrite: rwl - app_assoc; by rewrite <- app_cons_swap.
      cwr - Hrewrite in Hcreate.
      spc - Hfs_vl: r vl v (vl' ++ [v']) eff Hcreate Hbiforall Hresult.
      (* #3.2 Destruct: destruct *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl [Hresult_vl Hstep_vl]].
      (* #4.2 Scope: exists/split/scope_solver *)
      framestack_scope - Hresult_vl.
      (* #5.1 Step: constructor/framestack_step *)
      framestack_step - Hstep_v / kv.
      framestack_step - Hstep_vl.
  Qed.



  (* ! ident only can be ITuple/IMap/IValues *)
  Theorem framestack_ident_rev :
    forall el ident vl' e' k r,
        ⟨ [FParams ident vl' el], RExp e' ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
    ->  exists v' vl eff,
            create_result ident (vl' ++ v' :: vl) [] = Some (RValSeq r, eff)
        /\  list_biforall
              (fun (e0 : Exp) (v : Val) => ⟨ [], RExp e0 ⟩ -->* RValSeq [v])
              (e' :: el)
              (v' :: vl).
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



  (* Maybe new version*)
  (*NotUsing*)
  Theorem framestack_ident_rev2 :
    forall ident el e' r vl v' vl' eff k,
        create_result ident (vl' ++ v' :: vl) [] = Some (RValSeq r, eff)
    ->  ⟨ [FParams ident vl' el], RExp e' ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
    ->  list_biforall
          (fun (e : Exp) (v : Val) => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (e' :: el)
          (v' :: vl).
  Proof.
    itr - ident el e' r vl v' vl' eff k Hcreate Hstep.
    des - ident; ivc - Hcreate.
    * cns.
      admit.
      admit.
    * (* ivc - Hstep as Hstep1 Hstep2: H H0. *)
  Admitted.



  (*NotUsing*) (*Depricate*)
  Theorem framestack_ident_rev3 :
    forall el ident vl e r,
        ⟨ [FParams ident vl el], RExp e ⟩ -->* RValSeq r
    ->  exists v vl' eff,
            create_result ident (vl ++ v :: vl') [] = Some (RValSeq r, eff)
        /\  list_biforall
              (λ (e0 : Exp) (v : Val), ⟨ [], RExp e0 ⟩ -->* RValSeq [v])
              (e :: el)
              (v :: vl').
  Proof.
    ind - el as [|e' el IHel]; itr - ident vl e r Hstp.
    * pse - term_eval as Heval.
      pse - terminates_in_k_eq_terminates_in_k_sem as Hterm.
      ufl - terminates_in_k_sem in Hterm.
      des - Hstp as [k [Hres Hstp]].
      pose proof conj Hres Hstp as Hcon; clr - Hstp.
      apply ex_intro with (x := RValSeq r) in Hcon.
      app - Hterm in Hcon.
      app - Heval in Hcon.
      2: adm.
      des - Hcon as [v [kv [Hres_v [Hstp_v Hle_k]]]].
      ivc - Hres_v.
      adm.
  Admitted.

(*
  Theorem ident_reverse :
    forall el e' vl' v' vl ident k r eff,
        ⟨ [FParams ident vl' el], RExp e' ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
    ->  ident = ITuple \/ ident = IMap
    ->  create_result ident (vl' ++ v' :: vl) [] = Some (RValSeq r, eff)
    ->  list_biforall
          (fun (e : Exp) (v : Val) => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (e' :: el)
          (v' :: vl).
  Proof.
    ind - el; itr - e' vl' v' vl ident k r eff Hstep Hident Hcreate.
    * des - Hident; cwr - H in *; ivc - Hcreate.
      - admit.
      - admit.
    * des - Hident; cwr - H in *; ivc - Hcreate.
      - admit.
      - admit.
  Admitted.
*)

(*
Theorem tmp :
  forall v,
    ⟨ [], ˝ v ⟩ -->* RValSeq [v].
Proof.
  ind - v.
  * ens; spl.
    1: do 3 cns.
    step.
  * ens; spl.
    1: do 3 cns.
    step.
  * ens; spl.
    1: do 3 cns.
    step.
  * ivc - IHv1 as kv1: x.
    des - H as [Hscope_v1 Hstep_v1].
    ivc - Hscope_v1 as Hscope_v1: H0.
    ivc - Hscope_v1 as Hscope_v1: H1 / H2.
    ivc - IHv2 as kv2: x.
    des - H as [Hscope_v2 Hstep_v2].
    ivc - Hscope_v2 as Hscope_v2: H0.
    ivc - Hscope_v2 as Hscope_v2: H1 / H2.
    ens; spl; do 3 ens; asm.
  * ind - l.
    - scope.
      step.
      itr; smp - H; ivs - H.
    - admit.
  * admit.
  * ens; spl.
    1: do 3 cns; adm.
    step; adm.
  * ens; spl.
    1: do 3 cns; adm.
    step; adm.
  * ens; spl.
    1: do 3 cns; adm.
    step; adm.
  Admitted.
*)


End FrameStackLemmas.














(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MEASURE //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Import BigStep.



(**
* Help
  - Generic
    + measure_list
    + measure_map
  - Expression
    + measure_case
    + measure_letrec
  - Value
    + measure_env
* Main
  - measure_exp
  - measure_val
  - measure_env_exp
*)






Section Measure_Help.



  Section Measure_Help_Generic.

    Definition measure_list
      {A : Type}
      (measure : A -> nat)
      (al : list A)
      : nat 
      :=
    list_sum (map measure al).

    Definition measure_map
      {A : Type}
      (measure : A -> nat)
      (apl : list (A * A))
      : nat
      :=
    list_sum (map (fun '(a1, a2) => (measure a1) + (measure a2)) apl).

    Definition is_none
      {A : Type}
      (ao : option A)
      : bool 
      :=
    match ao with
    | Some _ => false
    | None => true
    end.

  End Measure_Help_Generic.



  Section Measure_Help_Expression.

    Definition measure_exp_case
      (measure_exp : Expression -> nat)
      (peel : list ((list Pattern) * Expression * Expression))
      : nat
      :=
    list_sum (map (fun '(pl, g, b) => (measure_exp g) + (measure_exp b)) peel).

    Definition measure_exp_ext
      {A : Type}
      (measure_exp : Expression -> nat)
      (ext : list (A * FunctionExpression))
      : nat
      :=
    list_sum (map (measure_exp ∘ snd ∘ snd) ext).

  End Measure_Help_Expression.



  Section Measure_Help_Value.

    Definition measure_val_env
      (measure_val : Value -> nat)
      (env : Environment)
      : nat
      :=
    list_sum (map (measure_val ∘ snd) env).

  End Measure_Help_Value.



End Measure_Help.






Section Measure_Main.



  Fixpoint measure_exp
    (e : Expression)
    : nat
    :=
  match e with
  | ENil => 1
  | ELit l => 1
  | EVar v => 1
  | EFunId f => 1

  | EFun vl e => 1
      + measure_exp e

  | ECons hd tl => 1
      + measure_exp hd
      + measure_exp tl

  | ESeq e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ELet l e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ETry e1 vl1 e2 vl2 e3 => 1
      + measure_exp e1
      + measure_exp e2
      + measure_exp e3

  | EValues el => 1
      + measure_list measure_exp el

  | EPrimOp f l => 1
      + measure_list measure_exp l

  | ETuple l => 1
      + measure_list measure_exp l

  | EMap l =>  1
      + measure_map measure_exp l

  | EApp exp l => 1
      + measure_exp exp
      + measure_list measure_exp l

  | ECall m f l => 1
      + measure_exp m
      + measure_exp f
      + measure_list measure_exp l

  | ECase e l => 1
      + measure_exp e
      + measure_exp_case measure_exp l

  | ELetRec l e => 1
      + measure_exp e
      + measure_exp_ext measure_exp l
  end.



  Fixpoint measure_val
    (v : Value) 
    : nat
    :=
  match v with
  | VNil => 1
  | VLit l => 1

  | VCons hd tl => 1
      + measure_val hd
      + measure_val tl

  | VTuple l => 1
      + measure_list measure_val l

  | VMap l => 1
      + measure_map measure_val l

  | VClos env ext id vl e fid => 1
      + (if   Nat.eqb (measure_exp_ext measure_exp ext) 0 || is_none fid
        then  measure_exp e
        else  measure_exp_ext measure_exp ext)
      + measure_val_env measure_val env
  end.



  Definition measure_env
    (env : Environment)
    : nat
    :=
  list_sum (map (measure_val ∘ snd) env).



  Definition measure_env_exp
    (env : Environment)
    (e : Expression)
    : nat
    :=
  measure_exp e
  + measure_env env.



End Measure_Main.