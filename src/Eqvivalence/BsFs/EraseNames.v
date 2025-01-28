From CoreErlang.Eqvivalence Require Export Basics.

Import BigStep.

(** CONTENT:
* MEASURE_VALUE (DEFINITIONS)
  - MeasureValue
    + measure_val_list
    + measure_val_map
    + measure_val_env
    + measure_val
* REMOVE_FROM_ENVIRONMENT (DEFINITIONS)
  - RemoveFromEnvironment
    + rem_keys
    + rem_fids
    + rem_vars
    + rem_ext
    + rem_ext_vars
* ADD_TO_ERASER (DEFINITIONS)
  - AddToEraser_Helpers
    + convert_lit
    + vars_of_pattern_list
    + sum_eqb
  - AddToEraser_Types
    + NameSub
    + Eraser
  - AddToEraser_Functions
    + add_name
    + add_names
    + add_keys
    + add_fids
    + add_vars
    + add_ext
    + add_ext_vars
    + add_expext
    + add_expext_vars
    + add_pats
* ERASE_NAMES (DEFINITIONS)
  - EraseNames
    + erase_pat
    + erase_exp
    + erase_subst
    + erase_val
    + erase_names
    + convert_class
    + erase_exc
    + erase_result
* MEASURE_REDUCTION (LEMMAS)
  - MeasureReduction_LesserOrEqualTactics
    + mred_le_solver
    + ass_le
    + ass_le_trn
  - MeasureReduction_RemoveFromEnvironment
    + rem_keys_length
    + rem_ext_vars_length
    + rem_ext_vars_single
    + rem_keys_cons
    + rem_ext_vars_cons
  - MeasureReduction_Theorem
    + measure_reduction_vnil
    + measure_reduction_vlit
    + measure_reduction_vcons
    + measure_reduction_vtuple
    + measure_reduction_vmap
    + measure_reduction_vclos
    + measure_reduction
    + measure_reduction_list
    + measure_reduction_map
  - MeasureReduction_Minimalize
    + mred_min
    + mred_min_list
    + mred_min_map
  - MeasureReduction_RewriteTactics
    + mred
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section MeasureValue.



  Definition measure_val_list
      (measure : Value -> nat)
      (vl : list Value)
      : nat 
      :=
    list_sum (map measure vl).



  Definition measure_val_map
      (measure : Value -> nat)
      (vll : list (Value * Value))
      : nat
      :=
    list_sum (map (fun '(x, y) => (measure x) + (measure y)) vll).



  Definition measure_val_env
      (measure : Value -> nat)
      (Γ : Environment)
      : nat
      :=
    list_sum (map (measure ∘ snd) Γ).



  Fixpoint measure_val
      (v : Value) 
      : nat
      :=
    match v with

    | VNil => 1
    | VLit l => 1

    | VCons v1 v2 => 1
      + measure_val v1
      + measure_val v2

    | VTuple vl => 1
      + measure_val_list measure_val vl

    | VMap vll => 1
      + measure_val_map measure_val vll

    | VClos Γ ext _ _ e => 2
      + measure_val_env measure_val Γ

    end.



End MeasureValue.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: REMOVE_FROM_ENVIRONMENT //////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section RemoveFromEnvironment.



  Definition rem_keys
      (keys : list (Var + FunctionIdentifier))
      (Γ : Environment)
      : Environment
      :=
    filter
      (fun '(k, v) =>
        negb (existsb
          (fun x => (var_funid_eqb x k))
          keys))
      Γ.



  Definition rem_fids
      (fids : list FunctionIdentifier)
      (Γ : Environment)
      : Environment
      :=
    rem_keys (map inr fids) Γ.



  Definition rem_vars
      (vars : list Var)
      (Γ : Environment)
      : Environment
      :=
    rem_keys (map inl vars) Γ.



  Definition rem_ext
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      (Γ : Environment)
      : Environment
      :=
    rem_fids (map (snd ∘ fst) ext) Γ.



  Definition rem_ext_vars
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      (vars : list Var)
      (Γ : Environment)
      : Environment
      :=
    rem_ext ext (rem_vars vars Γ).



End RemoveFromEnvironment.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ADD_TO_ERASER ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section AddToEraser_Helpers.



  Definition convert_lit
      (lit : Literal)
      : Lit
      :=
    match lit with
     | Atom s => s
     | Integer x => x
    end.



  Definition convert_class
      (class : ExceptionClass)
      : ExcClass
      :=
    match class with
    | Error =>  CoreErlang.Syntax.Error
    | Throw =>  CoreErlang.Syntax.Throw
    | Exit =>   CoreErlang.Syntax.Exit
    end.



  Definition vars_of_pattern_list
      (pl : list Pattern)
      : list Var
      :=
    fold_right
      (fun x acc => variable_occurances x ++ acc)
      nil
      pl.



  Definition sum_eqb
      {A B : Type}
      (eqbA : A -> A -> bool)
      (eqbB : B -> B -> bool)
      (a b : A + B)
      : bool
      :=
    match a, b with
    | inl a', inl b' => eqbA a' b'
    | inr a', inr b' => eqbB a' b'
    | _, _ => false
    end.



End AddToEraser_Helpers.









Section AddToEraser_Types.



  Definition NameSub
      {T}
      {dec : T -> T -> bool}
      :=
    T -> nat.



  Definition Eraser
      :=
    @NameSub
      (Var + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)).



End AddToEraser_Types.









Section AddToEraser_Functions.



  Definition add_name
      {T dec}
      (name : T)
      (σ : @NameSub _ dec)
      :=
    fun x =>
      if dec x name
      then 0
      else S (σ x).



  Definition add_names
      {T}
      {dec : T -> T -> bool}
      (names : list T)
      (σ : NameSub)
      : NameSub
      :=
    fold_right
      (@add_name _ dec)
      σ
      names.






  Definition add_keys
      (keys : list (Var + FunctionIdentifier))
      (σ : Eraser)
      : Eraser
      :=
    add_names keys σ.



  Definition add_fids
      (fids : list FunctionIdentifier)
      (σ : Eraser)
      : Eraser
      :=
    add_keys (map inr fids) σ.



  Definition add_vars
      (vars : list Var)
      (σ : Eraser)
      : Eraser
      :=
    add_keys (map inl vars) σ.



  Definition add_ext
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      (σ : Eraser)
      : Eraser
      :=
    add_fids (map (snd ∘ fst) ext) σ.



  Definition add_ext_vars
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      (vars : list Var)
      (σ : Eraser)
      : Eraser
      :=
    add_ext ext (add_vars vars σ).



  Definition add_expext
      (ext : list (FunctionIdentifier * FunctionExpression))
      (σ : Eraser)
      : Eraser
      :=
    add_fids (map fst ext) σ.



  Definition add_expext_vars
      (ext : list (FunctionIdentifier * FunctionExpression))
      (vars : list Var)
      (σ : Eraser)
      : Eraser
      :=
    add_expext ext (add_vars vars σ).



  Definition add_pats
      (pats : list Pattern)
      (σ : Eraser)
      : Eraser
      :=
    add_vars (vars_of_pattern_list pats) σ.



End AddToEraser_Functions.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_NAMES //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Section EraseNames.



  Fixpoint erase_pat
      (p : Pattern)
      : Pat
      :=
    match p with

    | PNil =>
      Syntax.PNil

    | PVar _ =>
      Syntax.PVar

    | PLit lit =>
      Syntax.PLit
        (convert_lit lit)

    | PCons p1 p2 =>
      Syntax.PCons
        (erase_pat p1)
        (erase_pat p2)

    | PTuple pl =>
      Syntax.PTuple
        (map erase_pat pl)

    | PMap pll =>
      Syntax.PMap
        (map
          (prod_map
            erase_pat
            erase_pat)
          pll)

    end.






  Fixpoint erase_exp
      (σ : NameSub)
      (e : Expression)
      : Exp
      :=
    match e with

    | ENil =>
      ˝Syntax.VNil

    | ELit lit =>
      ˝Syntax.VLit
        (convert_lit lit)

    | ECons e1 e2 =>
      Syntax.ECons
        (erase_exp σ e1)
        (erase_exp σ e2)

    | ESeq e1 e2 =>
      Syntax.ESeq
        (erase_exp σ e1)
        (erase_exp σ e2)

    | EValues el =>
      Syntax.EValues
        (map (erase_exp σ) el)

    | ETuple el =>
      Syntax.ETuple
        (map (erase_exp σ) el)

    | EPrimOp s el =>
      Syntax.EPrimOp
        s
        (map (erase_exp σ) el)

    | EApp e el =>
      Syntax.EApp
        (erase_exp σ e)
        (map (erase_exp σ) el)

    | ECall e1 e2 el =>
      Syntax.ECall
        (erase_exp σ e1)
        (erase_exp σ e2)
        (map (erase_exp σ) el)

    | EMap ell =>
      Syntax.EMap
        (map
          (prod_map
            (erase_exp σ)
            (erase_exp σ))
          ell)

    | EFun vars e =>
      Syntax.EFun
        (length vars)
        (erase_exp (add_vars vars σ) e)

    | ELet vars e1 e2 =>
      Syntax.ELet
        (length vars)
        (erase_exp σ e1)
        (erase_exp (add_vars vars σ) e2)

    | ETry e1 vars1 e2 vars2 e3 =>
      Syntax.ETry
        (erase_exp σ e1)
        (length vars1)
        (erase_exp (add_vars vars1 σ) e2)
        (length vars2)
        (erase_exp (add_vars vars2 σ) e3)

    | ELetRec ext e =>
      Syntax.ELetRec
        (map
          (fun '(_, (vars, body)) =>
            (length vars,
            erase_exp (add_expext_vars ext vars σ) body))
          ext)
        (erase_exp (add_expext ext σ) e)

    | ECase e case =>
      Syntax.ECase
        (erase_exp σ e)
        (map 
          (fun '(pats, e1, e2) =>
            ((map erase_pat pats),
            erase_exp (add_pats pats σ) e1,
            erase_exp (add_pats pats σ) e2))
          case)

    | EVar var =>
      ˝Syntax.VVar
        (σ (inl var))

    | EFunId fid =>
      ˝Syntax.VFunId
        ((σ (inr fid)), snd fid)

    end.






  Definition erase_subst
      (erase_val : nat -> NameSub -> Value -> Val)
      (n : nat)
      (σ : NameSub)
      (Γ : Environment)
      (e : Expression)
      : Exp
      :=
    match n with
    | 0 => ˝Syntax.VNil
    | S n' =>
      (erase_exp (add_keys (map fst Γ) σ) e)
      .[list_subst (map (erase_val n' σ) (map snd Γ)) idsubst]
    end.






  Fixpoint erase_val
      (n : nat)
      (σ : NameSub)
      (v : Value)
      : Val
      :=
    match n with
    | 0 => Syntax.VNil
    | S n' =>

      match v with

      | VNil =>
        Syntax.VNil

      | VLit lit =>
        Syntax.VLit
          (convert_lit lit)

      | VCons v1 v2 =>
        Syntax.VCons
          (erase_val n' σ v1)
          (erase_val n' σ v2)

      | VTuple vl =>
        Syntax.VTuple
          (map (erase_val n' σ) vl)

      | VMap vll =>
        Syntax.VMap
          (map
            (prod_map
              (erase_val n' σ)
              (erase_val n' σ))
            vll)

      | VClos env ext _ vars e =>
        Syntax.VClos
          (map
            (fun '(n, fid', (vars', body)) =>
              (n,
              length vars',
              erase_subst
                erase_val
                n'
                (add_ext_vars ext vars' σ)
                (rem_ext_vars ext vars' env)
                body))
            ext)
          0 (*id*)
          (length vars)
          (erase_subst
            erase_val
            n'
            (add_ext_vars ext vars σ)
            (rem_ext_vars ext vars env)
            e)

      end
    end.






  Definition erase_names
      (σ : NameSub)
      (Γ : Environment)
      (e : Expression)
      : Exp
      :=
    (erase_exp
      (add_keys (map fst Γ) σ)
      e)
    .[list_subst
      (map (fun v => erase_val (measure_val v) σ v) (map snd Γ))
      idsubst].



  Definition erase_exc
      (σ : NameSub)
      (exc : Exception)
      : CoreErlang.Syntax.Exception
      :=
    match exc with
    | (class, v1, v2) =>
        (convert_class class,
        erase_val (measure_val v1) σ v1,
        erase_val (measure_val v2) σ v2)
    end.



  Definition erase_result
      (σ : NameSub)
      (result : (ValueSequence + Exception))
      : Redex
      :=
    match result with
    | inl vs =>   RValSeq (map (fun v => erase_val (measure_val v) σ v) vs)
    | inr exc =>  RExc (erase_exc σ exc)
    end.



End EraseNames.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_REDUCTION ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






(* Section: MeasureReduction_LesserOrEqualTactics. *)



(* Trivial *)

  Ltac mred_le_solver :=
    smp;
    try unfold measure_val_list;
    try unfold measure_val_map;
    try unfold measure_val_env;
    try rewrite map_app, list_sum_app;
    sli.






(* Less or Equal *)

  Tactic Notation "ass_le"
      "as"  ident(Ile)
      ":"   constr(Cle)
      :=
    assert Cle as Ile by mred_le_solver.

  Tactic Notation "ass_le"
      ">"   constr(Cle)
      "as"  ident(Ile)
      ":"   hyp(Hm1) hyp(Hm2)
      :=
    assert Cle as Ile by
      (rewrite Hm1, Hm2;
      mred_le_solver).

  Tactic Notation "ass_le"
      ">"   constr(Cle)
      "as"  ident(Ile)
      ":"   hyp(Hm1) hyp(Hm2) hyp(Hm3)
      :=
    assert Cle as Ile by
      (rewrite Hm1, Hm2, Hm3;
      mred_le_solver).



  Tactic Notation "ass_le_trn"
      ">"   constr(Cle_n1_n3)
      "as"  ident(Ile_n1_n3)
      ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3)
      :=
    assert Cle_n1_n3 as Ile_n1_n3 by
      (eapply Nat.le_trans;
        [exact Hle_n1_n2 | exact Hle_n2_n3]).

  Tactic Notation "ass_le_trn"
      ">"   constr(Cle_n1_n4)
      "as"  ident(Ile_n1_n4)
      ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3) hyp(Hle_n3_n4)
      :=
    assert Cle_n1_n4 as Ile_n1_n4 by
      (eapply Nat.le_trans;
        [eapply Nat.le_trans;
          [exact Hle_n1_n2 | exact Hle_n2_n3]
        | exact Hle_n3_n4]).



(* End: MeasureReduction_LesserOrEqualTactics. *)









Section MeasureReduction_RemoveFromEnvironment.



  Lemma rem_keys_length :
    forall keys Γ,
      length (rem_keys keys Γ) <= length Γ.
  Proof.
    itr.
    ind - Γ as [| [k v] Γ IH]: sli.
    smp.
    des >
      (negb
        (existsb (λ x : Var + FunctionIdentifier, var_funid_eqb x k) keys)).
    all: slia.
  Qed.



  Lemma rem_ext_vars_length :
    forall ext vars Γ,
      length (rem_ext_vars ext vars Γ) <= length Γ.
  Proof.
    itr.
    ufl - rem_ext_vars rem_ext rem_fids rem_vars.
    remember ((map inr (map (snd ∘ fst) ext))) as keys1.
    remember (map inl vars) as keys2.
    clr - Heqkeys1 Heqkeys2.
    pse - rem_keys_length: keys2 Γ.
    pse - rem_keys_length: keys1 (rem_keys keys2 Γ).
    lia.
  Qed.



  Lemma rem_ext_vars_single :
    forall ext vars k v,
        rem_ext_vars ext vars [(k, v)]
      = [(k, v)]
    \/  rem_ext_vars ext vars [(k, v)]
      = [].
  Proof.
    itr.
    pse - rem_ext_vars_length as Hlength: ext vars [(k, v)].
    cbn.
    des >
      (existsb
        (λ x : Var + FunctionIdentifier, var_funid_eqb x k)
        (map inl vars)); smp.
    1: by rgt.
    des >
      (existsb
        (λ x : Var + FunctionIdentifier, var_funid_eqb x k)
        (map inr (map (snd ∘ fst) ext))); smp.
    1: by rgt.
    by lft.
  Qed.






  Lemma rem_keys_cons :
    forall keys k v Γ,
      rem_keys keys ((k, v) :: Γ)
    = rem_keys keys [(k, v)] ++ rem_keys keys Γ.
  Proof.
    itr.
    smp.
    des > (negb (existsb (fun x => var_funid_eqb x k) keys)) :- smp.
  Qed.



  Lemma rem_ext_vars_cons :
    forall ext vars k v Γ,
      rem_ext_vars ext vars ((k, v) :: Γ)
    = rem_ext_vars ext vars [(k, v)] ++ rem_ext_vars ext vars Γ.
  Proof.
    itr.
    ufl - rem_ext_vars.
    ufl - rem_vars.
    pose proof rem_keys_cons (map inl vars) k v Γ as Hvars.
    cwr - Hvars.
    pose proof rem_keys_length (map inl vars) [(k, v)] as Hlength.
    des > (rem_keys (map inl vars) [(k, v)]): smp.
    ivc - Hlength as Hzero: H0.
    2: ivs - Hzero.
    app - List.length_zero_iff_nil in Hzero.
    ivc - Hzero.
    clr - k v.
    des - p as [k v].
    rwl - cons_app.
    eapply rem_keys_cons.
  Qed.



End MeasureReduction_RemoveFromEnvironment.









Section MeasureReduction_Theorem.



  Lemma measure_reduction_vnil :
    forall σ n1 n2,
        measure_val VNil <= n1
    ->  measure_val VNil <= n2
    ->  erase_val n1 σ VNil
      = erase_val n2 σ VNil.
  Proof.
    itr - σ n1 n2 Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    bmp.
  Qed.






  Lemma measure_reduction_vlit :
    forall lit σ n1 n2,
        measure_val (VLit lit) <= n1
    ->  measure_val (VLit lit) <= n2
    ->  erase_val n1 σ (VLit lit)
      = erase_val n2 σ (VLit lit).
  Proof.
    itr - lit σ n1 n2 Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    bmp.
  Qed.






  Lemma measure_reduction_vcons :
    forall v1 v2 σ n1 n2,
        (forall σ n1 n2,
            measure_val v1 <= n1
        ->  measure_val v1 <= n2
        ->  erase_val n1 σ v1
          = erase_val n2 σ v1)
    ->  (forall σ n1 n2,
            measure_val v2 <= n1
        ->  measure_val v2 <= n2
        ->  erase_val n1 σ v2
          = erase_val n2 σ v2)
    ->  measure_val (VCons v1 v2) <= n1
    ->  measure_val (VCons v1 v2) <= n2
    ->  erase_val n1 σ (VCons v1 v2)
      = erase_val n2 σ (VCons v1 v2).
  Proof.
    itr - v1 v2 σ n1 n2 IHv1 IHv2 Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    smp.
    ass > (measure_val v1 ≤ n1) as Hv1n1: smp - Hn1; lia.
    ass > (measure_val v1 ≤ n2) as Hv1n2: smp - Hn2; lia.
    ass > (measure_val v2 ≤ n1) as Hv2n1: smp - Hn1; lia.
    ass > (measure_val v2 ≤ n2) as Hv2n2: smp - Hn2; lia.
    spc - IHv1: σ n1 n2 Hv1n1 Hv1n2.
    spc - IHv2: σ n1 n2 Hv2n1 Hv2n2.
    bwr - IHv1 IHv2.
  Qed.






  Lemma measure_reduction_vtuple :
    forall vl σ n1 n2,
        (Forall
          (fun v =>
            (forall σ n1 n2,
                measure_val v <= n1
            ->  measure_val v <= n2
            ->  erase_val n1 σ v
              = erase_val n2 σ v))
          vl)
    ->  measure_val (VTuple vl) <= n1
    ->  measure_val (VTuple vl) <= n2
    ->  erase_val n1 σ (VTuple vl)
      = erase_val n2 σ (VTuple vl).
  Proof.
    itr - vl σ n1 n2 IFH Hn1 Hn2.
    ind - vl as [| v vl].
    * clr - IFH.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      bmp.
    * ivc - IFH as IHv IFH: H1 H2.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      smp.
      ufl - measure_val_list in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val (VTuple vl) ≤ S n1) as Hvln1:
        smp; ufl - measure_val_list; lia.
      ass > (measure_val (VTuple vl) ≤ S n2) as Hvln2:
        smp; ufl - measure_val_list; lia.
      spc - IHv: σ n1 n2 Hvn1 Hvn2.
      spc - IHvl: IFH Hvln1 Hvln2.
      smp - IHvl.
      ivc - IHvl as IHvl: H0.
      bwr - IHv IHvl.
  Qed.






  Lemma measure_reduction_vmap :
    forall vll σ n1 n2,
        (Forall
          (fun v =>
            (forall σ n1 n2,
                measure_val v.1 <= n1
            ->  measure_val v.1 <= n2
            ->  erase_val n1 σ v.1
              = erase_val n2 σ v.1)
          /\(forall σ n1 n2,
                measure_val v.2 <= n1
            ->  measure_val v.2 <= n2
            ->  erase_val n1 σ v.2
              = erase_val n2 σ v.2))
          vll)
    ->  measure_val (VMap vll) <= n1
    ->  measure_val (VMap vll) <= n2
    ->  erase_val n1 σ (VMap vll)
      = erase_val n2 σ (VMap vll).
  Proof.
    itr - vll σ n1 n2 IFH Hn1 Hn2.
    ind - vll as [| v vll].
    * clr - IFH.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      bmp.
    * ivc - IFH as IHv IFH: H1 H2.
      des - IHv as [IHv1 IHv2].
      des - v as [v1 v2].
      smp - IHv1 IHv2.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      smp.
      ufl - measure_val_map in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v1 ≤ n1) as Hv1n1: lia.
      ass > (measure_val v1 ≤ n2) as Hv1n2: lia.
      ass > (measure_val v2 ≤ n1) as Hv2n1: lia.
      ass > (measure_val v2 ≤ n2) as Hv2n2: lia.
      ass > (measure_val (VMap vll) ≤ S n1) as Hvln1:
        smp; ufl - measure_val_map; lia.
      ass > (measure_val (VMap vll) ≤ S n2) as Hvln2:
        smp; ufl - measure_val_map; lia.
      spc - IHv1: σ n1 n2 Hv1n1 Hv1n2.
      spc - IHv2: σ n1 n2 Hv2n1 Hv2n2.
      spc - IHvll: IFH Hvln1 Hvln2.
      smp - IHvll.
      ivc - IHvll as IHvll: H0.
      bwr - IHv1 IHv2 IHvll.
  Qed.






  Lemma measure_reduction_vclos :
    forall Γ ext id vars e σ n1 n2,
        (Forall
          (fun x =>
            (forall σ n1 n2,
                measure_val x.2 <= n1
            ->  measure_val x.2 <= n2
            ->  erase_val n1 σ x.2
              = erase_val n2 σ x.2))
          Γ)
    ->  measure_val (VClos Γ ext id vars e) <= n1
    ->  measure_val (VClos Γ ext id vars e) <= n2
    ->  erase_val n1 σ (VClos Γ ext id vars e)
      = erase_val n2 σ (VClos Γ ext id vars e).
  Proof.
    itr - Γ ext id vars e σ n1 n2 IFH Hn1 Hn2.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    smp.
    feq.
    * clr - e.
      app - map_ext; itr.
      des - a as [[n fid] [vars' body]].
      feq.
      des - n1: lia.
      des - n2: lia.
      smp.
      do 2 feq.
      do 2 rwl - Nat.succ_le_mono in Hn1 Hn2.
      ind - Γ as [| [k v] Γ IHvl]: smp.
      ivc - IFH as IHv IFH: H1 H2.
      smp - IHv.
      ufl - measure_val_env in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val_env measure_val Γ ≤ n1) as Hvln1:
        smp; ufl - measure_val_env; lia.
      ass > (measure_val_env measure_val Γ ≤ n2) as Hvln2:
        smp; ufl - measure_val_env; lia.
      spc - IHv: (add_ext_vars ext vars' σ) n1 n2 Hvn1 Hvn2.
      spc - IHvl: IFH Hvln1 Hvln2.
      rwr - rem_ext_vars_cons map_app map_app.
      pse - rem_ext_vars_single as Hsingle: ext vars' k v.
      des - Hsingle.
      - cwr - H.
        smp.
        bwr - IHv IHvl.
      - cwr - H.
        smp.
        bwr - IHvl.
    * des - n1: lia.
      des - n2: lia.
      smp.
      do 2 feq.
      do 2 rwl - Nat.succ_le_mono in Hn1 Hn2.
      ind - Γ as [| [k v] Γ IHvl]: smp.
      ivc - IFH as IHv HForall: H1 H2.
      smp - IHv.
      ufl - measure_val_env in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val_env measure_val Γ ≤ n1) as Hvln1:
        smp; ufl - measure_val_env; lia.
      ass > (measure_val_env measure_val Γ ≤ n2) as Hvln2:
        smp; ufl - measure_val_env; lia.
      spc - IHv: (add_ext_vars ext vars σ) n1 n2 Hvn1 Hvn2.
      spc - IHvl: HForall Hvln1 Hvln2.
      rwr - rem_ext_vars_cons map_app map_app.
      pse - rem_ext_vars_single as Hsingle: ext vars k v.
      des - Hsingle.
      - cwr - H.
        smp.
        bwr - IHv IHvl.
      - cwr - H.
        smp.
        bwr - IHvl.
  Qed.






  Theorem measure_reduction :
    forall v σ n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  erase_val n1 σ v
      = erase_val n2 σ v.
  Proof.
    itr - v.
    ind ~ ind_bs_val - v; itr - σ n1 n2 Hn1 Hn2.
    1: bse - measure_reduction_vnil: σ n1 n2 Hn1 Hn2.
    1: bse - measure_reduction_vlit: l σ n1 n2 Hn1 Hn2.
    1: bse - measure_reduction_vcons: v1 v2 σ n1 n2 IHv1 IHv2 Hn1 Hn2.
    2: bse - measure_reduction_vtuple: l σ n1 n2 H Hn1 Hn2.
    2: bse - measure_reduction_vmap: l σ n1 n2 H Hn1 Hn2.
    1: bse - measure_reduction_vclos: ref ext id params body σ n1 n2 H Hn1 Hn2.
  Qed.






  Theorem measure_reduction_list :
    forall vl σ n1 n2,
        measure_val_list measure_val vl <= n1
    ->  measure_val_list measure_val vl <= n2
    ->  map (erase_val n1 σ) vl
      = map (erase_val n2 σ) vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl σ n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (measure_val_list measure_val vl)
      (measure_val_list measure_val (v :: vl)).
    (* #3 Assert: assert *)
    ass_le > (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_le > (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_le_trn > (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_le_trn > (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_le_trn > (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_le_trn > (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - measure_reduction as Heq_v: v σ n1 n2 Hle_v_n1 Hle_v_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.






  Theorem measure_reduction_map :
    forall vll σ n1 n2,
        measure_val_map measure_val vll <= n1
    ->  measure_val_map measure_val vll <= n2
    ->  map (prod_map (erase_val n1 σ) (erase_val n1 σ)) vll
      = map (prod_map (erase_val n2 σ) (erase_val n2 σ)) vll.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vll σ n1 n2 Hle_vvll_n1 Hle_vvll_n2.
    ind - vll as [| v vll Heq_vll]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    rem - mv1 mv2 mv mvll mvvll as Hmv1 Hmv2 Hmv Hmvll Hmvvll:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (measure_val_map measure_val vll)
      (measure_val_map measure_val ((v1, v2) :: vll)).
    (* #3 Assert: assert *)
    ass_le > (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_le > (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_le > (mv <= mvvll) as Hle_v_vvll: Hmv Hmvvll.
    ass_le > (mvll <= mvvll) as Hle_vll_vvll: Hmvll Hmvvll.
    ass_le_trn > (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvll Hle_vvll_n1.
    ass_le_trn > (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvll Hle_vvll_n2.
    ass_le_trn > (mvll <= n1) as Hle_vll_n1: Hle_vll_vvll Hle_vvll_n1.
    ass_le_trn > (mvll <= n2) as Hle_vll_n2: Hle_vll_vvll Hle_vvll_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvll Hmvvll in *.
    clr + Heq_vll Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vll_n1 Hle_vll_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vll: Hle_vll_n1 Hle_vll_n2.
    psc - measure_reduction as Heq_v1: v1 σ n1 n2 Hle_v1_n1 Hle_v1_n2.
    psc - measure_reduction as Heq_v2: v2 σ n1 n2 Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vll.
  Qed.



End MeasureReduction_Theorem.









Section MeasureReduction_Minimalize.



  Theorem mred_min :
    forall v σ n,
        measure_val v <= n
    ->  erase_val n σ v
      = erase_val (measure_val v) σ v.
  Proof.
    itr - v σ n Hn.
    pse - measure_reduction as Hmr.
    app - Hmr; lia.
  Qed.






  Theorem mred_min_list :
    forall vl σ n,
        measure_val_list measure_val vl <= n
    ->  map (erase_val n σ) vl
      = map (erase_val (measure_val_list measure_val vl) σ) vl.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vl σ n Hn.
    pse - measure_reduction_list as Hmr.
    app - Hmr; lia.
  Qed.






  Theorem mred_min_map :
    forall vll σ n,
        measure_val_map measure_val vll <= n
    ->  map (prod_map (erase_val n σ) (erase_val n σ)) vll
      = map (prod_map (erase_val n σ) (erase_val n σ)) vll.
  Proof.
    (* #1 Measure Reduction Solver: intro/mred_solver *)
    itr - vll σ n Hn.
    pse - measure_reduction_map as Hmr.
    app - Hmr; lia.
  Qed.



(*Not Necessary Using*)

  Lemma mred_vcons_v1 :
    forall σ v1 v2,
      erase_val (measure_val v1 + measure_val v2) σ v1
    = erase_val (measure_val v1) σ v1.
  Proof.
    itr.
    app - mred_min: mred_le_solver.
  Qed.



  Lemma mred_vcons_v2 :
    forall σ v1 v2,
      erase_val (measure_val v1 + measure_val v2) σ v2
    = erase_val (measure_val v2) σ v2.
  Proof.
    itr.
    app - mred_min: mred_le_solver.
  Qed.



  Lemma mred_vtuple_v :
    forall σ v vl,
      erase_val (measure_val_list measure_val (v :: vl)) σ v
    = erase_val (measure_val v) σ v.
  Proof.
    itr.
    app - mred_min: mred_le_solver.
  Qed.



  Lemma mred_vtuple_vl :
    forall σ v vl,
      map (erase_val (measure_val_list measure_val (v :: vl)) σ) vl
    = map (erase_val (measure_val_list measure_val vl) σ) vl.
  Proof.
    itr.
    app - mred_min_list: mred_le_solver.
  Qed.



End MeasureReduction_Minimalize.









(* Section: MeasureReduction_RewriteTactics. *)



  Ltac mred :=
    try (rewrite mred_min; [idtac | mred_le_solver]);
    try (rewrite mred_min_list; [idtac | mred_le_solver]);
    try (rewrite mred_min_map; [idtac | mred_le_solver]).



(* Section: MeasureReduction_RewriteTactics. *)