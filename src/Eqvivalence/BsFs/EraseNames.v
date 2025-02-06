From CoreErlang.Eqvivalence Require Export Basics.

Import BigStep.

(** CONTENT:
* MEASURE_VALUE (DEFINITIONS)
  - MeasureValue_Helpers (DEFINITIONS)
    + measure_val_list
    + measure_val_map
    + measure_val_env
  - MeasureValue_Main (DEFINITIONS)
    + measure_val
* REMOVE_FROM_ENVIRONMENT (DEFINITIONS; LEMMAS)
  - RemoveFromEnvironment (DEFINITIONS)
    + rem_keys
    + rem_fids
    + rem_vars
    + rem_ext
    + rem_ext_vars
  - RemoveFromEnvironment_Empty (LEMMAS)
    + rem_keys_empty
    + rem_fids_empty
    + rem_vars_empty
    + rem_ext_empty
    + rem_ext_vars_empty_ext
    + rem_ext_vars_empty_vars
    + rem_ext_vars_empty
  - RemoveFromEnvironment_Append (LEMMAS)
    + rem_keys_app
    + rem_ext_vars_app
* ADD_TO_ERASER (TYPE; DEFINITIONS)
  - AddToEraser_Helpers (DEFINITIONS)
    + convert_lit
    + vars_of_pattern_list
    + sum_eqb
  - AddToEraser_Types (TYPE)
    + NameSub
    + Eraser
    + σ0
  - AddToEraser (DEFINITIONS)
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
    + add_env
    + from_env
  - AddToEraser_Empty (LEMMAS)
    + add_keys_empty
    + add_fids_empty
    + add_vars_empty
    + add_ext_empty
    + add_ext_vars_empty_ext
    + add_ext_vars_empty_vars
    + add_ext_vars_empty
  - AddToEraser_Append (LEMMAS)
    + add_keys_app
    + add_ext_vars_app
  - AddToEraser_Others (LEMMAS)
    + from_env_cons
* ERASE_NAMES (DEFINITIONS; AXIOMS; LEMMAS; TACTICS)
  - EraseNames_Bigs (DEFINITIONS)
    + erase_pat
    + erase_exp
    + erase_val
    + erase_val'
  - EraseNames_Smalls (DEFINITIONS)
    + erase_names
    + convert_class
    + erase_exc
    + erase_result
  - EraseNames_Lemmas (LEMMAS)
    + erase_result_to_exception
    + erase_result_to_valseq
    + erase_result_to_value
  - EraseNames_Axioms (AXIOMS)
    + erase_val_fuel
  - EraseNames_AxiomLemmas (LEMMAS)
    + erase_val_fuel_list
    + erase_val_fuel_list_measure
    + erase_val_fuel_list_fun
    + erase_val_fuel_map
    + erase_val_fuel_map_measure
    + erase_val_fuel_map_fun
  - EraseNames_Tactics (TACTICS)
    + mvr (Measure Value Reduction)
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: MEASURE_VALUE ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section MeasureValue_Helpers.



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



End MeasureValue_Helpers.









Section MeasureValue_Main.



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



End MeasureValue_Main.












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









Section RemoveFromEnvironment_Empty.



  Lemma rem_keys_empty :
    forall Γ,
      rem_keys [] Γ = Γ.
  Proof.
    (* #1 Induction on Environment: induction + simpl*)
    ind - Γ as [| [k v] Γ IH] :> smp.
    (* #2 Rewrite by Induction: rewrite *)
    bwr - IH.
  Qed.



  Lemma rem_fids_empty :
    forall Γ,
      rem_fids [] Γ = Γ.
  Proof.
    app - rem_keys_empty.
  Qed.



  Lemma rem_vars_empty :
    forall Γ,
      rem_vars [] Γ = Γ.
  Proof.
    app - rem_keys_empty.
  Qed.



  Lemma rem_ext_empty :
    forall Γ,
      rem_ext [] Γ = Γ.
  Proof.
    app - rem_keys_empty.
  Qed.



  Lemma rem_ext_vars_empty_ext :
    forall vars Γ,
      rem_ext_vars [] vars Γ = rem_vars vars Γ.
  Proof.
    itr.
    ufl - rem_ext_vars.
    bwr - rem_ext_empty.
  Qed.



  Lemma rem_ext_vars_empty_vars :
    forall ext Γ,
      rem_ext_vars ext [] Γ = rem_ext ext Γ.
  Proof.
    itr.
    ufl - rem_ext_vars.
    bwr - rem_vars_empty.
  Qed.



  Lemma rem_ext_vars_empty :
    forall Γ,
      rem_ext_vars [] [] Γ = Γ.
  Proof.
    itr.
    ufl - rem_ext_vars.
    bwr - rem_ext_empty
          rem_vars_empty.
  Qed.



End RemoveFromEnvironment_Empty.









Section RemoveFromEnvironment_Append.



  Lemma rem_keys_app :
    forall keys1 keys2 Γ,
      rem_keys (keys1 ++ keys2) Γ
    = rem_keys keys1 (rem_keys keys2 Γ).
  Proof.
    itr.
    ind - Γ as [| [k v] Γ IHΓ]: smp.
    ufl - rem_keys in *.
    smp *.
    rwr - existsb_app.
    rwr - negb_orb.
    des > ((negb (existsb (fun x => var_funid_eqb x k) keys1))) as Hkeys1;
    des > ((negb (existsb (fun x => var_funid_eqb x k) keys2))) as Hkeys2;
    smp.
    * rwr - Hkeys1.
      bwr - IHΓ.
    * bwr - IHΓ.
    * rwr - Hkeys1.
      bwr - IHΓ.
    * bwr - IHΓ.
  Qed.



  Lemma rem_ext_vars_app :
    forall ext vars Γ,
      rem_keys ((map (inr ∘ snd ∘ fst) ext) ++ (map inl vars)) Γ
    = rem_ext_vars ext vars Γ.
  Proof.
    itr.
    rwr - rem_keys_app.
    ufl - rem_ext_vars
          rem_ext
          rem_vars
          rem_fids.
    bwr - map_map.
  Qed.



End RemoveFromEnvironment_Append.












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
      (var_funid_eqb).



  Definition σ0 : Eraser := (fun _ => 0).



End AddToEraser_Types.









Section AddToEraser.



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



  Definition add_env
      (Γ : Environment)
      (σ : Eraser)
      : Eraser
      :=
    add_keys (map fst Γ) σ.



  Definition from_env
      (Γ : Environment)
      : Eraser
      :=
    add_env Γ σ0.



End AddToEraser.









Section AddToEraser_Empty.



  Lemma add_keys_empty :
    forall σ,
      add_keys [] σ = σ.
  Proof.
    trv.
  Qed.



  Lemma add_fids_empty :
    forall σ,
      add_fids [] σ = σ.
  Proof.
    trv.
  Qed.



  Lemma add_vars_empty :
    forall σ,
      add_vars [] σ = σ.
  Proof.
    trv.
  Qed.



  Lemma add_ext_empty :
    forall σ,
      add_ext [] σ = σ.
  Proof.
    app - add_keys_empty.
  Qed.



  Lemma add_ext_vars_empty_ext :
    forall vars σ,
      add_ext_vars [] vars σ = add_vars vars σ.
  Proof.
    itr.
    ufl - add_ext_vars.
    app - add_ext_empty.
  Qed.



  Lemma add_ext_vars_empty_vars :
    forall ext σ,
      add_ext_vars ext [] σ = add_ext ext σ.
  Proof.
    itr.
    ufl - add_ext_vars.
    app - add_vars_empty.
  Qed.



  Lemma add_ext_vars_empty :
    forall σ,
      add_ext_vars [] [] σ = σ.
  Proof.
    trv.
  Qed.



End AddToEraser_Empty.









Section AddToEraser_Append.



  Lemma add_keys_app :
    forall keys1 keys2 σ,
      add_keys (keys1 ++ keys2) σ
    = add_keys keys1 (add_keys keys2 σ).
  Proof.
    itr.
    ufl - add_keys.
    unfold add_names.
    bwr - foldr_app.
  Qed.



  Lemma add_ext_vars_app :
    forall ext vars σ,
      add_keys ((map (inr ∘ snd ∘ fst) ext) ++ (map inl vars)) σ
    = add_ext_vars ext vars σ.
  Proof.
    itr.
    rwr - add_keys_app.
    ufl - add_ext_vars
          add_ext
          add_vars
          add_fids.
    bwr - map_map.
  Qed.



End AddToEraser_Append.









Section AddToEraser_Others.



  Lemma from_env_cons :
    forall key val Γ,
      from_env ((key, val) :: Γ)
    = fun k => if var_funid_eqb k key then 0 else S (from_env Γ k).
  Proof.
    itr.
    ufl - from_env add_env add_keys.
    smp.
    unfold add_name.
    trv.
  Qed.



End AddToEraser_Others.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_NAMES //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Section EraseNames_Bigs.



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
          (fun '(e1, e2) => (erase_exp σ e1, erase_exp σ e2))
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






  Fixpoint erase_val
      (n : nat)
      (v : Value)
      : Val
      :=

    let
      erase_subst
          (n : nat)
          (shift : nat)
          (σ : NameSub)
          (vl : list Value)
          (e : Expression)
          : Exp
          :=
        (erase_exp σ e)
        .[upn shift
          (list_subst (map (fun v => erase_val n v) vl) idsubst)]
    in

    let
      erase_body
          (n : nat)
          (Γ : Environment)
          (ext : list (nat * FunctionIdentifier * FunctionExpression))
          (vars : list Var)
          (e : Expression)
          : Exp
          :=
        erase_subst
          n
          (length ext + length vars)
          (add_ext_vars ext vars (from_env (rem_ext_vars ext vars Γ)))
          (map snd (rem_ext_vars ext vars Γ))
          e
        (* Refactor BigStep EFun/Letrec: Γ -> (rem_ext_vars ext vars Γ)  *)
    in

    let
      erase_clositem
          (n : nat)
          (Γ : Environment)
          (ext : list (nat * FunctionIdentifier * FunctionExpression))
          (ci : nat * FunctionIdentifier * FunctionExpression)
          : nat * nat * Exp
          :=
        match ci with
        | (id, fid, (vars, e)) =>
          (id, length vars, erase_body n Γ ext vars e)
        end
    in

    let
      erase_ext
          (n : nat)
          (Γ : Environment)
          (ext : list (nat * FunctionIdentifier * FunctionExpression))
          : list (nat * nat * Exp)
          :=
        map (erase_clositem n Γ ext) ext
    in

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
          (erase_val n' v1)
          (erase_val n' v2)

      | VTuple vl =>
        Syntax.VTuple
          (map (fun v => erase_val n' v) vl)

      | VMap vll =>
        Syntax.VMap
          (map
            (fun '(v1, v2) => (erase_val n' v1, erase_val n' v2))
            vll)

      | VClos Γ ext _ vars e =>
        Syntax.VClos
          (erase_ext n' Γ ext)
          0
          (length vars)
          (erase_body n' Γ ext vars e)

      end
    end.






  Definition erase_val'
      (v : Value)
      : Val
      :=

    let
      erase_subst
          (shift : nat)
          (σ : NameSub)
          (vl : list Value)
          (e : Expression)
          : Exp
          :=
        (erase_exp σ e)
        .[upn shift
          (list_subst (map (fun v => erase_val (measure_val v) v) vl) idsubst)]
    in

    let
      erase_body
          (Γ : Environment)
          (ext : list (nat * FunctionIdentifier * FunctionExpression))
          (vars : list Var)
          (e : Expression)
          : Exp
          :=
        erase_subst
          (length ext + length vars)
          (add_ext_vars ext vars (from_env (rem_ext_vars ext vars Γ)))
          (map snd (rem_ext_vars ext vars Γ))
          e
        (* Refactor BigStep EFun/Letrec: Γ -> (rem_ext_vars ext vars Γ)  *)
    in

    let
      erase_clositem
          (Γ : Environment)
          (ext : list (nat * FunctionIdentifier * FunctionExpression))
          (ci : nat * FunctionIdentifier * FunctionExpression)
          : nat * nat * Exp
          :=
        match ci with
        | (id, fid, (vars, e)) =>
          (id, length vars, erase_body Γ ext vars e)
        end
    in

    let
      erase_ext
          (Γ : Environment)
          (ext : list (nat * FunctionIdentifier * FunctionExpression))
          : list (nat * nat * Exp)
          :=
        map (erase_clositem Γ ext) ext
    in

    match v with

    | VNil =>
      Syntax.VNil

    | VLit lit =>
      Syntax.VLit
        (convert_lit lit)

    | VCons v1 v2 =>
      Syntax.VCons
        (erase_val (measure_val v1) v1)
        (erase_val (measure_val v2) v2)

    | VTuple vl =>
      Syntax.VTuple
        (map (fun v => erase_val (measure_val v) v) vl)

    | VMap vll =>
      Syntax.VMap
        (map
          (fun '(v1, v2) =>
            (erase_val (measure_val v1) v1,
             erase_val (measure_val v2) v2))
          vll)

    | VClos Γ ext _ vars e =>
      Syntax.VClos
        (erase_ext Γ ext)
        0
        (length vars)
        (erase_body Γ ext vars e)

    end.



End EraseNames_Bigs.









Section EraseNames_Smalls.



  Definition erase_names
      (Γ : Environment)
      (e : Expression)
      : Exp
      :=
    (erase_exp (from_env Γ) e)
    .[list_subst
      (map erase_val' (map snd Γ))
      idsubst].



  Definition erase_valseq
      (vs : ValueSequence)
      : ValSeq
      :=
    map erase_val' vs.



  Definition erase_exc
      (exc : Exception)
      : CoreErlang.Syntax.Exception
      :=
    match exc with
    | (class, v1, v2) =>
      (convert_class class, erase_val' v1, erase_val' v2)
    end.



  Definition erase_result
      (result : (ValueSequence + Exception))
      : Redex
      :=
    match result with
    | inl vs =>   RValSeq (erase_valseq vs)
    | inr exc =>  RExc (erase_exc exc)
    end.



End EraseNames_Smalls.









Section EraseNames_Notations.


(* 
Notation "δₚ( p )" := (erase_pat p)
  (p at level 200, format "δₚ( p )" ).
Notation "δₑ( e / σ )" := (erase_exp σ e)
  (e at level 200, σ at level 200, format "δₑ( e / σ )" ).
Notation "δₑ( e ) .[ Γ ]" := (erase_names Γ e)
  (e at level 200, Γ at level 200, format "δₑ( e ) .[ Γ ]" ).

Lemma tmp : forall p p', erase_pat p = p'. Proof. Admitted.
Lemma tmp2 : forall σ e e', erase_exp σ e = e'. Proof. Admitted.
Lemma tmp3 : forall Γ e e', erase_names Γ e = e'. Proof. Admitted.

Notation "'δₑ" := erase_exp.
Notation "`δᵥ" := erase_val.
Notation "'δᵥ" := erase_val'.
Notation "δₑ e .[ Γ ]" := (erase_names Γ e) 
  (at level 2, Γ at level 200, left associativity,
   format "δₑ e .[ Γ ]" ).



(* Example usage of the notation *)
Lemma example_lemma2 : forall e env, δₑ e .[ Γ ] = δₑ e .[ Γ ] .
Proof
  intros.
  reflexivity.
Qed. *)



End EraseNames_Notations.









Section EraseNames_UnfoldLemmas.



  Lemma erase_result_to_exception :
    forall exc,
      erase_result (inr exc)
    = erase_exc exc.
  Proof.
    trv.
  Qed.



  Lemma erase_result_to_valseq :
    forall vs,
      erase_result (inl vs)
    = erase_valseq vs.
  Proof.
    trv.
  Qed.



  Lemma erase_result_to_value :
    forall v,
      erase_result (inl [v])
    = RValSeq [erase_val' v].
  Proof.
    trv.
  Qed.



End EraseNames_UnfoldLemmas.









Section EraseNames_LengthLemmas.



  Lemma length_map_erase_exp :
    forall σ ξ el,
      length (map (fun e => (erase_exp σ e).[ξ]) el)
    = length el.
  Proof.
    itr.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_exp_eq :
    forall σ ξ el' el,
        el = (map (fun e => (erase_exp σ e).[ξ]) el')
    ->  length el'
      = length el.
  Proof.
    itr - σ ξ el' el Heq.
    cwr - Heq.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_val :
    forall vl,
      length (map erase_val' vl)
    = length vl.
  Proof.
    itr.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_val_eq :
    forall vl' vl,
        vl = (map erase_val' vl')
    ->  length vl'
      = length vl.
  Proof.
    itr - vl' vl Heq.
    cwr - Heq.
    bwr - length_map.
  Qed.



End EraseNames_LengthLemmas.









Section EraseNames_Axioms.



  Axiom erase_val_fuel :
    forall v n,
      erase_val n v = erase_val' v.



End EraseNames_Axioms.









Section EraseNames_AxiomLemmas.



  Lemma erase_val_fuel_list :
    forall vl n,
      map (fun v => erase_val n v) vl
    = map (fun v => erase_val' v) vl.
  Proof.
    itr.
    ind - vl as [| v vl IHvl]: smp.
    smp.
    feq.
    * app - erase_val_fuel.
    * exa - IHvl.
  Qed.



  Lemma erase_val_fuel_list_measure :
    forall vl,
      map (fun v => erase_val (measure_val v) v) vl
    = map (fun v => erase_val' v) vl.
  Proof.
    itr.
    ind - vl as [| v vl IHvl]: smp.
    smp.
    feq.
    * app - erase_val_fuel.
    * exa - IHvl.
  Qed.



  Lemma erase_val_fuel_list_fun :
    forall vl,
      map (fun v => erase_val' v) vl
    = map erase_val' vl.
  Proof.
    trv.
  Qed.



  Lemma erase_val_fuel_map :
    forall vll n,
      map (fun '(v1, v2) => (erase_val n v1, erase_val n v2)) vll
    = map (fun '(v1, v2) => (erase_val' v1, erase_val' v2)) vll.
  Proof.
    itr.
    ind - vll as [| [v1 v2] vll IHvl]: smp.
    smp.
    feq.
    * feq.
      - app - erase_val_fuel.
      - app - erase_val_fuel.
    * exa - IHvl.
  Qed.



  Lemma erase_val_fuel_map_measure :
    forall vll,
      map
        (fun '(v1, v2) =>
          (erase_val (measure_val v1) v1, erase_val (measure_val v2) v2))
        vll
    = map (fun '(v1, v2) => (erase_val' v1, erase_val' v2)) vll.
  Proof.
    itr.
    ind - vll as [| [v1 v2] vll IHvl]: smp.
    smp.
    feq.
    * feq.
      - app - erase_val_fuel.
      - app - erase_val_fuel.
    * exa - IHvl.
  Qed.



  Lemma erase_val_fuel_map_fun :
    forall vll,
      map (fun '(v1, v2) => (erase_val' v1, erase_val' v2)) vll
    = map (prod_map erase_val' erase_val') vll.
  Proof.
    itr.
    ind - vll as [| [v1 v2] vll IHvl]: smp.
    smp.
    bwr - IHvl.
  Qed.



End EraseNames_AxiomLemmas.









(* Section EraseNames_Tactics. *)



  Ltac mvr :=
    try (rewrite erase_val_fuel in *);
    try (rewrite erase_val_fuel_list in *);
    try (rewrite erase_val_fuel_list_measure in *);
    try (rewrite erase_val_fuel_list_fun in *);
    try (rewrite erase_val_fuel_map in *);
    try (rewrite erase_val_fuel_map_measure in *).



(* End EraseNames_Tactics. *)