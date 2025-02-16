From CoreErlang.Eqvivalence Require Export EX4Basics.

Import BigStep.
Import EX3Notations.

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
    + env_rem_keys
    + env_rem_fids
    + env_rem_vars
    + env_rem_ext
    + env_rem_ext_vars
  - RemoveFromEnvironment_Empty (LEMMAS)
    + env_rem_keys_empty
    + env_rem_fids_empty
    + env_rem_vars_empty
    + env_rem_ext_empty
    + env_rem_ext_vars_empty_ext
    + env_rem_ext_vars_empty_vars
    + env_rem_ext_vars_empty
  - RemoveFromEnvironment_Append (LEMMAS)
    + env_rem_keys_app
    + env_rem_ext_vars_app
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
      (vs : list Value)
      : nat 
      :=
    list_sum (map measure vs).



  Definition measure_val_map
      (measure : Value -> nat)
      (vvs : list (Value * Value))
      : nat
      :=
    list_sum (map (fun '(x, y) => (measure x) + (measure y)) vvs).



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

    | VCons v₁ v₂ => 1
      + measure_val v₁
      + measure_val v₂

    | VTuple vs => 1
      + measure_val_list measure_val vs

    | VMap vvs => 1
      + measure_val_map measure_val vvs

    | VClos Γ _ _ _ _ => 1
      + measure_val_env measure_val Γ

    end.



End MeasureValue_Main.









(* Section MeasureValue_Notations. *)



   Notation "'ᵛ|' v '|'" :=(measure_val v)
    (at level 1,
      format "ᵛ| v |").



   Notation "'ᵛˢ|' vs '|'" :=(measure_val_list measure_val vs)
    (at level 1,
      format "ᵛˢ| vs |").



   Notation "'ᵛᵛˢ|' vvs '|'" :=(measure_val_map measure_val vvs)
    (at level 1,
      format "ᵛᵛˢ| vvs |").



   Notation "'ᵉⁿᵛ|' Γ '|'" :=(measure_val_env measure_val Γ)
    (at level 1,
      format "ᵉⁿᵛ| Γ |").



(* End MeasureValue_Notations. *)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: REMOVE_FROM_ENVIRONMENT //////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section RemoveFromEnvironment.



  Definition env_rem_key_one
      (k : Key)
      (x : (Key * Value))
      : Environment
      :=
    if (k =ᵏ x.1)
      then []
      else [x].



  Definition env_rem_key
      (k : Key)
      (Γ : Environment)
      : Environment
      :=
    fold_right (fun x acc => env_rem_key_one k x  ++ acc) [] Γ.



  Definition env_rem_keys
      (ks : list Key)
      (Γ : Environment)
      : Environment
      :=
    fold_right (fun x acc => env_rem_key x acc) Γ ks.



  Definition env_rem_fids
      (fs : list FunctionIdentifier)
      (Γ : Environment)
      : Environment
      :=
    env_rem_keys (map inr fs) Γ.



  Definition env_rem_vars
      (xs : list Var)
      (Γ : Environment)
      : Environment
      :=
    env_rem_keys (map inl xs) Γ.



  Definition env_rem_ext
      (os : Extension)
      (Γ : Environment)
      : Environment
      :=
    env_rem_fids os.fids Γ.



End RemoveFromEnvironment.









(* Section RemoveFromEnvironment_Notations. *)



   Notation "x '-ᵏ' k" :=(env_rem_key_one k x)
    (at level 2,
      left associativity,
      format "x  -ᵏ  k").



   Notation "Γ '/ᵏ' k" :=(env_rem_key k Γ)
    (at level 2,
      left associativity,
      format "Γ  /ᵏ  k").



   Notation "Γ '//ᵏ' ks" :=(env_rem_keys ks Γ)
    (at level 2,
      left associativity,
      format "Γ  //ᵏ  ks").



   Notation "Γ '//ᶠ' fs" :=(env_rem_fids fs Γ)
    (at level 2,
      left associativity,
      format "Γ  //ᶠ  fs").



   Notation "Γ '//ˣ' xs" :=(env_rem_vars xs Γ)
    (at level 2,
      left associativity,
      format "Γ  //ˣ  xs").



   Notation "Γ '//ᵒ' os" :=(env_rem_ext os Γ)
    (at level 2,
      left associativity,
      format "Γ  //ᵒ  os").



(* End RemoveFromEnvironment_Notations. *)









Section RemoveFromEnvironment_Empty.



  Lemma env_rem_keys_nil_l :
    forall ks,
      [] //ᵏ ks
    = [].
  Proof.
    itr.
    ind - ks as [| k₁ ks IHks]: smp.
    smp.
    cwr - IHks.
    trv.
  Qed.



  Lemma env_rem_ext_vars_nil_l :
    forall xs os,
      [] //ˣ xs //ᵒ os
    = [].
  Proof.
    itr.
    ufl - env_rem_ext
          env_rem_fids
          env_rem_vars
          get_fids.
    do 2 rwr - env_rem_keys_nil_l.
    trv.
  Qed.



  Lemma env_rem_keys_nil_r :
    forall Γ,
      Γ //ᵏ []
    = Γ.
  Proof.
    trv.
  Qed.



  Lemma env_rem_fids_nil_r :
    forall Γ,
      Γ //ᶠ []
    = Γ.
  Proof.
    trv.
  Qed.



  Lemma env_rem_vars_nil_r :
    forall Γ,
      Γ //ˣ []
      = Γ.
  Proof.
    trv.
  Qed.



  Lemma env_rem_ext_nil_r :
    forall Γ,
      Γ //ᵒ []
    = Γ.
  Proof.
    trv.
  Qed.



  Lemma env_rem_ext_vars_nil_r :
    forall Γ xs,
      Γ //ˣ xs //ᵒ []
    = Γ //ˣ xs.
  Proof.
    trv.
  Qed.



  Lemma env_rem_ext_vars_nil_m :
    forall Γ os,
      Γ //ˣ [] //ᵒ os
    = Γ //ᵒ os.
  Proof.
    trv.
  Qed.



  Lemma env_rem_ext_vars_nil_mr :
    forall Γ,
      Γ //ˣ [] //ᵒ []
    = Γ.
  Proof.
    trv.
  Qed.



End RemoveFromEnvironment_Empty.









Section RemoveFromEnvironment_Append.



  Lemma env_rem_key_app :
    forall Γ₁ Γ₂ k,
      (Γ₁ ++ Γ₂) /ᵏ k
    = (Γ₁ /ᵏ k) ++ (Γ₂ /ᵏ k).
  Proof.
    itr.
    ind - Γ₁ as [| [k' v] Γ₁ IH]:
          smp |> smp.
    des > (k =ᵏ k') as Heq.
    * (* Case: k = k' *)
      ufl - env_rem_key_one.
      smp.
      cwr - Heq.
      smp.
      app - IH.
    * (* Case: k ≠ k' *)
      ufl - env_rem_key_one.
      smp.
      cwr - Heq.
      smp.
      bwr - IH.
  Qed.



  Lemma env_rem_keys_app_l :
    forall Γ₁ Γ₂ ks,
      (Γ₁ ++ Γ₂) //ᵏ ks
    = (Γ₁ //ᵏ ks) ++ (Γ₂ //ᵏ ks).
  Proof.
    itr.
    ind - ks as [| k₁ ks IHks]:
          do 3 rwr - env_rem_keys_nil_r.
    smp.
    bwr - IHks
          env_rem_key_app.
  Qed.



  Lemma env_rem_keys_cons_l :
    forall k₁ v₁ Γ ks,
      ((k₁, v₁) :: Γ) //ᵏ ks
    = ([(k₁, v₁)] //ᵏ ks) ++  Γ //ᵏ ks.
  Proof.
    itr.
    rwr - cons_app.
    app - env_rem_keys_app_l.
  Qed.



  Lemma env_rem_keys_app_r :
    forall Γ ks₁ ks₂,
      Γ //ᵏ (ks₁ ++ ks₂)
    = Γ //ᵏ ks₂ //ᵏ ks₁.
  Proof.
    itr.
    ufl - env_rem_keys.
    bwr - foldr_app.
  Qed.



  Lemma env_rem_ext_vars_r :
    forall Γ os xs,
      Γ //ᵏ (map (inr ∘ snd ∘ fst) os ++ map inl xs)
    = Γ //ˣ xs //ᵒ os.
  Proof.
    itr.
    ufl - env_rem_ext
          env_rem_fids
          env_rem_vars
          get_fids.
    bwr - env_rem_keys_app_r
          map_map.
  Qed.



End RemoveFromEnvironment_Append.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ADD_TO_ERASER ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section AddToEraser_Helpers.



  Definition convert_lit
      (l : Literal)
      : Lit
      :=
    match l with
     | Atom a => a
     | Integer z => z
    end.



  Definition convert_class
      (c : ExceptionClass)
      : ExcClass
      :=
    match c with
    | Error =>  CoreErlang.Syntax.Error
    | Throw =>  CoreErlang.Syntax.Throw
    | Exit =>   CoreErlang.Syntax.Exit
    end.



  Definition vars_of_pattern_list
      (ps : list Pattern)
      : list Var
      :=
    fold_right
      (fun x acc => variable_occurances x ++ acc)
      nil
      ps.



End AddToEraser_Helpers.









Section AddToEraser_Definition.



  Definition Eraser
      : Type
      :=
    list Key.



  Fixpoint apply_eraser
      (σ : Eraser)
      (k : Key)
      : nat
      :=
    match σ with
    | [] => 0
    | k' :: ks' =>  if k =ᵏ k'
                    then 0
                    else 1 + apply_eraser ks' k
    end.



End AddToEraser_Definition.









Section AddToEraser.



  Definition eraser_add_keys
      (ks : list Key)
      (σ : Eraser)
      : Eraser
      :=
    ks ++ σ.



  Definition eraser_add_fids
      (fs : list FunctionIdentifier)
      (σ : Eraser)
      : Eraser
      :=
    eraser_add_keys (map inr fs) σ.



  Definition eraser_add_vars
      (xs : list Var)
      (σ : Eraser)
      : Eraser
      :=
    eraser_add_keys (map inl xs) σ.



  Definition eraser_add_ext
      (os : Extension)
      (σ : Eraser)
      : Eraser
      :=
    eraser_add_fids os.fids σ.



  Definition eraser_add_ext_noid
      (os : ExtensionNoId)
      (σ : Eraser)
      : Eraser
      :=
    eraser_add_fids os.fids⁻ σ.



  Definition eraser_add_pats
      (ps : list Pattern)
      (σ : Eraser)
      : Eraser
      :=
    eraser_add_vars (vars_of_pattern_list ps) σ.



  Definition eraser_add_env
      (Γ : Environment)
      (σ : Eraser)
      : Eraser
      :=
    eraser_add_keys Γ.keys σ.



End AddToEraser.









(* Section AddToEraser_Notations. *)



   Notation "ks 'ᵏ++' σ" :=(eraser_add_keys ks σ)
    (at level 20,
      right associativity,
      format "ks  ᵏ++  σ").



   Notation "fs 'ᶠ++' σ" :=(eraser_add_fids fs σ)
    (at level 20,
      right associativity,
      format "fs  ᶠ++  σ").



   Notation "xs 'ˣ++' σ" :=(eraser_add_vars xs σ)
    (at level 20,
      right associativity,
      format "xs  ˣ++  σ").



   Notation "os 'ᵒ++' σ" :=(eraser_add_ext os σ)
    (at level 20,
      right associativity,
      format "os  ᵒ++  σ").



   Notation "os 'ᵒ⁻++' σ" :=(eraser_add_ext_noid os σ)
    (at level 20,
      right associativity,
      format "os  ᵒ⁻++  σ").



   Notation "ps 'ᵖ++' σ" :=(eraser_add_pats ps σ)
    (at level 20,
      right associativity,
      format "ps  ᵖ++  σ").



   Notation "Γ 'ᵉⁿᵛ++' σ" :=(eraser_add_env Γ σ)
    (at level 20,
      right associativity,
      format "Γ  ᵉⁿᵛ++  σ").



(* End AddToEraser_Notations. *)









Section AddToEraser_Empty.



  Lemma eraser_add_keys_nil_l :
    forall σ,
      [] ᵏ++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_fids_nil_l :
    forall σ,
      [] ᶠ++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_vars_nil_l :
    forall σ,
      [] ˣ++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_ext_nil_l :
    forall σ,
      [] ᵒ++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_ext_letrec_nil_l :
    forall σ,
      [] ᵒ⁻++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_pats_nil_l :
    forall σ,
      [] ᵖ++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_env_nil_l :
    forall σ,
      [] ᵉⁿᵛ++ σ = σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_ext_vars_nil_l :
    forall σ xs,
      [] ᵒ++ xs ˣ++ σ = xs ˣ++ σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_ext_vars_nil_m :
    forall σ os,
      os ᵒ++ [] ˣ++ σ = os ᵒ++ σ.
  Proof.
    trv.
  Qed.



  Lemma eraser_add_ext_vars_nil_lm :
    forall σ,
      [] ᵒ++ [] ˣ++ σ = σ.
  Proof.
    trv.
  Qed.






  Lemma eraser_add_keys_nil_r :
    forall ks,
      ks ᵏ++ [] = ks.
  Proof.
    itr.
    ufl - eraser_add_keys.
    bwr - app_nil_r.
  Qed.



  Lemma eraser_add_fids_nil_r :
    forall fs,
      fs ᶠ++ [] = (map inr fs).
  Proof.
    itr.
    app - eraser_add_keys_nil_r.
  Qed.



  Lemma eraser_add_vars_nil_r :
    forall xs,
      xs ˣ++ [] = (map inl xs).
  Proof.
    itr.
    app - eraser_add_keys_nil_r.
  Qed.



  Lemma eraser_add_ext_nil_r :
    forall os,
      os ᵒ++ [] = (map inr os.fids).
  Proof.
    itr.
    app - eraser_add_keys_nil_r.
  Qed.



  Lemma eraser_add_ext_letrec_nil_r :
    forall os,
      os ᵒ⁻++ [] = (map inr os.fids⁻).
  Proof.
    itr.
    app - eraser_add_keys_nil_r.
  Qed.



  Lemma eraser_add_pats_nil_r :
    forall ps,
      ps ᵖ++ [] = (map inl (vars_of_pattern_list ps)).
  Proof.
    itr.
    app - eraser_add_keys_nil_r.
  Qed.



  Lemma eraser_add_env_nil_r :
    forall Γ,
      Γ ᵉⁿᵛ++ [] = Γ.keys.
  Proof.
    itr.
    app - eraser_add_keys_nil_r.
  Qed.



End AddToEraser_Empty.









Section AddToEraser_Append.



  Lemma eraser_add_keys_app_l :
    forall σ ks₁ ks₂,
      (ks₁ ++ ks₂) ᵏ++  σ
    = ks₁ ᵏ++  ks₂ ᵏ++ σ.
  Proof.
    itr.
    ufl - eraser_add_keys.
    bwr - app_assoc.
  Qed.




  Lemma eraser_add_ext_vars_app_l :
    forall os xs σ,
      ((map (inr ∘ snd ∘ fst) os) ++ (map inl xs)) ᵏ++ σ
    = os ᵒ++ xs ˣ++ σ.
  Proof.
    itr.
    ufl - eraser_add_ext
          eraser_add_fids
          eraser_add_vars
          eraser_add_keys
          get_fids.
    bwr - eraser_add_keys_app_l
          map_map.
  Qed.



End AddToEraser_Append.









Section AddToEraser_Others.



  Lemma apply_eraser_cons :
    forall k k₁ v₁ Γ,
      apply_eraser (((k₁, v₁) :: Γ).keys) k
    = if var_funid_eqb k k₁
        then 0
        else S (apply_eraser Γ.keys k).
  Proof.
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

    | PLit l =>
      Syntax.PLit
        (convert_lit l)

    | PCons p₁ p₂ =>
      Syntax.PCons
        (erase_pat p₁)
        (erase_pat p₂)

    | PTuple ps =>
      Syntax.PTuple
        (map erase_pat ps)

    | PMap pps =>
      Syntax.PMap
        (map (fun '(ᵏp, ᵛp) => (erase_pat ᵏp, erase_pat ᵛp)) pps)

    end.






  Fixpoint erase_exp
      (σ : Eraser)
      (e : Expression)
      : Exp
      :=
    match e with

    | ENil =>
      ˝Syntax.VNil

    | ELit l =>
      ˝Syntax.VLit
        (convert_lit l)

    | ECons e₁ e₂ =>
      Syntax.ECons
        (erase_exp σ e₁)
        (erase_exp σ e₂)

    | ESeq e₁ e₂ =>
      Syntax.ESeq
        (erase_exp σ e₁)
        (erase_exp σ e₂)

    | EValues es =>
      Syntax.EValues
        (map (erase_exp σ) es)

    | ETuple es =>
      Syntax.ETuple
        (map (erase_exp σ) es)

    | EPrimOp a es =>
      Syntax.EPrimOp
        a
        (map (erase_exp σ) es)

    | EApp ᶠe es =>
      Syntax.EApp
        (erase_exp σ ᶠe)
        (map (erase_exp σ) es)

    | ECall ᵐe ᶠe es =>
      Syntax.ECall
        (erase_exp σ ᵐe)
        (erase_exp σ ᶠe)
        (map (erase_exp σ) es)

    | EMap ees =>
      Syntax.EMap
        (map (fun '(ᵏe, ᵛe) => (erase_exp σ ᵏe, erase_exp σ ᵛe)) ees)

    | EFun xs ᵇe =>
      Syntax.EFun
        (length xs)
        (erase_exp (xs ˣ++ σ) ᵇe)

    | ELet xs₁ e₁ e₂ =>
      Syntax.ELet
        (length xs₁)
        (erase_exp σ e₁)
        (erase_exp (xs₁ ˣ++ σ) e₂)

    | ETry e₁ xs₁ e₂ xsₓ e₃ =>
      Syntax.ETry
        (erase_exp σ e₁)
        (length xs₁)
        (erase_exp (xs₁ ˣ++ σ) e₂)
        (length xsₓ)
        (erase_exp (xsₓ ˣ++ σ) e₃)

    | ELetRec os ᵇe =>
      Syntax.ELetRec
        (map
          (fun '(_, (xs', ᵇe')) =>
            (length xs',
            erase_exp (os ᵒ⁻++ xs' ˣ++ σ) ᵇe'))
          os)
        (erase_exp (os ᵒ⁻++ σ) ᵇe)

    | ECase ᵖe us =>
      Syntax.ECase
        (erase_exp σ ᵖe)
        (map
          (fun '(ps, ᵍe, ᵇe) =>
            ((map erase_pat ps),
            erase_exp (ps ᵖ++ σ) ᵍe,
            erase_exp (ps ᵖ++ σ) ᵇe))
          us)

    | EVar x =>
      ˝Syntax.VVar
        (apply_eraser σ (inl x))

    | EFunId f =>
      ˝Syntax.VFunId
        ((apply_eraser σ (inr f)), f.2)
    end.






  Fixpoint erase_val'
      (n : nat)
      (v : Value)
      : Val
      :=

    let
      erase_subst
          (n shift : nat)
          (σ : Eraser)
          (vs : list Value)
          (e : Expression)
          : Exp
          :=
        (erase_exp σ e)
        .[upn shift (list_subst (map (fun v => erase_val' n v) vs) idsubst)]
    in

    let
      erase_body
          (n : nat)
          (Γ : Environment)
          (os : Extension)
          (xs : list Var)
          (e : Expression)
          : Exp
          :=
        erase_subst
          n
          (length os + length xs)
          (os ᵒ++ xs ˣ++ (Γ //ˣ xs //ᵒ os).keys)
          ((Γ //ˣ xs //ᵒ os).vals)
          e
    in

    let
      erase_clositem
          (n : nat)
          (Γ : Environment)
          (os : Extension)
          (o : ClosureItem)
          : ClosItem
          :=
        match o with
        | (id, f, (xs, e)) =>
          (id, length xs, erase_body n Γ os xs e)
        end
    in

    let
      erase_ext
          (n : nat)
          (Γ : Environment)
          (os : Extension)
          : Ext
          :=
        map (erase_clositem n Γ os) os
    in

    match n with
    | 0 => Syntax.VNil
    | S n' =>

      match v with

      | VNil =>
        Syntax.VNil

      | VLit l =>
        Syntax.VLit
          (convert_lit l)

      | VCons v₁ v₂ =>
        Syntax.VCons
          (erase_val' n' v₁)
          (erase_val' n' v₂)

      | VTuple vs =>
        Syntax.VTuple
          (map (fun v => erase_val' n' v) vs)

      | VMap vvs =>
        Syntax.VMap
          (map (fun '(ᵏv, ᵛv) => (erase_val' n' ᵏv, erase_val' n' ᵛv)) vvs)

      | VClos Γ os _ xs e =>
        Syntax.VClos
          (erase_ext n' Γ os)
          0
          (length xs)
          (erase_body n' Γ os xs e)

      end
    end.






  Definition erase_val
      (v : Value)
      : Val
      :=

    let
      erase_subst
          (shift : nat)
          (σ : Eraser)
          (vs : list Value)
          (e : Expression)
          : Exp
          :=
        (erase_exp σ e)
        .[upn shift (list_subst (map (fun v => erase_val' ᵛ|v| v) vs) idsubst)]
    in

    let
      erase_body
          (Γ : Environment)
          (os : Extension)
          (xs : list Var)
          (e : Expression)
          : Exp
          :=
        erase_subst
          (length os + length xs)
          (os ᵒ++ xs ˣ++ (Γ //ˣ xs //ᵒ os).keys)
          ((Γ //ˣ xs //ᵒ os).vals)
          e
    in

    let
      erase_clositem
          (Γ : Environment)
          (os : Extension)
          (o : ClosureItem)
          : ClosItem
          :=
        match o with
        | (id, f, (xs, e)) =>
          (id, length xs, erase_body Γ os xs e)
        end
    in

    let
      erase_ext
          (Γ : Environment)
          (os : Extension)
          : Ext
          :=
        map (erase_clositem Γ os) os
    in

    match v with

    | VNil =>
      Syntax.VNil

    | VLit l =>
      Syntax.VLit
        (convert_lit l)

    | VCons v₁ v₂ =>
      Syntax.VCons
        (erase_val' ᵛ|v₁| v₁)
        (erase_val' ᵛ|v₂| v₂)

    | VTuple vs =>
      Syntax.VTuple
        (map (fun v => erase_val' ᵛ|v| v) vs)

    | VMap vvs =>
      Syntax.VMap
        (map (fun '(ᵏv, ᵛv) => (erase_val' ᵛ|ᵏv| ᵏv, erase_val' ᵛ|ᵛv| ᵛv)) vvs)

    | VClos Γ os _ xs e =>
      Syntax.VClos
        (erase_ext Γ os)
        0
        (length xs)
        (erase_body Γ os xs e)

    end.



End EraseNames_Bigs.









Section EraseNames_Smalls.



  Definition erase_names
      (Γ : Environment)
      (e : Expression)
      : Exp
      :=
    (erase_exp Γ.keys e)
    .[list_subst (map erase_val Γ.vals) idsubst].



  Definition erase_valseq
      (vs : ValueSequence)
      : ValSeq
      :=
    map erase_val vs.



  Definition erase_exc
      (q : Exception)
      : CoreErlang.Syntax.Exception
      :=
    match q with
    | (c, ʳv, ᵈv) =>
      (convert_class c, erase_val ʳv, erase_val ᵈv)
    end.



  Definition erase_result
      (result : (ValueSequence + Exception))
      : Redex
      :=
    match result with
    | inl vs => RValSeq (erase_valseq vs)
    | inr q =>  RExc (erase_exc q)
    end.



End EraseNames_Smalls.









Module EraseNamesNotations.



   Notation "'δₗᶠ(' l ')'" := (convert_lit l)
    (at level 20,
      format "δₗᶠ( l )").

   Notation "'δᵧᶠ(' c ')'" := (convert_class c)
    (at level 20,
      format "δᵧᶠ( c )").

   Notation "ps 'ᵖ⇒ˣ'" := (vars_of_pattern_list ps)
    (at level 20,
      format "ps  ᵖ⇒ˣ").



  Notation "′δₚᶠ" := erase_pat
    (at level 1,
      format "′δₚᶠ" ).

  Notation "δₚᶠ( p )" := (erase_pat p)
    (at level 1,
      format "δₚᶠ( p )" ).



  Notation "k ./ σ" := (apply_eraser σ k)
    (at level 1,
      format "k  ./  σ" ).

  Notation "δₑᶠ( σ )" := (erase_exp σ)
    (at level 1,
      format "δₑᶠ( σ )" ).

  Notation "δₑᶠ( e .// σ )" := (erase_exp σ e)
    (at level 1,
      format "δₑᶠ( e  .//  σ )" ).

  Notation "δₑᶠ( e ⇓ Γ )" := (erase_names Γ e)
    (at level 1,
      format "δₑᶠ( e  ⇓  Γ )" ).



  Notation "′δᵥᶠ" := erase_val
    (at level 1,
      format "′δᵥᶠ" ).

  Notation "n :- ′δᵥᶠ" := (erase_val' n)
    (at level 1,
      format "n  :-  ′δᵥᶠ" ).

  Notation "δᵥᶠ( v )" := (erase_val v)
    (at level 1,
      format "δᵥᶠ( v )" ).

  Notation "n :- δᵥᶠ( v )" := (erase_val' n v)
    (at level 1,
      format "n  :-  δᵥᶠ( v )" ).



  Notation "δᵥₗᶠ( vs )" := (erase_valseq vs)
    (at level 1,
      format "δᵥₗᶠ( vs )" ).

  Notation "δₓᶠ( q )" := (erase_exc q)
    (at level 1,
      format "δₓᶠ( q )" ).

  Notation "δᶠ( r )" := (erase_result r)
    (at level 1,
      format "δᶠ( r )" ).



End EraseNamesNotations.









Section EraseNames_UnfoldLemmas.



  Lemma erase_result_to_exception :
    forall q,
      erase_result (inr q)
    = erase_exc q.
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
    = RValSeq [erase_val v].
  Proof.
    trv.
  Qed.



End EraseNames_UnfoldLemmas.









Section EraseNames_LengthLemmas.



  Lemma length_map_erase_exp :
    forall σ ξ es,
      length (map (fun e => (erase_exp σ e).[ξ]) es)
    = length es.
  Proof.
    itr.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_exp_eq :
    forall σ ξ es' es,
        es = (map (fun e => (erase_exp σ e).[ξ]) es')
    ->  length es'
      = length es.
  Proof.
    itr - σ ξ es' es Heq.
    cwr - Heq.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_exp_flatten_eq :
    forall σ ξ ees' ees,
        ees
      = (map
          (fun '(ᵏe, ᵛe) => ((erase_exp σ ᵏe).[ξ], (erase_exp σ ᵛe).[ξ]))
          ees')
    ->  length (flatten_list ees')
      = length (flatten_list ees).
  Proof.
    itr - σ ξ ees' ees Heq.
    cwr - Heq.
    do 2 rewrite length_flatten_list.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_val :
    forall vs,
      length (map erase_val vs)
    = length vs.
  Proof.
    itr.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_val_eq :
    forall vs' vs,
        vs = (map erase_val vs')
    ->  length vs'
      = length vs.
  Proof.
    itr - vs' vs Heq.
    cwr - Heq.
    bwr - length_map.
  Qed.



  Lemma length_map_erase_val_flatten_eq :
    forall vvs' vvs,
        vvs = (map (fun '(ᵏv, ᵛv) => (erase_val ᵏv, erase_val ᵛv)) vvs')
    ->  length (flatten_list vvs')
      = length (flatten_list vvs).
  Proof.
    itr - vvs' vvs Heq.
    cwr - Heq.
    do 2 rewrite length_flatten_list.
    bwr - length_map.
  Qed.



  Lemma erase_val_empty_or_single_also :
    forall vs,
        (vs = [] \/ exists v, vs = [v])
    ->  (map erase_val vs = [] \/ exists v,  map erase_val vs = [v]).
  Proof.
    itr - vs Heither.
    des - Heither as [Hempty| Hsingle].
    * lft.
      sbt.
      trv.
    * rgt.
      ivc - Hsingle as [v].
      exi - (erase_val v).
      bmp.
  Qed.



End EraseNames_LengthLemmas.