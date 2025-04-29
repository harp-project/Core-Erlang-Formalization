From CoreErlang.Eqvivalence Require Export E4Basics.

Import BigStep.
Import E3Notations.

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



(*Remove list of keys from Environment:*)
(*env.rem.keys*)
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



(*Remove empty list of keys from environment:*)
(*env.rem.keys.nil*)
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



(*Exception class to value:*)
(*exclass.to.val*)
  Definition convert_class
      (c : ExceptionClass)
      : ExcClass
      :=
    match c with
    | Error =>  CoreErlang.Syntax.Error
    | Throw =>  CoreErlang.Syntax.Throw
    | Exit =>   CoreErlang.Syntax.Exit
    end.



(*Get variables of pattern list:*)
(*get.vars.pats*)
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



(*Eraser:*)
(*erase.tpye*)
  Definition Eraser
      : Type
      :=
    list Key.



(*Erase the name of key:*)
(*erase.key*)
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



(*Erase names from pattern:*)
(*erase.pat*)
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






(*Erase names from expression:*)
(*erase.exp*)
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






(*Erase names from value:*)
(*erase.val*)
  Fixpoint erase_val'
      (n : nat)
      (v : Value)
      : Val
      :=

    (* let
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
          (os ᵒ++ xs ˣ++ Γ.keys)
          (Γ.vals)
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
    in *)

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
        (Syntax.VClos
          (map
            (fun '(id, f, (xs', e')) =>
              (id, length xs, erase_exp (os ᵒ++ xs' ˣ++ Γ.keys) e'))
            os)
          0
          (length xs)
          (erase_exp (os ᵒ++ xs ˣ++ Γ.keys) e))
          .[list_subst (map (fun v => erase_val' n' v) Γ.vals) idsubst]ᵥ
          (* (erase_ext n' Γ os)
          0
          (length xs)
          (erase_body n' Γ os xs e) *)
      end
    end.






(*Erase names from value:*)
(*erase.val*)
  Definition erase_val
      (v : Value)
      : Val
      :=

    (* let
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
          (os ᵒ++ xs ˣ++ Γ.keys)
          (Γ.vals)
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
    in *)

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
      (* Syntax.VClos
        (erase_ext Γ os)
        0
        (length xs)
        (erase_body Γ os xs e) *)
      (Syntax.VClos
          (map
            (fun '(id, f, (xs', e')) =>
              (id, length xs, erase_exp (os ᵒ++ xs' ˣ++ Γ.keys) e'))
            os)
          0
          (length xs)
          (erase_exp (os ᵒ++ xs ˣ++ Γ.keys) e))
          .[list_subst (map (fun v => erase_val' ᵛ|v| v) Γ.vals) idsubst]ᵥ

    end.



End EraseNames_Bigs.









Section EraseNames_Smalls.



(*Erase names from expression and substitute environment:*)
(*erase.exp.subst.env*)
  Definition erase_names
      (Γ : Environment)
      (e : Expression)
      : Exp
      :=
    (erase_exp Γ.keys e)
    .[list_subst (map erase_val Γ.vals) idsubst].



(*Erase names from value sequence:*)
(*erase.valseq*)
  Definition erase_valseq
      (vs : ValueSequence)
      : ValSeq
      :=
    map erase_val vs.



(*Erase names from exception:*)
(*erase.exc*)
  Definition erase_exc
      (q : Exception)
      : CoreErlang.Syntax.Exception
      :=
    match q with
    | (c, ʳv, ᵈv) =>
      (convert_class c, erase_val ʳv, erase_val ᵈv)
    end.



(*Erase names from result:*)
(*erase.result*)
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

















































(*
(* Section Scope_Destructs. *)



  (** DOCUMENTATION:
  * des_for --> destruct_foralls; rename
    - N:[ident]:1-10 : N:[ident]:1-10
  *)

  Tactic Notation "des_for"
      :=
    destruct_foralls.

  Tactic Notation "des_for"
      "-"   ident(In1)
      ":"   ident(Io1)
      :=
    destruct_foralls;
    ren - In1:
          Io1.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2)
      ":"   ident(Io1) ident(Io2)
      :=
    destruct_foralls;
    ren - In1 In2:
          Io1 Io2.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3)
      ":"   ident(Io1) ident(Io2) ident(Io3)
      :=
    destruct_foralls;
    ren - In1 In2 In3:
          Io1 Io2 Io3.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4:
          Io1 Io2 Io3 Io4.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5:
          Io1 Io2 Io3 Io4 Io5.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6:
          Io1 Io2 Io3 Io4 Io5 Io6.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7) ident(In8)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7) ident(Io8)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7) ident(In8) ident(In9)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7) ident(Io8) ident(Io9)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8 In9:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9.

  Tactic Notation "des_for"
      "-"   ident(In1) ident(In2) ident(In3) ident(In4) ident(In5)
            ident(In6) ident(In7) ident(In8) ident(In9) ident(In10)
      ":"   ident(Io1) ident(Io2) ident(Io3) ident(Io4) ident(Io5)
            ident(Io6) ident(Io7) ident(Io8) ident(Io9) ident(Io10)
      :=
    destruct_foralls;
    ren - In1 In2 In3 In4 In5 In6 In7 In8 In9 In10:
          Io1 Io2 Io3 Io4 Io5 Io6 Io7 Io8 Io9 Io10.



(* End Scope_Destructs. *)








Import SubstSemantics.
Section Scope_Lists.



  Lemma scope_list_nth_succ :
    forall A i vl (f : A -> Val),
        (i < length vl
        ->  VALCLOSED (nth i (map f vl) VNil))
    ->  (S i < S (length vl)
        ->  VALCLOSED (nth i (map f vl) VNil)).
  Proof.
    (* #1 Pose: intro/pose/destruct/ *)
    itr - A i vl f Hvl Hsucc_lt.
    pse - Nat.succ_lt_mono as Hmono_succ_lt: i (base.length vl).
    des - Hmono_succ_lt as [_ Hfrom_succ_lt].
    (* #2 Apply: apply *)
    app - Hfrom_succ_lt in Hsucc_lt as Hlt; clr - Hfrom_succ_lt.
    bpp - Hvl in Hlt.
  Qed.



  Lemma scope_list_nth_succ_id :
    forall i vl,
        (i < length vl
        ->  VALCLOSED (nth i vl VNil))
    ->  (S i < S (length vl)
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
    by pose proof scope_list_nth_succ Val i vl id Hvl.
  Qed.



  Lemma scope_list_to_nth :
    forall vl,
        (Forall (fun v => VALCLOSED v) vl)
    ->  (forall i,
            i < base.length vl
        ->  VALCLOSED (nth i vl VNil)).
  Proof.
    itr - vl Hvl.
    itr - i Hlt.
    erewrite -> Forall_nth in Hvl.
    bpe - Hvl: i VNil Hlt.
  Qed.



End Scope_Lists.









Section Scope_Value.



  Theorem scope_vcons :
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






  Theorem scope_vtuple :
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
    bse - scope_list_nth_succ_id: i vl (Hvl i) Hl.
  Qed.






  Theorem scope_vmap :
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
      by pose proof scope_list_nth_succ (Val * Val) i vl fst (Hvl i) Hl.
    * (* #4.2 Simplify: intro/simpl *)
      itr - i Hl.
      smp *.
      (* #5.2 Destruct: clear/destruct + exact *)
      clr - Hv1 v1.
      des - i: exa - Hv2.
      (* #6.2 Inversion: inversion *)
      ivc - Hvl as Hvl: H2 / H0 v2 Hv2.
      (* #7.2 Finish: pose *)
      by pose proof scope_list_nth_succ (Val * Val) i vl snd (Hvl i) Hl.
  Qed.






  Theorem scope_app :
    forall vl1 vl2,
        is_result (RValSeq vl1)
    ->  is_result (RValSeq vl2)
    ->  is_result (RValSeq (vl1 ++ vl2)).
  Proof.
    itr - vl1 vl2 Hvl1 Hvl2.
    (* #1 Inversion on Hypothesis: inversion/subst *)
    ivc - Hvl1 as Hvl1: H0.
    ivc - Hvl2 as Hvl2: H0.
    (* #2 Open IsResult: constructor *)
    cns.
    (* #3 Solve by Forall Application Theorem: apply; auto *)
    app - Forall_app.
    ato.
  Qed.






  Theorem scope_cons :
    forall v vl,
        is_result (RValSeq [v])
    ->  is_result (RValSeq vl)
    ->  is_result (RValSeq (v :: vl)).
  Proof.
    itr - v vl Hv Hvl.
    (* #1 Solve By Previues Theorem (Scope App): rewrite/apply + auto *)
    rwr - cons_app.
    app - scope_app; ato.
  Qed.






  Theorem scope_list_to_tuple :
    forall vl,
        is_result (RValSeq vl)
    ->  is_result (RValSeq [VTuple vl]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - vl Hvl.
    ivc - Hvl as Hvl: H0.
    (* #3 Constructor: constructor *)
    do 3 cns.
    (* #4 By List to Nth Lemma: apply/trivial *)
    bpp - scope_list_to_nth.
  Qed.






  Theorem scope_list_to_map :
    forall vll,
        is_result (RValSeq (flatten_list vll))
    ->  is_result (RValSeq [VMap vll]).
  Proof.
    (* #1 Inversion: intro/inversion/destruct_foralls *)
    itr - vll Hvll.
    ivc - Hvll as Hvll: H0.
    ind - vll as [| [v1 v2] vll IHvll].
    * do 3 cns.
      - smp; itr; lia.
      - smp; itr; lia.
    * do 3 cns.
      - ivc - Hvll as Hv1 Hvll: H1 H2.
        ivc - Hvll as Hv2 Hvll: H1 H2.
        spc - IHvll: Hvll.
        ivc - IHvll as IHvll: H0.
        ivc - IHvll as IHvll: H1 / H2.
        ivc - IHvll as Hvll_fst Hvll_snd: H0 H2.
        itr - i Hlt.
        smp *.
        des - i: asm |> clr - Hv1.
        app - Hvll_fst.
        lia.
      - ivc - Hvll as Hv1 Hvll: H1 H2.
        ivc - Hvll as Hv2 Hvll: H1 H2.
        spc - IHvll: Hvll.
        ivc - IHvll as IHvll: H0.
        ivc - IHvll as IHvll: H1 / H2.
        ivc - IHvll as Hvll_fst Hvll_snd: H0 H2.
        itr - i Hlt.
        smp *.
        des - i: asm |> clr - Hv2.
        app - Hvll_snd.
        lia.
  Qed.



End Scope_Value.









(* Section Scope_Tactics. *)



  Ltac scope :=
    try (apply scope_vcons; [assumption ..]);
    try (apply scope_vtuple; [assumption ..]);
    try (apply scope_vmap; [assumption ..]);
    try (simpl in *; assumption);
    try (constructor);
    try (destruct_foralls);
    try (assumption + scope_solver).



  (** DOCUMENTATION:
  * open --> eexists; split; [> scope]; clear.
    / [ident]:0-3
    - hyp
  *)

  Tactic Notation "open"
      :=
    eexists; split; [(scope + admit) | idtac].

  Tactic Notation "open"
      "/"   ident(I1)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1.

  Tactic Notation "open"
      "/"   ident(I1) ident(I2)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2.

  Tactic Notation "open"
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    eexists; split; [(scope + admit) | idtac];
    clear I1 I2 I3.

  Tactic Notation "open"
      "-"   ident(H)
      :=
    eexists; split; [ivs - H; (scope + admit) | clear H].



(* End Scope_Tactics. *)









(* Section Step. *)



  Ltac do_step
    :=
    (econstructor;
    [ (constructor; auto + scope_solver + congruence)
    + (econstructor; constructor)
    + (econstructor;
      [ congruence
      | constructor ])
    | simpl ])
    + (cbn; constructor).



  Ltac do_transitive H
    :=
    eapply transitive_eval;
    [ eapply frame_indep_core in H;
      exact H
    | clear H;
      simpl ].



  (** DOCUMENTATION:
  * step --> repeat step; (exact H + do_transitive H).
    / [ident]:0-5
    - hyp / [ident]:0-10
    - tactic / [ident]:0-5
  *)

  Tactic Notation "step"
      :=
    repeat do_step.

  Tactic Notation "step"
      "/"   ident(I1)
      :=
    repeat do_step;
    clear I1.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    clear I1 I2.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    clear I1 I2 I3.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    clear I1 I2 I3 I4 I5.

  Tactic Notation "step"
      "-"   hyp(H)
      :=
    repeat do_step;
    (exact H + do_transitive H).

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8) ident(I9)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

  Tactic Notation "step"
      "-"   hyp(H)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
            ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
      :=
    repeat do_step;
    (exact H + do_transitive H);
    clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

  Tactic Notation "step"
      ":"   tactic(T)
      :=
    repeat do_step;
    [T | idtac].

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1)
      :=
    repeat do_step;
    [T | idtac];
    clear I1.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2) ident(I3)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2 I3.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2 I3 I4.

  Tactic Notation "step"
      ":"   tactic(T)
      "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
      :=
    repeat do_step;
    [T | idtac];
    clear I1 I2 I3 I4 I5.

Import BigStep.

Open Scope string_scope.

(** CONTENT:
* ERASE_NAMES_TEST_SUCCESS (LEMMAS)
  - EraseNames_Test_Compute
  - EraseNames_Test_Success
* ERASE_NAMES_TEST_EXCEPTION (LEMMAS)
  - EraseNames_Test_Exception
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_NAMES_TEST_SUCCESS /////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EraseNames_Test_Compute.



Compute erase_names
  []
  (ECons ENil (ELit (Integer 1))).
(*
  ° Syntax.ECons (˝ Syntax.VNil) (˝ Syntax.VLit 1%Z)
*)



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (EVar "X").



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (ECons ENil (EVar "X")).
(*
  ° Syntax.ECons (˝ Syntax.VNil) (˝ Syntax.VLit 2%Z)
*)



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (EFun ["X"] (EVar "X")).
(*
  ° Syntax.EFun 1 (˝ VVar 0)
*)



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (ECons (EVar "X") (EFun ["X"] (EVar "X"))).
(*
  ° Syntax.ECons (˝ Syntax.VLit 2%Z) (° Syntax.EFun 1 (˝ VVar 0))
*)



Compute erase_names
  []
  (ELetRec [(("x", 1), (["X"], EApp (EFunId ("x", 1)) [EVar "X"])) ]
           (EApp (EFunId ("x", 1)) [ETuple []])).
(*
° Syntax.ELetRec [(1, ° Syntax.EApp (˝ VFunId (1, 1)) [˝ VVar 0])]
           (° Syntax.EApp (˝ VFunId (0, 1)) [° Syntax.ETuple []])
*)



Compute erase_names
  [(inl "X", (VLit (Integer 1))); (inl "Z", (VLit (Integer 4)))]
  (ELet
    ["X"; "Y"]
    (EValues [EVar "Z"; ELit (Integer 3)]) (EFun ["X"]
    (ETuple [EVar "X"; EVar "Y"; EVar "Z"]))).



Compute erase_names
  [(inl "X",
    (VClos
      [(inl "Z", (VLit (Integer 1))); (inl "X", (VLit (Integer 1))); (inl "Y", (VLit (Integer 4)))]
      []
      0
      ["Y";"X"]
      (ETuple [EVar "X"; EVar "Y"])))]
  (EVar "X").



End EraseNames_Test_Compute.









Section EraseNames_Test_Success.



  Lemma erase_names_test_X1 :
    step_any
      []
      (erase_names
        [(inr ("fun1",0), VLit (Integer 20));(inr ("fun2",0), VLit (Integer 20));(inr ("fun3",0), VLit (Integer 20))]
        ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                  (EApp (EFunId ("fun1",0)) []))))
      (erase_result
        ((inl [VLit (Integer 42)]))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X2 :
    step_any
      []
      (erase_names
        []
        (ELetRec
          [(("f", 1), (["X"],
            ECase (EVar "X")
              [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 5));
              ([PLit (Integer 1)], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 0)]);
              ([PVar "A"], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 1)])]
          ))]
          (ELet ["X"] (EFun ["F"]
               (ELetRec [(("f", 1), (["X"], ELit (Integer 0)))] 
                  (EApp (EVar "F") [ELit (Integer 2)])
               ))
            (EApp (EVar "X") [EFunId ("f", 1)])
           )))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 50 do_step.
  Qed.



  Lemma erase_names_test_X3 :
    step_any
      []
      (erase_names
        [(inr ("fun2", 0), 
         VClos [(inr ("fun1",0), VLit (Integer 20));(inr ("fun2",0), VLit (Integer 20));(inr ("fun3",0), VLit (Integer 20))] [(0, ("fun2", 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))]
        (ELetRec [(("fun2", 0), ([], ELit (Integer 40)))] 
           (EApp (EFunId ("fun2", 0)) [])))
      (erase_result
        (inl [VLit (Integer 40)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X4 :
    step_any
      []
      (erase_names
        [(inr ("fun2", 0), 
           VClos [] [(0, ("fun2", 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)))]
        (ELetRec [(("fun2", 1), (["X"], (ELit (Integer 40))))] 
           (EApp (EFunId ("fun2", 0)) [])))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X5 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] (EMap [])])
           (EMap [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X6 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["Y"] (EValues [EFun [] (EVar "X")])
          (EApp (EVar "Y") [])))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X7 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 1)) 
              (ELet ["X"] (ELit (Integer 2)) 
                 (EVar "X"))))
      (erase_result
        (inl [VLit (Integer 2)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X8 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ETuple []) (EMap [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X9 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyMap)]
        (ELet ["X"] (ETuple []) (EMap [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X10 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyMap)]
        (ELet ["X"; "X"; "Y"] (EValues [ETuple []; ENil; EVar "X"])
          (EVar "Y")))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X11 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 5)) (EVar "X")))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 5 do_step.
  Qed.



  Lemma erase_names_test_X12 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Atom "foo")); 
          (inl "Y", VEmptyTuple)]
        (ETuple [ELit (Integer 5); EVar "X"; EVar "Y"]))
      (erase_result
        (inl [VTuple [VLit (Integer 5); VLit (Atom "foo"); VEmptyTuple]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 9 do_step.
  Qed.



  Lemma erase_names_test_X13 :
    step_any
      []
      (erase_names
        [(inr ("Plus", 2), 
         VClos [] [(0, ("Plus", 2),
                       (["X" ; "Y"], ELit (Integer 3)))] 
                  0 ["X" ; "Y"] 
                  (ELit (Integer 3)))]
        (EApp (EFunId ("Plus", 2)) [ELit (Integer 2); ELit (Integer 3)]))
      (erase_result
        (inl [VLit (Integer 3)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X14 :
    step_any
      []
      (erase_names
        [(inl "Minus",
            VClos [] [] 0 ["X"; "Y"] (ELit (Integer 42))) ; 
          (inl "X", VEmptyMap)]
        (EApp (EVar "Minus") [EVar "X"; EVar "X"]))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X15 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (ECons (EVar "X") (ENil)))
      (erase_result
        (inl [VCons (VLit (Integer 5)) (VNil)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X16 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (ECons (EVar "X") 
           (ECons (EVar "X") 
                  (ENil))))
      (erase_result
        (inl [VCons (VLit (Integer 5))
                   (VCons (VLit (Integer 5)) 
                          (VNil))])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X17 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (EFun [] (ETuple [])) 
             (ELet ["X"] (ELit (Integer 5)) 
               (EVar "X"))))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X18 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (EMap [(ELit (Integer 5), EVar "X")]))
      (erase_result
        (inl [VMap [(VLit (Integer 5), VLit (Integer 42))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X19 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (EMap [(ELit (Integer 54), EVar "X"); (EVar "X", EVar "X")] ))
      (erase_result
        (inl [VMap [(VLit (Integer 42), VLit (Integer 42)); 
                   (VLit (Integer 54), VLit (Integer 42))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X20 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (EMap [(ELit (Integer 5), EVar "X"); 
           (EVar "X", ECall (ELit (Atom "erlang")) (ELit (Atom "+")) 
                                [ELit (Integer 1); (EVar "X")])]))
      (erase_result
        (inl [VMap [(VLit (Integer 5), VLit (Integer 6))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X21 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"; "Y"; "Z"] 
              (EValues [EFun [] (ELit (Integer 1)); 
                        EFun [] (ELit (Integer 2)); 
                        EFun [] (ELit (Integer 3))])
           (EMap [(EVar "Z", ELit (Integer 10)); 
                  (EVar "X", ELit (Integer 11));
                  (EVar "Y", ELit (Integer 12)); 
                  (EVar "X", ELit (Integer 13))])))
      (erase_result
        (inl [VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                    (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                    (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
      do 16 do_step.
      do 1 do_step.
      (* make_val_map different ?*)
      (* maybe the id?*)
  Admitted.



  Lemma erase_names_test_X22 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 42))
         (ELet ["Y"] (EFun ["X"] (EVar "X")) 
           (ELet ["X"] (ELit (Integer 5))
             (EApp (EVar "Y") [ELit (Integer 7)])))))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 17 do_step.
  Qed.



  Lemma erase_names_test_X23 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 42)) 
         (ELet ["Y"] (EFun [] (EVar "X"))
           (ELet ["X"] (ELit (Integer 5))
             (EApp (EVar "Y") [])))))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X24 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X" ; ELit (Integer 2)]))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



  Lemma erase_names_test_X25 :
    step_any
      []
      (erase_names
        []
        (ELet ["Z"] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 2) ; ELit (Integer 2)] ) 
         (ELet ["Y"] (EFun [] (EVar "Z"))
            (ELet ["X"] (EFun [] (EApp (EVar "Y") [])) 
              (EApp (EVar "X") [])))))
      (erase_result
        (inl [VLit (Integer 4)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 28 do_step.
  Qed.



  Lemma erase_names_test_X26 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyTuple)]
        (ECase (EVar "X")
           [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
            ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6)); 
            ([PVar "Z"], ELit (Atom "true"), EVar "Z") ]))
      (erase_result
        (inl [VEmptyTuple])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X27 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyTuple)]
        (ECase (EVar "X") 
           [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
            ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6));
            ([PVar "Z"], ELit (Atom "false"), EVar "Z");
            ([PVar "Z"], ELit (Atom "true"), EMap [])]))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X28 :
    step_any
      []
      (erase_names
        [(inl "X", VClos [(inl "Y", VLit (Atom "true"))] [] 0 [] (EVar "Y")); (inl "Y", VLit (Atom "true"))]
        (ECase (EValues [EVar "X"; EVar "Y"])
           [([PLit (Integer 5); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 5)); 
            ([PLit (Integer 6); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 6)); 
            ([PVar "Z"; PLit (Atom "true")], ELit (Atom "true"), EApp (EVar "Z") [])]))
      (erase_result
        (inl [VLit (Atom "true")])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 18 do_step.
  Qed.



  Lemma erase_names_test_X29 :
    step_any
      []
      (erase_names
        [(inr ("fun4", 0), VClos [] [(0, ("fun4", 0), ([], EMap []))] 0 [] (EMap [])) ; 
          (inl "X", VLit (Integer 42))]
        (ELetRec [(("fun2", 0), ([], EVar "X")); 
              (("fun4", 1), (["Z"], EVar "Z"))] 
          (EApp (EFunId ("fun4", 0)) [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X30 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (EApp (EFun ["Y"] (EVar "Y")) [EVar "X"]))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X31 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (EFun [] (ELit (Integer 5))) 
         (ELet ["X"] (EFun [] (ELit (Integer 6))) 
           (EApp (EVar "X") []))))
      (erase_result
        (inl [VLit (Integer 6)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X32 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 5)) (EVar "X")))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 5 do_step.
  Qed.



  Lemma erase_names_test_X33 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 4)) 
            (ELet ["X"] (EFun [] (EVar "X")) 
               (ELet ["X"] (EFun [] (EApp (EVar "X") []))
                  (EApp (EVar "X") [])))))
      (erase_result
        (inl [VLit (Integer 4)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X34 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (EFun [] (EFun [] (ELit (Integer 5))))
        (EApp (EApp (EVar "X") []) [])))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X35 :
    step_any
      []
      (erase_names
        []
        (ELetRec [(("fun1", 0), ([], (EFun [] (ELit (Integer 5)))))] 
        (EApp (EApp (EFunId ("fun1", 0)) []) [])))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



  Lemma erase_names_test_X36 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 7))]
        (ELet ["X"] (EFun [] (EFun [] (EVar "X")))
       (EApp (EApp (EVar "X") []) [])))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X37 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 7))]
        (ELetRec [(("fun1", 0), ([], EFun [] (EVar "X")))] 
        (EApp (EApp (EFunId ("fun1", 0)) []) [])))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



  Lemma erase_names_test_X38 :
    step_any
      []
      (erase_names
        []
        (ELet ["F"] 
       (EFun ["X"] 
          (ELet ["Y"] (ECall (ELit (Atom "erlang" ))  (ELit (Atom "+" )) [EVar "X"; ELit (Integer 3)] ) 
                (EFun ["Z"] 
                      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))
                            [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X"; EVar "Y"]
                       ; EVar "Z"]))))
    (EApp (EApp (EVar "F") [ELit (Integer 1)]) [ELit (Integer 1)])))
      (erase_result
        (inl [VLit (Integer 6)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 47 do_step.
  Qed.



  Lemma erase_names_test_X39 :
    step_any
      []
      (erase_names
        []
        (ELetRec [(("f", 1), (["X"], 
          ECase (EVar "X") [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 0)); 
                                 ([PVar "Y"], ELit (Atom "true"), 
                                 ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [
                                       EVar "Y"; 
                                       EApp (EFunId ("f", 1)) [ ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "Y"; ELit (Integer (Z.pred 0))] ]
                                ])]
        ))] (EApp (EFunId ("f", 1)) [ELit (Integer 2)])))
      (erase_result
        (inl [VLit (Integer 3)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 74 do_step.
  Qed.



  Lemma erase_names_test_X40 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 42)) 
         (ELetRec [(("f", 0), ([], EVar "X"))]
           (ELet ["X"] (ELit (Integer 5))
             (EApp (EFunId ("f", 0)) [])))))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X41 :
    step_any
      []
      (erase_names
        []
        (ESeq (ELet ["X"] (ELit (Integer 42)) (EVar "X"))
                  (ELet ["Y"] (ELit (Integer 20)) (EVar "Y"))))
      (erase_result
        (inl [VLit (Integer 20)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



End EraseNames_Test_Success.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_NAMES_TEST_EXCEPTION ///////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EraseNames_Test_Exception.



  Lemma erase_names_test_X42 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X43 :
    step_any
      []
      (erase_names
        []
        (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])   (ELit (Atom "error"%string))) )
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 16 do_step.
  Qed.



  Lemma erase_names_test_X44 :
    step_any
      []
      (erase_names
        []
        (ECons (ELit (Atom "error"%string)) (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ENil))))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 18 do_step.
  Qed.



  Lemma erase_names_test_X45 :
    step_any
      []
      (erase_names
        []
        (ETuple [ELit (Atom "error"%string) ; ELit (Atom "error"%string); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X46 :
    step_any
      []
      (erase_names
        []
        (ETry (ETuple []) ["X"%string]
                 (ELit (Atom "ok"%string)) 
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ELit (Atom "error"%string))))
      (erase_result
        (inl [VLit (Atom "ok")])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X47 :
    step_any
      []
      (erase_names
        []
        (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
                 (ELit (Atom "ok"%string))
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ELit (Atom "error"%string))))
      (erase_result
        (inl [VLit (Atom "error"%string)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X48 :
    step_any
      []
      (erase_names
        []
        (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
                 (ELit (Atom "ok"%string))
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 25 do_step.
  Qed.



  Lemma erase_names_test_X49 :
    step_any
      []
      (erase_names
        []
        (ETry (ETuple []) ["X"%string]
                 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ELit (Atom "error"%string))))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 16 do_step.
  Qed.



  Lemma erase_names_test_X50 :
    step_any
      []
      (erase_names
        []
        (ECase (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                   [([PVar "X"%string], ELit (Atom "true"), ELit (Integer 1))]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X51 :
    step_any
      []
      (erase_names
        [(inl "Y"%string, VLit (Integer 2))]
        (ECase (EVar "Y"%string)
            [([PLit (Integer 1)], ELit (Atom "true"), ELit (Integer 1)); 
             ([PVar "Z"%string], ELit (Atom "false"), ELit (Integer 2))]))
      (erase_result
        (inr (if_clause))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X52 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string []))
      (erase_result
        (inr (undef (VLit (Atom "+"))))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X53 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ETuple []]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X54 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 21 do_step.
  Qed.



  Lemma erase_names_test_X55 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"%string; "Y"%string] 
                 (EValues [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) (ETuple [])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X56 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
                 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 20 do_step.
  Qed.



  Lemma erase_names_test_X57 :
    step_any
      []
      (erase_names
        []
        (EApp (ELit (Integer 4)) [ELit (Integer 5); ELit (Integer 5)]))
      (erase_result
        (inr (badfun (VLit (Integer 4))))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 9 do_step.
  Qed.



  Lemma erase_names_test_X58 :
    step_any
      []
      (erase_names
        []
        (EApp (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) [ELit (Integer 5); ELit (Integer 5)]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X59 :
    step_any
      []
      (erase_names
        [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))]
        (EApp (EVar "X"%string) [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 17 do_step.
  Qed.



  Lemma erase_names_test_X60 :
    step_any
      []
      (erase_names
        [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))]
        (EApp (EVar "X"%string) [ELit (Integer 2)]))
      (erase_result
        (inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)))))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X61 :
    step_any
      []
      (erase_names
        [(inl "X"%string, VClos [] [] 0 [] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))]
        (EApp (EVar "X"%string) []))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 16 do_step.
  Qed.



  Lemma erase_names_test_X62 :
    step_any
      []
      (erase_names
        []
        (ELetRec [(("fun1"%string, 0), ([], ELit (Atom "error"%string)))] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X63 :
    step_any
      []
      (erase_names
        []
        (EMap [(ELit (Atom "error"%string),  ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []], ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string))]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 22 do_step.
  Qed.



  Lemma erase_names_test_X64 :
    step_any
      []
      (erase_names
        []
        (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string))]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 20 do_step.
  Qed.



  Lemma erase_names_test_X65 :
    step_any
      []
      (erase_names
        []
        (ESeq (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                  (ELit (Integer 42))))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X66 :
    step_any
      []
      (erase_names
        []
        (ESeq (ELit (Integer 42))
                  (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X67 :
    step_any
      []
      (erase_names
        []
        (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string))], ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])])])])])])]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 114 do_step.
  Qed.



End EraseNames_Test_Exception.

Section EraseValRemFuel_Theorems.

  Theorem erase_val_rem_fuel :
    forall v,
      erase_val' (measure_val v) v
    = erase_val v.
  Proof.
  Admitted.






  Theorem erase_val_rem_fuel_any :
    forall v n,
        measure_val v <= n
    ->  erase_val' n v
      = erase_val v.
  Proof.
  Admitted.



  Theorem erase_val_rem_fuel_list :
    forall vl,
      map (fun v => erase_val' (measure_val v) v) vl
    = map (fun v => erase_val v) vl.
  Proof.
  Admitted.



  Lemma erase_val_rem_fuel_map :
    forall vll,
      map
        (fun '(v1, v2) =>
          (erase_val' (measure_val v1) v1, erase_val' (measure_val v2) v2))
        vll
    = map (fun '(v1, v2) => (erase_val v1, erase_val v2)) vll.
  Proof.
  Admitted.



End EraseValRemFuel_Theorems.









(* Section EraseValRemFuel_Tactics. *)



  Ltac mred_le_solver :=
    smp;
    try unfold measure_val_list;
    try unfold measure_val_map;
    try unfold measure_val_env;
    try rewrite map_app, list_sum_app;
    sli.

  Ltac mvr :=
    try (rewrite erase_val_rem_fuel in * );
    try (rewrite erase_val_rem_fuel_any in *; [idtac | mred_le_solver]);
    try (rewrite erase_val_rem_fuel_list in * );
    try (rewrite erase_val_rem_fuel_map in * ).



(* End EraseValRemFuel_Tactics. *)

  Theorem eq_bsfs_elit_to_vlit :
    forall Γ lᴮ ,
      ⟨ [], erase_names Γ (ELit lᴮ) ⟩ -->* erase_valseq [VLit lᴮ].
  Proof.
    itr.
    (* #1 Unfold Converters: simpl *)
    smp.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
    rem - lᶠ as Hl / Hl lᴮ Γ:
      (convert_lit lᴮ).
    (* #3 FrameStack Evaluation: open/step *)
    open.
    step.
  Qed.


Theorem eq_bsfs_econs_to_vcons :
    forall Γ e₁ᴮ e₂ᴮ v₁ᴮ v₂ᴮ,
        ⟨ [], erase_names Γ e₁ᴮ ⟩ -->* erase_valseq [v₁ᴮ]
    ->  ⟨ [], erase_names Γ e₂ᴮ ⟩ -->* erase_valseq [v₂ᴮ]
    ->  ⟨ [], erase_names Γ (ECons e₁ᴮ e₂ᴮ) ⟩ -->* erase_valseq [VCons v₁ᴮ v₂ᴮ].
  Proof.
    itr - Γ e₁ᴮ e₂ᴮ v₁ᴮ v₂ᴮ IHFse_v₁ IHFse_v₂.
    (* #1 Unfold Converters: simpl/unfold/mvr *)
    smp *.
    ufl - erase_names in *.
    do 2 mvr.
    (* #2 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (Γ.keys).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ Γ:
      (list_subst (map erase_val Γ.vals) idsubst).
      (* Expressions *)
    rem - e₁ᶠ e₂ᶠ as Heqv_e₁ Heqv_e₂ / Heqv_e₁ Heqv_e₂ e₁ᴮ e₂ᴮ σ ξ:
      ((erase_exp σ e₁ᴮ).[ξ])
      ((erase_exp σ e₂ᴮ).[ξ]).
      (* Values *)
    rem - v₁ᶠ v₂ᶠ as Heqv_v₁ Heqv_v₂ / Heqv_v₁ Heqv_v₂ v₁ᴮ v₂ᴮ:
      (erase_val v₁ᴮ)
      (erase_val v₂ᴮ).
    (* #3 Destruct Inductive Hypothesis: destruct *)
    des - IHFse_v₁ as [k_v₁ [Hscp_v₁ Hstp_v₁]].
    des - IHFse_v₂ as [k_v₂ [Hscp_v₂ Hstp_v₂]].
    (* #4 FrameStack Evaluation: open;step *)
    open / Hscp_v₁ Hscp_v₂.
    step - Hstp_v₂ / e₂ᶠ k_v₂.
    step - Hstp_v₁ / e₁ᶠ k_v₁.
    step.
  Qed.



  Theorem eq_bsfs_efun_to_vclos :
    forall Γ xsᴮ eᴮ id,
        is_result (erase_valseq [VClos Γ [] id xsᴮ eᴮ])
    ->  ⟨ [], erase_names Γ (EFun xsᴮ eᴮ) ⟩ -->*
              erase_valseq [VClos Γ [] id xsᴮ eᴮ].
  Proof.
    itr - Γ xsᴮ eᴮ id Hscp.
    (* #1 Unfold Converters: simpl/mvr *)
    smp *.
    mvr.
    ufl - eraser_add_ext get_fids eraser_add_fids eraser_add_keys in *.
    smp *.
    (* #4 Convert Syntax from BigStep to FrameStack: remember *)
      (* Erasers *)
    rem - σ as Heqv_σ / Heqv_σ:
      (eraser_add_vars xsᴮ (Γ.keys)).
      (* Substs *)
    rem - ξ as Heqv_ξ / Heqv_ξ:
      (upn (base.length xsᴮ)
           (list_subst (map erase_val Γ.vals) idsubst)).
      (* Variables *)
    rem - xsᶠ as Heqv_xs / Heqv_xs:
      (base.length xsᴮ).
      (* Expressions *)
    rem - eᶠ as Heqv_e / Heqv_e eᴮ ξ:
      ((erase_exp σ eᴮ).[ξ]).
    (* #5 FrameStack Evaluation: open/step *)
    open / Hscp.
    step.
  Qed.
*)