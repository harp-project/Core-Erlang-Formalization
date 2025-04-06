From CoreErlang.BigStep Require BigStep.
From CoreErlang Require SubstSemantics.
Require Export stdpp.list.

Import BigStep.
Import SubstSemantics.

(** CONTENT:
* BASICS
  - NewListNotations
    + ...
  - EnvironmentNotations
    + ...
  - SubstitutionNotations
    + ...
  - OtherNotations
    + ...
* GETTERS
  - Getters_Types
    + Key
    + Clause
    + Cla
    + ClosureItem
    + ClosItem
    + ClosureItemNoId
    + ClosItemNoId
    + Extension
    + Ext
    + ExtensionNoId
    + ExtNoId
  - Getters_Definitions
    + get_keys
    + get_vals
    + get_fids
    + get_fids_noid
  - GetterNotations
    + ...
* SYNTAX
  - BigStepNotations
    + ...
  - FrameStackNotations
    + ...
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: BASICS ///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Module NewListNotations. 

Import Maps.



  Notation "ˡ| l |" := (length l)
    (at level 1,
      format "ˡ| l |").

  Notation "↤ x" := (inl x)
    (at level 10,
      format "↤  x").

  Notation "x ↦ " := (inr x)
    (at level 20,
      format "x  ↦").

  Notation "↤⟦ l ⟧" := (map inl l)
    (at level 1,
      format "↤⟦ l ⟧").

  Notation "⟦ l ⟧↦" := (map inr l)
    (at level 1,
      format "⟦ l ⟧↦").

  Notation "⟦ l ⟧.1" := (map fst l)
    (at level 1,
      format "⟦ l ⟧.1").

  Notation "⟦ l ⟧.2" := (map snd l)
    (at level 1,
      format "⟦ l ⟧.2").

  Notation "l1 '⊗' l2" := (zip l1 l2)
    (at level 40,
      left associativity,
      format "l1  '⊗'  l2").

  Notation "↓↓ l" := (flatten_list l)
    (at level 10,
      format "↓↓  l").

  Notation "↑↑ l" := (deflatten_list l)
    (at level 10,
      format "↑↑  l").



End NewListNotations.









Module EnvironmentNotations. 

Import Environment.



  Notation "∅" := None.

  Notation "Γ '[' key ']'" := (get_value Γ key)
    (at level 20,
      format "Γ [ key ]").

  Notation "key '=ᵏ' k" := (var_funid_eqb key k)
    (at level 70,
      no associativity,
      format "key  =ᵏ  k").



  Notation "{ xs ✕ vs } 'ˣ++ᵉⁿᵛ' Γ" := (append_vars_to_env xs vs Γ)
    (at level 20,
      right associativity,
      format "{ xs ✕  vs }  ˣ++ᵉⁿᵛ  Γ").

  Notation "os 'ᵒ++ᵉⁿᵛ' Γ" := (get_env os Γ)
    (at level 20,
      right associativity,
      format "os  ᵒ++ᵉⁿᵛ  Γ").

  Notation "{ os <- n } 'ᵒ⁻++ᵉⁿᵛ' Γ" := (append_funs_to_env os Γ n)
    (at level 20,
      right associativity,
      format "{ os <- n }  ᵒ⁻++ᵉⁿᵛ  Γ").



End EnvironmentNotations.

Export EnvironmentNotations.









Module SubstitutionNotations.

Import Manipulation.



  Notation " n ⇡ ξ" := (upn n ξ)
    (at level 20,
      format "n  ⇡  ξ").

  Notation "'ξᵛˢ' ⟦ vs ⟧ ξ" := (list_subst vs ξ)
    (at level 20,
      format "'ξᵛˢ'  ⟦ vs ⟧  ξ").

  Notation "'ξᵛˢ' ⟦ vs ⟧ 'ξⁱᵈ'" := (list_subst vs idsubst)
    (at level 20,
      format "'ξᵛˢ'  ⟦ vs ⟧  'ξⁱᵈ'").



End SubstitutionNotations.









Module OtherNotations.



  Notation "n % m" := (n mod m)
    (at level 20,
      format "n  %  m").



End OtherNotations.

Export OtherNotations.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: GETTERS //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section Getters_Types.

Import BigStep.



  Definition Key
      : Type
      :=
    Var + FunctionIdentifier.



  Definition Clause
      : Type
      :=
    (list Pattern) * Expression * Expression.

  Definition Cla
      : Type
      :=
    (list Pat) * Exp * Exp.



  Definition ClosureItem
      : Type
      :=
    nat * FunctionIdentifier * FunctionExpression.

  Definition ClosItem
      : Type
      :=
    nat * nat * Exp.


  Definition ClosureItemNoId
      : Type
      :=
    FunctionIdentifier * FunctionExpression.

  Definition ClosItemNoId
      : Type
      :=
    nat * Exp.



  Definition Extension
      : Type
      :=
    list (ClosureItem).

  Definition Ext
      : Type
      :=
    list (ClosItem).


  Definition ExtensionNoId
      : Type
      :=
    list (ClosureItemNoId).

  Definition ExtNoId
      : Type
      :=
    list (ClosItemNoId).



End Getters_Types.









Section Getters_Definitions.



(*Get keys of map:*)
(*get.keys*)
  Definition get_keys
      (Γ : Environment)
      : list Key
      :=
    map fst Γ.



(*Get values of map:*)
(*het.vals*)
  Definition get_vals
      (Γ : Environment)
      : list Value
      :=
    map snd Γ.



(*Get function identifiers of extension:*)
(*get.fids*)
  Definition get_fids
      (ext : Extension)
      : list FunctionIdentifier
      :=
    map (snd ∘ fst) ext.



  Definition get_fids_noid
      (ext : ExtensionNoId)
      : list FunctionIdentifier
      :=
    map fst ext.



End Getters_Definitions.









Section Getters_Lemmas.



  Lemma get_keys_eq :
    forall Γ,
      map fst Γ
    = get_keys Γ.
  Proof.
    trivial.
  Qed.



  Lemma get_vals_eq :
    forall Γ,
      map snd Γ
    = get_vals Γ.
  Proof.
    trivial.
  Qed.



  Lemma get_fids_eq :
    forall ext,
        map (snd ∘ fst) ext
      = get_fids ext.
  Proof.
    trivial.
  Qed.



  Lemma get_fids_noid_eq :
    forall ext,
      map fst ext
    = get_fids_noid ext.
  Proof.
    trivial.
  Qed.






  Lemma get_keys_app :
    forall Γ₁ Γ₂,
      get_keys (Γ₁ ++ Γ₂)
    = get_keys Γ₁ ++ get_keys Γ₂.
  Proof.
    intros.
    unfold get_keys.
    rewrite map_app.
    trivial.
  Qed.



  Lemma get_vals_app :
    forall Γ₁ Γ₂,
      get_vals (Γ₁ ++ Γ₂)
    = get_vals Γ₁ ++ get_vals Γ₂.
  Proof.
    intros.
    unfold get_vals.
    rewrite map_app.
    trivial.
  Qed.



End Getters_Lemmas.









Module GetterNotations.



   Notation "Γ '.keys'" :=(get_keys Γ)
    (at level 1,
      format "Γ .keys").

  Notation "Γ '.vals'" := (get_vals Γ)
    (at level 1,
      format "Γ .vals").

  Notation "ext '.fids'" := (get_fids ext)
    (at level 1,
      format "ext .fids").

  Notation "ext .fids⁻" := (get_fids_noid ext)
    (at level 1,
      format "ext .fids⁻").



End GetterNotations.

Export GetterNotations.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: SYNTAX ///////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Module BigStepNotations.

Import BigStep.
Import ListNotations.

  Notation "'ᵖᴬ' a 'ᴮ'" := (PLit (Atom a))
    (at level 1,
        format "'ᵖᴬ' a 'ᴮ'").

  Notation "'ᵛᴬ' a 'ᴮ'" := (VLit (Atom a))
    (at level 1,
        format "'ᵛᴬ' a 'ᴮ'").

  Notation "'ᵉᴬ' a 'ᴮ'" := (ELit (Atom a))
    (at level 1,
        format "'ᵉᴬ' a 'ᴮ'").


  Notation "'ᵖᶻ' z 'ᴮ'" := (PLit (Integer z))
    (at level 1,
        format "'ᵖᶻ' z 'ᴮ'").

  Notation "'ᵛᶻ' z 'ᴮ'" := (VLit (Integer z))
    (at level 1,
        format "'ᵛᶻ' z 'ᴮ'").

  Notation "'ᵉᶻ' z 'ᴮ'" := (ELit (Integer z))
    (at level 1,
        format "'ᵉᶻ' z 'ᴮ'").



  Notation "'ᵖᴸ' l 'ᴮ'" := (PLit l)
    (at level 1,
      format "'ᵖᴸ' l 'ᴮ'").

  Notation "'ᵛᴸ' l 'ᴮ'" := (VLit l)
    (at level 1,
      format "'ᵛᴸ' l 'ᴮ'").

  Notation "'ᵉᴸ' l 'ᴮ'" := (ELit l)
    (at level 1,
      format "'ᵉᴸ' l 'ᴮ'").



  Notation "'ᵖˣ' x 'ᴮ'" := (PVar x)
    (at level 1,
      format "'ᵖˣ' x 'ᴮ'").

  Notation "'ᵉˣ' x 'ᴮ'" := (EVar x)
    (at level 1,
      format "'ᵉˣ' x 'ᴮ'").


   Notation "ⁿa /ᴮ ᵃn" := ((@pair string nat ⁿa ᵃn) : FunctionIdentifier)
    (at level 70,
      format "ⁿa /ᴮ ᵃn").

  Notation "ⁿa ᵉ/ᴮ ᵃn" := (EFunId (ⁿa, ᵃn))
    (at level 1,
      format "ⁿa ᵉ/ᴮ ᵃn").

  Notation "'ᵉᶠ' f 'ᴮ'" := (EFunId f)
    (at level 1,
      format "'ᵉᶠ' f 'ᴮ'").






  Notation "ᵖ[]ᴮ" := PNil
    (at level 1,
      format "ᵖ[]ᴮ").

  Notation "ᵛ[]ᴮ" := VNil
    (at level 1,
      format "ᵛ[]ᴮ").

  Notation "ᵉ[]ᴮ" := ENil
    (at level 1,
      format "ᵉ[]ᴮ").


  Notation "ᵖ[ p₁ | p₂ ]ᴮ" := (PCons p₁ p₂)
    (at level 1,
      format "ᵖ[ p₁ | p₂ ]ᴮ").

  Notation "ᵛ[ v₁ | v₂ ]ᴮ" := (VCons v₁ v₂)
    (at level 1,
      format "ᵛ[ v₁ | v₂ ]ᴮ").

  Notation "ᵉ[ e₁ | e₂ ]ᴮ" := (ECons e₁ e₂)
    (at level 1,
      format "ᵉ[ e₁ | e₂ ]ᴮ").


  Notation "ᵖ[ p₁ , .. , pₙ ]ᴮ" := (PCons p₁ .. (PCons pₙ PNil) .. )
    (at level 1,
      format "ᵖ[ p₁ ,  .. ,  pₙ ]ᴮ").

  Notation "ᵛ[ v₁ , .. , vₙ ]ᴮ" := (VCons v₁ .. (VCons vₙ VNil) .. )
    (at level 1,
      format "ᵛ[ v₁ ,  .. ,  vₙ ]ᴮ").

  Notation "ᵉ[ e₁ , .. , eₙ ]ᴮ" := (ECons e₁ .. (ECons eₙ ENil) .. )
    (at level 1,
      format "ᵉ[ e₁ ,  .. ,  eₙ ]ᴮ").



  Notation "ᵖ{ ps }ᴮ" := (PTuple ps)
    (at level 1,
      format "ᵖ{ ps }ᴮ").

  Notation "ᵛ{ vs }ᴮ" := (VTuple vs)
    (at level 1,
      format "ᵛ{ vs }ᴮ").

  Notation "ᵉ{ es }ᴮ" := (ETuple es)
    (at level 1,
      format "ᵉ{ es }ᴮ").

  Notation "ᵉ< es >ᴮ" := (EValues es)
    (at level 1,
      format "ᵉ< es >ᴮ").


  Notation "ᵖ{ p₁ , ps }ᴮ" := (PTuple (p₁ :: ps))
    (at level 1,
      format "ᵖ{ p₁ ,  ps }ᴮ").

  Notation "ᵛ{ v₁ , vs }ᴮ" := (VTuple (v₁ :: vs))
    (at level 1,
      format "ᵛ{ v₁ ,  vs }ᴮ").

  Notation "ᵉ{ e₁ , es }ᴮ" := (ETuple (e₁ :: es))
    (at level 1,
      format "ᵉ{ e₁ ,  es }ᴮ").

  Notation "ᵉ< e₁ , es >ᴮ" := (EValues (e₁ :: es))
    (at level 1,
      format "ᵉ< e₁ ,  es >ᴮ").


  Notation "ᵖ{ }ᴮ" := (PTuple [])
    (at level 1,
      format "ᵖ{ }ᴮ").

  Notation "ᵛ{ }ᴮ" := (VTuple [])
    (at level 1,
      format "ᵛ{ }ᴮ").

  Notation "ᵉ{ }ᴮ" := (ETuple [])
    (at level 1,
      format "ᵉ{ }ᴮ").

  Notation "ᵉ< >ᴮ" := (EValues [])
    (at level 1,
      format "ᵉ< >ᴮ").


  Notation "ᵖ{ p₁ , .. , pₙ }ᴮ" := (PTuple (cons p₁ .. (cons pₙ nil) .. ))
    (at level 1,
      format "ᵖ{ p₁ ,  .. ,  pₙ }ᴮ").

  Notation "ᵛ{ v₁ , .. , vₙ }ᴮ" := (VTuple (cons v₁ .. (cons vₙ nil) .. ))
    (at level 1,
      format "ᵛ{ v₁ ,  .. ,  vₙ }ᴮ").

  Notation "ᵉ{ e₁ , .. , eₙ }ᴮ" := (ETuple (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "ᵉ{ e₁ ,  .. ,  eₙ }ᴮ").

  Notation "ᵉ< e₁ , .. , eₙ >ᴮ" := (EValues (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "ᵉ< e₁ ,  .. ,  eₙ >ᴮ").



  Notation "ᵖ∼{ pps }∼ᴮ" := (PMap pps)
    (at level 1,
      format "ᵖ∼{ pps }∼ᴮ").

  Notation "ᵛ∼{ vvs }∼ᴮ" := (VMap vvs)
    (at level 1,
      format "ᵛ∼{ vvs }∼ᴮ").

  Notation "ᵉ∼{ ees }∼ᴮ" := (EMap ees)
    (at level 1,
      format "ᵉ∼{ ees }∼ᴮ").


  Notation "ᵖ∼{ ᵏp₁ ᵖ:=ᴮ ᵛp₁ , pps }∼ᴮ" := (PMap ((ᵏp₁, ᵛp₁) :: pps))
    (at level 1,
      format "ᵖ∼{ ᵏp₁  ᵖ:=ᴮ ᵛp₁ ,  pps }∼ᴮ").

  Notation "ᵛ∼{ ᵏv₁ ᵛ=>ᴮ ᵛv₁ , vvs }∼ᴮ" := (VMap ((ᵏv₁, ᵛv₁) :: vvs))
    (at level 1,
      format "ᵛ∼{ ᵏv₁  ᵛ=>ᴮ  ᵛv₁ ,  vvs }∼ᴮ").

  Notation "ᵉ∼{ ᵏe₁ ᵉ=>ᴮ ᵛe₁ , ees }∼ᴮ" := (EMap ((ᵏe₁, ᵛe₁) :: ees))
    (at level 1,
      format "ᵉ∼{ ᵏe₁  ᵉ=>ᴮ  ᵛe₁ ,  ees }∼ᴮ").


  Notation "ᵖ∼{ }∼ᴮ" := (PMap [])
    (at level 1,
      format "ᵖ∼{ }∼ᴮ").

  Notation "ᵛ∼{ }∼ᴮ" := (VMap [])
    (at level 1,
      format "ᵛ∼{ }∼ᴮ").

  Notation "ᵉ∼{ }∼ᴮ" := (EMap [])
    (at level 1,
      format "ᵉ∼{ }∼ᴮ").


  Notation "ᵏp ᵖ:=ᴮ ᵛp" := (@pair Pattern Pattern ᵏp ᵛp)
    (at level 70,
      format "ᵏp  ᵖ:=ᴮ  ᵛp").

  Notation "ᵖ∼{ p₁ , .. , pₙ }∼ᴮ" := (PMap (cons p₁ .. (cons pₙ nil) .. ))
    (at level 1,
      format "ᵖ∼{ p₁ ,  .. ,  pₙ }∼ᴮ").

  Notation "ᵏv ᵛ=>ᴮ ᵛv" := (@pair Value Value ᵏv ᵛv)
    (at level 70,
      format "ᵏv  ᵛ=>ᴮ  ᵛv").

  Notation "ᵛ∼{ v₁ , .. , vₙ }∼ᴮ" := (VMap (cons v₁ .. (cons vₙ nil) .. ))
    (at level 1,
      format "ᵛ∼{ v₁ ,  .. ,  vₙ }∼ᴮ").

  Notation "ᵏe ᵉ=>ᴮ ᵛe" := (@pair Expression Expression ᵏe ᵛe)
    (at level 70,
      format "ᵏe  ᵉ=>ᴮ  ᵛe").

  Notation "ᵉ∼{ e₁ , .. , eₙ }∼ᴮ" := (EMap (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "ᵉ∼{ e₁ ,  .. ,  eₙ }∼ᴮ").







  Notation "k ⇰ v" := (@pair (Var + FunctionIdentifier) Value k v)
    (at level 70,
      format "k  ⇰  v").

  Notation "f '=ᴮ' 'funᴮ' ( x₁ , .. , xₙ ) -> ᵇe" :=
      (@pair FunctionIdentifier (list Var * Expression)
        f
        (@pair (list Var) Expression (cons x₁ .. (cons xₙ nil) .. ) ᵇe))
    (at level 200,
      format "f  '=ᴮ'  'funᴮ' ( x₁ ,  .. ,  xₙ )  ->  ᵇe").

  Notation "f '=ᴮ' 'funᴮ' ( xs ) '->ᴮ' ᵇe" :=
      (@pair FunctionIdentifier (list Var * Expression)
        f
        (@pair (list Var) Expression xs ᵇe))
    (at level 200,
      format "f  '=ᴮ'  'funᴮ' ( xs )  '->ᴮ'  ᵇe").

  Notation "ⁱᵈn ':' f '=ᴮ' 'funᴮ' ( x₁ , .. , xₙ ) -> ᵇe" :=
      (@pair (nat * FunctionIdentifier) FunctionExpression
        (@pair nat FunctionIdentifier ⁱᵈn f)
        (@pair (list Var) Expression (cons x₁ .. (cons xₙ nil) .. ) ᵇe))
    (at level 200,
      format "ⁱᵈn  ':'  f  '=ᴮ'  'funᴮ' ( x₁ ,  .. ,  xₙ )  ->  ᵇe").

  Notation "ⁱᵈn ':' f '=ᴮ' 'funᴮ' ( xs ) -> ᵇe" :=
      (@pair (nat * FunctionIdentifier) FunctionExpression
        (@pair nat FunctionIdentifier ⁱᵈn f)
        (@pair (list Var) Expression xs ᵇe))
    (at level 200,
      format "ⁱᵈn  ':'  f  '=ᴮ'  'funᴮ' ( xs )  ->  ᵇe").


  Notation "ᵛ⟨ ⁱᵈn ':' ext , xs , ᵇe , Γ ⟩ᴮ" := (VClos Γ ext ⁱᵈn xs ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ext ,  xs ,  ᵇe ,  Γ ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ᵉˣᵗ{ o₁ , .. , oₙ } , ˣˢ{ x₁ , .. , xₙ } , ᵇe , ᵉⁿᵛ{ m₁ , .. , mₙ } ⟩ᴮ" :=
      (VClos (cons m₁ .. (cons mₙ nil) .. )
             (cons o₁ .. (cons oₙ nil) .. ) ⁱᵈn
             (cons x₁ .. (cons xₙ nil) .. ) ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ᵉˣᵗ{ o₁ ,  .. ,  oₙ } ,  ˣˢ{ x₁ ,  .. ,  xₙ } ,  ᵇe ,  ᵉⁿᵛ{ m₁ ,  .. ,  mₙ } ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ∅ , ˣˢ{ x₁ , .. , xₙ } , ᵇe , ᵉⁿᵛ{ m₁ , .. , mₙ } ⟩ᴮ" :=
      (VClos (cons m₁ .. (cons mₙ nil) .. )
             [] ⁱᵈn
             (cons x₁ .. (cons xₙ nil) .. ) ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ∅ ,  ˣˢ{ x₁ ,  .. ,  xₙ } ,  ᵇe ,  ᵉⁿᵛ{ m₁ ,  .. ,  mₙ } ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ᵉˣᵗ{ o₁ , .. , oₙ } , ∅ , ᵇe , ᵉⁿᵛ{ m₁ , .. , mₙ } ⟩ᴮ" :=
      (VClos (cons m₁ .. (cons mₙ nil) .. )
             (cons o₁ .. (cons oₙ nil) .. ) ⁱᵈn
             [] ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ᵉˣᵗ{ o₁ ,  .. ,  oₙ } ,  ∅ ,  ᵇe ,  ᵉⁿᵛ{ m₁ ,  .. ,  mₙ } ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ᵉˣᵗ{ o₁ , .. , oₙ } , ˣˢ{ x₁ , .. , xₙ } , ᵇe , ∅ ⟩ᴮ" :=
      (VClos []
             (cons o₁ .. (cons oₙ nil) .. ) ⁱᵈn
             (cons x₁ .. (cons xₙ nil) .. ) ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ᵉˣᵗ{ o₁ ,  .. ,  oₙ } ,  ˣˢ{ x₁ ,  .. ,  xₙ } ,  ᵇe ,  ∅ ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ∅ , ∅ , ᵇe , ᵉⁿᵛ{ m₁ , .. , mₙ } ⟩ᴮ" :=
      (VClos (cons m₁ .. (cons mₙ nil) .. )
             [] ⁱᵈn
             [] ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ∅ ,  ∅ ,  ᵇe ,  ᵉⁿᵛ{ m₁ ,  .. ,  mₙ } ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ᵉˣᵗ{ o₁ , .. , oₙ } , ∅ , ᵇe , ∅ ⟩ᴮ" :=
      (VClos []
             (cons o₁ .. (cons oₙ nil) .. ) ⁱᵈn
             [] ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ᵉˣᵗ{ o₁ ,  .. ,  oₙ } ,  ∅ ,  ᵇe ,  ∅ ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ∅ , ˣˢ{ x₁ , .. , xₙ } , ᵇe , ∅ ⟩ᴮ" :=
      (VClos []
             [] ⁱᵈn
             (cons x₁ .. (cons xₙ nil) .. ) ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ∅ ,  ˣˢ{ x₁ ,  .. ,  xₙ } ,  ᵇe ,  ∅ ⟩ᴮ").

  Notation "ᵛ⟨ ⁱᵈn ':' ∅ , ∅ , ᵇe , ∅ ⟩ᴮ" := (VClos [] [] ⁱᵈn [] ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ∅ ,  ∅ ,  ᵇe ,  ∅ ⟩ᴮ").



  Notation "ᵉˣᶜ⟨ c , ʳv , ᵈv ⟩ᴮ" :=
      (@pair (ExceptionClass * Value) Value
        (@pair ExceptionClass Value c ʳv)
        ᵈv)
    (at level 1,
      format "ᵉˣᶜ⟨ c ,  ʳv ,  ᵈv ⟩ᴮ").






  Notation "'ᵉdoᴮ' e₁ e₂" := (ESeq e₁ e₂)
    (at level 1,
      format "'ᵉdoᴮ'  e₁  e₂").


  Notation "'ᵉfunᴮ' ( ) -> ᵇe" := (EFun [] ᵇe)
    (at level 1,
      format "'ᵉfunᴮ' ( )  ->  ᵇe").

  Notation "'ᵉfunᴮ' ( x₁ , .. , xₙ ) -> ᵇe" :=
      (EFun (cons x₁ .. (cons xₙ nil) .. ) ᵇe)
    (at level 1,
      format "'ᵉfunᴮ' ( x₁ ,  .. ,  xₙ )  ->  ᵇe").

  Notation "'ᵉfunᴮ' ( xs ) -> ᵇe" := (EFun xs ᵇe)
    (at level 1,
      format "'ᵉfunᴮ' ( xs )  ->  ᵇe").


  Notation "'ᵉletrecᴮ' o₁ , .. , oₙ 'in' ᵇe" :=
      (ELetRec (cons o₁ .. (cons oₙ nil) .. ) ᵇe)
    (at level 1,
      format "'ᵉletrecᴮ'  o₁ ,  .. ,  oₙ  'in'  ᵇe").

  Notation "'ᵉletrecᴮ' ext 'in' ᵇe" := (ELetRec ext ᵇe)
    (at level 1,
      format "'ᵉletrecᴮ'  ext  'in'  ᵇe").


  Notation "'ᵉletᴮ' < x₁ , .. , xₙ > '=' e₁ 'in' e₂" :=
      (ELet (cons x₁ .. (cons xₙ nil) .. ) e₁ e₂)
    (at level 1,
      format "'ᵉletᴮ' < x₁ ,  .. ,  xₙ >  '='  e₁  'in'  e₂").

  Notation "'ᵉletᴮ' < xs₁ > '=' e₁ 'in' e₂" := (ELet xs₁ e₁ e₂)
    (at level 1,
      format "'ᵉletᴮ' < xs₁ >  '='  e₁  'in'  e₂").


 Notation "'ᵉtryᴮ' e₁ 'of' < x₁ , .. , xₙ > -> e₂ 'catch' < y₁ , .. , yₙ > -> e₃" :=
      (ETry e₁ (cons x₁ .. (cons xₙ nil) .. )
            e₂ (cons y₁ .. (cons yₙ nil) .. ) e₃)
    (at level 1,
      format "'ᵉtryᴮ'  e₁  'of'  < x₁ ,  .. ,  xₙ >  ->  e₂  'catch'  < y₁ ,  .. ,  yₙ >  ->  e₃").

  Notation "'ᵉtryᴮ' e₁ 'of' < xs₁ > -> e₂ 'catch' < xsₓ > -> e₃" :=
      (ETry e₁ xs₁ e₂ xsₓ e₃)
    (at level 1,
      format "'ᵉtryᴮ'  e₁  'of'  < xs₁ >  ->  e₂  'catch'  < xsₓ >  ->  e₃").


  Notation "'ᵉapplyᴮ' ᶠe ( )" := (EApp ᶠe [])
    (at level 1,
      format "'ᵉapplyᴮ'  ᶠe  ( )").

  Notation "'ᵉapplyᴮ' ᶠe ( e₁ , .. , eₙ )" :=
      (EApp ᶠe (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᵉapplyᴮ'  ᶠe  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᵉapplyᴮ' ᶠe ( es )" := (EApp ᶠe es)
    (at level 1,
      format "'ᵉapplyᴮ'  ᶠe  ( es )").


  Notation "'ᵉcallᴮ' ᵐe : ᶠe ( )" := (ECall ᵐe ᶠe [])
    (at level 1,
      format "'ᵉcallᴮ'  ᵐe  :  ᶠe  ( )").

  Notation "'ᵉcallᴮ' ᵐe : ᶠe ( e₁ , .. , eₙ )" :=
      (ECall ᵐe ᶠe (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᵉcallᴮ'  ᵐe  :  ᶠe  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᵉcallᴮ' ᵐe : ᶠe ( es )" := (ECall ᵐe ᶠe es)
    (at level 1,
      format "'ᵉcallᴮ'  ᵐe  :  ᶠe  ( es )").


  Notation "'ᵉprimopᴮ' a ( )" := (EPrimOp a [])
    (at level 1,
      format "'ᵉprimopᴮ'  a  ( )").

  Notation "'ᵉprimopᴮ' a ( e₁ , .. , eₙ )" :=
      (EPrimOp a (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᵉprimopᴮ'  a  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᵉprimopᴮ' a ( es )" := (EPrimOp a es)
    (at level 1,
      format "'ᵉprimopᴮ'  a  ( es )").


  Notation "< p₁ , .. , pₙ > 'whenᴮ' ᵍe -> ᵇe" :=
      (@pair ((list Pattern) * Expression) Expression
        (@pair (list Pattern) Expression (cons p₁ .. (cons pₙ nil) .. ) ᵍe)
        ᵇe)
    (at level 70,
      format "< p₁ ,  .. ,  pₙ >  'whenᴮ'  ᵍe  ->  ᵇe").

  Notation "< ps > 'whenᴮ' ᵍe -> ᵇe" :=
      (@pair ((list Pattern) * Expression) Expression
        (@pair (list Pattern) Expression ps ᵍe)
        ᵇe)
    (at level 70,
      format "< ps >  'whenᴮ'  ᵍe  ->  ᵇe").

  Notation "'ᵉcaseᴮ' ᵖe 'of' u₁ .. uₙ 'end'" :=
      (ECase ᵖe (cons u₁ .. (cons uₙ nil) .. ))
    (at level 1,
      format "'ᵉcaseᴮ'  ᵖe  'of'  u₁  ..  uₙ  'end'").

  Notation "'ᵉcaseᴮ' ᵖe 'of' us 'end'" := (ECase ᵖe us)
    (at level 1,
      format "'ᵉcaseᴮ'  ᵖe  'of'  us  'end'").



End BigStepNotations.









Module FrameStackNotations.

Import SubstSemantics.



  Notation "'ᵖᴬ' a 'ᶠ'" := (PLit (Atom a))
    (at level 1,
        format "'ᵖᴬ' a 'ᶠ'").

  Notation "'ᵛᴬ' a 'ᶠ'" := (VLit (Atom a))
    (at level 1,
        format "'ᵛᴬ' a 'ᶠ'").


  Notation "'ᵖᶻ' z 'ᶠ'" := (PLit (Integer z))
    (at level 1,
        format "'ᵖᶻ' z 'ᶠ'").

  Notation "'ᵛᶻ' z 'ᶠ'" := (VLit (Integer z))
    (at level 1,
        format "'ᵛᶻ' z 'ᶠ'").



  Notation "'ᵖᴸ' l 'ᶠ'" := (PLit l)
    (at level 1,
      format "'ᵖᴸ' l 'ᶠ'").

  Notation "'ᵛᴸ' l 'ᶠ'" := (VLit l)
    (at level 1,
      format "'ᵛᴸ' l 'ᶠ'").



  Notation "'ᵖˣ' '‗' 'ᶠ'" := PVar
    (at level 1,
      format "'ᵖˣ' '‗' 'ᶠ'").

  Notation "'ᵛˣ' '‗' ⁱn 'ᶠ'" := (VVar ⁱn)
    (at level 1,
      format "'ᵛˣ' '‗' ⁱn 'ᶠ'").


   Notation "'‗' ⁱn /ᶠ ᵃn" := (@pair nat nat ⁱn ᵃn)
    (at level 70,
      format "'‗' ⁱn /ᶠ ᵃn").

  Notation "'‗.' ⁱn 'ᵛ/ᶠ' ᵃn" := (VFunId (ⁱn, ᵃn))
    (at level 1,
      format "'‗.' ⁱn 'ᵛ/ᶠ' ᵃn").

  Notation "'ᵛᶠ' f 'ᶠ'" := (VFunId f)
    (at level 1,
      format "'ᵛᶠ' f 'ᶠ'").






  Notation "ᵖ[]ᶠ" := PNil
    (at level 1,
      format "ᵖ[]ᶠ").

  Notation "ᵛ[]ᶠ" := VNil
    (at level 1,
      format "ᵛ[]ᶠ").


  Notation "ᵖ[ p₁ | p₂ ]ᶠ" := (PCons p₁ p₂)
    (at level 1,
      format "ᵖ[ p₁ | p₂ ]ᶠ").

  Notation "ᵛ[ v₁ | v₂ ]ᶠ" := (VCons v₁ v₂)
    (at level 1,
      format "ᵛ[ v₁ | v₂ ]ᶠ").

  Notation "ᵉ[ e₁ | e₂ ]ᶠ" := (ECons e₁ e₂)
    (at level 1,
      format "ᵉ[ e₁ | e₂ ]ᶠ").


  Notation "ᵖ[ p₁ , .. , pₙ ]ᶠ" := (PCons p₁ .. (PCons pₙ PNil) .. )
    (at level 1,
      format "ᵖ[ p₁ ,  .. ,  pₙ ]ᶠ").

  Notation "ᵛ[ v₁ , .. , vₙ ]ᶠ" := (VCons v₁ .. (VCons vₙ VNil) .. )
    (at level 1,
      format "ᵛ[ v₁ ,  .. ,  vₙ ]ᶠ").

  Notation "ᵉ[ e₁ , .. , eₙ ]ᶠ" := (ECons e₁ .. (ECons eₙ ENil) .. )
    (at level 1,
      format "ᵉ[ e₁ ,  .. ,  eₙ ]ᶠ").



  Notation "ᵖ{ ps }ᶠ" := (PTuple ps)
    (at level 1,
      format "ᵖ{ ps }ᶠ").

  Notation "ᵛ{ vs }ᶠ" := (VTuple vs)
    (at level 1,
      format "ᵛ{ vs }ᶠ").

  Notation "ᵉ{ es }ᶠ" := (ETuple es)
    (at level 1,
      format "ᵉ{ es }ᶠ").

  Notation "ᵉ< es >ᶠ" := (EValues es)
    (at level 1,
      format "ᵉ< es >ᶠ").


  Notation "ᵖ{ p₁ , ps }ᶠ" := (PTuple (p₁ :: ps))
    (at level 1,
      format "ᵖ{ p₁ ,  ps }ᶠ").

  Notation "ᵛ{ v₁ , vs }ᶠ" := (VTuple (v₁ :: vs))
    (at level 1,
      format "ᵛ{ v₁ ,  vs }ᶠ").

  Notation "ᵉ{ e₁ , es }ᶠ" := (ETuple (e₁ :: es))
    (at level 1,
      format "ᵉ{ e₁ ,  es }ᶠ").

  Notation "ᵉ< e₁ , es >ᶠ" := (EValues (e₁ :: es))
    (at level 1,
      format "ᵉ< e₁ ,  es >ᶠ").


  Notation "ᵖ{ }ᶠ" := (PTuple [])
    (at level 1,
      format "ᵖ{ }ᶠ").

  Notation "ᵛ{ }ᶠ" := (VTuple [])
    (at level 1,
      format "ᵛ{ }ᶠ").

  Notation "ᵉ{ }ᶠ" := (ETuple [])
    (at level 1,
      format "ᵉ{ }ᶠ").

  Notation "ᵉ< >ᶠ" := (EValues [])
    (at level 1,
      format "ᵉ< >ᶠ").


  Notation "ᵖ{ p₁ , .. , pₙ }ᶠ" := (PTuple (cons p₁ .. (cons pₙ nil) .. ))
    (at level 1,
      format "ᵖ{ p₁ ,  .. ,  pₙ }ᶠ").

  Notation "ᵛ{ v₁ , .. , vₙ }ᶠ" := (VTuple (cons v₁ .. (cons vₙ nil) .. ))
    (at level 1,
      format "ᵛ{ v₁ ,  .. ,  vₙ }ᶠ").

  Notation "ᵉ{ e₁ , .. , eₙ }ᶠ" := (ETuple (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "ᵉ{ e₁ ,  .. ,  eₙ }ᶠ").

  Notation "ᵉ< e₁ , .. , eₙ >ᶠ" := (EValues (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "ᵉ< e₁ ,  .. ,  eₙ >ᶠ").



  Notation "ᵖ∼{ pps }∼ᶠ" := (PMap pps)
    (at level 1,
      format "ᵖ∼{ pps }∼ᶠ").

  Notation "ᵛ∼{ vvs }∼ᶠ" := (VMap vvs)
    (at level 1,
      format "ᵛ∼{ vvs }∼ᶠ").

  Notation "ᵉ∼{ ees }∼ᶠ" := (EMap ees)
    (at level 1,
      format "ᵉ∼{ ees }∼ᶠ").


  Notation "ᵖ∼{ ᵏp₁ ᵖ:=ᶠ ᵛp₁ , pps }∼ᶠ" := (PMap ((ᵏp₁, ᵛp₁) :: pps))
    (at level 1,
      format "ᵖ∼{ ᵏp₁  ᵖ:=ᶠ ᵛp₁ ,  pps }∼ᶠ").

  Notation "ᵛ∼{ ᵏv₁ ᵛ=>ᶠ ᵛv₁ , vvs }∼ᶠ" := (VMap ((ᵏv₁, ᵛv₁) :: vvs))
    (at level 1,
      format "ᵛ∼{ ᵏv₁  ᵛ=>ᶠ  ᵛv₁ ,  vvs }∼ᶠ").

  Notation "ᵉ∼{ ᵏe₁ ᵉ=>ᶠ ᵛe₁ , ees }∼ᶠ" := (EMap ((ᵏe₁, ᵛe₁) :: ees))
    (at level 1,
      format "ᵉ∼{ ᵏe₁  ᵉ=>ᶠ  ᵛe₁ ,  ees }∼ᶠ").


  Notation "ᵖ∼{ }∼ᶠ" := (PMap [])
    (at level 1,
      format "ᵖ∼{ }∼ᶠ").

  Notation "ᵛ∼{ }∼ᶠ" := (VMap [])
    (at level 1,
      format "ᵛ∼{ }∼ᶠ").

  Notation "ᵉ∼{ }∼ᶠ" := (EMap [])
    (at level 1,
      format "ᵉ∼{ }∼ᶠ").


  Notation "ᵏp ᵖ:=ᶠ ᵛp" := (@pair Pat Pat ᵏp ᵛp)
    (at level 70,
      format "ᵏp  ᵖ:=ᶠ  ᵛp").

  Notation "ᵖ∼{ p₁ , .. , pₙ }∼ᶠ" := (PMap (cons p₁ .. (cons pₙ nil) .. ))
    (at level 1,
      format "ᵖ∼{ p₁ ,  .. ,  pₙ }∼ᶠ").

  Notation "ᵏv ᵛ=>ᶠ ᵛv" := (@pair Val Val ᵏv ᵛv)
    (at level 70,
      format "ᵏv  ᵛ=>ᶠ  ᵛv").

  Notation "ᵛ∼{ v₁ , .. , vₙ }∼ᶠ" := (VMap (cons v₁ .. (cons vₙ nil) .. ))
    (at level 1,
      format "ᵛ∼{ v₁ ,  .. ,  vₙ }∼ᶠ").

  Notation "ᵏe ᵉ=>ᶠ ᵛe" := (@pair Exp Exp ᵏe ᵛe)
    (at level 70,
      format "ᵏe  ᵉ=>ᶠ  ᵛe").

  Notation "ᵉ∼{ e₁ , .. , eₙ }∼ᶠ" := (EMap (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "ᵉ∼{ e₁ ,  .. ,  eₙ }∼ᶠ").








  Notation "'‗/ᶠ‗' '=ᶠ' 'funᶠ' ˣˢn -> ᵇe" :=
      (@pair nat Exp ˣˢn ᵇe)
    (at level 200,
      format "'‗/ᶠ‗'  '=ᶠ'  'funᶠ'  ˣˢn  ->  ᵇe").

  Notation "ⁱᵈn ':' '‗/ᶠ‗' '=ᶠ' 'funᶠ' ˣˢn -> ᵇe" :=
      (@pair (nat * nat) Exp
        (@pair nat nat ⁱᵈn ˣˢn)
        ᵇe)
    (at level 200,
      format "ⁱᵈn  ':'  '‗/ᶠ‗'  '=ᶠ'  'funᶠ'  ˣˢn  ->  ᵇe").

  Notation "ᵛ⟨ ⁱᵈn ':' ext , ˣˢn , ᵇe ⟩ᶠ" := (VClos ext ⁱᵈn ˣˢn ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ext ,  ˣˢn ,  ᵇe ⟩ᶠ").

  Notation "ᵛ⟨ ⁱᵈn ':' ᵉˣᵗ{ o₁ , .. , oₙ } , ˣˢn , ᵇe ⟩ᶠ" :=
      (VClos (cons o₁ .. (cons oₙ nil) .. ) ⁱᵈn ˣˢn ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ᵉˣᵗ{ o₁ ,  .. ,  oₙ } ,  ˣˢn ,  ᵇe ⟩ᶠ").

  Notation "ᵛ⟨ ⁱᵈn ':' ∅ , ˣˢn , ᵇe ⟩ᶠ" := (VClos [] ⁱᵈn ˣˢn ᵇe)
    (at level 1,
      format "ᵛ⟨ ⁱᵈn  ':'  ∅ ,  ˣˢn ,  ᵇe ⟩ᶠ").



  Notation "ᵉˣᶜ⟨ c , ʳv , ᵈv ⟩ᶠ" :=
      (@pair (ExcClass * Val) Val
        (@pair ExcClass Val c ʳv)
        ᵈv)
    (at level 1,
      format "ᵉˣᶜ⟨ c ,  ʳv ,  ᵈv ⟩ᶠ").






  Notation "'ᵉdoᶠ' e₁ e₂" := (ESeq e₁ e₂)
    (at level 1,
      format "'ᵉdoᶠ'  e₁  e₂").


  Notation "'ᵉfunᶠ' ˣˢn -> ᵇe" := (EFun ˣˢn ᵇe)
    (at level 1,
      format "'ᵉfunᶠ'  ˣˢn  ->  ᵇe").


  Notation "'ᵉletrecᶠ' o₁ , .. , oₙ 'in' ᵇe" :=
      (ELetRec (cons o₁ .. (cons oₙ nil) .. ) ᵇe)
    (at level 1,
      format "'ᵉletrecᶠ'  o₁ ,  .. ,  oₙ  'in'  ᵇe").

  Notation "'ᵉletrecᶠ' ext 'in' ᵇe" := (ELetRec ext ᵇe)
    (at level 1,
      format "'ᵉletrecᶠ'  ext  'in'  ᵇe").


  Notation "'ᵉletᶠ' ˣˢn₁ '=' e₁ 'in' e₂" := (ELet ˣˢn₁ e₁ e₂)
    (at level 1,
      format "'ᵉletᶠ'  ˣˢn₁  '='  e₁  'in'  e₂").


 Notation "'ᵉtryᶠ' e₁ 'of' ˣˢn₁ -> e₂ 'catch' ˣˢnₓ -> e₃" :=
      (ETry e₁ ˣˢn₁ e₂ ˣˢnₓ e₃)
    (at level 1,
      format "'ᵉtryᶠ'  e₁  'of'  ˣˢn₁  ->  e₂  'catch'  ˣˢnₓ  ->  e₃").


  Notation "'ᵉapplyᶠ' ᶠe ( )" := (EApp ᶠe [])
    (at level 1,
      format "'ᵉapplyᶠ'  ᶠe  ( )").

  Notation "'ᵉapplyᶠ' ᶠe ( e₁ , .. , eₙ )" :=
      (EApp ᶠe (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᵉapplyᶠ'  ᶠe  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᵉapplyᶠ' ᶠe ( es )" := (EApp ᶠe es)
    (at level 1,
      format "'ᵉapplyᶠ'  ᶠe  ( es )").


  Notation "'ᵉcallᶠ' ᵐe : ᶠe ( )" := (ECall ᵐe ᶠe [])
    (at level 1,
      format "'ᵉcallᶠ'  ᵐe  :  ᶠe  ( )").

  Notation "'ᵉcallᶠ' ᵐe : ᶠe ( e₁ , .. , eₙ )" :=
      (ECall ᵐe ᶠe (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᵉcallᶠ'  ᵐe  :  ᶠe  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᵉcallᶠ' ᵐe : ᶠe ( es )" := (ECall ᵐe ᶠe es)
    (at level 1,
      format "'ᵉcallᶠ'  ᵐe  :  ᶠe  ( es )").


  Notation "'ᵉprimopᶠ' a ( )" := (EPrimOp a [])
    (at level 1,
      format "'ᵉprimopᶠ'  a  ( )").

  Notation "'ᵉprimopᶠ' a ( e₁ , .. , eₙ )" :=
      (EPrimOp a (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᵉprimopᶠ'  a  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᵉprimopᶠ' a ( es )" := (EPrimOp a es)
    (at level 1,
      format "'ᵉprimopᶠ'  a  ( es )").


  Notation "< p₁ , .. , pₙ > 'whenᶠ' ᵍe -> ᵇe" :=
      (@pair ((list Pat) * Exp) Exp
        (@pair (list Pat) Exp (cons p₁ .. (cons pₙ nil) .. ) ᵍe)
        ᵇe)
    (at level 70,
      format "< p₁ ,  .. ,  pₙ >  'whenᶠ'  ᵍe  ->  ᵇe").

  Notation "< ps > 'whenᶠ' ᵍe -> ᵇe" :=
      (@pair ((list Pat) * Exp) Exp
        (@pair (list Pat) Exp ps ᵍe)
        ᵇe)
    (at level 70,
      format "< ps >  'whenᶠ'  ᵍe  ->  ᵇe").

  Notation "'ᵉcaseᶠ' ᵖe 'of' u₁ .. uₙ 'end'" :=
      (ECase ᵖe (cons u₁ .. (cons uₙ nil) .. ))
    (at level 1,
      format "'ᵉcaseᶠ'  ᵖe  'of'  u₁  ..  uₙ  'end'").

  Notation "'ᵉcaseᶠ' ᵖe 'of' us 'end'" := (ECase ᵖe us)
    (at level 1,
      format "'ᵉcaseᶠ'  ᵖe  'of'  us  'end'").






  Notation "ᴱ′ e" := (RExp e)
    (at level 1,
      format "ᴱ′ e").

  Notation "ᵛˢ′ vs" := (RValSeq vs)
    (at level 1,
      format "ᵛˢ′ vs").

  Notation "ᵉˣᶜ′ q" := (RExc q)
    (at level 1,
      format "ᵉˣᶜ′ q").

  Notation "□" := (RBox)
    (at level 1,
      format "□").



  Notation "'ⁱvalues'" := (IValues)
    (at level 1,
      format "'ⁱvalues'").

  Notation "'ⁱtuple'" := (ITuple)
    (at level 1,
      format "'ⁱtuple'").

  Notation "'ⁱmap'" := (IMap)
    (at level 1,
      format "'ⁱmap'").

  Notation "'ⁱapply' ( ᶠv )" := (IApp ᶠv)
    (at level 1,
      format "'ⁱapply' ( ᶠv )").

  Notation "'ⁱcall' ( ᵐv , ᶠv )" := (ICall ᵐv ᶠv)
    (at level 1,
      format "'ⁱcall' ( ᵐv ,  ᶠv )").

  Notation "'ⁱprimop' ( a )" := (IPrimOp a)
    (at level 1,
      format "'ⁱprimop' ( a )").



  Notation "ᶠ[ e₁ | □ ]" := (FCons1 e₁)
    (at level 1,
      format "ᶠ[ e₁ | □ ]").

  Notation "ᶠ[ □ | v₂ ]" := (FCons2 v₂)
    (at level 1,
      format "ᶠ[ □ | v₂ ]").

  Notation "'ᶠdo' □ e₂" := (FSeq e₂)
    (at level 1,
      format "'ᶠdo'  □  e₂").

  Notation "'ᶠlet' ˣˢn₁ '=' □ 'in' e₂" := (FLet ˣˢn₁ e₂)
    (at level 1,
      format "'ᶠlet'  ˣˢn₁  '='  □  'in'  e₂").

  Notation "'ᶠtry' □ 'of' ˣˢn₁ -> e₂ 'catch' ˣˢnₓ -> e₃" :=
      (FTry ˣˢn₁ e₂ ˣˢnₓ e₃)
    (at level 1,
      format "'ᶠtry'  □  'of'  ˣˢn₁  ->  e₂  'catch'  ˣˢnₓ  ->  e₃").


  Notation "'ᶠcase' □ 'of' u₁ .. uₙ 'end'" :=
      (FCase1 (cons u₁ .. (cons uₙ nil) .. ))
    (at level 1,
      format "'ᶠcase'  □  'of'  u₁  ..  uₙ  'end'").

  Notation "'ᶠcase' □ 'of' us 'end'" := (FCase1 us)
    (at level 1,
      format "'ᶠcase'  □  'of'  us  'end'").

  Notation "'ᶠcase' ᵖv 'of' < p₁ , .. , pₙ > 'when' □ -> ᵇe u₂ .. uₙ 'end'" :=
      (FCase2 ᵖv (cons p₁ .. (cons pₙ nil) .. ) ᵇe (cons u₂ .. (cons uₙ nil) .. ))
    (at level 1,
      format "'ᶠcase'  ᵖv  'of'  < p₁ ,  .. ,  pₙ >  'when'  □  ->  ᵇe  u₂  ..  uₙ  'end'").

  Notation "'ᶠcase' ᵖv 'of' < ps > 'when' □ -> ᵇe us 'end'" :=
      (FCase2 ᵖv ps ᵇe us)
    (at level 1,
      format "'ᶠcase'  ᵖv  'of'  < ps >  'when'  □  ->  ᵇe  us  'end'").


  Notation "'ᶠapply' □ ( )" := (FApp1 [])
    (at level 1,
      format "'ᶠapply'  □  ( )").

  Notation "'ᶠapply' □ ( e₁ , .. , eₙ )" :=
      (FApp1 (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᶠapply'  □  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᶠapply' □ ( es )" := (FApp1 es)
    (at level 1,
      format "'ᶠapply'  □  ( es )").


  Notation "'ᶠcall' □ : ᶠe ( )" := (FCallMod ᶠe [])
    (at level 1,
      format "'ᶠcall'  □  :  ᶠe  ( )").

  Notation "'ᶠcall' □ : ᶠe ( e₁ , .. , eₙ )" :=
      (FCallMod ᶠe (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᶠcall'  □  :  ᶠe  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᶠcall' □ : ᶠe ( es )" := (FCallMod ᶠe es)
    (at level 1,
      format "'ᶠcall'  □  :  ᶠe  ( es )").

  Notation "'ᶠcall' ᵐv : □ ( )" := (FCallFun ᵐv [])
    (at level 1,
      format "'ᶠcall'  ᵐv  :  □  ( )").

  Notation "'ᶠcall' ᵐv : □ ( e₁ , .. , eₙ )" :=
      (FCallFun ᵐv (cons e₁ .. (cons eₙ nil) .. ))
    (at level 1,
      format "'ᶠcall'  ᵐv  :  □  ( e₁ ,  .. ,  eₙ )").

  Notation "'ᶠcall' ᵐv : □ ( es )" := (FCallFun ᵐv es)
    (at level 1,
      format "'ᶠcall'  ᵐv  :  □  ( es )").


  Notation "ident ( vs , □ , es )" := (FParams ident vs es)
    (at level 200,
      format "ident ( vs ,  □ ,  es )").



  Notation "'ε'" := ([] : FrameStack)
    (at level 1,
      format "'ε'").



End FrameStackNotations.