From CoreErlang.Eqvivalence Require Export EX4Basics.

Import BigStep.

Open Scope string_scope.












Section Digits.



Inductive digit : Set :=
  | D0
  | D1
  | D2
  | D3
  | D4
  | D5
  | D6
  | D7
  | D8
  | D9.



Definition increase_digit
    (d : digit)
    : (digit * bool)
    :=
  match d with
  | D0 => (D1, false)
  | D1 => (D2, false)
  | D2 => (D3, false)
  | D3 => (D4, false)
  | D4 => (D5, false)
  | D5 => (D6, false)
  | D6 => (D7, false)
  | D7 => (D8, false)
  | D8 => (D9, false)
  | D9 => (D0, true)
  end.



Fixpoint increase_digits
    (ds : list digit)
    : list digit
    :=
  match ds with
  | [] => []
  | d :: ds' =>
    match increase_digit d with
    | (d', false) => d' :: ds'
    | (d', true) => 
      match ds' with
      | [] => d' :: [D1]
      | _ :: _ => d' :: increase_digits ds'
      end
    end
  end.



Fixpoint nat_to_digits
    (n : nat)
    : list digit
    :=
  match n with
  | 0 => [D0]
  | S n' => increase_digits (nat_to_digits n')
  end.



End Digits.












Section ToString.



Definition digit_to_string
    (d : digit)
    : string
    :=
  match d with
  | D0 => "0"
  | D1 => "1"
  | D2 => "2"
  | D3 => "3"
  | D4 => "4"
  | D5 => "5"
  | D6 => "6"
  | D7 => "7"
  | D8 => "8"
  | D9 => "9"
  end.



Fixpoint digits_to_string
    (ds : list digit)
    : string
    :=
  match ds with
  | [] => ""
  | d :: ds' => digits_to_string ds' ++ digit_to_string d
  end.






Definition nat_to_sting
    (n : nat)
    : string
    :=
  digits_to_string (nat_to_digits n).



Definition nat_to_name
    (n : nat)
    : string
    :=
  "X" ++ nat_to_sting n.









Definition digit_to_string_var
    (d : digit)
    : string
    :=
  match d with
  | D0 => "X"
  | D1 => "Y"
  | D2 => "Z"
  | D3 => "W"
  | D4 => "V"
  | D5 => "T"
  | D6 => "S"
  | D7 => "R"
  | D8 => "Q"
  | D9 => "P"
  end.



Fixpoint digits_to_string_var
    (ds : list digit)
    : string
    :=
  match ds with
  | [] => ""
  | d :: ds' => digits_to_string_var ds' ++ digit_to_string_var d
  end.



Definition nat_to_var
    (n : nat)
    : string
    :=
  digits_to_string_var (nat_to_digits n).









Definition digit_to_string_fid
    (d : digit)
    : string
    :=
  match d with
  | D0 => "f"
  | D1 => "g"
  | D2 => "h"
  | D3 => "l"
  | D4 => "m"
  | D5 => "e"
  | D6 => "d"
  | D7 => "c"
  | D8 => "b"
  | D9 => "a"
  end.



Fixpoint digits_to_string_fid
    (ds : list digit)
    : string
    :=
  match ds with
  | [] => ""
  | d :: ds' => digits_to_string_fid ds' ++ digit_to_string_fid d
  end.



Definition nat_to_fid
    (n : nat)
    : string
    :=
  digits_to_string_fid (nat_to_digits n).



End ToString.












Section Count.



Fixpoint count_vars_pat
    (p : Pat)
    : nat
    :=
  match p with

  | Syntax.PNil => 0

  | Syntax.PVar => 1

  | Syntax.PLit l => 0

  | Syntax.PCons p₁ p₂ => count_vars_pat p₁ + count_vars_pat p₂

  | Syntax.PTuple ps => list_sum (map count_vars_pat ps)

  | Syntax.PMap pps =>
    list_sum (map (fun '(x, y) => (count_vars_pat x) + (count_vars_pat y)) pps)

  end.



Definition count_vars_pats
    (ps : list Pat)
    : nat
    :=
  list_sum (map count_vars_pat ps).








Fixpoint count_binds_exp
    (e : Exp)
    : nat
    :=
  match e with
  | VVal v => count_binds_vval v
  | EExp nv => count_binds_eexp nv
  end



with count_binds_vval
    (v : Val)
    : nat
    :=
  match v with

  | Syntax.VClos os id xs e =>
    list_sum
      (map (fun '(_, xs', e') => 1 + xs' + (count_binds_exp e')) os)
    + xs
    + count_binds_exp e

  | _ => 0

  end



with count_binds_eexp
    (nv : NonVal)
    : nat
    :=
  match nv with

  | Syntax.ECons e₁ e₂ =>
    count_binds_exp e₁ +
    count_binds_exp e₂

  | Syntax.ETuple es =>
    list_sum (map count_binds_exp es)

  | Syntax.EMap ees =>
    list_sum
      (map (fun '(x, y) => count_binds_exp x + count_binds_exp y) ees)

  | Syntax.ESeq e₁ e₂ =>
    count_binds_exp e₁ +
    count_binds_exp e₂

  | Syntax.EValues es =>
    list_sum (map count_binds_exp es)

  | Syntax.EPrimOp s es =>
    list_sum (map count_binds_exp es)

  | Syntax.EApp ᶠe es =>
    count_binds_exp ᶠe +
    list_sum (map count_binds_exp es)

  | Syntax.ECall ᵐe ᶠe es =>
    count_binds_exp ᵐe +
    count_binds_exp ᶠe +
    list_sum (map count_binds_exp es)

  | Syntax.ECase ᵖe us =>
    count_binds_exp ᵖe +
      list_sum
        (map
          (fun '(ps, ᵍe, ᵇe) =>
            (count_vars_pats ps +
            count_binds_exp ᵍe +
            count_binds_exp ᵇe))
          us)

  | Syntax.EFun xs ᵇe =>
    xs +
    count_binds_exp ᵇe

  | Syntax.ELet xs e₁ e₂ =>
    xs +
    count_binds_exp e₁ +
    count_binds_exp e₂

  | Syntax.ETry e₁ xs₁ e₂ xs₂ e₃ =>
    xs₁ +
    xs₂ +
    count_binds_exp e₁ +
    count_binds_exp e₂ +
    count_binds_exp e₃

  | Syntax.ELetRec os ᵇe =>
    list_sum
      (map (fun '(xs', e') => 1 + xs' + (count_binds_exp e')) os)
    + count_binds_exp ᵇe

  end.



End Count.












Section GiveNamesHelpers.



Definition convert_lit
    (l : Lit)
    : Literal
    :=
  match l with
  | Syntax.Atom s => Atom s
  | Syntax.Integer x => Integer x
  end.



Definition convert_class
    (c : ExcClass)
    : ExceptionClass
    :=
  match c with
  | CoreErlang.Syntax.Error =>  Error
  | CoreErlang.Syntax.Throw =>  Throw
  | CoreErlang.Syntax.Exit =>   Exit
  end.






Definition give_name
    (n i : nat)
    : string
    :=
  nat_to_name (i + n).



Definition give_name_var
    (n i : nat)
    : string
    :=
  nat_to_var (i + n).



Definition give_name_fid
    (n i : nat)
    : string
    :=
  nat_to_fid (i + n).






(* give_name - give_name_var *)
Definition give_var
    (n : nat)
    (x : Syntax.Var)
    : Var
    :=
  give_name_var n x.



(* give_name - give_name_fid *)
Definition give_fid
    (n : nat)
    (f : FunId)
    : FunctionIdentifier
    :=
  match f with
  | (i, a) => (give_name_fid n i, a)
  end.



(* nat_to_name - nat_to_var *)
Fixpoint give_vars
    (n xs : nat)
    : list string
    :=
  match xs with
  | 0 => []
  | S xs' => nat_to_var n :: give_vars (S n) xs'
  end.






Fixpoint give_pat_list
    (f : nat -> Pat -> Pattern)
    (n : nat)
    (ps : list Pat)
    : list Pattern
    :=
  match ps with
  | [] => []
  | p :: ps' =>
    f n p :: give_pat_list f (count_vars_pat p + n) ps'
  end.



Fixpoint give_pat_map
    (f : nat -> Pat -> Pattern)
    (n : nat)
    (pps : list (Pat * Pat))
    : list (Pattern * Pattern)
    :=
  match pps with
  | [] => []
  | (p₁, p₂) :: pps' =>
    (f n p₁, f (count_vars_pat p₁ + n) p₂)
    :: give_pat_map f (count_vars_pat p₁ + count_vars_pat p₂ + n) pps'
  end.



Fixpoint give_ext_noid_base
    (i : nat)
    (f : nat -> Exp -> Expression)
    (n : nat)
    (os : list (nat * Exp))
    : list (FunctionIdentifier * ((list Var) * Expression))
    :=
  match os with
  | [] => []
  | (xs, e) :: os' =>
    (give_fid (count_binds_exp e + n) (i, xs),
    (give_vars (length os + count_binds_exp e + n) xs,
    f n e))
    :: give_ext_noid_base (S i) f (xs + length os + count_binds_exp e + n) os'
  end.



Definition give_ext_noid
    (f : nat -> Exp -> Expression)
    (n : nat)
    (os : list (nat * Exp))
    : list (FunctionIdentifier * ((list Var) * Expression))
    :=
  give_ext_noid_base 0 f n os.



Fixpoint give_ext_base
    (i : nat)
    (f : nat -> Exp -> Expression)
    (n : nat)
    (os : list (nat * nat * Exp))
    : list (nat * FunctionIdentifier * FunctionExpression)
    :=
  match os with
  | [] => []
  | (id, xs, e) :: os' =>
    (id,
    give_fid (count_binds_exp e + n) (i, xs),
    (give_vars (length os + count_binds_exp e + n) xs,
    f n e))
    :: give_ext_base (S i) f (xs + length os + count_binds_exp e + n) os'
  end.



Definition give_ext
    (f : nat -> Exp -> Expression)
    (n : nat)
    (os : list (nat * nat * Exp))
    : list (nat * FunctionIdentifier * FunctionExpression)
    :=
  give_ext_base 0 f n os.



End GiveNamesHelpers.












Section GiveNamesMain.



Fixpoint give_pat
    (n : nat)
    (p : Pat)
    : Pattern
    :=
  match p with

  | Syntax.PNil =>
    PNil

  | Syntax.PVar =>
    PVar (give_var n 0)

  | Syntax.PLit l =>
    PLit
      (convert_lit l)

  | Syntax.PCons p₁ p₂ =>
    PCons
      (give_pat n p₁)
      (give_pat (count_vars_pat p₁ + n) p₂)

  | Syntax.PTuple ps =>
    PTuple
      (give_pat_list give_pat n ps)

  | Syntax.PMap pps =>
    PMap
      (give_pat_map give_pat n pps)

  end.



Fixpoint give_pats
    (n : nat)
    (ps : list Pat)
    : list Pattern
    :=
  match ps with
  | [] => []
  | p :: ps' => give_pat n p :: give_pats (count_vars_pat p + n) ps'
  end.









Fixpoint give_exp
    (n : nat)
    (e : Exp)
    : Expression
    :=
  match e with
  | VVal v => give_vval n v
  | EExp nv => give_eexp n nv
  end



with give_vval
    (n : nat)
    (v : Val)
    : Expression
    :=
  match v with

  | Syntax.VNil =>
    ENil

  | Syntax.VLit l =>
    ELit
      (convert_lit l)

  | Syntax.VCons v₁ v₂ =>
    ECons
      (give_vval n v₁)
      (give_vval n v₂)

  | Syntax.VTuple vs =>
    ETuple
      (map (give_vval n) vs)

  | Syntax.VMap vvs =>
    EMap
      (map (fun '(x, y) => (give_vval n x, give_vval n y)) vvs)

  | Syntax.VVar x =>
    EVar
      (give_var n x)

  | Syntax.VFunId f =>
    EFunId
      (give_fid n f)

  | Syntax.VClos os id xs e =>
    EFun
      (give_vars (count_binds_exp e + n) xs)
      (give_exp n e)

  | Syntax.VPid _ => ENil

  end



with give_eexp
    (n : nat)
    (nv : NonVal)
    : Expression
    :=
  match nv with

  | Syntax.ECons e₁ e₂ =>
    ECons
      (give_exp n e₁)
      (give_exp n e₂)

  | Syntax.ETuple es =>
    ETuple
      (map (give_exp n) es)

  | Syntax.EMap ees =>
    EMap
      (map (fun '(x, y) => (give_exp n x, give_exp n y)) ees)

  | Syntax.ESeq e₁ e₂ =>
    ESeq
      (give_exp n e₁)
      (give_exp n e₂)

  | Syntax.EValues es =>
    EValues
      (map (give_exp n) es)

  | Syntax.EPrimOp s es =>
    EPrimOp
      s
      (map (give_exp n) es)

  | Syntax.EApp ᶠe es =>
    EApp
      (give_exp n ᶠe)
      (map (give_exp n) es)

  | Syntax.ECall ᵐe ᶠe es =>
    ECall
      (give_exp n ᵐe)
      (give_exp n ᶠe)
      (map (give_exp n) es)

  | Syntax.ECase ᵖe us =>
    ECase
      (give_exp n ᵖe)
      (map
        (fun '(ps, ᵍe, ᵇe) =>
          (give_pats n ps,
          give_exp (count_vars_pats ps + n) ᵍe,
          give_exp (count_vars_pats ps + n) ᵇe))
        us)

  | Syntax.EFun xs ᵇe =>
    EFun
      (give_vars (count_binds_exp ᵇe + n) xs)
      (give_exp n ᵇe)

  | Syntax.ELet xs e₁ e₂ =>
    ELet
      (give_vars (count_binds_exp e₂ + n) xs)
      (give_exp (count_binds_exp e₂ + xs + n) e₁)
      (give_exp n e₂)
(* TODO*)
  | Syntax.ETry e₁ xs₁ e₂ xs₂ e₃ =>
    ETry
      (give_exp (count_binds_exp e₂ + xs₁ + n) e₁)
      (give_vars (count_binds_exp e₂ + n) xs₁)
      (give_exp n e₂)
      (give_vars (count_binds_exp e₃ + n) xs₂)
      (give_exp n e₃)

  | _ => ENil
  (* | Syntax.ELetRec os ᵇe =>
    ELetRec
      (give_ext_noid give_exp (count_binds_exp ᵇe + n) os)
      (give_exp n ᵇe) *)

  end.






Fixpoint give_val
    (v : Val)
    : Value
    :=
  match v with

  | Syntax.VNil =>
    VNil

  | Syntax.VLit l =>
    VLit
      (convert_lit l)

  | Syntax.VCons v₁ v₂ =>
    VCons
      (give_val v₁)
      (give_val v₂)

  | Syntax.VTuple vs =>
    VTuple
      (map give_val vs)

  | Syntax.VMap vvs =>
    VMap
      (map (fun '(x, y) => (give_val x, give_val y)) vvs)

  (* TMP *)
  | Syntax.VClos _ _ _ _ => VNil

  | _ => VNil

  end.









Definition give_valseq
    (vs : ValSeq)
    : ValueSequence
    :=
  map give_val vs.



Definition give_exc
    (q : CoreErlang.Syntax.Exception)
    : Exception
    :=
  match q with
  | (c, ʳv, ᵈv) =>
    (convert_class c, give_val ʳv, give_val ᵈv)
  end.



Definition give_redex
    (redex : Redex)
    : (ValueSequence + Exception)
    :=
  match redex with
  | RValSeq vs => inl (give_valseq vs)
  | RExc q => inr (give_exc q)
  | _ => inl []
  end.



Definition give_result
    (result : (ValSeq + CoreErlang.Syntax.Exception))
    : (ValueSequence + Exception)
    :=
  match result with
  | inl vs => inl (give_valseq vs)
  | inr q => inr (give_exc q)
  end.



Definition to_redex
    (result : (ValSeq + CoreErlang.Syntax.Exception))
    : Redex
    :=
  match result with
  | inl vs => RValSeq vs
  | inr q => RExc q
  end.



Definition give_names
    (e : Exp)
    : Expression
    :=
  give_exp 0 e.



End GiveNamesMain.




Import SubstSemantics.
Compute give_exp 0
  (˝VTuple [VVar 0; VVar 1; VVar 2]).
Compute give_exp 0
  (°EFun 2
    (˝VTuple [VVar 0; VVar 1; VVar 2])).
Compute give_exp 0
  (°EFun 2
    (°EFun 2
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (˝VTuple [VVar 0; VVar 1; VVar 2])).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (°ELet 2
      (˝VNil)
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VNil)
    (°ELet 2
      (˝VTuple [VVar 0; VVar 1; VVar 2])
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).
Compute give_exp 0
  (°ELet 2
    (˝VTuple [VVar 0; VVar 1; VVar 2])
    (°ELet 2
      (˝VTuple [VVar 0; VVar 1; VVar 2])
      (˝VTuple [VVar 0; VVar 1; VVar 2; VVar 3; VVar 4]))).










From CoreErlang.Eqvivalence Require Export BX1EraseNames.
Import BigStep.

Section FullCircle.



Definition full_names
    (Γ : Environment)
    (e : Expression)
    : Expression
    :=
  give_names (erase_names Γ e).



Definition full_result
    (r : (ValueSequence + Exception))
    : (ValueSequence + Exception)
    :=
  give_redex (erase_result r).



End FullCircle.










From CoreErlang Require Export FunctionalBigStep.


Section TestSuccess.



  Lemma erase_names_test_X1A :
    eval_expr
      []
      []
      ""
      0
      (full_names
        []
        ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                  (EApp (EFunId ("fun1",0)) []))))
      []
      3
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X1A :
    fbs_expr 1000
      []
      []
      ""
      0
      (full_names
        []
        ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                  (EApp (EFunId ("fun1",0)) []))))
      []
    =
    Result
      3
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X6A :
    eval_expr
      []
      []
      ""
      0
      (full_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["Y"] (EValues [EFun [] (EVar "X")])
          (EApp (EVar "Y") [])))
      []
      1
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X6B :
    fbs_expr 1000
      []
      []
      ""
      0
      (full_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["Y"] (EValues [EFun [] (EVar "X")])
          (EApp (EVar "Y") [])))
      []
    =
    Result
      1
      (full_result
        ((inl [VLit (Integer 42)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X7A :
    eval_expr
      []
      []
      ""
      0
      (full_names
        []
        (ELet ["X"] (ELit (Integer 1)) 
              (ELet ["X"] (ELit (Integer 2)) 
                 (EVar "X"))))
      []
      0
      (full_result
        ((inl [VLit (Integer 2)])))
      [].
  Proof.
    cbn.
  Admitted.



  Lemma full_names_test_X7B :
    fbs_expr 1000
      []
      []
      ""
      0
      (full_names
        []
        (ELet ["X"] (ELit (Integer 1)) 
              (ELet ["X"] (ELit (Integer 2)) 
                 (EVar "X"))))
      []
    =
    Result
      0
      (full_result
        ((inl [VLit (Integer 2)])))
      [].
  Proof.
    cbn.
    auto.
  Qed.



End TestSuccess.










From CoreErlang.Eqvivalence Require Export BX3Tactics.

Section FsBs.



Lemma destruct_vnil :
  forall r,
      ⟨ [], ˝VNil ⟩ -->* (to_redex r)
  ->  r = inl [VNil].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vlit :
  forall l r,
      ⟨ [], ˝(VLit l) ⟩ -->* (to_redex r)
  ->  r = inl [VLit l].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vvar :
  forall x r,
      ⟨ [], ˝(VVar x) ⟩ -->* (to_redex r)
  ->  False.
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H3.
    ivc - H1.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vfunid :
  forall f r,
      ⟨ [], ˝(VFunId f) ⟩ -->* (to_redex r)
  ->  False.
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H3.
    ivc - H1.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vcons :
  forall v1 v2 r,
      ⟨ [], ˝(VCons v1 v2) ⟩ -->* (to_redex r)
  ->  r = inl [VCons v1 v2].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vtuple :
  forall vl r,
      ⟨ [], ˝(VTuple vl) ⟩ -->* (to_redex r)
  ->  r = inl [VTuple vl].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vmap :
  forall vvl r,
      ⟨ [], ˝(VMap vvl) ⟩ -->* (to_redex r)
  ->  r = inl [VMap vvl].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.



Lemma destruct_vclos :
  forall os id xs e r,
      ⟨ [], ˝(VClos os id xs e) ⟩ -->* (to_redex r)
  ->  r = inl [VClos os id xs e].
Proof.
  itr.
  des - r as [vs | q]; smp *.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.


Axiom no_pid :
  forall v,
    v <> VPid.

Axiom no_reference :
  forall e,
  (forall x, e <> give_names (˝VVar x))
  /\
  (forall f, e <> give_names (˝VFunId f)).



Theorem destruct_value :
  forall v r,
      ⟨ [], ˝v ⟩ -->* (to_redex r)
  ->  r = inl [v].
Proof.
  itr.
  des - v.
  bpp - destruct_vnil.
  bpp - destruct_vlit.
  pse - no_pid. con.
  bpp - destruct_vcons.
  bpp - destruct_vtuple.
  bpp - destruct_vmap.
  app - destruct_vvar in H. ivs - H.
  app - destruct_vfunid in H. ivs - H.
  bpp - destruct_vclos.
Qed.





Import BigStep.
Definition eval_expr_simpl
    (e : Expression)
    (r : (ValueSequence + Exception))
    : Prop
    := 
    forall id1, exists id2,
        eval_expr [] [] "" id1 e [] id2 r [].


Import SubstSemantics.

Theorem value_to_value :
  forall v,
    eval_expr_simpl (give_names (˝v)) (give_result (inl [v])).
Proof.
  itr.
  smp.
  ind ~ ind_fs_val - v.
  * sbn. eei. cns.
  * sbn. eei. cns.
  * pse - no_pid. eei. con.
  * pse - no_reference: (give_names (˝ VVar x)).
    des - H as [H _].
    spe - H: x.
    con.
  * pse - no_reference: (give_names (˝ VFunId f)).
    des - H as [_ H].
    spe - H: f.
    con.
  * sbn *.
    rem - v1' v2' v1'' v2'' as H1 H2 H3 H4 / H1 H2 H3 H4:
          (give_vval 0 v1)
          (give_vval 0 v2)
          (give_val v1)
          (give_val v2).
    unfold eval_expr_simpl.
    itr.
    spe - IHv2: id1.
    des - IHv2 as [id2 IHv2].
    spe - IHv1: id2.
    des - IHv1 as [id3 IHv1].
    exi - id3.
    ens.
    exa - IHv2.
    exa - IHv1.
  * sbn *.
    admit.
  * admit.
  * admit.
Admitted.



(* Theorem if_valseq_than_value :
  forall Fs e vs,
      ⟨ Fs, e ⟩ -->* (RValSeq vs)
  ->  exists vs',
        ⟨ Fs, RValSeq vs' ⟩ -->* (RValSeq vs).
Proof.
  itr.
  ivc - H as [k [H1 H2]].
  ivs - H2.
  * exi - vs.
    open.
    step.
  * ivs - H.
    - exi - [v].
      open.
      exa - H0.
    -  *)



Lemma destruct_econs :
  forall e1 e2 r,
      ((exists v1 v2,
          r = inl [VCons v1 v2]
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inl [v1]))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q1 v2,
          r = inr q1
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inr q1))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q2,
          r = inr q2
      /\  ⟨ [], e2 ⟩ -->* (to_redex (inr q2))))
  ->  ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r).
Proof.
  itr.
  des - H as [H | [H | H]].
  * des - H as [v1 [v2 [Heq [Hv1 Hv2]]]].
    sbt.
    des - Hv1 as [k1 [Hscope1 Hstep1]].
    des - Hv2 as [k2 [Hscope2 Hstep2]].
    open / Hscope1 Hscope2.
    step - Hstep2.
    step - Hstep1.
    step.
  * des - H as [v1 [v2 [Heq [Hv1 Hv2]]]].
    sbt.
    des - Hv1 as [k1 [Hscope1 Hstep1]].
    des - Hv2 as [k2 [Hscope2 Hstep2]].
    open / Hscope1 Hscope2.
    step - Hstep2.
    step - Hstep1.
    step.
  * des - H as [v2 [Heq Hv2]].
    sbt.
    des - Hv2 as [k2 [Hscope2 Hstep2]].
    open / Hscope2.
    step - Hstep2.
    step.
Qed.

Theorem exi_nat_plus :
  forall n,
    exists n1 n2,
      n = n1 + n2.
Proof.
  ind - n.
  exi - 0 0.
  trv.
  des - IHn as [n1 [n2 IHn]].
  exi - (S n1) n2.
  rwr - Nat.add_succ_l.
  bwr - IHn.
Qed.

Theorem trans_middle :
  forall k Fs1 Fs3 e1 e3,
      ⟨ Fs1, e1 ⟩ -[k]-> ⟨ Fs3, e3 ⟩
  ->  exists k1 k2 Fs2 e2,
          ⟨ Fs1, e1 ⟩ -[k1]-> ⟨ Fs2, e2 ⟩
      /\  ⟨ Fs2, e2 ⟩ -[k2]-> ⟨ Fs3, e3 ⟩.
Proof.
  itr.
  induction H.
  * exi - 0 0 fs e.
    spl.
    cns.
    cns.
  * (* pse - exi_nat_plus: k.
    des - H1 as [k1 [k2 Heqk]].
    sbt. *)
    des - IHstep_rt as [k1 [k2 [Fs2 [e2 [Hstep1 Hstep2]]]]].
    exi - (S k1) k2 Fs2 e2.
    spl.
    2: asm.
    ens.
    exa - H.
    asm.
Qed.



Theorem split_econs_first :
  forall e1 e2 vs,
    ⟨ [], °(ECons e1 e2) ⟩ -->* (RValSeq vs)
  ->  exists v2,
      ⟨ [], RExp e2 ⟩ -->* (RValSeq [v2]).
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  pse - trans_middle:
        k ([] : FrameStack) ([] : FrameStack)
        (°(ECons e1 e2)) (RValSeq vs)
        Hstep.
  des - H as [k1 [k2 [Fs [e [Hstep1 Hstep2]]]]].
  ivs - Hstep1.
  * ivs - Hstep2.
    ivc - H.
    clr + H0.
    ivs - H0.
    ivs - H1.
    - ivs - H0.
      ivs - H6.
      ivs - H3.
    - ivs - H.
Admitted.
    



Lemma destruct_econs2 :
  forall e1 e2 r,
      ⟨ [], °(ECons e1 e2) ⟩ -->* (to_redex r)
  ->  (exists v1 v2,
          r = inl [VCons v1 v2]
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inl [v1]))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q1 v2,
          r = inr q1
      /\  ⟨ [], RExp e1 ⟩ -->* (to_redex (inr q1))
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inl [v2])))
  \/  (exists q2,
          r = inr q2
      /\  ⟨ [], RExp e2 ⟩ -->* (to_redex (inr q2))).
Proof.
  itr.
  ivc - H as [k [Hscope Hstep]].
  eapply transitive_eval in Hstep.
  ivc - Hstep.
  des - r; ivc - H2.
  ivs - H.
  eapply transitive_eval_rev in H0.
  ivs - H0.
  ivs - H1.
  des - r as [vs | q]; smp *.
  * lft.
    ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
    2: {
    trv.
    ivc - H.
  * ivc - H as [k [_ H1]].
    ivc - H1.
    ivc - H.
    ivc - H0.
    ivc - H.
Qed.













Theorem eq_fsbs :
  forall e r,
      step_any [] (RExp e) (to_redex r)
  ->  eval_expr_simpl (give_names e) (give_result r).
Proof.
  ind ~ ind_fs_exp - e;
        itr - r HF.
  (* VNil*)
  14:{
    app - destruct_value in HF.
    sbt.
    app - value_to_value.
  }
  3: {
    app - destruct_econs in HF.
  }
Admitted.




































(* Definition result_in_scope
    ()

Axiom result_scope :
    forall r,
    to_redex. *)

Fixpoint no_reference_val
    (v : Val)
    : Prop
    :=
  match v with

  | VNil => True

  | VLit _ => True

  | VVar _ => False

  | VFunId _ => False

  | VPid _ => False

  | VCons v1 v2 => no_reference_val v1 /\ no_reference_val v2

  | VTuple vs =>
    fold_right
        (fun v acc =>
          no_reference_val v /\ acc)
        True
        vs

  | VMap vvs =>
    fold_right
        (fun '(vk, vv) acc =>
          no_reference_val vk /\ no_reference_val vv /\ acc)
        True
        vvs

  | VClos _ _ _ _ => True

  end.

Import BigStep.

Fixpoint no_reference_exp
    (e : Expression)
    : Prop
    :=
  match e with

  | ENil => True

  | ELit _ => True

  | EVar _ => False

  | EFunId _ => False

  | ECons e1 e2 => no_reference_exp e1 /\ no_reference_exp e2

  | ESeq e1 e2 => no_reference_exp e1 /\ no_reference_exp e2

  | ETuple es =>
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EValues es =>
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EPrimOp _ es =>
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EApp e es =>
    no_reference_exp e /\
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | ECall em ef es =>
    no_reference_exp em /\
    no_reference_exp ef /\
    fold_right
        (fun e acc =>
          no_reference_exp e /\ acc)
        True
        es

  | EMap ees =>
    fold_right
        (fun '(ek, ev) acc =>
          no_reference_exp ek /\ no_reference_exp ev /\ acc)
        True
        ees

  | _ => True

  end.



Theorem eval_value_no_reference :
  forall v r,
      ⟨ [], ˝v ⟩ -->* r
  ->  no_reference_val v.
Proof.
  itr.
  ind ~ ind_fs_val - v; smp; trv.
  * admit.
  * ivc - H as [k [H1 H2]].
    ivc - H2.
    ivc - H1.
    ivc - H.
    ivc - H4.
    ivc - H3.
  * ivc - H as [k [H1 H2]].
    ivc - H2.
    ivc - H1.
    ivc - H.
    ivc - H4.
    ivc - H3.
  * 
  
    unfold is_result in H1.
    1: con.



Lemma any_cool_value :
  forall v,
      VALCLOSED v
  ->  ⟨ [], ˝v ⟩ -->* (RValSeq [v]).
Proof.
  itr.
  open.
  step.
Qed.

Lemma rt_cool_value :
  forall v,
      VALCLOSED v
  ->  ⟨ [], ˝v ⟩ -[ 1 ]-> ⟨ [], RValSeq [v] ⟩.
Proof.
  itr.
  step.
Qed.

Lemma one_cool_value :
  forall v,
      VALCLOSED v
  ->  ⟨ [], ˝v ⟩ --> ⟨ [], RValSeq [v] ⟩.
Proof.
  itr.
  step.
  asm.
Qed.

Lemma eq_cool_value :
  forall v r,
      step_any [] (˝v) (to_redex r)
  ->  (to_redex r) = RValSeq [v].
Proof.
  itr.
  ind ~ ind_fs_val - v.
  * des - H as [k [Hscope Hstep]].
    ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ass > (VALCLOSED VNil) as Hclosed; ato.
      pse - one_cool_value as Hcool_value: VNil Hclosed.
      (* pse - cool_value: VNil ([] : FrameStack) 1 Hclosed. *)
      pose proof step_determinism Hcool_value fs' e' H.
      des - H1.
      sbt.
      ivs - H0; ato.
      ivs - H1.
  * des - H as [k [Hscope Hstep]].
    ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ass > (VALCLOSED (VLit l)) as Hclosed; ato.
      pse - one_cool_value as Hcool_value: (VLit l) Hclosed.
      (* pse - cool_value: VNil ([] : FrameStack) 1 Hclosed. *)
      pose proof step_determinism Hcool_value fs' e' H.
      des - H1.
      sbt.
      ivs - H0; ato.
      ivs - H1.
  * des - H as [k [Hscope Hstep]].
    ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ass > (VALCLOSED (VPid p)) as Hclosed; ato.
      pse - one_cool_value as Hcool_value: (VPid p) Hclosed.
      (* pse - cool_value: VNil ([] : FrameStack) 1 Hclosed. *)
      pose proof step_determinism Hcool_value fs' e' H.
      des - H1.
      sbt.
      ivs - H0; ato.
      ivs - H1.
   *  des - H as [k [Hscope Hstep]].
      ivc - Hstep.
    - des - r as [vs | q]; smp *; con.
    - ivc - H.
      admit.
   * admit.
Admitted.




Theorem eq_fsbs :
  forall e r,
      step_any [] (RExp e) (to_redex r)
  ->  exists id,
        eval_expr [] [] "" 0 (give_names e) [] id (give_result r) [].
Proof.
  itr - e r HF.
  ind ~ ind_fs_exp - e.
  (* VNil*)
  14:{
    app - eq_cool_value in HF.
    des - r as [vs | q]; ivc - HF.
    sbn.
    exi - 0.
    cns.
  }
Admitted.



End FsBs.