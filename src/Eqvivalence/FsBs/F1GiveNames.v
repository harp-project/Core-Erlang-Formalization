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

  | _ => VNil

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