From CoreErlang.Eq.Tactics Require Export T1ParamZero.
From CoreErlang.Eq.Tactics Require Export T2ParamSingle.
From CoreErlang.Eq.Tactics Require Export T3ParamMultiple.
From CoreErlang.Eq.Tactics Require Export T4Name.
From CoreErlang.Eq.Tactics Require Export T5Transform.
From CoreErlang.Eq.Tactics Require Export T6Destruct.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.

(* CHAPTERS:
* Measure
* Remove Environment
* Add Names
* Erase Names
*)


  Lemma cons_app :
    forall (T : Type) (x : T) (l : list T),
      x :: l = [x] ++ l.
  Proof.
    trv.
  Qed.







(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MEASURE //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.

(* SECTIONS
* Measure_Definitions
  - measure_val_list
  - measure_val_map
  - measure_val_env
  + measure_val
*)



Section Measure_Definitions.



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
    (env : Environment)
    : nat
    :=
  list_sum (map (measure ∘ snd) env).



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

  | VClos env ext _ _ e fid => 2
    + measure_val_env measure_val env

  end.



End Measure_Definitions.


































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: REMOVE_ENVIRONMENT ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.

(* SECTIONS
* Remove_Environment_Definitions
  - rem_keys
  - rem_fids
  + rem_vars
  + rem_ext
  + rem_ext_vars
*)





Section Remove_Environment_Definitions.



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



  Definition rem_fids
    (fids : list FunctionIdentifier)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inr fids) env.



  Definition rem_vars
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_keys (map inl vars) env.



  Definition rem_ext
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (env : Environment)
    : Environment
    :=
  rem_fids (map (snd ∘ fst) ext) env.



  Definition rem_ext_vars
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (vars : list Var)
    (env : Environment)
    : Environment
    :=
  rem_ext ext (rem_vars vars env).



End Remove_Environment_Definitions.


































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ADD_NAMES ////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.

(* SECTIONS
* Add_Names_Help_Transfrom
  = literal_to_lit
  = vars_of_pattern_list
* Add_Names_Help_Sum
  = sum_eqb
* Add_Names_Help_Name_Sub
  - name_sub
  # NameSub
* Add_Names
  - add_name
  - add_names
  - add_keys
  - add_fids
  + add_vars
  + add_ext
  + add_ext_vars
  + add_pats
*)



Section Add_Names_Help_Transfrom.



    Definition literal_to_lit
      (lit : Literal)
      : Lit
      :=
    match lit with
     | Atom s => s
     | Integer x => x
    end.



    Definition vars_of_pattern_list
      (pl : list Pattern)
      : list Var
      :=
    fold_right
      (fun x acc => variable_occurances x ++ acc)
      nil
      pl.



End Add_Names_Help_Transfrom.






Section Add_Names_Help_Sum.



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



End Add_Names_Help_Sum.






Section Add_Names_Help_Name_Sub.



  Definition name_sub
    {T}
    {dec : T -> T -> bool}
    :=
  T -> nat.



  Definition NameSub
    :=
  @name_sub
    (Var + FunctionIdentifier)
    (sum_eqb eqb (prod_eqb eqb Nat.eqb)).



End Add_Names_Help_Name_Sub.






Section Add_Names.



  Definition add_name
    {T dec}
    (name : T)
    (fns : @name_sub _ dec)
    :=
  fun x =>
    if dec x name
    then 0
    else S (fns x).



  Definition add_names
    {T}
    {dec : T -> T -> bool}
    (names : list T)
    (fns : name_sub)
    : name_sub
    :=
  fold_right
    (@add_name _ dec)
    fns
    names.



  Definition add_keys
    (keys : list (Var + FunctionIdentifier))
    (fns : NameSub)
    : NameSub
    :=
  add_names keys fns.



  Definition add_fids
    (fids : list FunctionIdentifier)
    (fns : NameSub)
    : NameSub
    :=
  add_keys (map inr fids) fns.



  Definition add_vars
    (vars : list Var)
    (fns : NameSub)
    : NameSub
    :=
  add_keys (map inl vars) fns.



  Definition add_ext
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (fns : NameSub)
    : NameSub
    :=
  add_fids (map (snd ∘ fst) ext) fns.



  Definition add_ext_vars
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    (vars : list Var)
    (fns : NameSub)
    : NameSub
    :=
  add_ext ext (add_vars vars fns).



  Definition add_expext
    (ext : list (FunctionIdentifier * FunctionExpression))
    (fns : NameSub)
    : NameSub
    :=
  add_fids (map fst ext) fns.



  Definition add_expext_vars
    (ext : list (FunctionIdentifier * FunctionExpression))
    (vars : list Var)
    (fns : NameSub)
    : NameSub
    :=
  add_expext ext (add_vars vars fns).



  Definition add_pats
    (pats : list Pattern)
    (fns : NameSub)
    : NameSub
    :=
  add_vars (vars_of_pattern_list pats) fns.



End Add_Names.


































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ERASE_NAMES //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.

(* SECTIONS
* Erase_Names
  - erase_pat
  - erase_exp
  - erase_env
  - erase_val
  # erase_names
*)



Section Erase_Names.



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
      (literal_to_lit lit)

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
    (fns : NameSub)
    (e : Expression)
    : Exp
    :=
  match e with

  | ENil =>
    ˝Syntax.VNil

  | ELit lit =>
    ˝Syntax.VLit
      (literal_to_lit lit)

  | ECons e1 e2 =>
    Syntax.ECons
      (erase_exp fns e1)
      (erase_exp fns e2)

  | ESeq e1 e2 =>
    Syntax.ESeq
      (erase_exp fns e1)
      (erase_exp fns e2)

  | EValues el =>
    Syntax.EValues
      (map (erase_exp fns) el)

  | ETuple el =>
    Syntax.ETuple
      (map (erase_exp fns) el)

  | EPrimOp s el =>
    Syntax.EPrimOp
      s
      (map (erase_exp fns) el)

  | EApp e el =>
    Syntax.EApp
      (erase_exp fns e)
      (map (erase_exp fns) el)

  | ECall e1 e2 el =>
    Syntax.ECall
      (erase_exp fns e1)
      (erase_exp fns e2)
      (map (erase_exp fns) el)

  | EMap ell =>
    Syntax.EMap
      (map
        (prod_map
          (erase_exp fns)
          (erase_exp fns))
        ell)

  | EFun vars e =>
    Syntax.EFun
      (length vars)
      (erase_exp (add_vars vars fns) e)

  | ELet vars e1 e2 =>
    Syntax.ELet
      (length vars)
      (erase_exp fns e1)
      (erase_exp (add_vars vars fns) e2)

  | ETry e1 vars1 e2 vars2 e3 =>
    Syntax.ETry
      (erase_exp fns e1)
      (length vars1)
      (erase_exp (add_vars vars1 fns) e2)
      (length vars2)
      (erase_exp (add_vars vars2 fns) e3)

  | ELetRec ext e =>
    Syntax.ELetRec
      (map
        (fun '(_, (vars, body)) =>
          (length vars,
          erase_exp (add_expext_vars ext vars fns) body))
        ext)
      (erase_exp (add_expext ext fns) e)

  | ECase e case =>
    Syntax.ECase
      (erase_exp fns e)
      (map 
        (fun '(pats, e1, e2) =>
          ((map erase_pat pats),
          erase_exp (add_pats pats fns) e1,
          erase_exp (add_pats pats fns) e2))
        case)

  | EVar var =>
    ˝Syntax.VVar
      (fns (inl var))

  | EFunId fid =>
    ˝Syntax.VFunId
      ((fns (inr fid)), snd fid)

  end.






  Definition erase_env
    (erase_val : nat -> NameSub -> Value -> Val)
    (n : nat)
    (fns : NameSub)
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  match n with
  | 0 => ˝Syntax.VNil
  | S n' =>
    (erase_exp (add_keys (map fst env) fns) e)
    .[list_subst (map (erase_val n' fns) (map snd env)) idsubst]
  end.






  Fixpoint erase_val
    (n : nat)
    (fns : NameSub)
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
        (literal_to_lit lit)

    | VCons v1 v2 =>
      Syntax.VCons
        (erase_val n' fns v1)
        (erase_val n' fns v2)

    | VTuple vl =>
      Syntax.VTuple
        (map (erase_val n' fns) vl)

    | VMap vll =>
      Syntax.VMap
        (map
          (prod_map
            (erase_val n' fns)
            (erase_val n' fns))
          vll)

    | VClos env ext _ vars e fid =>
      Syntax.VClos
        (map
          (fun '(n, fid', (vars', body)) =>
            (n,
            length vars',
            erase_env
              erase_val
              n'
              (add_ext_vars ext vars' fns)
              (rem_ext_vars ext vars' env)
              body))
          ext)
        0 (*id*)
        (length vars)
        (erase_env
          erase_val
          n'
          (add_ext_vars ext vars fns)
          (rem_ext_vars ext vars env)
          e)
    end
  end.






  Definition erase_names
    (fns : NameSub)
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  (erase_exp
    (add_keys (map fst env) fns)
    e)
  .[list_subst
    (map (fun v => erase_val (measure_val v) fns v) (map snd env))
    idsubst].






  Definition erase_cla
    (ec : ExceptionClass)
    : ExcClass
    :=
  match ec with
  | Error =>  CoreErlang.Syntax.Error
  | Throw =>  CoreErlang.Syntax.Throw
  | Exit =>   CoreErlang.Syntax.Exit
  end.






  Definition erase_exc
    fns
    (exc : Exception)
    : CoreErlang.Syntax.Exception
    :=
  match exc with
  | (ec, v1, v2) =>
      (erase_cla ec,
      erase_val (measure_val v1) fns v1,
      erase_val (measure_val v2) fns v2)
  end.






  Definition erase_names_result
    fns
    (result : (ValueSequence + Exception))
    : Redex
    :=
  match result with
  | inl vs =>   RValSeq (map (fun v => erase_val (measure_val v) fns v) vs)
  | inr exc =>  RExc (erase_exc fns exc)
  end.



End Erase_Names.


































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: STEP_TACTICS /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.

(* SECTIONS
* Step_Tactics_Help
* Step_Tactics_Main
*)



(* Help: *)



Ltac do_framestack_step
  :=
  (econstructor;
  [ (constructor; auto + scope_solver + congruence)
  + (econstructor; constructor)
  + (econstructor;
    [ congruence
    | constructor ])
  | simpl ])
  + (cbn; constructor).



Ltac do_framestack_transitive H
  :=
  eapply transitive_eval;
  [ eapply frame_indep_core in H;
    exact H
  | clear H;
    simpl ].






(* Main: *)

Tactic Notation "step"
  :=
  repeat do_framestack_step.

Tactic Notation "step"
  "-"   hyp(H)
  :=
  repeat do_framestack_step;
  (solve [exact H] + do_framestack_transitive H).

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
    clear I1 I2 I3 I4 I5.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9.

Tactic Notation "step"
  "-"   hyp(H)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
        ident(I6) ident(I7) ident(I8) ident(I9) ident(I10)
  :=
  repeat do_framestack_step;
  do_framestack_transitive H;
  clear I1 I2 I3 I4 I5 I6 I7 I8 I9 I10.

Tactic Notation "step"
  ":"   tactic(T)
  :=
  repeat do_framestack_step + T.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1)
  :=
  repeat do_framestack_step + T;
  clear I1.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3 I4.

Tactic Notation "step"
  ":"   tactic(T)
  "/"   ident(I1) ident(I2) ident(I3) ident(I4) ident(I5)
  :=
  repeat (do_framestack_step + T);
  clear I1 I2 I3 I4 I5.


































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: INDUCTION ////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
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



  Theorem ind_val :
    forall v, P v.
  Proof.
    induction v using Value_ind2 with
      (Q := Forall P)
      (R := Forall (fun x => P (fst x) /\ P (snd x)))
      (W := Forall (fun x => P (snd x)));
      intuition.
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
//// SECTION: MEASURE_REDUCTION ////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



Lemma measure_not_zero :
  forall v,
    1 <= measure_val v.
Proof.
  itr.
  des - v; sli.
Qed.


(*
Lemma measure_step :
  forall n fns v,
      1 <= n
  ->  erase_val n fns v 
    = match v with
      | VNil =>
        Syntax.VNil

      | VLit lit =>
        Syntax.VLit
          (literal_to_lit lit)

      | VCons v1 v2 =>
        Syntax.VCons
          (erase_val (n - 1) fns v1)
          (erase_val (n - 1) fns v2)

      | VTuple vl =>
        Syntax.VTuple
          (map (erase_val (n - 1) fns) vl)

      | VMap vll =>
        Syntax.VMap
          (map
            (prod_map
              (erase_val (n - 1) fns)
              (erase_val (n - 1) fns))
            vll)

      | VClos env ext id vars e fid =>
        Syntax.VClos
          (map
            (fun '(n', fid', (vars', body)) =>
              (n',
              length vars',
              erase_env
                erase_val
                (n - 1)
                (add_ext_vars ext vars' fns)
                (rem_ext_vars ext vars' env)
                body))
            ext)
          id
          (length vars)
          (erase_env
            erase_val
            (n - 1)
            (add_ext_vars ext vars fns)
            (rem_ext_vars ext vars env)
            e)
      end.
Proof.
  itr.
  des - n: lia.
  smp.
  bwr - Nat.sub_0_r.
Qed.
*)



  Lemma rem_keys_length :
    forall keys env,
      length (rem_keys keys env) <= length env.
  Proof.
    itr.
    ind - env as [| [k v] env IHenv]: sli.
    smp.
    des >
      (negb
        (existsb (λ x : Var + FunctionIdentifier, var_funid_eqb x k) keys)).
    all: slia.
  Qed.



  Lemma rem_ext_vars_length :
    forall ext vars env,
      length (rem_ext_vars ext vars env) <= length env.
  Proof.
    itr.
    ufl - rem_ext_vars rem_ext rem_fids rem_vars.
    remember ((map inr (map (snd ∘ fst) ext))) as keys1.
    remember (map inl vars) as keys2.
    clr - Heqkeys1 Heqkeys2.
    pse - rem_keys_length: keys2 env.
    pse - rem_keys_length: keys1 (rem_keys keys2 env).
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



  Lemma rem_keys_cons :
    forall keys k v env,
      rem_keys keys ((k, v) :: env)
    = rem_keys keys [(k, v)] ++ rem_keys keys env.
  Proof.
    itr.
    smp.
    des > (negb (existsb (fun x => var_funid_eqb x k) keys)) :- smp.
  Qed.



  Lemma rem_ext_vars_cons :
    forall ext vars k v env,
      rem_ext_vars ext vars ((k, v) :: env)
    = rem_ext_vars ext vars [(k, v)] ++ rem_ext_vars ext vars env.
  Proof.
    itr.
    ufl - rem_ext_vars.
    ufl - rem_vars.
    pose proof rem_keys_cons (map inl vars) k v env as Hvars.
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



Theorem measure_reduction :
  forall v fns n1 n2,
      measure_val v <= n1
  ->  measure_val v <= n2
  ->  erase_val n1 fns v
    = erase_val n2 fns v.
Proof.
  itr - v.
  ind ~ ind_val - v; itr - fns n1 n2 Hn1 Hn2.
  (* ind ~ ind_val - v. *)
  * smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    bmp.
  * smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    bmp.
  * smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    smp.
    ass > (measure_val v1 ≤ n1) as Hv1n1: smp - Hn1; lia.
    ass > (measure_val v1 ≤ n2) as Hv1n2: smp - Hn2; lia.
    ass > (measure_val v2 ≤ n1) as Hv2n1: smp - Hn1; lia.
    ass > (measure_val v2 ≤ n2) as Hv2n2: smp - Hn2; lia.
    spc - IHv1: fns n1 n2 Hv1n1 Hv1n2.
    spc - IHv2: fns n1 n2 Hv2n1 Hv2n2.
    bwr - IHv1 IHv2.
  * ren - env vars HForall: ref params H.
    smp - Hn1 Hn2.
    des - n1: lia.
    des - n2: lia.
    smp.
    feq.
    - clr - body.
      app - map_ext; itr.
      des - a as [[n fid] [vars' body]].
      feq.
      des - n1: lia.
      des - n2: lia.
      smp.
      do 2 feq.
      do 2 rwl - Nat.succ_le_mono in Hn1 Hn2.
      ind - env as [| [k v] env IHvl]: smp.
      ivc - HForall as IHv HForall: H1 H2.
      smp - IHv.
      ufl - measure_val_env in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val_env measure_val env ≤ n1) as Hvln1:
        smp; ufl - measure_val_env; lia.
      ass > (measure_val_env measure_val env ≤ n2) as Hvln2:
        smp; ufl - measure_val_env; lia.
      spc - IHv: (add_ext_vars ext vars' fns) n1 n2 Hvn1 Hvn2.
      spc - IHvl: HForall Hvln1 Hvln2.
      rwr - rem_ext_vars_cons map_app map_app.
      pse - rem_ext_vars_single as Hsingle: ext vars' k v.
      des - Hsingle.
      + cwr - H.
        smp.
        bwr - IHv IHvl.
      + cwr - H.
        smp.
        bwr - IHvl.
    - des - n1: lia.
      des - n2: lia.
      smp.
      do 2 feq.
      do 2 rwl - Nat.succ_le_mono in Hn1 Hn2.
      ind - env as [| [k v] env IHvl]: smp.
      ivc - HForall as IHv HForall: H1 H2.
      smp - IHv.
      ufl - measure_val_env in Hn1 Hn2.
      smp - Hn1 Hn2.
      ass > (measure_val v ≤ n1) as Hvn1: lia.
      ass > (measure_val v ≤ n2) as Hvn2: lia.
      ass > (measure_val_env measure_val env ≤ n1) as Hvln1:
        smp; ufl - measure_val_env; lia.
      ass > (measure_val_env measure_val env ≤ n2) as Hvln2:
        smp; ufl - measure_val_env; lia.
      spc - IHv: (add_ext_vars ext vars fns) n1 n2 Hvn1 Hvn2.
      spc - IHvl: HForall Hvln1 Hvln2.
      rwr - rem_ext_vars_cons map_app map_app.
      pse - rem_ext_vars_single as Hsingle: ext vars k v.
      des - Hsingle.
      + cwr - H.
        smp.
        bwr - IHv IHvl.
      + cwr - H.
        smp.
        bwr - IHvl.
  * ren - vl HForall: l H.
    ind - vl as [| v vl].
    - clr - HForall.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      bmp.
    - ivc - HForall as IHv HForall: H1 H2.
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
      spc - IHv: fns n1 n2 Hvn1 Hvn2.
      spc - IHvl: HForall Hvln1 Hvln2.
      smp - IHvl.
      ivc - IHvl as IHvl: H0.
      bwr - IHv IHvl.
  * ren - vl HForall: l H.
    ind - vl as [| v vl].
    - clr - HForall.
      smp - Hn1 Hn2.
      des - n1: lia.
      des - n2: lia.
      bmp.
    - ivc - HForall as IHv HForall: H1 H2.
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
      ass > (measure_val (VMap vl) ≤ S n1) as Hvln1:
        smp; ufl - measure_val_map; lia.
      ass > (measure_val (VMap vl) ≤ S n2) as Hvln2:
        smp; ufl - measure_val_map; lia.
      spc - IHv1: fns n1 n2 Hv1n1 Hv1n2.
      spc - IHv2: fns n1 n2 Hv2n1 Hv2n2.
      spc - IHvl: HForall Hvln1 Hvln2.
      smp - IHvl.
      ivc - IHvl as IHvl: H0.
      bwr - IHv1 IHv2 IHvl.
Qed.



Theorem measure_reduction_min :
  forall v fns n,
      measure_val v <= n
  ->  erase_val n fns v
    = erase_val (measure_val v) fns v.
Proof.
  itr - v fns n Hn.
  pse - measure_reduction as Hmr.
  app - Hmr; lia.
Qed.

(*
(erase_val (measure_val v1 + measure_val v2) fns v1)
*)


Theorem mred_v1v2_v1 :
  forall fns v1 v2,
    erase_val (measure_val v1 + measure_val v2) fns v1
  = erase_val (measure_val v1) fns v1.
Proof.
  itr.
  app - measure_reduction_min: lia.
Qed.


Theorem mred_v1v2_v2 :
  forall fns v1 v2,
    erase_val (measure_val v1 + measure_val v2) fns v2
  = erase_val (measure_val v2) fns v2.
Proof.
  itr.
  app - measure_reduction_min: lia.
Qed.





























(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ENVIRONMENT_LEMMAS ///////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



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
  Qed.



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


  (* Lemma get_value_det :
    forall env key  *)

  Lemma get_value_single_det :
    forall k1 k2 v1 v2,
        get_value [(k1, v1)] k2 = Some [v2]
    ->  k1 = k2 /\  v1 = v2.
  Proof.
    itr - k1 k2 v1 v2 Hget.
    smp - Hget.
    des > (var_funid_eqb k2 k1) as Hk; ivc - Hget.
    spl.
    2: rfl.
    ufl - var_funid_eqb in Hk.
    des - k1 as [s1 | f1]; des - k2 as [s2 | f2]; smp - Hk.
    * app - String.eqb_eq in Hk.
      bvs - Hk.
    * con.
    * con.
    * ufl - funid_eqb in Hk.
      des - f1 as [i1 n1]; des - f2 as [i2 n2]; smp - Hk.
      app - andb_prop in Hk.
      des - Hk as [Hi Hn].
      app - String.eqb_eq in Hi.
      app - Nat.eqb_eq in Hn.
      sbt.
      rfl.
  Qed.



  Lemma rem_keys_empty :
    forall env,
      rem_keys [] env = env.
  Proof.
    (* #1 Induction on Environment: induction + simpl*)
    ind - env as [| [k v] env IHenv] :> smp.
    (* #2 Rewrite by Induction: rewrite *)
    bwr - IHenv.
  Qed.



  Lemma rem_ext_empty :
    forall env,
      rem_ext [] env = env.
  Proof.
    app - rem_keys_empty.
  Qed.


  Lemma valclosed_to_isresult :
    forall v,
        VALCLOSED v
    ->  is_result (RValSeq [v]).
  Proof.
    itr.
    cns.
    scope_solver.
  Qed.
    

































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCE //////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Theorem eq_bsfs :
  forall env modules own_module id id' e e' eff eff',
      (eval_expr env modules own_module id e eff id' e' eff')
  ->  forall fns r,
        is_result r
    ->  erase_names_result fns e' = r
    ->  ⟨ [], (erase_names fns env e) ⟩ -->* r.
Proof.
  itr - env modules own_module id id' e e' eff eff' B.
  ind - B; itr - fns r Hscope Hresult.
  (* ENil *)
  3: {
    ivc - Hresult.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  (* ELit *)
  3: {
    ivc - Hresult.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  (* EVar *)
  3: {
    ren - var vs Hget: s res H.
    ivc - Hresult.
    sbn.
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    sbn - Hscope.
    (**)
    ind - env as [| [k1 v1] env IHenv]: ivs - Hget.
    app + get_value_cons as Hget_cons in Hget.
    des - Hget_cons as [Hget1 | Hgets].
    * app - get_value_single_det in Hget1.
      des - Hget1 as [Hk1 Hv1].
      sbt.
      rwr - cons_app.
      do 3 rwr - map_app.
      ufl - list_subst idsubst add_keys.
      unfold add_names.
      unfold add_name.
      smp.
      rwr - String.eqb_refl.
      smp.
      eei; spl.
      1: exa - Hscope.
      step.
      ivc - Hscope as Hscope: H0.
      ivc - Hscope as Hscope: H1 / H2.
      exa - Hscope.
    * spe - IHenv: Hgets.
      rwr - cons_app.
      do 3 rwr - map_app.
      ufl - list_subst idsubst add_keys.
      unfold add_names.
      unfold add_name.
      smp.
      des - k1 as [var1 | fid1].
      - des > ((var =? var1)%string) as Hvar.
        + smp - Hget.
          rwr - Hvar in Hget.
          ivc - Hget.
          app - String.eqb_eq in Hvar.
          sbt.
          smp.
          eei; spl.
          1: exa - Hscope.
          step.
          ivc - Hscope as Hscope: H0.
          ivc - Hscope as Hscope: H1 / H2.
          exa - Hscope.
        + smp.
          app - IHenv.
      - smp.
        app - IHenv.
     (**)
     (*
     rem - vs1 vs2 ks1 ks2 as Hvs1 Hvs2 Hks1 Hks2:
      (map (λ v0 : Value, erase_val (measure_val v0) fns v0) (map snd env1))
      (map (λ v0 : Value, erase_val (measure_val v0) fns v0) (map snd env2))
      (map fst env1)
      (map fst env2).
     *)
     (*
    app + get_value_in in Hget as HIn.
    app + In_split in HIn as Heq_env.
    des - Heq_env as [env1]; ren - Heq_env: H.
    des - Heq_env as [env2]; ren - Heq_env: H.
    rwr - Heq_env. (* clr - env. *)
    rwr - cons_app.
    do 6 rwr - map_app.
    (**)
    smp.
    ufl - list_subst idsubst add_keys.
    unfold add_names.
    unfold add_name.
    ind - env as [| [k1 v1] env IHenv].
    * des - env1; ivs - Heq_env.
    * app - get_value_cons in Hget.
      des - Hget as [Hget1 | Hgets].
      - smp - Hget1.
        des - k1 as [var1 | fid1].
        + des > ((var =? var1)%string).
          ** ivs - Hget1.
            
    
    
      smp.
      rwr - String.eqb_refl.
      smp.
      eei; spl.
      1: exa - Hscope.
      step.
      ivc - Hscope as Hscope: H0.
      ivc - Hscope as Hscope: H1 / H2.
      exa - Hscope.
    * smp.
      des - k1 as [var1 | fid1].
      - des > ((var =? var1)%string) as Hvar; smp.
        (*wfm env -> this cant be true*)
        + admit.
        + 
      - 
      rwr - String.eqb_refl.
      
    
    
    
    
    
    
    
    
    
    
    (**)
    rem - vs1 vs2 ks1 ks2 as Hvs1 Hvs2 Hks1 Hks2:
      (map (λ v0 : Value, erase_val (measure_val v0) fns v0) (map snd env1))
      (map (λ v0 : Value, erase_val (measure_val v0) fns v0) (map snd env2))
      (map fst env1)
      (map fst env2).
    ass > (length ks1 = length vs1) as Hlength1:
      rwr - Hks1 Hvs1; do 3 rwr - map_length.
    ass > (length ks2 = length vs2) as Hlength2:
      rwr - Hks2 Hvs2; do 3 rwr - map_length.
    (* clr - Hvs1 Hvs2 Hks1 Hks2. *)
    smp.
    rem - v' as Hv:
      (erase_val (measure_val v) fns v);
      clr - Hv v; ren - v: v'.
    remember (inl var) as k eqn: Hk. (* clr - Hk var. *)
    ufl - list_subst idsubst add_keys.
    unfold add_names.
    unfold add_name.
    ind - env1 as [| kv1 env1 IHenv1].
    * smp - Hks1 Hvs1.
      rwr - Hks1 Hvs1.
      ivc - Hk.
      sbn.
      rwr - String.eqb_refl.
      smp.
      eei; spl.
      1: exa - Hscope.
      step.
      ivc - Hscope as Hscope: H0.
      ivc - Hscope as Hscope: H1 / H2.
      exa - Hscope.
    * smp - Hks1 Hvs1.
      des - ks1 as [| k1 ks1]: ivs - Hks1.
      des - vs1 as [| v1 vs1]: ivs - Hvs1.
      admit.
      
      unfold 
      des > (sum_eqb eqb (prod_eqb eqb Nat.eqb) k k).
      
    eei; spl.
    1: cns; scope_solver.
    step.
    *)
  }
  5: {
    ivc - Hresult.
    sbn + Hscope.
    ufl - rem_ext_vars in *.
    rwr - rem_ext_empty in *.
    eei; spl.
    1: exa - Hscope.
    clr - Hscope.
    step.
    admit.
  }
  6: {
    ren - e1 e2 v1 v2: hd tl hdv tlv.
    ivc - Hresult.
    sbn.
    ivc - Hscope as Hscope: H0.
    ivc - Hscope as Hscope: H1 / H2.
    ivc - Hscope as Hscope_v1 Hscope_v2: H2 H3.
    rwr - mred_v1v2_v1 in Hscope_v1.
    rwr - mred_v1v2_v2 in Hscope_v2.
    app - valclosed_to_isresult in Hscope_v1.
    app - valclosed_to_isresult in Hscope_v2.
    ass - as Heq_v1 >
      (erase_names_result (add_keys (map fst env) fns) (inl [v1]) =
       RValSeq [erase_val (measure_val v1) fns v1]).
    sbn. (* 
    spe - IHB2:
      (add_keys (map fst env) fns)
      (RValSeq [erase_val (measure_val v1) fns v1])
      (Hscope_v1). *)
    
  }
  11: {
    ivc - Hresult.
    sbn + Hscope.
    eei; spl.
    1: exa - Hscope.
    clr - Hscope.
    step.
    sbn - IHB1 IHB2.
  }

Admitted.


Theorem eq_bsfs1 :
  forall env modules own_module id id' e e' eff eff',
      (eval_expr env modules own_module id e eff id' e' eff')
  ->  forall fadde (faddv : NameSub -> NameSub) fns,
        is_result (erase_names_result (faddv fns) e')
    ->  ⟨ [], (erase_names (fadde fns) env e) ⟩ -->* erase_names_result (faddv fns) e'.
Proof.
  itr - env modules own_module id id' e e' eff eff' B.
  ind - B; itr - fadde faddv fns Hscope.
  (* ENil *)
  3: {
    clr - modules own_module id eff Hscope.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  (* ELit *)
  3: {
    clr - modules own_module id eff Hscope.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  8: {
    clr - B1 B2 id id' id'' eff1 eff2 eff3 modules own_module.
    ren - e1 e2 v1 v2 IHF_v1 IHF_v2: hd tl hdv tlv IHB2 IHB1.
    sbn.
    (*scope*)
    ivc - Hscope as Hscope: H0.
    ivc - Hscope as Hscope: H1 / H2.
    ivc - Hscope as Hscope_v1 Hscope_v2: H2 H3.
    rwr + mred_v1v2_v1 in Hscope_v1.
    rwr + mred_v1v2_v2 in Hscope_v2.
    app - valclosed_to_isresult in Hscope_v1.
    app - valclosed_to_isresult in Hscope_v2.
    (*spec*)
    spc - IHF_v1: (add_keys (map fst env) ∘ fadde) faddv fns Hscope_v1.
    spc - IHF_v2: (add_keys (map fst env) ∘ fadde) faddv fns Hscope_v2.
    (*des*)
    des - IHF_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHF_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    eei; spl.
    1: {
      ivc - Hscope_v1.
      ivc - Hscope_v2.
      destruct_foralls.
      cns; scope_solver.
    }
    step.
  }
Admitted.


Theorem eq_bsfs2 :
  forall env modules own_module id id' e e' eff eff',
      (eval_expr env modules own_module id e eff id' e' eff')
  ->  forall fe fv,
        is_result (erase_names_result fv e')
    ->  ⟨ [], (erase_names fe env e) ⟩ -->* erase_names_result fv e'.
Proof.
  itr - env modules own_module id id' e e' eff eff' B.
  ind - B; itr - fe fv Hscope.
  (* ENil *)
  3: {
    clr - modules own_module id eff Hscope.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  (* ELit *)
  3: {
    clr - modules own_module id eff Hscope.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  8: {
    clr - B1 B2 id id' id'' eff1 eff2 eff3 modules own_module.
    ren - e1 e2 v1 v2 IHF_v1 IHF_v2: hd tl hdv tlv IHB2 IHB1.
    sbn.
    (*scope*)
    ivc - Hscope as Hscope: H0.
    ivc - Hscope as Hscope: H1 / H2.
    ivc - Hscope as Hscope_v1 Hscope_v2: H2 H3.
    rwr + mred_v1v2_v1 in Hscope_v1.
    rwr + mred_v1v2_v2 in Hscope_v2.
    app - valclosed_to_isresult in Hscope_v1.
    app - valclosed_to_isresult in Hscope_v2.
    (*spec*)
    spc - IHF_v1: fe fv Hscope_v1.
    spc - IHF_v2: fe fv Hscope_v2.
    (*des*)
    des - IHF_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHF_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (*ufl*)
    ufl - erase_names in Hstep_v1.
    ufl - erase_names in Hstep_v2.
    eei; spl.
    1: {
      ivc - Hscope_v1.
      ivc - Hscope_v2.
      destruct_foralls.
      cns; scope_solver.
    }
    step.
  }
Admitted.


Theorem eq_bsfs3 :
  forall env modules own_module id id' e e' eff eff',
      (eval_expr env modules own_module id e eff id' e' eff')
  ->  forall fns,
        is_result (erase_names_result fns e')
    ->  ⟨ [], (erase_names fns env e) ⟩ -->* erase_names_result fns e'.
Proof.
  itr - env modules own_module id id' e e' eff eff' B.
  ind - B; itr - fns Hscope.
  (* ENil *)
  3: {
    clr - modules own_module id eff Hscope.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  (* ELit *)
  3: {
    clr - modules own_module id eff Hscope.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  8: {
    clr - B1 B2 id id' id'' eff1 eff2 eff3 modules own_module.
    ren - e1 e2 v1 v2 IHF_v1 IHF_v2: hd tl hdv tlv IHB2 IHB1.
    sbn.
    (*scope*)
    ivc - Hscope as Hscope: H0.
    ivc - Hscope as Hscope: H1 / H2.
    ivc - Hscope as Hscope_v1 Hscope_v2: H2 H3.
    rwr + mred_v1v2_v1 in Hscope_v1.
    rwr + mred_v1v2_v2 in Hscope_v2.
    app - valclosed_to_isresult in Hscope_v1.
    app - valclosed_to_isresult in Hscope_v2.
    (*spec*)
    spc - IHF_v1: fns Hscope_v1.
    spc - IHF_v2: fns Hscope_v2.
    (*des*)
    des - IHF_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHF_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (*ufl*)
    ufl - erase_names in Hstep_v1.
    ufl - erase_names in Hstep_v2.
    eei; spl.
    1: {
      ivc - Hscope_v1.
      ivc - Hscope_v2.
      destruct_foralls.
      cns; scope_solver.
    }
    step - Hstep_v2.
    step - Hstep_v1.
    step.
  }
  13: {
    clr - B1 B2 id id' id'' eff1 eff' eff'' modules own_module.
    ren - vars vs Hlength_vars IHF_v1 IHF_v2: l vals H IHB2 IHB1.
    sbn.
    (*scope*)
    admit.
  }
Admitted.





(*IMPORTANT*)
Lemma list_subst_cons :
  forall v vs ξ,
    list_subst [v] (list_subst vs ξ)
  = list_subst (v::vs) ξ.
Proof.
  trv.
Qed.

(*IMPORTANT*)
Lemma list_subst_fold_right :
  forall vs ξ,
    fold_right (fun v σ => v .: σ) ξ vs
  = list_subst vs ξ.
Proof.
  trv.
Qed.

(*IMPORTANT*)
Lemma list_subst_app :
  forall vs1 vs2 ξ,
    list_subst vs1 (list_subst vs2 ξ)
  = list_subst (vs1 ++ vs2) ξ.
Proof.
  itr.
  rewrite <- list_subst_fold_right with (vs:= vs1 ++ vs2).
  rewrite <- list_subst_fold_right with (vs:= vs1).
  rewrite <- list_subst_fold_right with (vs:= vs2).
  bwr - foldr_app.
Qed.

(*(add_keys (map inl vars) (add_keys (map fst env) fns))*)
(*(add_keys keys1 (add_keys keys2 fns))*)

Lemma add_keys_app :
  forall keys1 keys2 fns,
    add_keys keys1 (add_keys keys2 fns)
  = (add_keys (keys1 ++ keys2) fns).
Proof.
  itr.
  ufl - add_keys.
  unfold add_names.
  bwr - foldr_app.
Qed.

Theorem eq_bsfs4 :
  forall env modules own_module id id' e e' eff eff',
      (eval_expr env modules own_module id e eff id' e' eff')
  ->  forall fns,
        ⟨ [], (erase_names fns env e) ⟩ -->* erase_names_result fns e'.
Proof.
  itr - env modules own_module id id' e e' eff eff' B.
  ind - B; itr - fns.
  (* ENil *)
  3: {
    clr - modules own_module id eff.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  (* ELit *)
  3: {
    clr - modules own_module id eff.
    sbn.
    eei; spl.
    1: cns; scope_solver.
    step.
  }
  8: {
    clr - B1 B2 id id' id'' eff1 eff2 eff3 modules own_module.
    ren - e1 e2 v1 v2 IHF_v1 IHF_v2: hd tl hdv tlv IHB2 IHB1.
    sbn.
    (*mred*)
    rwr - mred_v1v2_v1.
    rwr - mred_v1v2_v2.
    (*spec*)
    spc - IHF_v1: fns.
    spc - IHF_v2: fns.
    (*des*)
    des - IHF_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHF_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (*ufl*)
    ufl - erase_names in Hstep_v1.
    ufl - erase_names in Hstep_v2.
    eei; spl.
    1: {
      ivc - Hscope_v1.
      ivc - Hscope_v2.
      destruct_foralls.
      cns; scope_solver.
    }
    step - Hstep_v2.
    step - Hstep_v1.
    step.
  }
  13: {
    clr - B1 B2 id id' id'' eff1 eff' eff'' modules own_module.
    ren - vars vs Hlength_vars IHF_v1 IHF_v2: l vals H IHB1 IHB2.
    sbn.
    (*spec*)
    spc - IHF_v1: fns.
    spc - IHF_v2: fns.
    (*des*)
    des - IHF_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - IHF_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (*ufl*)
    ufl - erase_names in Hstep_v1.
    ufl - erase_names in Hstep_v2.
    eei; spl.
    1: {
      admit.
    }
    step - Hstep_v1.
    step.
    1: rwr - map_length; bym.
    rwr - subst_comp_exp.
    assert
      (length vs = length (map (λ v : Value, erase_val (measure_val v) fns v) vs)).
    1: admit.
    (*list_subst*)
    rwr - Hlength_vars.
    rwr - H.
    rwr - substcomp_list.
    rwr - substcomp_id_r.
    rwr - list_subst_app.
    clr - H.
    (*add_keys*)
    ufl - add_vars.
    rwr - add_keys_app.
    (* pse - list_subst_app:
      (map (λ v : Value, erase_val (measure_val v) fns v) vs)
      (map (λ v : Value, erase_val (measure_val v) fns v) (map snd env))
      (idsubst).
    rwr - H0.
    rewrite list_subst_app. *)
    Print upn.
    Print iterate.
    Check iterate.
    Print fold_right.
    Search "length" "map".
    admit.
  }
Admitted.


(*
Hlength_vars : base.length vars = base.length vs
fns : NameSub
kv1 : nat
Hscope_v1 : is_result (erase_names_result fns (inl vs))
kv2 : nat
Hscope_v2 : is_result (erase_names_result fns res)
Hstep_v2 : ⟨ [],
           (erase_exp (add_keys (map fst (append_vars_to_env vars vs env)) fns) e2).[
           list_subst
             (map (λ v : Value, erase_val (measure_val v) fns v)
                (map snd (append_vars_to_env vars vs env))) idsubst] ⟩ -[ kv2 ]-> ⟨ [],
           erase_names_result fns res ⟩
______________________________________(1/1)
⟨ [],
(erase_exp (add_vars vars (add_keys (map fst env) fns)) e2).[upn (base.length vars)
                                                               (list_subst
                                                                  (map
                                                                     (λ v : Value,
                                                                       erase_val 
                                                                       (measure_val v) fns v)
                                                                     (map snd env)) idsubst)].[
list_subst (map (λ v : Value, erase_val (measure_val v) fns v) vs) idsubst] ⟩ -[ 
?k ]-> ⟨ [], erase_names_result fns res ⟩
*)

(*Not Need*)
Lemma add_keys_empty :
  forall fns,
    add_keys [] fns = fns.
Proof.
  bmp.
Qed.

Lemma add_vars_empty :
  forall fns,
    add_vars [] fns = fns.
Proof.
  bmp.
Qed.


Theorem append_to_upn_vars :
  forall fns env vars vs e k r,
      base.length vars = base.length vs
  ->  ⟨ [], (erase_exp
              (add_keys
                (map fst (append_vars_to_env vars vs env))
                fns)
              e)
            .[list_subst
              (map
                (fun v => erase_val (measure_val v) fns v)
                (map snd (append_vars_to_env vars vs env)))
              idsubst] ⟩
        -[ k ]-> ⟨ [], erase_names_result fns r ⟩
    = ⟨ [], (erase_exp
              (add_vars
                vars
                (add_keys (map fst env) fns))
              e)
            .[upn
              (base.length vars)
              (list_subst
                (map
                   (fun v =>
                     erase_val 
                     (measure_val v) fns v)
                   (map snd env)) idsubst)]
            .[list_subst
              (map
                (fun v => erase_val (measure_val v) fns v) vs)
                idsubst] ⟩
        -[ k ]-> ⟨ [], erase_names_result fns r ⟩.
Proof.
  itr - fns env vars vs e k r Hlength.
  ind - vs as [| v vs IHvs].
  * ivc - Hlength as Hzero: H0.
    app - List.length_zero_iff_nil in Hzero.
    ivc - Hzero.
    smp.
    rwr - add_vars_empty.
    pse - idsubst_is_id.
    des - H as [Hid _].
    bwr - Hid.
  * admit.
Admitted.


Fixpoint pair_list {A B : Type} (al : list A) (bl : list B) : option (list (A * B)) :=
match al, bl with
| [], [] => Some []
| a :: al', b :: bl' =>
  match pair_list al' bl' with
  | Some l => Some ((a, b) :: l)
  | None => None
  end
| _, _ => None
end.

Lemma pair_list_unfold :
  forall  A B (al : list A) (bl : list B),
    pair_list al bl
  = match al, bl with
    | [], [] => Some []
    | a :: al', b :: bl' =>
      match pair_list al' bl' with
      | Some l => Some ((a, b) :: l)
      | None => None
      end
    | _, _ => None
    end.
Proof.
  itr.
  des - al; des - bl; bmp.
Qed.

Lemma some_pair_list :
  forall A B (al : list A) (bl : list B),
      length al = length bl
  ->  exists l, pair_list al bl = Some l.
Proof.
  intros A B al bl H.
  generalize dependent bl.
  induction al as [| a al' IH]; intros bl H.
  - (* Case: al = [] *)
    destruct bl as [| b bl'].
    + (* Case: bl = [] *)
      exists []. reflexivity.
    + (* Case: bl = b :: bl' *)
      simpl in H. discriminate.
  - (* Case: al = a :: al' *)
    destruct bl as [| b bl'].
    + (* Case: bl = [] *)
      simpl in H. discriminate.
    + (* Case: bl = b :: bl' *)
      simpl in H. inversion H.
      apply IH in H1.
      destruct H1 as [l H1].
      exists ((a, b) :: l).
      simpl. rewrite H1. reflexivity.
Qed.
(* 
Lemma some_pair_list1 :
  forall A B (al : list A) (bl : list B),
      (exists l, pair_list al bl = Some l)
  ->  length al = length bl.
Proof.
  intros A B al bl H.
  destruct H as [l H].
  generalize dependent bl.
  induction al as [| a al' IH]; intros bl H.
  - (* Case: al = [] *)
    simpl in H.
    destruct bl as [| b bl'].
    + (* Case: bl = [] *)
      reflexivity.
    + (* Case: bl = b :: bl' *)
      simpl in H. discriminate.
  - (* Case: al = a :: al' *)
    simpl in H.
    destruct bl as [| b bl'].
    + (* Case: bl = [] *)
      simpl in H. discriminate.
    + (* Case: bl = b :: bl' *)
      simpl in H.
      destruct (pair_list al' bl') eqn:Hpair.
      * (* Case: pair_list al' bl' = Some l0 *)
        inversion H. subst.
        simpl. f_equal.
        apply IH.  admit.
      * (* Case: pair_list al' bl' = None *)
        discriminate.



  itr - A B al bl HSome.
  des - al; des - bl; smp - HSome.
  * rfl.
  * des - HSome as [l HSome]; con.
  * des - HSome as [l HSome]; con.
  * 
  
  
  
  des - HSome as [l HSome].
  des - al; des - bl; smp - HSome.
    - rfl.
    - con.
    - con.
    - des > (pair_list al bl).
      + con.
      + con.
  
  
  ind - l.
  * rwr - pair_list_unfold in HSome.
    des - al; des - bl.
    - rfl.
    - con.
    - con.
    - des > (pair_list al bl).
      + con.
      + con.
  * 
    
  * ivc - Hlength as Hzero: H0.
    sym - Hzero.
    app - List.length_zero_iff_nil in Hzero.
    ivc - Hzero.
    smp.
    eei.
    cns.
  * admit.
Admitted. *)
  

Lemma connect_two :
  forall A B (al : list A) (bl : list B),
      length al = length bl
  ->  exists l,
          al = (map fst l)
      /\  bl = (map snd l).
Proof.
  itr - A B al bl Hlength.
  app - some_pair_list as HSome in Hlength.
  des - HSome as [l HSome].
  exi - l.
  generalize dependent bl.
  generalize dependent l.
  induction al as [| a al' IH]; intros l bl HSome.
  - (* Case: al = [] *)
    destruct bl as [| b bl'].
    + (* Case: bl = [] *)
      simpl in HSome.
      inversion HSome. subst.
      split; reflexivity.
    + (* Case: bl = b :: bl' *)
      simpl in HSome. discriminate.
  - (* Case: al = a :: al' *)
    destruct bl as [| b bl'].
    + (* Case: bl = [] *)
      simpl in HSome. discriminate.
    + (* Case: bl = b :: bl' *)
      simpl in HSome.
      destruct (pair_list al' bl') eqn:Hpair.
      * (* Case: pair_list al' bl' = Some l0 *)
        inversion HSome. subst.
        apply IH in Hpair.
        destruct Hpair as [Hfst Hsnd].
        split.
        -- simpl. f_equal. assumption.
        -- simpl. f_equal. assumption.
      * (* Case: pair_list al' bl' = None *)
        discriminate.
Qed.


Theorem append_to_upn_vars1 :
  forall fns env vars vs e k r,
      base.length vars = base.length vs
  ->  ⟨ [], (erase_exp
              (add_keys
                (map fst (append_vars_to_env vars vs env))
                fns)
              e)
            .[list_subst
              (map
                (fun v => erase_val (measure_val v) fns v)
                (map snd (append_vars_to_env vars vs env)))
              idsubst] ⟩
        -[ k ]-> ⟨ [], erase_names_result fns r ⟩
    = ⟨ [], (erase_exp
              (add_vars
                vars
                (add_keys (map fst env) fns))
              e)
            .[upn
              (base.length vars)
              (list_subst
                (map
                   (fun v =>
                     erase_val 
                     (measure_val v) fns v)
                   (map snd env)) idsubst)]
            .[list_subst
              (map
                (fun v => erase_val (measure_val v) fns v) vs)
                idsubst] ⟩
        -[ k ]-> ⟨ [], erase_names_result fns r ⟩.
Proof.
  itr - fns env vars vs e k r Hlength.
  app - connect_two as Hexists in Hlength.
  des - Hexists as [l [Hvars Hvs]].
  cwr - Hvars Hvs.
  ind - l as [| [var v] l IH].
  * smp.
    rwr - add_vars_empty.
    pse - idsubst_is_id.
    des - H as [Hid _].
    bwr - Hid.
  * admit.
Admitted.


Theorem append_to_upn_vars2 :
  forall e fns env vars vs k r,
      base.length vars = base.length vs
  ->  ⟨ [], (erase_exp
              (add_keys
                (map fst (append_vars_to_env vars vs env))
                fns)
              e)
            .[list_subst
              (map
                (fun v => erase_val (measure_val v) fns v)
                (map snd (append_vars_to_env vars vs env)))
              idsubst] ⟩
        -[ k ]-> ⟨ [], erase_names_result fns r ⟩
    = ⟨ [], (erase_exp
              (add_vars
                vars
                (add_keys (map fst env) fns))
              e)
            .[upn
              (base.length vars)
              (list_subst
                (map
                   (fun v =>
                     erase_val 
                     (measure_val v) fns v)
                   (map snd env)) idsubst)]
            .[list_subst
              (map
                (fun v => erase_val (measure_val v) fns v) vs)
                idsubst] ⟩
        -[ k ]-> ⟨ [], erase_names_result fns r ⟩.
Proof.
  itr - e.
  ind ~ ind_exp - e; itr - fns env vars vs k r Hlength.
  (*ENil-ELit*)
  2-3: bmp.
  (*EVar*)
  2: {
    smp.
    feq.
    admit.
  }
Admitted.


Theorem append_to_upn_vars3 :
  forall e fns env vars vs,
      base.length vars = base.length vs
  ->  (erase_exp
        (add_keys
          (map fst (append_vars_to_env vars vs env))
          fns)
        e)
      .[list_subst
        (map
          (fun v => erase_val (measure_val v) fns v)
          (map snd (append_vars_to_env vars vs env)))
        idsubst]
    = (erase_exp
        (add_vars
          vars
          (add_keys (map fst env) fns))
        e)
      .[upn
        (base.length vars)
        (list_subst
          (map
             (fun v =>
               erase_val 
               (measure_val v) fns v)
             (map snd env)) idsubst)]
      .[list_subst
        (map
          (fun v => erase_val (measure_val v) fns v) vs)
          idsubst].
Proof.
  itr - e.
  ind ~ ind_exp - e; itr - fns env vars vs Hlength.
  (*ENil-ELit*)
  2-3: bmp.
  (*EVar*)
  2: {
    smp.
    ind - env.
    * smp.
      Print append_vars_to_env.
      Print insert_value.
      admit.
      ufl - append_vars_to_env.
  }

(*New Idea*)
(*No NameSub*)
(*
  let xs e1 in e2.
  (erase_exp e2).[erase_val]
*)



(*fns env vars vs e2 kv2 res*)



Search "tmp".



























(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: TEST /////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.
Open Scope string_scope.

(* SECTIONS
* Erase_Names_Test
*)



Section Erase_Names_Test.


(* #Simples *)

Compute erase_names
  (fun _ => 0)
  []
  (ECons ENil (ELit (Integer 1))).
(* ° Syntax.ECons (˝ Syntax.VNil) (˝ Syntax.VLit 1%Z) *)

Compute erase_names
  (fun _ => 0)
  [(inl "X", (VLit (Integer 2)))]
  (ECons ENil (EVar "X")).
(* ° Syntax.ECons (˝ Syntax.VNil) (˝ Syntax.VLit 2%Z) *)

Compute erase_names
  (fun _ => 0)
  [(inl "X", (VLit (Integer 2)))]
  (EFun ["X"] (EVar "X")).
(* ° Syntax.EFun 1 (˝ VVar 0) *)

Compute erase_names
  (fun _ => 0)
  [(inl "X", (VLit (Integer 2)))]
  (ECons (EVar "X") (EFun ["X"] (EVar "X"))).
(* ° Syntax.ECons (˝ Syntax.VLit 2%Z) (° Syntax.EFun 1 (˝ VVar 0)) *)






(* #From Automated Test *)

Compute erase_names
  (fun _ => 0)
  []
  (ELetRec [(("x", 1), (["X"], EApp (EFunId ("x", 1)) [EVar "X"])) ]
           (EApp (EFunId ("x", 1)) [ETuple []])).
(*
° Syntax.ELetRec [(1, ° Syntax.EApp (˝ VFunId (1, 1)) [˝ VVar 0])]
           (° Syntax.EApp (˝ VFunId (0, 1)) [° Syntax.ETuple []])
*)






(* #From Automated Test Combined *)


(*
fun1/0 = fun() -> fun3()
fun2/0 = fun() -> 42
fun3/0 = fun() -> fun2()

fun1/0()
*)
Lemma erase_names_test_X1 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                  (("fun2",0), ([], ELit (Integer 42))); 
                  (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                (EApp (EFunId ("fun1",0)) []))))
    (erase_names_result
      (fun _ => 0)
      ((inl [VLit (Integer 42)]))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 15 do_framestack_step.
Qed.



(*
f/1 = fun(X) ->
  case X of
  <0> when true -> 5
  <1> when true -> f/1(0)
  <A> when true -> f/1(1)

X = fun(F) -> F(2)
  where "f/1 = fun(X) -> 0"

X(f/1)

CALCULATE:
- X(f/1)
- fun(f/1) -> f/1(2)
- fun(2) ->
  case 2 of
    <0> when true -> 5
    <1> when true -> f/1(0)
    <A> when true -> f/1(1)
- fun(1) ->
  case 1 of
    <0> when true -> 5
    <1> when true -> f/1(0)
    <A> when true -> f/1(1)
- fun(0) ->
  case 0 of
    <0> when true -> 5
    <1> when true -> f/1(0)
    <A> when true -> f/1(1)
- 5

*)
Lemma erase_names_test_X2 :
  step_any
    []
    (erase_names
      (fun _ => 0)
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
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 50 do_framestack_step.
    (* Fixed by switchin ext - vars*)
    (* do 30 do_framestack_step. *)
Qed.



(*

*)
Lemma erase_names_test_X3 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inr ("fun2", 0), 
       VClos [] [(0, ("fun2", 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)) None)]
      (ELetRec [(("fun2", 0), ([], ELit (Integer 40)))] 
         (EApp (EFunId ("fun2", 0)) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 40)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 7 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X4 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inr ("fun2", 0), 
         VClos [] [(0, ("fun2", 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)) None)]
      (ELetRec [(("fun2", 1), (["X"], (ELit (Integer 40))))] 
         (EApp (EFunId ("fun2", 0)) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 42)])).
Proof.
(*
⟨ [], ° Syntax.ELetRec [(0, ˝ Syntax.VLit 40%Z)] (° Syntax.EApp (˝ VFunId (0, 0)) []) ⟩ -->*
[Syntax.VLit 40%Z]
*)
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 7 do_framestack_step.
Qed.



(*
Compute erase_names
  (fun _ => 0)
  [(inl "X", VLit (Integer 42))]
  (ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] (EMap [])])
     (EMap [])).
(*
° Syntax.ELetRec [(0, ˝ Syntax.VLit 40%Z)] (° Syntax.EApp (˝ VFunId (0, 0)) [])
*)
Compute erase_names_result
  (fun _ => 0)
  (inl [VEmptyMap]).
(*
[Syntax.VMap []]
*)
*)
Lemma erase_names_test_X5 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 42))]
      (ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] (EMap [])])
         (EMap [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyMap])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X6 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 42))]
      (ELet ["Y"] (EValues [EFun [] (EVar "X")])
        (EApp (EVar "Y") [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 42)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 12 do_framestack_step.
Qed.



(*
*)
Lemma erase_names_test_X7 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 1)) 
            (ELet ["X"] (ELit (Integer 2)) 
               (EVar "X"))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 2)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 8 do_framestack_step.
Qed.



(*
*)
Lemma erase_names_test_X8 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ETuple []) (EMap [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyMap])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 6 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X9 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VEmptyMap)]
      (ELet ["X"] (ETuple []) (EMap [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyMap])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 6 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X10 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VEmptyMap)]
      (ELet ["X"; "X"; "Y"] (EValues [ETuple []; ENil; EVar "X"])
        (EVar "Y")))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyMap])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 14 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X11 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 5)) (EVar "X")))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 5 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X12 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Atom "foo")); 
        (inl "Y", VEmptyTuple)]
      (ETuple [ELit (Integer 5); EVar "X"; EVar "Y"]))
    (erase_names_result
      (fun _ => 0)
      (inl [VTuple [VLit (Integer 5); VLit (Atom "foo"); VEmptyTuple]])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 9 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X13 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inr ("Plus", 2), 
       VClos [] [(0, ("Plus", 2),
                     (["X" ; "Y"], ELit (Integer 3)))] 
                0 ["X" ; "Y"] 
                (ELit (Integer 3)) None)]
      (EApp (EFunId ("Plus", 2)) [ELit (Integer 2); ELit (Integer 3)]))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 3)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X14 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "Minus",
          VClos [] [] 0 ["X"; "Y"] (ELit (Integer 42)) None) ; 
        (inl "X", VEmptyMap)]
      (EApp (EVar "Minus") [EVar "X"; EVar "X"]))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 42)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X15 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 5))]
      (ECons (EVar "X") (ENil)))
    (erase_names_result
      (fun _ => 0)
      (inl [VCons (VLit (Integer 5)) (VNil)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 6 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X16 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 5))]
      (ECons (EVar "X") 
         (ECons (EVar "X") 
                (ENil))))
    (erase_names_result
      (fun _ => 0)
      (inl [VCons (VLit (Integer 5))
                 (VCons (VLit (Integer 5)) 
                        (VNil))])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X17 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (EFun [] (ETuple [])) 
           (ELet ["X"] (ELit (Integer 5)) 
             (EVar "X"))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 8 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X18 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 42))]
      (EMap [(ELit (Integer 5), EVar "X")]))
    (erase_names_result
      (fun _ => 0)
      (inl [VMap [(VLit (Integer 5), VLit (Integer 42))]])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 6 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X19 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 42))]
      (EMap [(ELit (Integer 54), EVar "X"); (EVar "X", EVar "X")] ))
    (erase_names_result
      (fun _ => 0)
      (inl [VMap [(VLit (Integer 42), VLit (Integer 42)); 
                 (VLit (Integer 54), VLit (Integer 42))]])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X20 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 5))]
      (EMap [(ELit (Integer 5), EVar "X"); 
         (EVar "X", ECall (ELit (Atom "erlang")) (ELit (Atom "+")) 
                              [ELit (Integer 1); (EVar "X")])]))
    (erase_names_result
      (fun _ => 0)
      (inl [VMap [(VLit (Integer 5), VLit (Integer 6))]])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 19 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X21 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"; "Y"; "Z"] 
            (EValues [EFun [] (ELit (Integer 1)); 
                      EFun [] (ELit (Integer 2)); 
                      EFun [] (ELit (Integer 3))])
         (EMap [(EVar "Z", ELit (Integer 10)); 
                (EVar "X", ELit (Integer 11));
                (EVar "Y", ELit (Integer 12)); 
                (EVar "X", ELit (Integer 13))])))
    (erase_names_result
      (fun _ => 0)
      (inl [VMap [(VClos [] [] 0 [] (ELit (Integer 1)) None, VLit (Integer 13));
                  (VClos [] [] 1 [] (ELit (Integer 2)) None, VLit (Integer 12));
                  (VClos [] [] 2 [] (ELit (Integer 3)) None, VLit (Integer 10))]])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
    do 16 do_framestack_step.
    do 1 do_framestack_step.
    (* make_val_map different ?*)
    (* maybe the id?*)
Admitted.



(*

*)
Lemma erase_names_test_X22 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 42))
       (ELet ["Y"] (EFun ["X"] (EVar "X")) 
         (ELet ["X"] (ELit (Integer 5))
           (EApp (EVar "Y") [ELit (Integer 7)])))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 7)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 17 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X23 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 42)) 
       (ELet ["Y"] (EFun [] (EVar "X"))
         (ELet ["X"] (ELit (Integer 5))
           (EApp (EVar "Y") [])))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 42)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 15 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X24 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 5))]
      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X" ; ELit (Integer 2)]))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 7)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 11 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X25 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["Z"] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 2) ; ELit (Integer 2)] ) 
       (ELet ["Y"] (EFun [] (EVar "Z"))
          (ELet ["X"] (EFun [] (EApp (EVar "Y") [])) 
            (EApp (EVar "X") [])))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 4)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 28 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X26 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VEmptyTuple)]
      (ECase (EVar "X")
         [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6)); 
          ([PVar "Z"], ELit (Atom "true"), EVar "Z") ]))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyTuple])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 10 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X27 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VEmptyTuple)]
      (ECase (EVar "X") 
         [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6));
          ([PVar "Z"], ELit (Atom "false"), EVar "Z");
          ([PVar "Z"], ELit (Atom "true"), EMap [])]))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyMap])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 12 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X28 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VClos [(inl "Y", VLit (Atom "true"))] [] 0 [] (EVar "Y") None); (inl "Y", VLit (Atom "true"))]
      (ECase (EValues [EVar "X"; EVar "Y"])
         [([PLit (Integer 5); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 6)); 
          ([PVar "Z"; PLit (Atom "true")], ELit (Atom "true"), EApp (EVar "Z") [])]))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Atom "true")])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 18 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X29 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inr ("fun4", 0), VClos [] [(0, ("fun4", 0), ([], EMap []))] 0 [] (EMap []) None) ; 
        (inl "X", VLit (Integer 42))]
      (ELetRec [(("fun2", 0), ([], EVar "X")); 
            (("fun4", 1), (["Z"], EVar "Z"))] 
        (EApp (EFunId ("fun4", 0)) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VEmptyMap])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 7 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X30 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 5))]
      (EApp (EFun ["Y"] (EVar "Y")) [EVar "X"]))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 8 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X31 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (EFun [] (ELit (Integer 5))) 
       (ELet ["X"] (EFun [] (ELit (Integer 6))) 
         (EApp (EVar "X") []))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 6)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 12 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X32 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 5)) (EVar "X")))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 5 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X33 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 4)) 
          (ELet ["X"] (EFun [] (EVar "X")) 
             (ELet ["X"] (EFun [] (EApp (EVar "X") []))
                (EApp (EVar "X") [])))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 4)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 19 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X34 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (EFun [] (EFun [] (ELit (Integer 5))))
      (EApp (EApp (EVar "X") []) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 13 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X35 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELetRec [(("fun1", 0), ([], (EFun [] (ELit (Integer 5)))))] 
      (EApp (EApp (EFunId ("fun1", 0)) []) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 5)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 11 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X36 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 7))]
      (ELet ["X"] (EFun [] (EFun [] (EVar "X")))
     (EApp (EApp (EVar "X") []) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 7)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 13 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X37 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X", VLit (Integer 7))]
      (ELetRec [(("fun1", 0), ([], EFun [] (EVar "X")))] 
      (EApp (EApp (EFunId ("fun1", 0)) []) [])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 7)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 11 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X38 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["F"] 
     (EFun ["X"] 
        (ELet ["Y"] (ECall (ELit (Atom "erlang" ))  (ELit (Atom "+" )) [EVar "X"; ELit (Integer 3)] ) 
              (EFun ["Z"] 
                    (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))
                          [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X"; EVar "Y"]
                     ; EVar "Z"]))))
  (EApp (EApp (EVar "F") [ELit (Integer 1)]) [ELit (Integer 1)])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 6)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 47 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X39 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELetRec [(("f", 1), (["X"], 
        ECase (EVar "X") [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 0)); 
                               ([PVar "Y"], ELit (Atom "true"), 
                               ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [
                                     EVar "Y"; 
                                     EApp (EFunId ("f", 1)) [ ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "Y"; ELit (Integer (Z.pred 0))] ]
                              ])]
      ))] (EApp (EFunId ("f", 1)) [ELit (Integer 2)])))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 3)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 74 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X40 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"] (ELit (Integer 42)) 
       (ELetRec [(("f", 0), ([], EVar "X"))]
         (ELet ["X"] (ELit (Integer 5))
           (EApp (EFunId ("f", 0)) [])))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 42)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 13 do_framestack_step.
Qed.



(*

*)
Lemma erase_names_test_X41 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ESeq (ELet ["X"] (ELit (Integer 42)) (EVar "X"))
                (ELet ["Y"] (ELit (Integer 20)) (EVar "Y"))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Integer 20)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 11 do_framestack_step.
Qed.



(*EXCEPTION*)



Lemma erase_names_test_X42 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 12 do_framestack_step.
Qed.



Lemma erase_names_test_X43 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])   (ELit (Atom "error"%string))) )
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 16 do_framestack_step.
Qed.



Lemma erase_names_test_X44 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECons (ELit (Atom "error"%string)) (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ENil))))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 18 do_framestack_step.
Qed.



Lemma erase_names_test_X45 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ETuple [ELit (Atom "error"%string) ; ELit (Atom "error"%string); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 19 do_framestack_step.
Qed.



Lemma erase_names_test_X46 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ETry (ETuple []) ["X"%string]
               (ELit (Atom "ok"%string)) 
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Atom "ok")])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 6 do_framestack_step.
Qed.



Lemma erase_names_test_X47 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string))))
    (erase_names_result
      (fun _ => 0)
      (inl [VLit (Atom "error"%string)])).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 15 do_framestack_step.
Qed.



Lemma erase_names_test_X48 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 25 do_framestack_step.
Qed.



Lemma erase_names_test_X49 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ETry (ETuple []) ["X"%string]
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string))))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 16 do_framestack_step.
Qed.



Lemma erase_names_test_X50 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECase (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                 [([PVar "X"%string], ELit (Atom "true"), ELit (Integer 1))]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 14 do_framestack_step.
Qed.



Lemma erase_names_test_X51 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "Y"%string, VLit (Integer 2))]
      (ECase (EVar "Y"%string)
          [([PLit (Integer 1)], ELit (Atom "true"), ELit (Integer 1)); 
           ([PVar "Z"%string], ELit (Atom "false"), ELit (Integer 2))]))
    (erase_names_result
      (fun _ => 0)
      (inr (if_clause))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 8 do_framestack_step.
Qed.



Lemma erase_names_test_X52 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string []))
    (erase_names_result
      (fun _ => 0)
      (inr (undef (VLit (Atom "+"))))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 7 do_framestack_step.
Qed.



Lemma erase_names_test_X53 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ETuple []]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 12 do_framestack_step.
Qed.



Lemma erase_names_test_X54 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 21 do_framestack_step.
Qed.



Lemma erase_names_test_X55 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"%string; "Y"%string] 
               (EValues [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) (ETuple [])))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 19 do_framestack_step.
Qed.



Lemma erase_names_test_X56 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 20 do_framestack_step.
Qed.



Lemma erase_names_test_X57 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (EApp (ELit (Integer 4)) [ELit (Integer 5); ELit (Integer 5)]))
    (erase_names_result
      (fun _ => 0)
      (inr (badfun (VLit (Integer 4))))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 9 do_framestack_step.
Qed.



Lemma erase_names_test_X58 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (EApp (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) [ELit (Integer 5); ELit (Integer 5)]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 14 do_framestack_step.
Qed.



Lemma erase_names_test_X59 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)) None)]
      (EApp (EVar "X"%string) [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 17 do_framestack_step.
Qed.



Lemma erase_names_test_X60 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)) None)]
      (EApp (EVar "X"%string) [ELit (Integer 2)]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)) None)))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 7 do_framestack_step.
Qed.



Lemma erase_names_test_X61 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      [(inl "X"%string, VClos [] [] 0 [] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) None)]
      (EApp (EVar "X"%string) []))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 16 do_framestack_step.
Qed.



Lemma erase_names_test_X62 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ELetRec [(("fun1"%string, 0), ([], ELit (Atom "error"%string)))] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 13 do_framestack_step.
Qed.



Lemma erase_names_test_X63 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (EMap [(ELit (Atom "error"%string),  ELit (Atom "error"%string)); 
                (ELit (Atom "error"%string), ELit (Atom "error"%string));
                (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []], ELit (Atom "error"%string));
                (ELit (Atom "error"%string), ELit (Atom "error"%string))]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 22 do_framestack_step.
Qed.



Lemma erase_names_test_X64 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                (ELit (Atom "error"%string), ELit (Atom "error"%string));
                (ELit (Atom "error"%string), ELit (Atom "error"%string))]))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 20 do_framestack_step.
Qed.



Lemma erase_names_test_X65 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ESeq (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                (ELit (Integer 42))))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 14 do_framestack_step.
Qed.



Lemma erase_names_test_X66 :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      (ESeq (ELit (Integer 42))
                (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 15 do_framestack_step.
Qed.



Lemma erase_names_test_X67 :
  step_any
    []
    (erase_names
      (fun _ => 0)
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
    (erase_names_result
      (fun _ => 0)
      (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 114 do_framestack_step.
Qed.



(*
Lemma erase_names_test_X :
  step_any
    []
    (erase_names
      (fun _ => 0)
      []
      ())
    (erase_names_result
      (fun _ => 0)
      ()).
Proof.
  cbn.
  eei; spl.
  * cns; scope_solver.
  * do 1 do_framestack_step.
Qed.
*)



End Erase_Names_Test.