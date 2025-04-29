From CoreErlang.Eqvivalence Require Export E4Basics.
From CoreErlang.Eqvivalence.BsFs Require Export B1EraseNames.

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
  give_name n x.



(* give_name - give_name_fid *)
Definition give_fid
    (n : nat)
    (f : FunId)
    : FunctionIdentifier
    :=
  match f with
  | (i, a) => (give_name n i, a)
  end.



(* nat_to_name - nat_to_var *)
Fixpoint give_vars
    (n xs : nat)
    : list string
    :=
  match xs with
  | 0 => []
  | S xs' => nat_to_name n :: give_vars (S n) xs'
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




Definition Giver : Type := list string.

Definition apply_giver (i : nat) (σ : Giver) : string :=
  nth i σ (give_name (0) i).





Fixpoint give_exp
    (σ : Giver)
    (e : Exp)
    : Expression
    :=
  match e with
  | VVal v => give_vval σ v
  | EExp nv => give_eexp σ nv
  end



with give_vval
    (σ : Giver)
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
      (give_vval σ v₁)
      (give_vval σ v₂)

  | Syntax.VTuple vs =>
    ETuple
      (map (give_vval σ) vs)

  | Syntax.VMap vvs =>
    EMap
      (map (fun '(x, y) => (give_vval σ x, give_vval σ y)) vvs)

  | Syntax.VVar x =>
    EVar
      (apply_giver x σ)

  | Syntax.VFunId (f, n) =>
    EFunId
      ((apply_giver f σ), n)

  | Syntax.VClos os id xs e =>
    EFun
      (give_vars (length σ) xs)
      (give_exp (app (give_vars (length σ) xs) σ) e)

  | Syntax.VPid _ => ENil

  end



with give_eexp
    (σ : Giver)
    (nv : NonVal)
    : Expression
    :=
  match nv with

  | Syntax.ECons e₁ e₂ =>
    ECons
      (give_exp σ e₁)
      (give_exp σ e₂)

  | Syntax.ETuple es =>
    ETuple
      (map (give_exp σ) es)

  | Syntax.EMap ees =>
    EMap
      (map (fun '(x, y) => (give_exp σ x, give_exp σ y)) ees)

  | Syntax.ESeq e₁ e₂ =>
    ESeq
      (give_exp σ e₁)
      (give_exp σ e₂)

  | Syntax.EValues es =>
    EValues
      (map (give_exp σ) es)

  | Syntax.EPrimOp s es =>
    EPrimOp
      s
      (map (give_exp σ) es)

  | Syntax.EApp ᶠe es =>
    EApp
      (give_exp σ ᶠe)
      (map (give_exp σ) es)

  | Syntax.ECall ᵐe ᶠe es =>
    ECall
      (give_exp σ ᵐe)
      (give_exp σ ᶠe)
      (map (give_exp σ) es)

  | Syntax.ECase ᵖe us =>
    ENil

  | Syntax.EFun xs ᵇe =>
    EFun
      (give_vars (length σ) xs)
      (give_exp (app (give_vars (length σ) xs) σ) ᵇe)

  | Syntax.ELet xs e₁ e₂ =>
    ELet
      (give_vars (length σ) xs)
      (give_exp σ e₁)
      (give_exp (app (give_vars (length σ) xs) σ) e₂)
(* TODO*)
  | Syntax.ETry e₁ xs₁ e₂ xs₂ e₃ =>
    ENil

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
  give_exp [] e.



End GiveNamesMain.












Section FrameStack.

Import SubstSemantics.



Definition frame_to_exp
    (F : Frame)
    (e : Exp)
    : Exp
    :=
  match F with
  | FCons1 e1 => °ECons e1 e
  | FCons2 v2 => °ECons e (˝v2)
  | FSeq e2 => °ESeq e e2
  | FLet xs e2 => °ELet xs e e2
  | FTry xs1 e2 xs2 e3 => °ETry e xs1 e2 xs2 e3
  | FCase1 us => °ECase e us
  (* | FCase2 vs eb us => °ECase (EValues (map VVal vs)) us *)
  | FApp1 es => °EApp e es
  | FCallMod ef es => °ECall e ef es
  | FCallFun vm es => °ECall (˝vm) e es
  | FParams ident vs es =>
    match ident with
    | IValues => °EValues (map VVal vs ++ es)
    | ITuple => °ETuple (map VVal vs ++ es)
    | IMap => °EMap (deflatten_list (map VVal vs ++ es))
    | IPrimOp s => °EPrimOp s (map VVal vs ++ es)
    | IApp vf  => °EApp (˝vf) (map VVal vs ++ es)
    | ICall vm vf  => °ECall (˝vm) (˝vf) (map VVal vs ++ es)
    end
  | _ => ˝VNil
  end.



Fixpoint frames_to_exp
    (Fs : FrameStack)
    (e : Exp)
    : Exp
    :=
  match Fs with
  | [] => e
  | F :: Fs' => frames_to_exp Fs' (frame_to_exp F e)
  end.



Definition give_names_frames
    (Fs : FrameStack)
    (e : Exp)
    : Expression
    :=
  give_names (frames_to_exp Fs e).


End FrameStack.



(* Theorem eq_fsbs :
  forall Fs e r,
      ⟨ Fs, RExp e ⟩ -->*  r
  ->  exists id id' eff eff',
        eval_expr [] [] "" id (give_names_frames Fs e) eff
                  id' (give_redex r) eff'.
Proof.
  itr - Fs e r H.
  des - H as [k [Hscope H]].
  gen - r e Fs.
  ind - k as [| k IH];
        itr.
  * ivc - H.
    ivc - Hscope.
  * ivc - H.
    ren - Fs': fs'.
    des - e' as [e' | vs | q |].
    - spe - IH: Fs' e' r Hscope H4.
      clr - H4.
      des - IH as [id [id' [eff [eff' IH]]]].
      ivc - H1;
            sbn *;
            unfold give_names_frames;
            unfold give_names.
      4: { (*CONS*)
        exi - id id' eff eff'.
        exa - IH.
      }
      5: { (*SEQ*)
        exi - id id' eff eff'.
        exa - IH.
      }
      4: { (*LET*)
        exi - id id' eff eff'.
        exa - IH.
      }
      6: { (*Try*)
        exi - id id' eff eff'.
        exa - IH.
      }
      4: { (*Case*)
        exi - id id' eff eff'.
        exa - IH.
      }
      1: { (*Map*)
        exi - id id' eff eff'.
        admit.
        (*flatten-delflatten*)
      }
      2: { (*App*)
        exi - id id' eff eff'.
        exa - IH.
      }
      1: { (*Call*)
        exi - id id' eff eff'.
        exa - IH.
      }
      1: { (*LetRec*)
        admit.
        (*Unique theorem*)
      }
    - des - vs as [| v [| v' vs]].
      + ivs - H1.
      + spe - IH: Fs' (˝v) r Hscope.
        (*needs on more step (k)*)
        admit.
      + admit.
    - ivc - H1.
    - ivs - H1.
      (*needs on more step (k)*)
      + admit.
      + admit.
      + admit.
Admitted. *)





Section Test.

Definition full_fs_exp (e : Exp) : Exp :=
  erase_names [] (give_names e).


Import SubstSemantics.

Definition exp1 : Exp :=
  EFun 1 (ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0;˝VLit 1%Z]).

Definition exp2 : Exp :=
  ELet 2
    (EValues [˝VVar 0;˝VLit 1%Z])
    (EValues [˝VVar 0;˝VVar 1;˝VVar 2]).

Definition exp3 : Exp :=
  ELet 2
    (EValues [˝VVar 0;˝VLit 1%Z])
    (ELet 2
      (EValues [˝VVar 0;˝VVar 1;˝VVar 2;˝VLit 1%Z])
      (EValues [˝VVar 0;˝VVar 1;˝VVar 2;˝VVar 3;˝VVar 4])).

Definition exp4 : Exp :=
  EValues
  [°(EFun 1 (ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0;˝VLit 1%Z]));
  °(ELet 2
    (EValues [˝VVar 0;˝VLit 1%Z])
    (EValues [˝VVar 0;˝VVar 1;˝VVar 2]));
  °(ELet 2
    (EValues [˝VVar 0;˝VLit 1%Z])
    (ELet 2
      (EValues [˝VVar 0;˝VVar 1;˝VVar 2;˝VLit 1%Z])
      (EValues [˝VVar 0;˝VVar 1;˝VVar 2;˝VVar 3;˝VVar 4])))].

Import BigStep.
Compute give_names exp1.
Compute give_names exp2.
Compute give_names exp3.
Compute give_names exp4.

Lemma test1 :
  full_fs_exp exp1 = exp1.
Proof.
  unfold exp1.
  cbn.
  ato.
Qed.

Lemma test2 :
  full_fs_exp exp2 = exp2.
Proof.
  unfold exp2.
  cbn.
  ato.
Qed.

Lemma test3 :
  full_fs_exp exp3 = exp3.
Proof.
  unfold exp3.
  cbn.
  ato.
Qed.
(*problem at not scoped expression, circle transformation is working*)

Lemma test4 :
  full_fs_exp exp4 = exp4.
Proof.
  unfold exp4.
  cbn.
  ato.
Qed.


Theorem eq_fsbs :
  forall e r,
      ⟨ [], RExp e ⟩ -->*  r
  ->  exists id id' eff eff',
        eval_expr [] [] "" id (give_names e) eff
                  id' (give_redex r) eff'.
Proof.
  itr - e r H.
  des - H as [k [Hscope H]].
  gen - r e.
  ind - k as [| k IH];
        itr.
  * ivc - H.
    ivc - Hscope.
  * ivc - H.
    ren - Fs: fs'.
    des - e' as [e' | vs | q |].
Admitted.

Theorem eq_fsbs2 :
  forall Fs e r,
      ⟨ Fs, RExp e ⟩ -->*  r
  ->  exists id id' eff eff',
        eval_expr [] [] "" id (give_names_frames Fs e) eff
                  id' (give_redex r) eff'.
Proof.
  itr - Fs e r H.
  des - H as [k [Hscope H]].
  gen - r e Fs.
  ind - k as [| k IH];
        itr.
  * ivc - H.
    ivc - Hscope.
  * ivc - H.
    ren - Fs': fs'.
    des - e' as [e' | vs | q |].
    - spe - IH: Fs' e' r Hscope H4.
      clr - H4.
      des - IH as [id [id' [eff [eff' IH]]]].
      ivc - H1;
            sbn *;
            unfold give_names_frames;
            unfold give_names.
      4: { (*CONS*)
        exi - id id' eff eff'.
        exa - IH.
      }
      5: { (*SEQ*)
        exi - id id' eff eff'.
        exa - IH.
      }
      4: { (*LET*)
        exi - id id' eff eff'.
        exa - IH.
      }
      6: { (*Try*)
        exi - id id' eff eff'.
        exa - IH.
      }
      4: { (*Case*)
        exi - id id' eff eff'.
        exa - IH.
      }
      1: { (*Map*)
        exi - id id' eff eff'.
        admit.
        (*flatten-delflatten*)
      }
      2: { (*App*)
        exi - id id' eff eff'.
        exa - IH.
      }
      1: { (*Call*)
        exi - id id' eff eff'.
        exa - IH.
      }
      1: { (*LetRec*)
        admit.
        (*Unique theorem*)
      }
    - des - vs as [| v [| v' vs]].
      + ivs - H1.
      + spe - IH: Fs' (˝v) r Hscope.
        (*needs on more step (k)*)
        admit.
      + admit.
    - ivc - H1.
    - ivs - H1.
      (*needs on more step (k)*)
      + admit.
      + admit.
      + admit.
Admitted.

End Test.