From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.


Definition Key : Type := (Var + FunctionIdentifier).
Definition Bonds : Type := list Key.







  Definition bonds_add_vars
    (vars : list Var)
    (bonds : Bonds)
    : list (Var + FunctionIdentifier)
    :=
  bonds ++ (map inl vars).


  Definition bonds_add_fids
    (fids : list FunctionIdentifier)
    (bonds : Bonds)
    : list (Var + FunctionIdentifier)
    :=
  bonds ++ (map inr fids).

  Definition bonds_add_fids_from_ext1
    (ext : list (FunctionIdentifier * ((list Var) * Expression)))
    (bonds : Bonds)
    : list (Var + FunctionIdentifier)
    :=
  bonds ++ (map (inr ∘ fst) ext).

  Definition bonds_add_fids_from_ext2
    (ext : list (nat * FunctionIdentifier * ((list Var) * Expression)))
    (bonds : Bonds)
    : list (Var + FunctionIdentifier)
    :=
  bonds ++ (map (inr ∘ snd ∘ fst) ext).

  Definition bonds_add_both1
    (ext : list (FunctionIdentifier * ((list Var) * Expression)))
    (vars : list Var)
    (bonds : Bonds)
    : list (Var + FunctionIdentifier)
    :=
  bonds ++ (map (inr ∘ fst) ext) ++ (map inl vars).

  Definition bonds_add_both2
    (ext : list (nat * FunctionIdentifier * ((list Var) * Expression)))
    (vars : list Var)
    (bonds : Bonds)
    : list (Var + FunctionIdentifier)
    :=
  bonds ++ (map (inr ∘ snd ∘ fst) ext) ++ (map inl vars).




  Definition bonds_from_vars
    (vars : list Var)
    : list (Var + FunctionIdentifier)
    :=
  (map inl vars).


  Definition bonds_from_fids
    (fids : list FunctionIdentifier)
    : list (Var + FunctionIdentifier)
    :=
  (map inr fids).

  Definition bonds_from_fids_from_ext1
    (ext : list (FunctionIdentifier * ((list Var) * Expression)))
    : list (Var + FunctionIdentifier)
    :=
  (map (inr ∘ fst) ext).

  Definition bonds_from_fids_from_ext2
    (ext : list (nat * FunctionIdentifier * ((list Var) * Expression)))
    : list (Var + FunctionIdentifier)
    :=
  (map (inr ∘ snd ∘ fst) ext).

  Definition bonds_from_both1
    (ext : list (FunctionIdentifier * ((list Var) * Expression)))
    (vars : list Var)
    : list (Var + FunctionIdentifier)
    :=
  (map (inr ∘ fst) ext) ++ (map inl vars).

  Definition bonds_from_both2
    (ext : list (nat * FunctionIdentifier * ((list Var) * Expression)))
    (vars : list Var)
    : list (Var + FunctionIdentifier)
    :=
  (map (inr ∘ snd ∘ fst) ext) ++ (map inl vars).

  Definition bonds_from_both3
    (fid : FunctionIdentifier)
    (vars : list Var)
    : list (Var + FunctionIdentifier)
    :=
  (inr fid) :: (map inl vars).






  Definition in_bonds
    (key : (Var + FunctionIdentifier))
    (bonds : list (Var + FunctionIdentifier))
    : bool :=
  existsb (fun k => var_funid_eqb key k) bonds.



  Lemma bonds_add_vars_in :
    forall key bonds vars,
      in_bonds key (bonds_add_vars vars bonds)
    = in_bonds key bonds || in_bonds key (map inl vars).
  Proof.
    itr.
    ufl - bonds_add_vars.
    ufl - in_bonds.
    bwr - existsb_app.
  Qed.




(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: VALTOEXP /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - bval_to_bexp_ext
* Main
  - bval_to_bexp
*)






Section ValToExp_Help.



  Definition bval_to_bexp_ext
	  (subst_env : Environment -> Bonds -> Expression -> Expression)
	  (env : Environment)
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) =>
    	(fid,
      	(vl,
      	(subst_env env (bonds_from_both2 ext vl) e))))
	  ext.



End ValToExp_Help.






Section ValToExp_Main.



  Fixpoint bval_to_bexp
	  (subst_env : Environment -> Bonds -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
    	(bval_to_bexp subst_env hd)
    	(bval_to_bexp subst_env tl)

  | VTuple l => ETuple
  	  (map (bval_to_bexp subst_env) l)

  | VMap l => EMap
    	(map
      	(prod_map
        	(bval_to_bexp subst_env)
        	(bval_to_bexp subst_env))
      	l)

  | VClos env ext id vl e fid =>
    	match ext, fid with
    	| [], _ => EFun
        	vl
        	(subst_env env (bonds_from_vars vl) e)

    	(* This case will not happen, do to Semmantics *)
    	| _, None => EFun
        	vl
        	(subst_env env (bonds_from_vars vl) e)

    	| _, Some fid' => ELetRec
        	(bval_to_bexp_ext subst_env env ext)
        	(EFunId fid')
    	end
  end.



End ValToExp_Main.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SUBSTITUTE ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - subst_env
  - subst_env2
*)




Section Substitue.


Print get_value.

(*
  Fixpoint key_in_bonds
    (key : Var + FunctionIdentifier)
    (bonds : list (Var + FunctionIdentifier))
    : Prop
    :=
  match bonds with
  | [] => False
  | k :: bonds' => var_funid_eqb key k
      \/ key_in_bonds key bonds'
  end.

  Lemma key_in_bonds_unfold :
    forall key bonds,
      key_in_bonds key bonds
    = match bonds with
      | [] => False
      | k :: bonds' => var_funid_eqb key k
          \/ key_in_bonds key bonds'
      end.
  Proof.
    itr.
    des - bonds; ufl - key_in_bonds; trv.
  Qed.

  Lemma key_in_bonds_add :
    forall key bonds1 bonds2,
        key_in_bonds key (bonds1 ++ bonds2)
    <-> key_in_bonds key bonds1
    \/  key_in_bonds key bonds2.
  Proof.
    itr.
    spl; itr - Hin.
    * adm.
    * des - Hin.
      - ren - Hin: H.
        ind - bonds1.
        + ivr - Hin.
        + rwl - app_comm_cons.
          rwr + key_in_bonds_unfold in Hin.
          des - Hin.
          ** lft; asm.
          ** spc - IHbonds1: H.
             rgt; asm.
      - Print in_or_app.
  Admitted.
*)
(* 
Lemma bonds_add_vars_in :
  forall key bonds vars,
      In key (bonds_add_vars vars bonds)
  ->  In key bonds \/ In key (map inl vars).
Proof.
  itr - key bonds vars Hin.
  ufl - bonds_add_vars in Hin.
  app - in_app_or in Hin.
  asm.
Qed. *)



  Fixpoint subst_env
	  (fuel : nat)
	  (env : Environment)
	  (bonds : list (Var + FunctionIdentifier))
	  (e : Expression)
	  : Expression
	  :=
  match fuel with
  (* This Case will not happen,
    because it will start with a big enought number *)
  | O => e
  | S fuel' =>
      match e with
      | ENil => e
      | ELit l => e

      | EValues el => EValues
          (map (subst_env fuel' env bonds) el)

      (*bonds_add_vars*)
      | EFun vl e => EFun
          vl
          ((subst_env fuel' env (bonds_add_vars vl bonds)) e)

      | ECons hd tl => ECons
          (subst_env fuel' env bonds hd)
          (subst_env fuel' env bonds tl)

      | ETuple l => ETuple
          (map (subst_env fuel' env bonds) l)

      | ECall m f l => ECall
          (subst_env fuel' env bonds m)
          (subst_env fuel' env bonds f)
          (map (subst_env fuel' env bonds) l)

      | EPrimOp f l => EPrimOp
          f
          (map (subst_env fuel' env bonds) l)

      | EApp exp l => EApp
          (subst_env fuel' env  bonds exp)
          (map (subst_env fuel' env bonds) l)

      | ECase e l => ECase
          (subst_env fuel' env bonds e)
          (map
            (fun '(pl, g, b) =>
              (pl,
              (subst_env fuel' env bonds g),
              (subst_env fuel' env bonds b)))
            l)

      (*bonds_add_vars*)
      | ELet l e1 e2 => ELet
          l
          (subst_env fuel' env bonds e1)
          (subst_env fuel' env (bonds_add_vars l bonds) e2)

      | ESeq e1 e2 => ESeq
          (subst_env fuel' env bonds e1)
          (subst_env fuel' env bonds e2)

      | ELetRec l e => ELetRec
          (map
            (fun '(fid, (vl, b)) =>
              (fid,
              (vl,
              (subst_env fuel' env (bonds_add_both1 l vl bonds) b))))
            l)
          (subst_env fuel' env (bonds_add_fids_from_ext1 l bonds) e)

      | EMap l => EMap
          (map
            (prod_map
              (subst_env fuel' env bonds)
              (subst_env fuel' env bonds))
            l)

      | ETry e1 vl1 e2 vl2 e3 => ETry
          (subst_env fuel' env bonds e1)
          vl1
          (subst_env fuel' env (bonds_add_vars vl1 bonds) e2)
          vl2
          (subst_env fuel' env (bonds_add_vars vl2 bonds) e3)

      | EVar var =>
          if in_bonds (inl var) bonds
            then
              e
            else
              match (get_value env (inl var)) with
              | Some [v] => bval_to_bexp (subst_env fuel') v
              | Some vs => EValues
                  (map (bval_to_bexp (subst_env fuel')) vs)
              | _ => e
              end

      | EFunId funid =>
          if in_bonds (inr funid) bonds
            then
              e
            else
              match (get_value env (inr funid)) with
              | Some [v] => bval_to_bexp (subst_env fuel') v
              | Some vs => EValues
                  (map (bval_to_bexp (subst_env fuel')) vs)
              | _ => e
              end
      end
  end.


End Substitue.





















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: ERASENAMES ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - Simple
    + name_sub
    + sum_eqb
    + literal_to_lit
    + vars_of_pattern_list
  - Add
    + add_name
    + add_names
    + add_vars
    + add_fids
* Main
  - bpat_to_fpat
  - bexp_to_fexp
*)






Section EraseNames_Help.



  Section EraseNames_Help_Simple.

    Definition name_sub
      {T}
      {dec : T -> T -> bool}
      :=
    T -> nat.

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

    Definition literal_to_lit
      (l : Literal)
      : Lit
      :=
    match l with
     | Atom s => s
     | Integer x => x
    end.

    Definition vars_of_pattern_list
      (l : list Pattern)
      : list Var
      :=
    fold_right 
      (fun x acc => variable_occurances x ++ acc)
      nil
      l.

  End EraseNames_Help_Simple.



  Section EraseNames_Help_Add.

    Definition add_name
      {T dec}
      (v : T)
      (σ : @name_sub _ dec)
      :=
    fun x =>
      if dec x v
      then 0
      else S (σ x).

    Definition add_names
      {T}
      {dec : T -> T -> bool}
      (vl : list T)
      (σ : name_sub)
      : name_sub
      :=
    fold_right
      (@add_name _ dec)
      σ
      vl.

    Definition add_vars
      (vl : list string)
      (σ : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
      : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb))
      :=
    add_names (map inl vl) σ.

    Definition add_fids
      (vl : list FunctionIdentifier)
      (σ : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
      : @name_sub
        (string + FunctionIdentifier)
        (sum_eqb eqb (prod_eqb eqb Nat.eqb))
      :=
      add_names (map inr vl) σ.

  End EraseNames_Help_Add.



End EraseNames_Help.






Section EraseNames_Main.



  Fixpoint bpat_to_fpat
    (p : Pattern)
    : Pat
    :=
  match p with
  | PNil => Syntax.PNil
  | PVar v => Syntax.PVar

  | PLit l => Syntax.PLit
      (literal_to_lit l)

  | PCons hd tl => Syntax.PCons
      (bpat_to_fpat hd)
      (bpat_to_fpat tl)

  | PTuple l => Syntax.PTuple
      (map bpat_to_fpat l)

  | PMap l => Syntax.PMap
      (map (fun '(x, y) => (bpat_to_fpat x, bpat_to_fpat y)) l)
  end.


  (* History: ETry: at e3 it used vl1 instead of vl2 *)
  Fixpoint bexp_to_fexp
    (σᵥ : @name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
    (e : Expression)
    : Exp
    :=
  match e with
  | ENil => ˝Syntax.VNil

  | ELit l => ˝Syntax.VLit
      (literal_to_lit l)

  | EVar v => ˝Syntax.VVar
      (σᵥ (inl v))

  | EFunId f => ˝Syntax.VFunId
      ((σᵥ (inr f)), snd f)

  | EValues el => Syntax.EValues
      (map (bexp_to_fexp σᵥ) el)

  | EFun vl e => Syntax.EFun
      (length vl)
      (bexp_to_fexp (add_vars vl σᵥ) e)

  | ECons hd tl => Syntax.ECons
      (bexp_to_fexp σᵥ hd)
      (bexp_to_fexp σᵥ tl)

  | ETuple l => Syntax.ETuple
      (map (bexp_to_fexp σᵥ) l)

  | ECall m f l => Syntax.ECall
      (bexp_to_fexp σᵥ m)
      (bexp_to_fexp σᵥ f)
      (map (bexp_to_fexp σᵥ) l)

  | EPrimOp f l => Syntax.EPrimOp
      f
      (map (bexp_to_fexp σᵥ) l)

  | EApp exp l => Syntax.EApp
      (bexp_to_fexp σᵥ exp)
      (map (bexp_to_fexp σᵥ) l)

  | ECase e l => Syntax.ECase
      (bexp_to_fexp σᵥ e)
      (map 
        (fun '(pl, g, b) =>
          ((map bpat_to_fpat pl),
          bexp_to_fexp (add_vars (vars_of_pattern_list pl) σᵥ) g,
          bexp_to_fexp (add_vars (vars_of_pattern_list pl) σᵥ) b))
        l)

  | ELet l e1 e2 => Syntax.ELet
      (length l)
      (bexp_to_fexp σᵥ e1)
      (bexp_to_fexp (add_vars l σᵥ) e2)

  | ESeq e1 e2 => Syntax.ESeq
      (bexp_to_fexp σᵥ e1)
      (bexp_to_fexp σᵥ e2)

  | ELetRec l e => Syntax.ELetRec
      (map
        (fun '(fid, (vl, b)) =>
          (length vl,
          bexp_to_fexp
            (add_names (map (inr ∘ fst) l ++ map inl vl) σᵥ)
            b))
        l)
      (bexp_to_fexp (add_fids (map fst l) σᵥ) e)

  | EMap l => Syntax.EMap
      (map
        (fun '(x, y) =>
          (bexp_to_fexp σᵥ x,
          bexp_to_fexp σᵥ y))
      l)

  | ETry e1 vl1 e2 vl2 e3 => Syntax.ETry
      (bexp_to_fexp σᵥ e1)
      (length vl1) (bexp_to_fexp (add_vars vl1 σᵥ) e2)
      (length vl2) (bexp_to_fexp (add_vars vl2 σᵥ) e3)
  end.


  (* Update
  * id = 0 (no id in Fs)
  * Clos e: add_vars added OLD: (add_fids (map (snd ∘ fst) ext) σᵥ)
  * Clos env: env -> (rem_vars vl env) & (rem_fid fid env)
  *)
  Fixpoint bval_to_fval
    (σᵥ : @name_sub
      (string + FunctionIdentifier)
      (sum_eqb eqb (prod_eqb eqb Nat.eqb)))
    (v : Value)
    : Val
    :=
  match v with
  | VNil => Syntax.VNil

  | VLit l => Syntax.VLit
      (literal_to_lit l)

  | VClos env ext id vl e fid => Syntax.VClos
      (map
        (fun '(n, fid, (vl0, b)) =>
          (n,
          length vl0,
          bexp_to_fexp
            (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vl0) σᵥ)
            (subst_env
              (measure_env_exp env b)
              env
              (bonds_from_both2 ext vl0)
              b)))
        ext)
      0
      (length vl)
      (bexp_to_fexp
        (add_names (map (inr ∘ snd ∘ fst) ext ++ map inl vl) σᵥ)
        (subst_env (measure_env_exp env e) env (bonds_from_vars vl) e))

  | VCons vhd vtl => Syntax.VCons
      (bval_to_fval σᵥ vhd)
      (bval_to_fval σᵥ vtl)

  | VTuple vl => Syntax.VTuple
      (map (bval_to_fval σᵥ) vl)

  | VMap l => Syntax.VMap
      (map
        (fun '(x, y) =>
          (bval_to_fval σᵥ x,
          bval_to_fval σᵥ y))
        l)
  end.



End EraseNames_Main.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: CONVERT //////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - bexp_to_fexp_subst
  - bvs_to_fvs
  - bexcc_to_fexcc
  - bexc_to_fexc
  - bres_to_fres
*)






Section Convert.



  Definition bexp_to_fexp_subst
    f
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  bexp_to_fexp
    f
    (subst_env
      (measure_env_exp
        env
        e)
      env
      []
      e).



  Definition bvs_to_fvs
    f
    (vs : ValueSequence)
    : ValSeq
    :=
  map
    (bval_to_fval f)
    vs.



  Definition bec_to_fec
    (ec : ExceptionClass)
    : CoreErlang.Syntax.ExcClass
    :=
  match ec with
  | Error => CoreErlang.Syntax.Error
  | Throw => CoreErlang.Syntax.Throw
  | Exit => CoreErlang.Syntax.Exit
  end.


  (* History: excc part separated in a new bexcc_to_fexcc *)
  Definition bexc_to_fexc
    f
    (exc : Exception)
    : CoreErlang.Syntax.Exception
    :=
  match exc with
  | (ec, v1, v2) =>
      (bec_to_fec ec,
      bval_to_fval f v1,
      bval_to_fval f v2)
  end.



  Definition bres_to_fres
    f
    (res : (ValueSequence + Exception))
    : Redex
    :=
  match res with
  | inl vs =>
      match (bvs_to_fvs f vs) with
      | vs' => RValSeq vs'
      end
  | inr exc => 
      match (bexc_to_fexc f exc) with
      | exc' => RExc exc'
      end
  end.



End Convert.










(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MeasureLemmas ////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Environment
  - measure_env_rem_le
* Tactics
  - ass_le_trans
  - ass_le_trans2
* Value
  - mred_val_cons
  - mred_val_tuple
  - mred_val_map
  - mred_val_clos
  - mred_val
* Expression
  - mred_exp
* Separate
  - mred_exp_separate
  - mred_exp_only_exp
  - mred_exp_only_env
* Mapper
  - mred_val_list
  - mred_val_list_map
* Minimum
  - mred_val_min
  - mred_val_list_min
  - mred_val_list_map_min
  - measure_exp_reduction_min
* Specials
  - mred_vcons_v1
  - mred_vcons_v2
  - mred_vtuple_v
  - mred_vtuple_vl
  - mred_vmap_v1
  - mred_vmap_v2
  - mred_vmap_vl
* Split
  - mred_exp_list_split
*)






(* Section MeasureLemmas_Tactics *)



Ltac triv_nle_solver := 
  smp;
  try unfold measure_env_exp;
  try unfold measure_env;
  try unfold measure_list;
  try unfold measure_map;
  try rewrite map_app, list_sum_app;
  sli.



Tactic Notation "ass_nle"
  "as"  ident(Ile)
  ":"   constr(Cle)
  :=
  assert Cle as Ile by triv_nle_solver.

Tactic Notation "ass_nle"
        constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2;
    triv_nle_solver).

Tactic Notation "ass_nle"
        constr(Cle)
  "as"  ident(Ile)
  ":"   hyp(Hm1) hyp(Hm2) hyp(Hm3)
  :=
  assert Cle as Ile by
    (rewrite Hm1, Hm2, Hm3;
    triv_nle_solver).


Tactic Notation "ass_nle_trn"
        constr(Cle_n1_n3)
  "as"  ident(Ile_n1_n3)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3)
  :=
  assert Cle_n1_n3 as Ile_n1_n3 by
    (eapply Nat.le_trans;
      [exact Hle_n1_n2 | exact Hle_n2_n3]).

Tactic Notation "ass_nle_trn"
        constr(Cle_n1_n4)
  "as"  ident(Ile_n1_n4)
  ":"   hyp(Hle_n1_n2) hyp(Hle_n2_n3) hyp(Hle_n3_n4)
  :=
  assert Cle_n1_n4 as Ile_n1_n4 by
    (eapply Nat.le_trans;
      [eapply Nat.le_trans;
        [exact Hle_n1_n2 | exact Hle_n2_n3]
      | exact Hle_n3_n4]).



Tactic Notation "mred_val_solver"
  "-" ident(v) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n1) constr(n2)
  :=
  ass_nle as Hle1: (mv <= n1);
  ass_nle as Hle2: (mv <= n2);
  ase - theorem: v n1 n2 Hle1 Hle2.

Tactic Notation "mred_val_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(mv) constr(n2)
  :=
  ass_nle as Hle2: (mv <= n2);
  ase - theorem: v n1 n2 Hle1 Hle2.

Tactic Notation "mred_val_solver"
  "-" ident(v) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_nle as Hle2: (n2 <= n2);
  ase - theorem: v n1 n2 Hle1 Hle2.

Tactic Notation "mred_val_solver"
  "-" ident(v) ident(Hle)
  ":" constr(theorem) constr(mv) constr(n)
  :=
  ass_nle as Hle: (mv <= n);
  bse - theorem: v n Hle.

Tactic Notation "mred_exp_solver"
  "-" ident(env) ident(bonds) ident(e) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n1) constr(n2)
  :=
  ass_nle as Hle1: (me <= n1);
  ass_nle as Hle2: (me <= n2);
  ase - theorem: env bonds e n1 n2 Hle1 Hle2.

Tactic Notation "mred_exp_solver"
  "-" ident(env) ident(bonds) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(me) constr(n2)
  :=
  ass_nle as Hle2: (me <= n2);
  ase - theorem: env bonds e n1 n2 Hle1 Hle2.

Tactic Notation "mred_exp_solver"
  "-" ident(env) ident(bonds) ident(e) ident(n1) ident(Hle1) ident(Hle2)
  ":" constr(theorem) constr(n2)
  :=
  ass_nle as Hle2: (n2 <= n2);
  ase - theorem: env bonds e n1 n2 Hle1 Hle2.

Tactic Notation "mred_exp_solver"
  "-" ident(env) ident(bonds) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_nle as Hle: (me <= n);
  ase - theorem: env bonds e n Hle.

Tactic Notation "mred_exp_solver"
  ">" constr(env) ident(bonds) ident(e) ident(Hle)
  ":" constr(theorem) constr(me) constr(n)
  :=
  ass_nle as Hle: (me <= n);
  ase - theorem: env bonds e n Hle.

(* End MeasureLemmas_Tactics *)






Section MeasureLemmas_Environment.



  Lemma measure_env_rem_keys_le :
    forall env keys,
    measure_env (rem_keys keys env) <= measure_env env.
  Proof.
    (* #1 Induction on Environment: intro/induction + simpl *)
    itr.
    ind - env as [| [k v] env Hle_e1k_e1]: smp.
    (* #2 Pose Cons: remember/pose/subst *)
    rem - env' as Heq_env:
      (rem_keys keys ((k, v) :: env)).
    pse - rem_keys_cons_env as Hcons: keys k v env env' Heq_env.
    sbt.
    (* #3 Destruct Cons: destuct + rewrite *)
    des - Hcons; cwr - H in *.
    * (* #4.1 Assert Le: assert + triv_nle_solver *)
      ass - as Hle_e1_e2: triv_nle_solver >
        (measure_env env <= measure_env ((k, v) :: env)).
      (* #5.1 Apply Transitive: apply + exact *)
      epp - Nat.le_trans: exa - Hle_e1k_e1 | exa - Hle_e1_e2.
    * (* #4.2 Solve by Lia: unfold/simpl/lia *)
      ufl + measure_env in Hle_e1k_e1.
      sli.
  Qed.



  Lemma measure_env_rem_vars_le :
    forall env vars,
    measure_env (rem_vars vars env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_vars.
    by pose proof measure_env_rem_keys_le env (map inl vars).
  Qed.



  Lemma measure_env_rem_fids_le :
    forall env fids,
    measure_env (rem_fids fids env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_fids.
    by pose proof measure_env_rem_keys_le env (map inr (map fst fids)).
  Qed.



  Lemma measure_env_rem_both_le :
    forall env vars fids,
    measure_env (rem_both fids vars env) <= measure_env env.
  Proof.
    (* #1 Pose Previus Theorems: intro/unfold/pose *)
    itr.
    ufl - rem_both.
    pse - measure_env_rem_fids_le as Hle_fids: (rem_vars vars env) fids.
    pse - measure_env_rem_vars_le as Hle_vars: env vars.
    (* #2 Apply Transitive: apply/exact *)
    epp - Nat.le_trans: exa - Hle_fids | exa - Hle_vars.
  Qed.



  Lemma measure_env_rem_nfifes_le :
    forall env nfifes,
    measure_env (rem_nfifes nfifes env) <= measure_env env.
  Proof.
    (* #1 Prove by Previus Theorem: intro/unfold/pose *)
    itr.
    ufl - rem_nfifes.
    by pose proof measure_env_rem_keys_le env
          (map inr (map snd (map fst nfifes))).
  Qed.



End MeasureLemmas_Environment.






Section MeasureLemmas_Value.



  Theorem mred_val_cons :
      forall v1 v2 n1 n2,
          measure_val (VCons v1 v2) <= n1
      ->  measure_val (VCons v1 v2) <= n2
      ->  ( measure_val v1 <= n1
        ->  measure_val v1 <= n2
        ->  bval_to_bexp (subst_env n1) v1
          = bval_to_bexp (subst_env n2) v1)
      ->  ( measure_val v2 <= n1
        ->  measure_val v2 <= n2
        ->  bval_to_bexp (subst_env n1) v2
          = bval_to_bexp (subst_env n2) v2)
      ->  bval_to_bexp (subst_env n1) (VCons v1 v2)
        = bval_to_bexp (subst_env n2) (VCons v1 v2).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - v1 v2 n1 n2 Hle_v1v2_n1 Hle_v1v2_n2 Heq_v1 Heq_v2.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv1 mv2 mv1v2 as Hmv1 Hmv2 Hmv1v2:
      (measure_val v1)
      (measure_val v2)
      (measure_val (VCons v1 v2)).
    (* #3 Assert: assert *)
    ass_nle (mv1 <= mv1v2) as Hle_v1_v1v2: Hmv1 Hmv1v2.
    ass_nle (mv2 <= mv1v2) as Hle_v2_v1v2: Hmv2 Hmv1v2.
    ass_nle_trn (mv1 <= n1) as Hle_v1_n1: Hle_v1_v1v2 Hle_v1v2_n1.
    ass_nle_trn (mv1 <= n2) as Hle_v1_n2: Hle_v1_v1v2 Hle_v1v2_n2.
    ass_nle_trn (mv2 <= n1) as Hle_v2_n1: Hle_v2_v1v2 Hle_v1v2_n1.
    ass_nle_trn (mv2 <= n2) as Hle_v2_n2: Hle_v2_v1v2 Hle_v1v2_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv1v2 in *.
    clr + Heq_v1 Heq_v2 Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2.
  Qed.



  Theorem mred_val_tuple :
    forall vl n1 n2,
        measure_val (VTuple vl) <= n1
    ->  measure_val (VTuple vl) <= n2
    ->  Forall (fun v =>
            measure_val v <= n1
        ->  measure_val v <= n2
        ->  bval_to_bexp (subst_env n1) v
          = bval_to_bexp (subst_env n2) v)
          vl
    ->  bval_to_bexp (subst_env n1) (VTuple vl)
      = bval_to_bexp (subst_env n2) (VTuple vl).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2 HForall.
    ind - vl as [| v vl Heq_vl]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
    (* #3 Assert: assert *)
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_v Heq_vl HForall Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v: Hle_v_n1 Hle_v_n2.
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2 HForall.
    inj - Heq_vl as Heq_vl.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.



  Theorem mred_val_map :
    forall vl n1 n2,
        measure_val (VMap vl) <= n1
    ->  measure_val (VMap vl) <= n2
    ->  Forall (fun v =>
           (measure_val v.1 <= n1
        ->  measure_val v.1 <= n2
        ->  bval_to_bexp (subst_env n1) v.1
          = bval_to_bexp (subst_env n2) v.1)
        /\ (measure_val v.2 <= n1
        ->  measure_val v.2 <= n2
        ->  bval_to_bexp (subst_env n1) v.2
          = bval_to_bexp (subst_env n2) v.2))
          vl
    ->  bval_to_bexp (subst_env n1) (VMap vl)
      = bval_to_bexp (subst_env n2) (VMap vl).
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2 HForall.
    ind - vl as [| v vl Heq_vl]: bmp.
    ivc - HForall as Heq_v HForall: H1 H2.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    des - Heq_v as [Heq_v1 Heq_v2].
    smp - Heq_v1 Heq_v2.
    rem - mv1 mv2 mv mvl mvvl as Hmv1 Hmv2 Hmv Hmvl Hmvvl:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (measure_val (VMap vl))
      (measure_val (VMap ((v1, v2) :: vl))).
    (* #3 Assert: assert *)
    ass_nle (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_nle (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvl Hmvvl in *.
    clr + Heq_v1 Heq_v2 Heq_vl HForall
      Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_v1: Hle_v1_n1 Hle_v1_n2.
    spc - Heq_v2: Hle_v2_n1 Hle_v2_n2.
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2 HForall.
    inj - Heq_vl as Heq_vl.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vl.
  Qed.



  Theorem mred_val_clos :
    forall env ext id vars e fid n1 n2,
        measure_val (VClos env ext id vars e fid) <= n1
    ->  measure_val (VClos env ext id vars e fid) <= n2
    ->  Forall (fun x =>
            measure_val x.2 <= n1
        ->  measure_val x.2 <= n2
        ->  bval_to_bexp (subst_env n1) x.2
          = bval_to_bexp (subst_env n2) x.2)
          env
    ->  bval_to_bexp (subst_env n1) (VClos env ext id vars e fid)
      = bval_to_bexp (subst_env n2) (VClos env ext id vars e fid).
  Proof.
    itr - env ext id vars e fid n1 n2 Hle_env_n1 Hle_env_n2 HForall.
    (* Problem: HForall only talks about env, but not of e & ext *)
    admit.
  Admitted.



(** NOTES
* FULL NAME:
  - Measure Reduction at Value
* OLD NAME:
  - measure_reduction
  - measure_val_reduction
* FUNCTION:
  - When converting Value to Expression in Bigstep,
    the subst_env's fuel can be rewriten,
    if both the previus and the new fuel is bigger or equal,
    than the Value being converted
* USING:
  -
* USED AT:
  -
* History:
  - Relatively was easy to prove, except VClos
    (Might need a dual Proof with measure_exp_reduction)
  - !maybe measure_val and measure_exp needs to be dual defined because of Clos
*)
  Theorem mred_val :
    forall v n1 n2,
        measure_val v <= n1
    ->  measure_val v <= n2
    ->  bval_to_bexp (subst_env n1) v
      = bval_to_bexp (subst_env n2) v.
  Proof.
    (* #1 Value Induction: intro/induction + cbn *)
    itr - v n1 n2 Hn1 Hn2.
    ind + ind_val - v :- sbn.
    (* #2 Cons: pose *)
    1: bse - mred_val_cons:   v1 v2 n1 n2
                              Hn1 Hn2 IHv1 IHv2.
    (* #3 Tuple: pose *)
    2: bse - mred_val_tuple:  l n1 n2
                              Hn1 Hn2 H.
    (* #4 Map: pose *)
    2: bse - mred_val_map:    l n1 n2
                              Hn1 Hn2 H.
    (* #4 Closure: pose *)
    bse - mred_val_clos:      ref ext id params body funid n1 n2
                              Hn1 Hn2 H.
  Qed.



End MeasureLemmas_Value.






Section MeasureLemmas_Expression.



  (**
  * OLD NAMES:
    - measure_env_exp_reduction
  *)
  Theorem mred_exp :
    forall env bonds e n1 n2,
        measure_env_exp env e <= n1
    ->  measure_env_exp env e <= n2
    ->  subst_env n1 env bonds e
      = subst_env n2 env bonds e.
  Proof.
  Admitted.



End MeasureLemmas_Expression.






Section MeasureLemmas_Separate.



  Theorem mred_exp_separate :
    forall env bonds e ne1 ne2 nenv1 nenv2,
        measure_exp e <= ne1
    ->  measure_exp e <= ne2
    ->  measure_env env <= nenv1
    ->  measure_env env <= nenv2
    ->  subst_env (ne1 + nenv1) env bonds e
      = subst_env (ne2 + nenv2) env bonds e.
  Proof.
    (* #1 Pose Larger or Equal Mono: intro/pose *)
    itr - env bonds e ne1 ne2 nenv1 nenv2 Hle_e1 Hle_e2 Hle_env1 Hle_env2.
    psc - Nat.add_le_mono as Hle1:
      (measure_exp e) ne1
      (measure_env env) nenv1
      Hle_e1 Hle_env1.
    psc - Nat.add_le_mono as Hle2:
      (measure_exp e) ne2
      (measure_env env) nenv2
      Hle_e2 Hle_env2.
    (* #2 Prove by Previus Theorem: pose/unfold/specialize *)
    pse - mred_exp as Heq: env bonds e (ne1 + nenv1) (ne2 + nenv2).
    ufl - measure_env_exp in Heq.
    bpe - Heq: Hle1 Hle2.
  Qed.



  Theorem mred_exp_only_exp :
    forall env bonds e n1 n2,
        measure_exp e <= n1
    ->  measure_exp e <= n2
    ->  subst_env (n1 + measure_env env) env bonds e
      = subst_env (n2 + measure_env env) env bonds e.
  Proof.
    (* #1 Prove by Previus Theorem: intro/assert/pose *)
    itr - env bonds e n1 n2 Hle1 Hle2.
    ass > (measure_env env <= measure_env env) as Hle_env: lia.
    bse - mred_exp_separate:  env bonds e n1 n2 (measure_env env) (measure_env env)
                              Hle1 Hle2 Hle_env Hle_env.
  Qed.



  Theorem mred_exp_only_env :
    forall env bonds e n1 n2,
        measure_env env <= n1
    ->  measure_env env <= n2
    ->  subst_env (measure_exp e + n1) env bonds e
      = subst_env (measure_exp e + n2) env bonds e.
  Proof.
    (* #1 Prove by Previus Theorem: intro/assert/pose *)
    itr - env bonds e n1 n2 Hle1 Hle2.
    ass > (measure_exp e <= measure_exp e) as Hle_e: lia.
    bse - mred_exp_separate:  env bonds e (measure_exp e) (measure_exp e) n1 n2 
                              Hle_e Hle_e Hle1 Hle2.
  Qed.



End MeasureLemmas_Separate.






Section MeasureLemmas_Mappers.



(**
* OLD NAMES:
  - measure_val_reduction_list
*)
  Theorem mred_val_list :
    forall vl n1 n2,
        list_sum (map measure_val vl) <= n1
    ->  list_sum (map measure_val vl) <= n2
    ->  map (bval_to_bexp (subst_env n1)) vl
      = map (bval_to_bexp (subst_env n2)) vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - mv mvl mvvl as Hmv Hmvl Hmvvl:
      (measure_val v)
      (list_sum (map measure_val vl))
      (list_sum (map measure_val (v :: vl))).
    (* #3 Assert: assert *)
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv <= n1) as Hle_v_n1: Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv <= n2) as Hle_v_n2: Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v_n1 Hle_v_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - mred_val as Heq_v: v n1 n2 Hle_v_n1 Hle_v_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v Heq_vl.
  Qed.



(**
* OLD NAMES:
  - measure_val_reduction_map
*)
  Theorem mred_val_list_map :
    forall vl n1 n2,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= n1
    ->  list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= n2
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n1))
            (bval_to_bexp (subst_env n1)))
          vl
      = map
          (prod_map
            (bval_to_bexp (subst_env n2))
            (bval_to_bexp (subst_env n2)))
          vl.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - vl n1 n2 Hle_vvl_n1 Hle_vvl_n2.
    ind - vl as [| v vl Heq_vl]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - v as [v1 v2].
    rem - mv1 mv2 mv mvl mvvl as Hmv1 Hmv2 Hmv Hmvl Hmvvl:
      (measure_val v1)
      (measure_val v2)
      (measure_val v1 + measure_val v2)
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y) vl))
      (list_sum (map (fun '(x, y) => measure_val x + measure_val y)
        ((v1, v2) :: vl))).
    (* #3 Assert: assert *)
    ass_nle (mv1 <= mv) as Hle_v1_v: Hmv1 Hmv.
    ass_nle (mv2 <= mv) as Hle_v2_v: Hmv2 Hmv.
    ass_nle (mv <= mvvl) as Hle_v_vvl: Hmv Hmvvl.
    ass_nle (mvl <= mvvl) as Hle_vl_vvl: Hmvl Hmvvl.
    ass_nle_trn (mv1 <= n1) as Hle_v1_n1: Hle_v1_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv1 <= n2) as Hle_v1_n2: Hle_v1_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mv2 <= n1) as Hle_v2_n1: Hle_v2_v Hle_v_vvl Hle_vvl_n1.
    ass_nle_trn (mv2 <= n2) as Hle_v2_n2: Hle_v2_v Hle_v_vvl Hle_vvl_n2.
    ass_nle_trn (mvl <= n1) as Hle_vl_n1: Hle_vl_vvl Hle_vvl_n1.
    ass_nle_trn (mvl <= n2) as Hle_vl_n2: Hle_vl_vvl Hle_vvl_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmv1 Hmv2 Hmv Hmvl Hmvvl in *.
    clr + Heq_vl Hle_v1_n1 Hle_v1_n2 Hle_v2_n1 Hle_v2_n2 Hle_vl_n1 Hle_vl_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_vl: Hle_vl_n1 Hle_vl_n2.
    psc - mred_val as Heq_v1: v1 n1 n2 Hle_v1_n1 Hle_v1_n2.
    psc - mred_val as Heq_v2: v2 n1 n2 Hle_v2_n1 Hle_v2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_v1 Heq_v2 Heq_vl.
  Qed.



  Theorem mred_exp_list :
    forall env bonds el n1 n2,
        list_sum (map measure_exp el) + measure_env env <= n1
    ->  list_sum (map measure_exp el) + measure_env env <= n2
    ->  map (subst_env n1 env bonds) el
      = map (subst_env n2 env bonds) el.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env bonds el n1 n2 Hle_eel_n1 Hle_eel_n2.
    ind - el as [| e el Heq_el]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    rem - menv me mel meel as Hmenv Hme Hmel Hmeel:
      (measure_env env)
      (measure_exp e)
      (list_sum (map measure_exp el))
      (list_sum (map measure_exp (e :: el))).
    (* #3 Assert: assert *)
    ass_nle (me + menv <= meel + menv) as Hle_e_eel: Hme Hmeel Hmenv.
    ass_nle (mel + menv <= meel + menv) as Hle_el_eel: Hmel Hmeel Hmenv.
    ass_nle_trn (me + menv <= n1) as Hle_e_n1: Hle_e_eel Hle_eel_n1.
    ass_nle_trn (me + menv <= n2) as Hle_e_n2: Hle_e_eel Hle_eel_n2.
    ass_nle_trn (mel + menv <= n1) as Hle_el_n1: Hle_el_eel Hle_eel_n1.
    ass_nle_trn (mel + menv <= n2) as Hle_el_n2: Hle_el_eel Hle_eel_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme Hmel Hmeel in *.
    clr + Heq_el Hle_e_n1 Hle_e_n2 Hle_el_n1 Hle_el_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_el: Hle_el_n1 Hle_el_n2.
    psc - mred_exp as Heq_e: env bonds e n1 n2 Hle_e_n1 Hle_e_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e Heq_el.
  Qed.



  Theorem mred_exp_list_map :
    forall env bonds el n1 n2,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
           + measure_env env <= n1
    ->  list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
          + measure_env env <= n2
    ->  map
          (prod_map
            (subst_env n1 env bonds)
            (subst_env n1 env bonds))
          el
      = map
          (prod_map
            (subst_env n2 env bonds)
            (subst_env n2 env bonds))
          el.
  Proof.
    (* #1 Intro: intro/induction/inversion *)
    itr - env bonds el n1 n2 Hle_eel_n1 Hle_eel_n2.
    ind - el as [| e el Heq_el]: bmp.
    (* #2 Remember: destruct/simpl/remember *)
    des - e as [e1 e2].
    rem - menv me1 me2 me mel meel as Hmenv Hme1 Hme2 Hme Hmel Hmeel:
      (measure_env env)
      (measure_exp e1)
      (measure_exp e2)
      (measure_exp e1 + measure_exp e2)
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y) el))
      (list_sum (map (fun '(x, y) => measure_exp x + measure_exp y)
        ((e1, e2) :: el))).
    (* #3 Assert: assert *)
    ass_nle (me1 + menv <= me + menv) as Hle_e1_e: Hme1 Hme Hmenv.
    ass_nle (me2 + menv <= me + menv) as Hle_e2_e: Hme2 Hme Hmenv.
    ass_nle (me + menv <= meel + menv) as Hle_e_eel: Hme Hmeel Hmenv.
    ass_nle (mel + menv <= meel + menv) as Hle_el_eel: Hmel Hmeel Hmenv.
    ass_nle_trn (me1 + menv <= n1) as Hle_e1_n1: Hle_e1_e Hle_e_eel Hle_eel_n1.
    ass_nle_trn (me1 + menv <= n2) as Hle_e1_n2: Hle_e1_e Hle_e_eel Hle_eel_n2.
    ass_nle_trn (me2 + menv <= n1) as Hle_e2_n1: Hle_e2_e Hle_e_eel Hle_eel_n1.
    ass_nle_trn (me2 + menv <= n2) as Hle_e2_n2: Hle_e2_e Hle_e_eel Hle_eel_n2.
    ass_nle_trn (mel + menv <= n1) as Hle_el_n1: Hle_el_eel Hle_eel_n1.
    ass_nle_trn (mel + menv <= n2) as Hle_el_n2: Hle_el_eel Hle_eel_n2.
    (* #4 Clear: rewrite/clear *)
    cwr - Hmenv Hme1 Hme2 Hme Hmel Hmeel in *.
    clr + Heq_el Hle_e1_n1 Hle_e1_n2 Hle_e2_n1 Hle_e2_n2 Hle_el_n1 Hle_el_n2.
    (* #5 Specify: specialize/pose proof/injection *)
    spc - Heq_el: Hle_el_n1 Hle_el_n2.
    psc - mred_exp as Heq_e1: env bonds e1 n1 n2 Hle_e1_n1 Hle_e1_n2.
    psc - mred_exp as Heq_e2: env bonds e2 n1 n2 Hle_e2_n1 Hle_e2_n2.
    (* #6 Rewrite: simpl/rewrite *)
    smp.
    bwr - Heq_e1 Heq_e2 Heq_el.
  Qed.



End MeasureLemmas_Mappers.






Section MeasureLemmas_Min.



  Theorem mred_val_min :
    forall v n,
        measure_val v <= n
    ->  bval_to_bexp (subst_env n) v
    =   bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    itr - v n Hle1.
    mred_val_solver - v n Hle1 Hle2:
      mred_val
      (measure_val v)
      (measure_val v).
  Qed.



  Theorem mred_val_list_min :
    forall vl n,
        list_sum (map measure_val vl) <= n
    ->  map (bval_to_bexp (subst_env n)) vl
      = map (bval_to_bexp (subst_env (list_sum (map measure_val vl)))) vl.
  Proof.
    itr - vl n Hle1.
    mred_val_solver - vl n Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl)).
  Qed.



  Theorem mred_val_list_map_min :
    forall vl n,
        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)
          <= n
    ->  map
          (prod_map
            (bval_to_bexp (subst_env n))
            (bval_to_bexp (subst_env n)))
          vl
      = map
          (prod_map
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vl))))
            (bval_to_bexp
              (subst_env
                (list_sum
                  (map
                    (fun '(x, y) => (measure_val x) + (measure_val y))
                    vl)))))
          vl.
  Proof.
    itr - vl n Hle1.
    mred_val_solver - vl n Hle1 Hle2:
      mred_val_list_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl)).
  Qed.



  Theorem mred_exp_min :
    forall env bonds e n,
        measure_env_exp env e <= n
    ->  subst_env n env bonds e
    =   subst_env (measure_env_exp env e) env bonds e.
  Proof.
    itr -  env bonds e n Hle1.
    mred_exp_solver - env bonds e n Hle1 Hle2:
      mred_exp
      (measure_env_exp env e).
  Qed.



  Theorem mred_exp_only_exp_min :
    forall env bonds e n m,
        measure_exp e <= n
    ->  measure_env env <= m
    ->  subst_env (n + m) env bonds e
    =   subst_env (measure_exp e + m) env bonds e.
  Proof.
    itr -  env bonds e n m Hle_e Hle_env.
    app - mred_exp_separate; lia.
  Qed.



  Theorem mred_exp_only_env_min :
    forall env bonds e n m,
        measure_exp e <= n
    ->  measure_env env <= m
    ->  subst_env (n + m) env bonds e
    =   subst_env (n + measure_env env) env bonds e.
  Proof.
    itr -  env bonds e n m Hle_e Hle_env.
    app - mred_exp_separate; lia.
  Qed.



  Theorem mred_exp_list_min :
    forall env bonds el n,
        list_sum (map measure_exp el) + measure_env env <= n
    ->  map (subst_env n env bonds) el
      = map
        (subst_env (list_sum (map measure_exp el) + measure_env env) env bonds)
         el.
  Proof.
    itr -  env bonds el n Hle1.
    mred_exp_solver - env bonds el n Hle1 Hle2:
      mred_exp_list
      (list_sum (map measure_exp el) + measure_env env).
  Qed.



  Theorem mred_exp_list_map_min :
    forall env bonds el n,
        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
           + measure_env env <= n
    ->  map
          (prod_map
            (subst_env n env bonds)
            (subst_env n env bonds))
          el
      = map
          (prod_map
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
                + measure_env env)
              env
              bonds)
            (subst_env
              (list_sum
                (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
                + measure_env env)
              env
              bonds))
          el.
  Proof.
    itr -  env bonds el n Hle1.
    mred_exp_solver - env bonds el n Hle1 Hle2:
      mred_exp_list_map
      (list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) el)
        + measure_env env).
  Qed.



End MeasureLemmas_Min.





Section MeasureLemmas_Specials.



  Theorem mred_vclos :
    forall env bonds e id vars fid,
      subst_env (measure_val (VClos env [] id vars e fid)) env bonds e
    = subst_env (measure_env_exp env e) env bonds e.
  Proof.
    itr.
    rfl - measure_val.
    des > (measure_ext [] =? 0) as Heq :- smp - Heq; con |> clr - Heq.
    ass - as Hmeasure: ufl - measure_env_exp measure_env measure_env';
      rwr - Nat.add_comm >
      (measure_env' measure_val env + measure_exp e = measure_env_exp env e).
    rwl - Nat.add_assoc.
    cwr - Hmeasure.
    ass - as Hle: lia >
      (measure_env_exp env e
      <= 1 + measure_env_exp env e).
    bse - mred_exp_min: env bonds e
      (1 + measure_env_exp env e)
      Hle.
  Qed.



  Theorem mred_vclos_vars :
    forall env bonds e id vars fid,
      subst_env
        (measure_val (VClos env [] id vars e fid)) (rem_vars vars env) bonds e
    = subst_env
      (measure_env_exp (rem_vars vars env) e) (rem_vars vars env) bonds e.
  Proof.
    itr.
    rfl - measure_val measure_env_exp.
    des > (measure_ext [] =? 0) as Heq :- smp - Heq; con |> clr - Heq.
    ass - as Henv: ufl - measure_env >
      (measure_env' measure_val env = measure_env env).
    cwr - Henv.
    rwr - Nat.add_comm Nat.add_assoc.
    ass > (measure_exp e <= measure_exp e + 1) as Hle_e: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) bonds e
      (measure_exp e + 1) (measure_env env)
      Hle_e Hle_env.
    rwr - Heq_env.
    ass - as Hle: lia >
      (measure_exp e + measure_env (rem_vars vars env)
      <= measure_exp e + 1 + measure_env (rem_vars vars env)).
    bse - mred_exp_min: (rem_vars vars env) bonds e
      (measure_exp e + 1 + measure_env (rem_vars vars env))
      Hle.
  Qed.



  Theorem mred_vcons_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_val_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VCons v1 v2)).
  Qed.



  Theorem mred_v1v2_v1 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_val_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2).
  Qed.



  Theorem mred_vcons_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val (VCons v1 v2))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_val_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VCons v1 v2)).
  Qed.



  Theorem mred_v1v2_v2 :
    forall v1 v2,
      bval_to_bexp (subst_env (measure_val v1 + measure_val v2)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_val_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2).
  Qed.



  Theorem mred_vtuple_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val (VTuple (v :: vl)))) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    itr.
    mred_val_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val (VTuple (v :: vl))).
  Qed.



  Theorem mred_vvl_v :
    forall v vl,
      bval_to_bexp (subst_env (measure_val v + measure_list measure_val vl)) v
    = bval_to_bexp (subst_env (measure_val v)) v.
  Proof.
    itr.
    mred_val_solver - v Hle:
      mred_val_min
      (measure_val v)
      (measure_val v + measure_list measure_val vl).
  Qed.



  Theorem mred_vtuple_vl :
    forall v vl,
      map (bval_to_bexp (subst_env (measure_val (VTuple (v :: vl))))) vl
    = map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl.
  Proof.
    itr.
    mred_val_solver - vl Hle1 Hle2:
      mred_val_list
      (list_sum (map measure_val vl))
      (measure_val (VTuple vl))
      (measure_val (VTuple (v :: vl))).
  Qed.



  Theorem mred_vvl_vl :
    forall v vl,
      map
        (bval_to_bexp
          (subst_env (measure_val v + measure_list measure_val vl))) vl
    = map (bval_to_bexp (subst_env (measure_list measure_val vl))) vl.
  Proof.
    itr.
    mred_val_solver - vl Hle:
      mred_val_list_min
      (measure_list measure_val vl)
      (measure_val v + measure_list measure_val vl).
  Qed.



  Theorem mred_vmap_v1 :
    forall v1 v2 vl,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_val_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_v1v2vl_v1 :
    forall v1 v2 vl,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vl)) v1
    = bval_to_bexp (subst_env (measure_val v1)) v1.
  Proof.
    itr.
    mred_val_solver - v1 Hle:
      mred_val_min
      (measure_val v1)
      (measure_val v1 + measure_val v2 + measure_map measure_val vl).
  Qed.



  Theorem mred_vmap_v2 :
    forall v1 v2 vl,
      bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_val_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_v1v2vl_v2 :
    forall v1 v2 vl,
      bval_to_bexp
        (subst_env
          (measure_val v1 + measure_val v2 + measure_map measure_val vl)) v2
    = bval_to_bexp (subst_env (measure_val v2)) v2.
  Proof.
    itr.
    mred_val_solver - v2 Hle:
      mred_val_min
      (measure_val v2)
      (measure_val v1 + measure_val v2 + measure_map measure_val vl).
  Qed.



  Theorem mred_vmap_vl :
    forall v1 v2 vl,
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl)))))
          (bval_to_bexp (subst_env (measure_val (VMap ((v1, v2) :: vl))))))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_val (VMap vl))))
          (bval_to_bexp (subst_env (measure_val (VMap vl)))))
        vl.
  Proof.
    itr.
    mred_val_solver - vl Hle1 Hle2:
      mred_val_list_map
      (list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vl))
      (measure_val (VMap vl))
      (measure_val (VMap ((v1, v2) :: vl))).
  Qed.



  Theorem mred_v1v2vl_vl :
    forall v1 v2 vl,
      map
        (prod_map
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vl)))
          (bval_to_bexp
            (subst_env
              (measure_val v1 + measure_val v2 + measure_map measure_val vl))))
        vl
    =
      map
        (prod_map
          (bval_to_bexp (subst_env (measure_map measure_val vl)))
          (bval_to_bexp (subst_env (measure_map measure_val vl))))
        vl.
  Proof.
    itr.
    mred_val_solver - vl Hle:
      mred_val_list_map_min
      (measure_map measure_val vl)
      (measure_val v1 + measure_val v2 + measure_map measure_val vl).
  Qed.



  Theorem mred_e_vars :
    forall vars env bonds e,
      subst_env (measure_exp e + measure_env env)
        (rem_vars vars env) bonds e
    = subst_env (measure_env_exp (rem_vars vars env) e)
        (rem_vars vars env) bonds e.
  Proof.
    itr.
    ass > (measure_exp e <= measure_exp e) as Hle_e: lia.
    pse - measure_env_rem_vars_le as Hle_env: env vars.
    psc - mred_exp_only_env_min as Heq_env: (rem_vars vars env) bonds e
      (measure_exp e) (measure_env env)
      Hle_e Hle_env.
    bwr - Heq_env.
  Qed.



  Theorem mred_e1e2_e1 :
    forall env bonds e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env bonds e1
    = subst_env (measure_env_exp env e1) env bonds e1.
  Proof.
    itr.
    mred_exp_solver - env bonds e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2_e2 :
    forall env bonds e1 e2,
      subst_env (measure_exp e1 + measure_exp e2 + measure_env env) env bonds e2
    = subst_env (measure_env_exp env e2) env bonds e2.
  Proof.
    itr.
    mred_exp_solver - env bonds e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_exp e1 + measure_exp e2 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e1 :
    forall env bonds e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env bonds e1
    = subst_env (measure_env_exp env e1) env bonds e1.
  Proof.
    itr.
    mred_exp_solver - env bonds e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e2 :
    forall env bonds e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env bonds e2
    = subst_env (measure_env_exp env e2) env bonds e2.
  Proof.
    itr.
    mred_exp_solver - env bonds e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_e1e2e3_e3 :
    forall env bonds e1 e2 e3,
      subst_env (measure_exp e1 + measure_exp e2 + measure_exp e3
        + measure_env env) env bonds e3
    = subst_env (measure_env_exp env e3) env bonds e3.
  Proof.
    itr.
    mred_exp_solver - env bonds e3 Hle:
      mred_exp_min
      (measure_env_exp env e3)
      (measure_exp e1 + measure_exp e2 + measure_exp e3 + measure_env env).
  Qed.



  Theorem mred_eel_e :
    forall env bonds e el,
      subst_env (measure_list measure_exp (e :: el) + measure_env env) env bonds e
    = subst_env (measure_env_exp env e) env bonds e.
  Proof.
    itr.
    mred_exp_solver - env bonds e Hle:
      mred_exp_min
      (measure_env_exp env e)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.



  Theorem mred_eel_el :
    forall env bonds e el,
      map
        (subst_env
          (measure_list measure_exp (e :: el) + measure_env env)
          env
          bonds)
        el
    = map
      (subst_env (measure_list measure_exp el + measure_env env) env bonds) el.
  Proof.
    itr.
    mred_exp_solver - env bonds el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_list measure_exp (e :: el) + measure_env env).
  Qed.



  Theorem mred_e1e2el_e1 :
    forall env bonds e1 e2 el,
      subst_env
        (measure_map measure_exp ((e1, e2) :: el) + measure_env env)
        env
        bonds
        e1
    = subst_env (measure_env_exp env e1) env bonds e1.
  Proof.
    itr.
    mred_exp_solver - env bonds e1 Hle:
      mred_exp_min
      (measure_env_exp env e1)
      (measure_map measure_exp ((e1, e2) :: el) + measure_env env).
  Qed.



  Theorem mred_e1e2el_e2 :
    forall env bonds e1 e2 el,
      subst_env
        (measure_map measure_exp ((e1, e2) :: el) + measure_env env)
        env
        bonds
        e2
    = subst_env (measure_env_exp env e2) env bonds e2.
  Proof.
    itr.
    mred_exp_solver - env bonds e2 Hle:
      mred_exp_min
      (measure_env_exp env e2)
      (measure_map measure_exp ((e1, e2) :: el) + measure_env env).
  Qed.



  Theorem mred_e1e2el_el :
    forall env bonds e1 e2 el,
      map
        (prod_map
          (subst_env
            (measure_map measure_exp ((e1, e2) :: el) + measure_env env)
            env
            bonds)
          (subst_env
            (measure_map measure_exp ((e1, e2) :: el) + measure_env env)
            env
            bonds))
        el
    = map
        (prod_map
          (subst_env (measure_map measure_exp el + measure_env env) env bonds)
          (subst_env (measure_map measure_exp el + measure_env env) env bonds))
        el.
  Proof.
    itr.
    mred_exp_solver - env bonds el Hle:
      mred_exp_list_map_min
      (measure_map measure_exp el + measure_env env)
      (measure_map measure_exp ((e1, e2) :: el) + measure_env env).
  Qed.


  Theorem mred_expel_exp :
    forall env bonds exp el,
      subst_env
        (measure_exp exp + measure_list measure_exp el + measure_env env)
        env
        bonds
        exp
    = subst_env (measure_env_exp env exp) env bonds exp.
  Proof.
    itr.
    mred_exp_solver - env bonds exp Hle:
      mred_exp_min
      (measure_env_exp env exp)
      (measure_exp exp + measure_list measure_exp el + measure_env env).
  Qed.



  Theorem mred_expel_el :
    forall env bonds exp el,
      map
        (subst_env
          (measure_exp exp + measure_list measure_exp el + measure_env env)
          env
          bonds)
        el
    = map
      (subst_env (measure_list measure_exp el + measure_env env) env bonds)
      el.
  Proof.
    itr.
    mred_exp_solver - env bonds el Hle:
      mred_exp_list_min
      (measure_list measure_exp el + measure_env env)
      (measure_exp exp + measure_list measure_exp el + measure_env env).
  Qed.



End MeasureLemmas_Specials.






Section MeasureLemmas_Split.



  (* create for tuple exception *)
  Lemma mred_exp_list_split :
    forall fns env bonds el el',
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp (el ++ el') + measure_env env)
            env bonds)
          (el ++ el'))
    = map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el + measure_env env)
            env bonds)
          el) ++
      map
        (bexp_to_fexp fns)
        (map
          (subst_env
            (measure_list measure_exp el' + measure_env env)
            env bonds)
          el').
  Proof.
    (* #1 Intro: intro *)
    itr.
    (* #2 Rewrite Applicative: rewrite *)
    do 2 rwr - map_app.
    (* #3 Measure Reduction: rewrite/triv_nle_solver *)
    rwr - mred_exp_list_min.
    rewrite mred_exp_list_min with (el := el').
    2-3: triv_nle_solver.
    (* #4 Prove by Unfold: unfold *)
    by unfold measure_list.
  Qed.



End MeasureLemmas_Split.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: CONVERTERLEMMAS //////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

(** STRUCTURE:
* Basics Injective
  - cons_inj
  - fcons_inj
  - ftuple_inj
  - fmap_inj
* Value Helpers
  - bval_to_fval_tuple
  - bval_to_fval_map
* Value Main
* Expression
*)



(** NOTES
* HISTORY:
  - bexp_to_fexp_add_vars: EFun need new theorem ->
    + bvs_to_fvs_add_vars: but this is list Val, and need a Val version ->
      ** bval_to_fval_add_vars: each path needed special injection lemmas ->
        -- See in -> Basics Injective & Value Helpers
*)









Section ConverterLemmas_Basics_Injective.



  Lemma cons_inj :
    forall
      (A : Type)
      (x y : A)
      (xs ys : list A),
        x :: xs = y :: ys
    ->  x = y /\ xs = ys.
  Proof.
    itr.
    ivc - H.
    ato.
  Qed.



  Lemma fcons_inj :
    forall x1 x2 y,
        Syntax.VCons x1 x2 = y
    ->  exists z1 z2,
            x1 = z1
        /\  x2 = z2
        /\  y = Syntax.VCons z1 z2.
  Proof.
    itr.
    exi - x1 x2.
    ato.
  Qed.



  Lemma ftuple_inj :
    forall
      (A : Type)
      (f : A -> Val)
      (x : A)
      (xl : list A)
      (y : Val),
        Syntax.VTuple ((f x) :: (map f xl)) = y
    ->  exists z zl,
            (f x) = z
        /\  (map f xl) = zl
        /\  y = Syntax.VTuple (z :: zl).
  Proof.
    itr.
    exi - (f x) (map f xl).
    ato.
  Qed.



  Lemma fmap_inj :
    forall
      (A : Type)
      (f : A -> Val)
      (x1 x2 : A)
      (xl : list (A * A))
      (y : Val),
        Syntax.VMap (((f x1), (f x2)) :: (map (fun '(k, v) => (f k, f v)) xl)) = y
    ->  exists z1 z2 zl,
            (f x1) = z1
        /\  (f x2) = z2
        /\  (map (fun '(k, v) => (f k, f v)) xl) = zl
        /\  y = Syntax.VMap ((z1, z2) :: zl).
  Proof.
    itr.
    exi - (f x1) (f x2) (map (fun '(k, v) => (f k, f v)) xl).
    ato.
  Qed.



End ConverterLemmas_Basics_Injective.






Section ConverterLemmas_Value_Help.



  Lemma bval_to_fval_tuple :
    forall f bvl fvl,
        map (bval_to_fval f) bvl = fvl
    <-> bval_to_fval f (VTuple bvl) = Syntax.VTuple fvl.
  Proof.
    itr.
    spl; itr.
    * smp; f_equal; exact H.
    * smp - H; inj - H as H; exact H.
  Qed.



  Lemma bval_to_fval_map :
    forall f bvl fvl,
        map (fun '(x, y) => ((bval_to_fval f x), (bval_to_fval f y))) bvl = fvl
    <-> bval_to_fval f (VMap bvl) = Syntax.VMap fvl.
  Proof.
    itr.
    spl; itr.
    * smp; f_equal; exact H.
    * smp - H; inj - H as H; exact H.
  Qed.



End ConverterLemmas_Value_Help.






Section ConverterLemmas_Value_Main.



  Theorem bval_to_fval_add_vars_cons :
    forall bv1 bv2 vars f,
        (forall fv,
            bval_to_fval f bv1 = fv
        ->  bval_to_fval (add_vars vars f) bv1 = fv)
    ->  (forall fv,
            bval_to_fval f bv2 = fv
        ->  bval_to_fval (add_vars vars f) bv2 = fv)
    ->  (forall fv,
            bval_to_fval f (VCons bv1 bv2) = fv
        ->  bval_to_fval (add_vars vars f) (VCons bv1 bv2) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bv1 bv2 vars f Heq_v1 Heq_v2 fv Heq.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - fcons_inj in Heq.
    ivc - Heq as fv1 Heq: x H.
    ivc - Heq as fv2 Heq: x H.
    des - Heq as [Hv1 [Hv2 Heq]].
    cwr - Heq.
    (* #3 Specialize: specialize/apply *)
    spc - Heq_v1: fv1 Hv1.
    spc - Heq_v2: fv2 Hv2.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal; asm.
  Qed.



  Theorem bval_to_fval_add_vars_tuple :
    forall bvl vars f,
        Forall (fun bv =>
            (forall fv,
                  bval_to_fval f bv = fv
              ->  bval_to_fval (add_vars vars f) bv = fv))
          bvl
    ->  (forall fv,
            bval_to_fval f (VTuple bvl) = fv
        ->  bval_to_fval (add_vars vars f) (VTuple bvl) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvl vars f HForall.
    ind - bvl as [| bv bvl Heq_vl]: itr; bmp |> smp.
    itr - fv' Heq.
    ivr - HForall; clr - HForall H H0 x l; ren - Heq_v HForall: H1 H2.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - ftuple_inj in Heq.
    ivc - Heq as fv Heq: x H.
    ivc - Heq as fvl Heq: x H.
    des - Heq as [Hv [Hvl Heq]].
    cwr - Heq in *.
    (* #3 Specialize: specialize/apply *)
    app - bval_to_fval_tuple in Hvl.
    spc - Heq_v: fv Hv.
    spc - Heq_vl: HForall (Syntax.VTuple fvl) Hvl.
    app - bval_to_fval_tuple in Heq_vl.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal.
    bwr - Heq_v Heq_vl.
  Qed.



  Theorem bval_to_fval_add_vars_map :
    forall bvl vars f,
        Forall (fun bv =>
            (forall fv,
                bval_to_fval f bv.1 = fv
            ->  bval_to_fval (add_vars vars f) bv.1 = fv)
        /\  (forall fv,
                bval_to_fval f bv.2 = fv
            ->  bval_to_fval (add_vars vars f) bv.2 = fv))
          bvl
    ->  (forall fv,
            bval_to_fval f (VMap bvl) = fv
        ->  bval_to_fval (add_vars vars f) (VMap bvl) = fv).
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvl vars f HForall.
    ind - bvl as [| bv bvl Heq_vl]: itr; bmp |> smp.
    des - bv as [bv1 bv2].
    itr - fv' Heq.
    ivr - HForall; clr - HForall H H0 x l; ren - Heq_v HForall: H1 H2.
    des - Heq_v as [Heq_v1 Heq_v2].
    smp + Heq Heq_v1 Heq_v2.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - fmap_inj in Heq.
    ivc - Heq as fv1 Heq: x H.
    ivc - Heq as fv2 Heq: x H.
    ivc - Heq as fvl Heq: x H.
    des - Heq as [Hv1 [Hv2 [Hvl Heq]]].
    cwr - Heq in *.
    (* #3 Specialize: specialize/apply *)
    app - bval_to_fval_map in Hvl.
    spc - Heq_v1: fv1 Hv1.
    spc - Heq_v2: fv2 Hv2.
    spc - Heq_vl: HForall (Syntax.VMap fvl) Hvl.
    app - bval_to_fval_map in Heq_vl.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    f_equal.
    bwr - Heq_v1 Heq_v2 Heq_vl.
  Qed.



  Theorem bval_to_fval_add_vars :
    forall bv vars f fv,
        bval_to_fval f bv = fv
    ->  bval_to_fval (add_vars vars f) bv = fv.
  Proof.
    (* #1 Intro: intro/induction using ind_val *)
    itr - bv vars f.
    ind + ind_val - bv.
    (* #2 Nil & Lit: *)
    1-2: itr - fv Heq; ivr - Heq; bbn.
    (* #3 Cons: *)
    1: bse - bval_to_fval_add_vars_cons: bv1 bv2 vars f IHbv1 IHbv2.
    (* #4 Tuple: *)
    2: bse - bval_to_fval_add_vars_tuple: l vars f H.
    (* #5 Map: *)
    2: bse - bval_to_fval_add_vars_map: l vars f H.
    (* #6 Clos: *)
    admit.
  Admitted.



  Theorem bvs_to_fvs_add_vars :
    forall bvs fvs vars f,
        bvs_to_fvs f bvs = fvs
    ->  bvs_to_fvs (add_vars vars f) bvs = fvs.
  Proof.
    (* #1 Intro: intro/induction/destruct/inversion/simpl *)
    itr - bvs.
    ind - bvs as [| bv bvs IHbvs]: itr; bvs - H.
    itr - fvs vars f Heq.
    des - fvs as [| fv fvs]: ivs - Heq.
    smp + Heq.
    (* #2 Apply: apply/inversion/destruct/rewrite *)
    app - cons_inj in Heq.
    des - Heq as [Hv Hvs].
    (* #3 Specialize: specialize/apply *)
    psc - bval_to_fval_add_vars as Heq_v: bv vars f fv Hv.
    spc - IHbvs as Heq_vs: fvs vars f Hvs.
    (* #4 Rewrite: f_equal/rewrite/assumption *)
    bwr - Heq_v Heq_vs.
  Qed.



  Lemma bvs_to_fvs_length :
    forall fns vs,
      Datatypes.length (bvs_to_fvs fns vs)
    = Datatypes.length vs.
  Proof.
    itr.
    ind - vs as [| v vs Hvs]: bmp |> smp.
    bwr - Hvs.
  Qed.



End ConverterLemmas_Value_Main.






Section ConverterLemmas_Expression.



  Theorem bexp_to_fexp_add_vars_comm :
    forall env bonds e vars1 vars2 f,
      bexp_to_fexp
        (add_vars vars1 (add_vars vars2 f))
        (subst_env (measure_exp e + measure_env env) env bonds e)
    = bexp_to_fexp
        (add_vars vars2 (add_vars vars1 f))
        (subst_env (measure_exp e + measure_env env) env bonds e).
  Proof.
    (* #1 Intro: *)
    itr.
    ind + ind_exp - e.
    (* #2 Nil & Lit: *)
    2-3: bmp.
    admit.
  Admitted.


  Theorem bexp_to_fexp_add_vars :
    forall e bonds fns vars vs env,
      bexp_to_fexp fns
        (subst_env (measure_env_exp (append_vars_to_env vars vs env) e)
           (append_vars_to_env vars vs env) bonds e)
    = (bexp_to_fexp (add_vars vars fns)
        (subst_env (measure_env_exp env e) env bonds e))
        .[list_subst (bvs_to_fvs fns vs) idsubst].
  Proof.
    (* #1 Intro: *)
    itr - e.
    ind + ind_exp - e; itr; ufl - bexp_to_fexp_subst measure_env_exp; smp.
    8,10: ren - el: l.
    (* #2 Atom: (Nil & Lit) {SAME} *)
    2-3: bbn.
    (* #3 Double: [e1;e2] (Cons & Seq) {SAME} *)
    5: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2.
      (* +3 Specialize: specialize/injection *)
      spe - Heq_e1: bonds fns vars vs env.
      spc - Heq_e2: bonds fns vars vs env.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e1 Heq_e2.
    }
    11: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - Heq_e1 Heq_e2: IHe1 IHe2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_e1e2_e1.
      do 2 rwr - mred_e1e2_e2.
      (* +3 Specialize: specialize/injection *)
      spe - Heq_e1: bonds fns vars vs env.
      spc - Heq_e2: bonds fns vars vs env.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e1 Heq_e2.
    }
    (* #4 List: [(e::el)] (Tuple, Values & PrimOp) {SAME} *)
    5: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - HForall: H.
      ind - el as [| e el Heq_el]: bbn |> smp.
      ivr - HForall; clr - HForall H H0 x l; ren - Heq_e HForall: H1 H2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_eel_e.
      do 2 rwr - mred_eel_el.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: bonds fns vars vs env.
      spc - Heq_el: HForall.
      inj - Heq_el as Heq_el.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e Heq_el.
    }
    1: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - HForall: H.
      ind - el as [| e el Heq_el]: bbn |> smp.
      ivr - HForall; clr - HForall H H0 x l; ren - Heq_e HForall: H1 H2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_eel_e.
      do 2 rwr - mred_eel_el.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: bonds fns vars vs env.
      spc - Heq_el: HForall.
      inj - Heq_el as Heq_el.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e Heq_el.
    }
    4:
    {
      (* +1 Simplify: rename/induction/inversion *)
      ren - HForall: H.
      ind - el as [| e el Heq_el]: bbn |> smp.
      ivr - HForall; clr - HForall H H0 x l; ren - Heq_e HForall: H1 H2.
      (* +2 Measure Reduction: rewrite *)
      do 2 rwr - mred_eel_e.
      do 2 rwr - mred_eel_el.
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: bonds fns vars vs env.
      spc - Heq_el: HForall.
      inj - Heq_el as Heq_el.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      bwr - Heq_e Heq_el.
    }
    (* Fun *)
    3: {
      (* +1 Simplify: rename/induction/inversion *)
      ren - Heq_e: IHe.
      (* +2 Measure Reduction: rewrite *)
      (* do 2 rwr - mred_exp. *)
      (* +3 Specialize: specialize/injection *)
      spc - Heq_e: (bonds_add_vars vl bonds) (add_vars vl fns) vars vs env.
      (* +4 Rewrite: unfold/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp in *.
      rwr - bexp_to_fexp_add_vars_comm in Heq_e.
      rwr - bexp_to_fexp_add_vars_comm in Heq_e.
      rwr - Heq_e.
      (* rwr - Heq_e. *)
      (* bwr - Heq_e. *)
      (*
      list_subst (bvs_to_fvs (add_vars vl fns) vs) idsubst
      =
      upn (Datatypes.length vl) (list_subst (bvs_to_fvs fns vs) idsubst)
      *)
      admit.
    }
    1-9: admit.
  Admitted.



End ConverterLemmas_Expression.






















































(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCEREDUCTION /////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(** STRUCTURE:
* Tactics
  - rem_sbt
  - rem_sbt_smp
* Help
  - create_result_vtuple
  - create_result_vmap
  - list_biforall_vtuple
  - list_biforall_vmap
* Main Small
  - eq_bs_to_fs_reduction_vnil
  - eq_bs_to_fs_reduction_vlit
  - eq_bs_to_fs_reduction_vcons
  - eq_bs_to_fs_reduction_vtuple_nil
  - eq_bs_to_fs_reduction_vtuple
  - eq_bs_to_fs_reduction_vmap_nil
  - eq_bs_to_fs_reduction_vmap
  - eq_bs_to_fs_reduction_vmap_clos
* Main Big
  - bs_to_fs_equivalence_reduction
*)






(* Section: EquivalenceReduction_Tactics. *)



Tactic Notation "rem_sbt"
  ":"   constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt.

Tactic Notation "rem_sbt"
  ":"   constr(v1) constr(v2)
  :=
  remember
    (subst_env (measure_val v1))
    as sbt1
    eqn:Hsbt1;
  remember
    (subst_env (measure_val v2))
    as sbt2
    eqn:Hsbt2;
  clear Hsbt1 Hsbt2.

Tactic Notation "rem_sbt"
  ":"   constr(v1) constr(v2) constr(v3)
  :=
  remember
    (subst_env (measure_val v1))
    as sbt1
    eqn:Hsbt1;
  remember
    (subst_env (measure_val v2))
    as sbt2
    eqn:Hsbt2;
  remember
    (subst_env (measure_val v3))
    as sbt3
    eqn:Hsbt3;
  clear Hsbt1 Hsbt2 Hsbt3.



Tactic Notation "rem_sbt_smp"
  ":" constr(v)
  :=
  remember
    (subst_env (measure_val v))
    as sbt
    eqn:Hsbt;
  simpl;
  inversion Hsbt;
  subst;
  clear_refl.



(* End: EquivalenceReduction_Tactics. *)






Section EquivalenceReduction_Help.



  Lemma create_result_vtuple :
    forall v vl,
      create_result ITuple ([] ++ v :: vl) []
    = Some (RValSeq [Syntax.VTuple (v :: vl)], []).
  Proof.
   trv.
  Qed.



  Lemma create_result_vmap :
    forall v1 v2 vl,
      create_result IMap ([v1] ++ v2 :: (flatten_list vl)) []
    = Some (RValSeq [Syntax.VMap (make_val_map ((v1, v2) :: vl))], []).
  Proof.
    (* #1 Simply: intro/simpl/f_equal *)
    itr.
    smp.
    f_equal.
    (* Rewrite Lemma: rewrite *)
    bwr - flatten_deflatten.
  Qed.



  Lemma create_result_values :
    forall v vl,
      create_result IValues ([] ++ v :: vl) []
    = Some (RValSeq (v :: vl), []).
  Proof.
   trv.
  Qed.



  Theorem list_biforall_vtuple :
    forall fns kvl vl vl',
        vl' = map (bval_to_fval fns) vl
    ->  ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val (VTuple vl))) (VTuple vl)) ⟩
        -[ kvl ]-> ⟨ [], RValSeq [Syntax.VTuple vl'] ⟩
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl))
          vl'.
  Proof.
    (* #1 Rewrite Equivality: intro/rewrite *)
    itr - fns kvl vl vl' Heq_vl Hstep.
    cwr - Heq_vl in *.
    (* #2 Simplify: refold *)
    rfl - bval_to_bexp
          bexp_to_fexp in Hstep.
    (* #3 Inversion Step: inversion/remember_subst *)
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VTuple vl).
    ivc - Hstep1 as Hstep: Hstep2.
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VTuple vl).
    ivc - Hstep1 as Hexp Hnot Hstep: H2 H5 Hstep2.
    * (* #4.1 Prove by Pose Reverse: pose/destruct/rename/simpl/inversion *)
      pose proof framestack_ident_rev _ _ _ _ _ _ Hstep.
      do 4 des - H.
      ren - Hcreate Hlist v'' vl'' eff: H H0 x x0 x1.
      smp - Hcreate.
      bvs - Hcreate.
    * (* #4.2 Prove by Contraction: rename/inversion/constructor *)
      ren - Hcreate: H6.
      ivc - Hcreate.
      ivc - Hstep.
      1: cns.
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
  Qed.



  Theorem list_biforall_vmap :
    forall fns kvl vl vl',
        vl' = make_val_map vl'
    ->  vl' = map (fun '(x, y) => (bval_to_fval fns x, bval_to_fval fns y)) vl
    ->  ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val (VMap vl))) (VMap vl)) ⟩
        -[ kvl ]-> ⟨ [], RValSeq [Syntax.VMap vl'] ⟩
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (flatten_list
            (map
              (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
              (map
                (prod_map
                  (bval_to_bexp (subst_env (measure_val (VMap vl))))
                  (bval_to_bexp (subst_env (measure_val (VMap vl)))))
                 vl)))
          (flatten_list vl').
  Proof.
    (* #1 Rewrite Equivality: intro/rewrite *)
    itr - fns kvl vl vl' Heq_map Heq_vl Hstep.
    cwr - Heq_vl in *; clr - vl'.
    (* #2 Simplify: refold *)
    rfl - bval_to_bexp
          bexp_to_fexp in Hstep.
    (* #3 Inversion Step: inversion/remember_subst *)
    ivc - Hstep as Hstep1 Hstep2: H H0.
    rem_sbt: (VMap vl).
    ivc - Hstep1 as Hstep Heq_list: Hstep2 H1.
    {
      ivc - Hstep.
      {
        cns.
      }
      ren - Hstep1 Hstep2: H H0.
      ivc - Hstep1.
    }
    rem_sbt: (VMap vl).
    (* #4 Fix List *)
    des - vl as [| [v1 v2] vl]: ivs - Heq_list.
    smp + Heq_list.
    ivc - Heq_list.
    (* Pose *)
    pose proof framestack_ident_rev _ _ _ _ _ _ Hstep.
    do 4 des - H.
    clr - Hstep k.
    (* Rename*)
    ren - Hcreate Hlist v'' vl'' eff: H H0 x x0 x1.
    (* Inversion Create*)
    ivc - Hcreate as Heq_map': H0.
    des - vl'': ivc - Heq_map'.
    (* Rewrite Eq Map *)
    simpl map in Heq_map.
    simpl map in Heq_map'.
    rwr - Heq_map in Heq_map'.
    (* Remember *)
    rwr + mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vl in Hlist.
    
    rwl - Heq_map in Heq_map'.
    (*
    rem_sbt: (VMap vl).
    ivs - Hlist.
    rem_sbt: (VMap vl).
    ivs - H4.
    cns.
    2: cns.
    *)
    (*
    rem - e1 e2 el as Heq_e1 Heq_e2 Heq_el:
      (bexp_to_fexp fns (bval_to_bexp (subst_env (measure_val v1)) v1))
      (bexp_to_fexp fns (bval_to_bexp (subst_env (measure_val v2)) v2))
      (map
        (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
        (map
          (prod_map
            (bval_to_bexp (subst_env (measure_val (VMap vl))))
            (bval_to_bexp (subst_env (measure_val (VMap vl)))))
          vl));
       clr - Heq_e1 Heq_e2 Heq_el.
    rem - v1' v2' vl' as Heq_v1 Heq_v2 Heq_vl:
      (bval_to_fval fns v1)
      (bval_to_fval fns v2)
      (map (fun '(x, y) => (bval_to_fval fns x, bval_to_fval fns y)) vl);
      clr - Heq_v1 Heq_v2 Heq_vl v1 v2 vl fns.
    rwl - Heq_map in Heq_map'.
    *)
    (* ALMOST *)
    (*
      Maps.map_insert v'' v (make_val_map (deflatten_list vl'')) =
      Maps.map_insert v1' v2' (make_val_map vl')

      list_biforall (λ (e0 : Exp) (v : Val), ⟨ [], e0 ⟩ -->* [v]) (e1 :: e2 :: flatten_list el)
        (v'' :: v :: vl'')
      ______________________________________(1/1)
      list_biforall (λ (e : Exp) (v0 : Val), ⟨ [], e ⟩ -->* [v0]) (e1 :: e2 :: flatten_list el)
        (v1' :: v2' :: flatten_list vl')
    *)
  Admitted.



End EquivalenceReduction_Help.






Section EquivalenceReduction_Main_Small.



  Theorem eq_bs_to_fs_reduction_vnil :
    forall fns v',
        v' = bval_to_fval fns VNil
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val VNil))
                  VNil) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' Hresult.
    ivc - Hresult.
    (* #2 Simplify: simpl/clear *)
    smp; clr - fns.
    (* #3 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.


  Theorem eq_bs_to_fs_reduction_vlit :
    forall fns v' l,
        v' = bval_to_fval fns (VLit l)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VLit l)))
                  (VLit l)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' l Hresult.
    ivc - Hresult.
    (* #2 Simplify: simpl/clear *)
    smp; clr - fns.
    (* #3 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vcons :
    forall fns v' v1 v2,
        (forall v,
            Forall fs_wfm_val [v]
        ->  v = bval_to_fval fns v1
        ->  ⟨ [], bexp_to_fexp fns
                    (bval_to_bexp
                      (subst_env (measure_val v1))
                      v1) ⟩
              -->* RValSeq [v])
    ->  (forall v,
            Forall fs_wfm_val [v]
        ->  v = bval_to_fval fns v2
        ->  ⟨ [], bexp_to_fexp fns
                    (bval_to_bexp
                      (subst_env (measure_val v2))
                      v2) ⟩
              -->* RValSeq [v])
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VCons v1 v2)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VCons v1 v2)))
                   (VCons v1 v2)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' v1 v2 Hfs_v1 Hfs_v2 Hwfm Hresult.
    ivc - Hresult.
    (* #2 Simplify: refold *)
    rfl + bval_to_fval
          bval_to_bexp
          bexp_to_fexp in Hwfm.
    (* #3 Measure Reduction: rewrite *)
    rwr - mred_vcons_v1
          mred_vcons_v2.
    (* #4 Well Formed Map: apply/destruct *)
    app - fs_wfm_vcons in Hwfm.
    des - Hwfm as [Hwfm_v1 Hwfm_v2].
    (* #5 Remember Values: remember/clear *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bval_to_fval fns v1)
      (bval_to_fval fns v2);
      clr - Heq_v1 Heq_v2.
    (* #7 Specialize Inductive Hypothesis: specialize *)
    spc - Hfs_v1: v1' Hwfm_v1.
    spc - Hfs_v2: v2' Hwfm_v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #9 FrameStack Proof: scope/step *)
    framestack_scope - v1' v2' Hscope_v1 Hscope_v2.
    framestack_step - Hstep_v2 / kv2 v2.
    framestack_step - Hstep_v1 / kv1 v1 fns.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vtuple_nil :
    forall fns,
      ⟨ [], bexp_to_fexp fns
              (bval_to_bexp
                (subst_env (measure_val (VTuple [])))
                 (VTuple [])) ⟩
        -->* RValSeq [bval_to_fval fns (VTuple [])].
  Proof.
    (* #1 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vtuple :
    forall fns v' vl,
        (Forall (fun v => forall v'',
            Forall fs_wfm_val [v'']
        ->  v'' = bval_to_fval fns v
        ->  ⟨ [], bexp_to_fexp fns
                    (bval_to_bexp
                      (subst_env (measure_val v))
                      v) ⟩
              -->* RValSeq [v''])
          vl)
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VTuple vl)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VTuple vl)))
                   (VTuple vl)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' vl HForall Hwfm Hresult.
    ivc - Hresult.
    (* #2 Induction on Value List: induction + pose *)
    ind - vl as [| v vl Hfs_vl]:
      pse - eq_bs_to_fs_reduction_vtuple_nil: fns.
    (* #3 Inversion Forall: inversion *)
    ivc - HForall as Hfs_v HForall: H1 H2.
    (* #4 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp
          bexp_to_fexp.
    rfl - bval_to_fval in Hwfm Hfs_vl.
    rem_sbt_smp: (VTuple (v :: vl)).
    smp - Hwfm.
    (* #5 Measure Reduction: rewrite *)
    rwr - mred_vtuple_v
          mred_vtuple_vl.
    (* #6 Well Formed Map: apply/destruct *)
    app - fs_wfm_vtuple in Hwfm.
    des - Hwfm as [Hwfm_v Hwfm_vl].
    (* #7 Remember Values: remember/clear *)
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl);
      clr - Heq_v.
    (* #7 Specialize Inductive Hypothesis: specialize *)
    spc - Hfs_v: v' Hwfm_v.
    spc - Hfs_vl: HForall Hwfm_vl.
    spe_rfl - Hfs_v.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [Hscope_v Hstep_v]].
    des - Hfs_vl as [kvl [Hscope_vl Hstep_vl]].
      (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    psc - list_biforall_vtuple as Hlist: fns kvl vl vl' Heq_vl Hstep_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (bval_to_bexp (subst_env (measure_val (VTuple vl)))) vl))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hlist
      as Hident_vl;
      clr - kvl Hcreate Hlist.
    (* #8 Destruct Ident Hypothesis: destruct *)
    des - Hident_vl as [kvl Hstep_vl].
    (* #9 FrameStack Proof: scope/step *)
    framestack_scope - v' vl' Hscope_v Hscope_vl.
    rem_sbt: v (VTuple vl).
    framestack_step - Hstep_v / kv v sbt1.
    framestack_step - Hstep_vl.
  Qed.



  Theorem eq_bs_to_fs_reduction_vmap_nil :
    forall fns,
      ⟨ [], bexp_to_fexp fns
              (bval_to_bexp
                (subst_env (measure_val (VMap [])))
                 (VMap [])) ⟩
        -->* RValSeq [bval_to_fval fns (VMap [])].
  Proof.
    (* #1 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  Theorem eq_bs_to_fs_reduction_vmap :
    forall fns v' vl,
        (Forall (fun v =>
            (forall v'',
                Forall fs_wfm_val [v'']
            ->  v'' = bval_to_fval fns v.1
            ->  ⟨ [], bexp_to_fexp fns
                        (bval_to_bexp
                          (subst_env (measure_val v.1))
                          v.1) ⟩
                  -->* RValSeq [v''])
        /\  (forall v'',
                Forall fs_wfm_val [v'']
            ->  v'' = bval_to_fval fns v.2
            ->  ⟨ [], bexp_to_fexp fns
                        (bval_to_bexp
                          (subst_env (measure_val v.2))
                          v.2) ⟩
                  -->* RValSeq [v'']))
              vl)
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VMap vl)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VMap vl)))
                   (VMap vl)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' vl HForall Hwfm Hresult.
    ivc - Hresult.
    (* #2 Induction on Value List: induction + pose *)
    ind - vl as [| [v1 v2] vl Hfs_vl]:
      pse - eq_bs_to_fs_reduction_vmap_nil: fns.
    (* #3 Inversion Forall: inversion/destruct *)
    ivc - HForall as Hfs_v HForall: H1 H2.
    des - Hfs_v as [Hfs_v1 Hfs_v2].
    (* #4 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp
          bexp_to_fexp.
    rfl - bval_to_fval in Hwfm Hfs_vl.
    rem_sbt_smp: (VMap ((v1, v2) :: vl)).
    smp - Hwfm Hfs_v1 Hfs_v2.
    (* #5 Measure Reduction: rewrite *)
    rwr - mred_vmap_v1
          mred_vmap_v2
          mred_vmap_vl.
    (* #6 Well Formed Map: inversion/destruct/apply *)
    ivs - Hwfm as Hwfm_v1v2vl: H1 / H2.
    des - Hwfm_v1v2vl as [Heq_map _].
    app - fs_wfm_vmap in Hwfm.
    des - Hwfm as [Hwfm_v1 [Hwfm_v2 Hwfm_vl]].
    (* #7 Remember Values: remember/clear *)
    rem - v1' v2' vl' as Heq_v1 Heq_v2 Heq_vl:
      (bval_to_fval fns v1)
      (bval_to_fval fns v2)
      (map (fun '(x, y) => (bval_to_fval fns x, bval_to_fval fns y)) vl);
      clr - Heq_v1 Heq_v2.
    (* #7 Specialize Inductive Hypothesis: specialize *)
    spc - Hfs_v1: v1' Hwfm_v1.
    spc - Hfs_v2: v2' Hwfm_v2.
    spc - Hfs_vl: HForall Hwfm_vl.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #8 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    des - Hfs_vl as [kvl [Hscope_vl Hstep_vl]].
    (* #7 Pose Ident Theorem: pose/rewrite + clear *)
    pse - make_val_map_cons as Heq_map_vl: v1' v2' vl' Heq_map.
    pse - create_result_vmap as Hcreate: v1' v2' vl'.
    psc - list_biforall_vmap as Hlist: fns kvl vl vl' Heq_map_vl Heq_vl Hstep_vl.
    pose proof framestack_ident
      IMap
      (flatten_list
        (map
          (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
          (map
            (prod_map
              (bval_to_bexp (subst_env (measure_val (VMap vl))))
              (bval_to_bexp (subst_env (measure_val (VMap vl)))))
             vl)))
      (RValSeq [Syntax.VMap (make_val_map ((v1', v2') :: vl'))])
      (flatten_list vl') v2' [v1'] [] []
      Hcreate Hlist
      as Hident_vl;
      clr - kvl Hcreate Hlist.
    cwl - Heq_map in Hident_vl.
    (* #8 Destruct Ident Hypothesis: destruct *)
    des - Hident_vl as [kvl Hstep_vl].
    (* #9 FrameStack Proof: scope/step *)
    framestack_scope - v1' v2' vl' Hscope_v1 Hscope_v2 Hscope_vl.
    rem_sbt: v1 v2 (VMap vl).
    framestack_step - Hstep_v1 / kv1 v1 sbt1.
    framestack_step - Hstep_v2 / kv2 v2 sbt2.
    framestack_step - Hstep_vl.
  Qed.



  Theorem eq_bs_to_fs_reduction_vclos :
    forall fns v' env ext id vars e fid,
        (Forall (fun v =>
            forall v'',
                Forall fs_wfm_val [v'']
            ->  v'' = bval_to_fval fns v.2
            ->  ⟨ [], bexp_to_fexp fns
                        (bval_to_bexp
                          (subst_env (measure_val v.2))
                          v.2) ⟩
                  -->* RValSeq [v''])
              env)
    ->  Forall fs_wfm_val [v']
    ->  v' = bval_to_fval fns (VClos env ext id vars e fid)
    ->  ⟨ [], bexp_to_fexp fns
                (bval_to_bexp
                  (subst_env (measure_val (VClos env ext id vars e fid)))
                   (VClos env ext id vars e fid)) ⟩
          -->* RValSeq [v'].
  Proof.
    (* #1 Inversion Result: intro/inversion *)
    itr - fns v' env ext id vars e fid HForall Hwfm Hresult.
    ivc - Hresult.
    (* #2 Simplify: refold/remember/simpl *)
    rfl - bval_to_fval
          bval_to_bexp.
    (* #3 Destruct Matching: destuct/refold *)
    des - ext; [idtac | des - fid]; rfl - bexp_to_fexp.
    1: {
      (* #4.1 Measure Reduction: rewrite *)
      rwr - mred_vclos.
      (* #5.1 FrameStack Proof: scope/step *)
      eei; spl.
      1: adm. (* Scope *)
      framestack_step.
    }
    2: {
      (* #4.2 Measure Reduction: rewrite *)
      admit.
      (* #5.2 FrameStack Proof: scope/step *)
      (* eei; spl.
      1: adm. (* Scope *)
      framestack_step. *)
    }
    admit.
  Admitted.



End EquivalenceReduction_Main_Small.






Section EquivalenceReduction_Main_Big.



  Theorem bs_to_fs_equivalence_reduction :
    forall v fns v',
      Forall fs_wfm_val [v'] ->
      v' = bval_to_fval fns v
      -> ⟨ [], bexp_to_fexp fns
          (bval_to_bexp (subst_env (measure_val v))
          v) ⟩
         -->* RValSeq [v'].
  Proof.
    (* #1 Value Induction: intros/induction v using ind_val *)
    itr - v fns.
    ind + ind_val - v; itr - v' Hwfm Hresult.
    (* #2 Atoms: (Nil, Lit) {SAME} *)
    1: bse - eq_bs_to_fs_reduction_vnil: fns v' Hresult.
    1: bse - eq_bs_to_fs_reduction_vlit: fns v' l Hresult.
    (* #3 Doubles: [v1; v2] (Cons) *)
    1: bse - eq_bs_to_fs_reduction_vcons: fns v' v1 v2 IHv1 IHv2 Hwfm Hresult.
    (* #4 Lists: [(v; vl)] (Tuple, Map) {STRUCTURE} *)
    2: bse - eq_bs_to_fs_reduction_vtuple: fns v' l H Hwfm Hresult.
    2: bse - eq_bs_to_fs_reduction_vmap: fns v' l H Hwfm Hresult.
    (* #5 Complexes: (Clos) *)
    1: bse - eq_bs_to_fs_reduction_vclos: fns v' ref ext id params body funid
                                          H Hwfm Hresult.
  Qed.



End EquivalenceReduction_Main_Big.
















(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: EQUIVALENCE  /////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(** STRUCTURE:
* Help
  - list_biforall_vtuple_nth_le
  - list_biforall_vtuple_nth_eq
* Atoms1
  - eq_bs_to_fs_suc_nil
  - eq_bs_to_fs_suc_lit
* Atoms2
  - eq_bs_to_fs_suc_var
  - eq_bs_to_fs_su1_funid
  - eq_bs_to_fs_su2_funid
* Closures
  - eq_bs_to_fs_suc_fun
  - eq_bs_to_fs_suc_letrec
* Double1
  - eq_bs_to_fs_suc_cons
  - eq_bs_to_fs_ex1_cons
  - eq_bs_to_fs_ex2_cons
  - eq_bs_to_fs_suc_seq
  - eq_bs_to_fs_exc_seq
* Double2
  - eq_bs_to_fs_suc_let
  - eq_bs_to_fs_exc_let
  - eq_bs_to_fs_suc_try
  - eq_bs_to_fs_exc_try
* List1
  - eq_bs_to_fs_nil_tuple
  - eq_bs_to_fs_suc_tuple
  - eq_bs_to_fs_exc_tuple
  - eq_bs_to_fs_nil_values
  - eq_bs_to_fs_suc_values
  - eq_bs_to_fs_exc_values
* List2
  - eq_bs_to_fs_nil_map
  - eq_bs_to_fs_suc_map
  - eq_bs_to_fs_exc_map
  - eq_bs_to_fs_nil_primop
  - eq_bs_to_fs_suc_primop
  - eq_bs_to_fs_exc_primop
*)









Section Equivalence_Help.



  (* Solved *)
  Theorem list_biforall_vtuple_nth_le :
    forall fns env e el1 el2 v vl1 v' vl1',
        v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->  Datatypes.length (e :: el1) = Datatypes.length (v :: vl1)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl1)]))
    ->  (forall i,
            i < Datatypes.length (e :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl1) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (e :: el1 ++ el2) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env
                (measure_list measure_exp el1 + measure_env env) env [])
              el1))
          vl1'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el1 el2 v0 vl1 v0' vl1' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    sbt.
    gen - vl1.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el1 as [| e1 el1 IHel1] :> itr; des - vl1 as [| v1 vl1]; smp + Hlength
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: clear/rewrite *)
      clr - IHel1 Hlength.
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [[_ [Hwfm_v1 _]] _].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs_nth as Hfs_v1:
        1 Hnlt fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs_v1.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs_v1.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel1: smp; ivs - Hlength | smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel1 Hwfm fns.
      des - i; itr - Hnlt' fns r Hwfm_vi Hresult; ivc - Hresult.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hnlt'.
        smp - Hwfm_vi.
        des - Hwfm_vi as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs_nth as Hfs_v0: 
          0 Hnlt fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs_v0.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs_v0.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp + Hnlt' Hwfm_vi.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        clr - Hnlt'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs_nth as Hfs_vi: (S (S i)) Hnlt fns
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.



  (* Solved *)
  Theorem list_biforall_vtuple_nth_eq :
    forall fns env e el v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i (e :: el) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env
                (measure_list measure_exp el + measure_env env)env [])
              el))
          vl'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e el v vl v' vl' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    (* #2 Rewrite Add Nil: remember/assert/rewrite + rewrite *)
    rem - length_el as Hlength_el: (Datatypes.length (e :: el)).
    ass > (e :: el = e :: el ++ []) as Heq_el: rwr - app_nil_r.
    cwr - Heq_el in Hfs_nth.
    cwr - Hlength_el in *.
    (* #3 Pose by Previus Theorem: pose *)
    by pose proof list_biforall_vtuple_nth_le
      fns env e el [] v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth.
  Qed.



  (* Solved *)
  Theorem list_biforall_values_nth_le :
    forall fns env e el1 el2 v vl1 v' vl1',
        v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->  Datatypes.length (e :: el1) = Datatypes.length (v :: vl1)
    ->  fs_wfm_result (bres_to_fres fns (inl (v :: vl1)))
    ->  (forall i,
            i < Datatypes.length (e :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl1) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (e :: el1 ++ el2) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env
                (measure_list measure_exp el1 + measure_env env) env [])
              el1))
          vl1'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el1 el2 v0 vl1 v0' vl1' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    sbt.
    gen - vl1.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el1 as [| e1 el1 IHel1] :> itr; des - vl1 as [| v1 vl1]; smp + Hlength
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: clear/rewrite *)
      clr - IHel1 Hlength.
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [_ [Hwfm_v1]].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs_nth as Hfs_v1:
        1 Hnlt fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs_v1.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs_v1.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel1: smp; ivs - Hlength | smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel1 Hwfm fns.
      des - i; itr - Hnlt' fns r Hwfm_vi Hresult; ivc - Hresult.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hnlt'.
        smp - Hwfm_vi.
        des - Hwfm_vi as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs_nth as Hfs_v0: 
          0 Hnlt fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs_v0.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs_v0.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp + Hnlt' Hwfm_vi.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        clr - Hnlt'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs_nth as Hfs_vi: (S (S i)) Hnlt fns
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.



  (* Solved *)
  Theorem list_biforall_values_nth_eq :
    forall fns env e el v vl v' vl',
        v' = bval_to_fval fns v
    ->  vl' = map (bval_to_fval fns) vl
    ->  Datatypes.length (e :: el) = Datatypes.length (v :: vl)
    ->  fs_wfm_result (bres_to_fres fns (inl (v :: vl)))
    ->  (forall i,
            i < Datatypes.length (e :: el)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i (v :: vl) ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i (e :: el) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (map
            (bexp_to_fexp fns)
            (map
              (subst_env
                (measure_list measure_exp el + measure_env env) env [])
              el))
          vl'.
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e el v vl v' vl' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    (* #2 Rewrite Add Nil: remember/assert/rewrite + rewrite *)
    rem - length_el as Hlength_el: (Datatypes.length (e :: el)).
    ass > (e :: el = e :: el ++ []) as Heq_el: rwr - app_nil_r.
    cwr - Heq_el in Hfs_nth.
    cwr - Hlength_el in *.
    (* #3 Pose by Previus Theorem: pose *)
    by pose proof list_biforall_values_nth_le
      fns env e el [] v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth.
  Qed.

(*
env : Environment
ke, ve : Expression
el : list (Expression * Expression)
kv : Value
kvl : list Value
vv : Value
vvl : list Value
mkv : Value
mkvl : list Value
mvv : Value
mvvl : list Value
Hlength_kvl : Datatypes.length ((ke, ve) :: el) = Datatypes.length (kv :: kvl)
Hlength_vvl : Datatypes.length ((ke, ve) :: el) = Datatypes.length (vv :: vvl)
Hmake_vl : make_value_map (kv :: kvl) (vv :: vvl) = (mkv :: mkvl, mvv :: mvvl)
Hfs_nth : ∀ i : nat,
            i < Datatypes.length (make_map_exps ((ke, ve) :: el))
            → ∀ (fns : name_sub) (r : Redex),
                fs_wfm_result r
                → bres_to_fres fns (inl [nth i (make_map_vals (kv :: kvl) (vv :: vvl)) ErrorValue]) =
                  r
                  → ⟨ [],
                    bexp_to_fexp_subst fns env (nth i (make_map_exps ((ke, ve) :: el)) ErrorExp)
                    ⟩ -->* r
kv' : Val
Heq_kv : kv' = bval_to_fval fns mkv
vv' : Val
Heq_vv : vv' = bval_to_fval fns mvv
vl' : list (Val * Val)
Heq_vl : vl' = map (λ '(x, y), (bval_to_fval fns x, bval_to_fval fns y)) (combine mkvl mvvl)
Hmake_vvl : (kv', vv') :: vl' = make_val_map ((kv', vv') :: vl')
Hwfm_kv : fs_wfm_result [kv']
Hwfm_vv : fs_wfm_result [vv']
Hlength : Datatypes.length kvl = Datatypes.length vvl
Hwfm_vl : vl' = make_val_map vl'
Hcreate : create_result IMap ([kv'] ++ vv' :: flatten_list vl') [] =
          Some ([Syntax.VMap (make_val_map ((kv', vv') :: vl'))], [])
______________________________________(1/1)
⟨ [],
° Syntax.EMap
    ((bexp_to_fexp fns (subst_env (measure_env_exp env ke) env ke),
      bexp_to_fexp fns (subst_env (measure_env_exp env ve) env ve))
     :: map (λ '(x, y), (bexp_to_fexp fns x, bexp_to_fexp fns y))
          (map
             (prod_map (subst_env (measure_map measure_exp el + measure_env env) env)
                (subst_env (measure_map measure_exp el + measure_env env) env)) el)) ⟩ -->*
[Syntax.VMap ((kv', vv') :: vl')]
*)

(*
  Theorem list_biforall_vmap_nth_le1 :
    forall fns env ke ve el1 el2 kv vv kvl1 vvl1 kv' vv' vl1' vl',
        (* v' = bval_to_fval fns v
    ->  vl1' = map (bval_to_fval fns) vl1
    ->   *)Datatypes.length ((ke, ve) :: el1) = Datatypes.length ((kv, vv) :: vl1)
    ->  fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl1)]))
    ->  (forall i,
            i < Datatypes.length ((ke, ve) :: el1)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns
                  (inl [nth i
                    (make_map_vals (kv :: kvl1) (vv :: vvl1) ErrorValue])) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env
                    (nth i (make_map_exps ((ke, ve) :: el1 ++ el2)) ErrorExp) ⟩
                  -->* r))
    ->  list_biforall
          (fun e v => ⟨ [], RExp e ⟩ -->* RValSeq [v])
          (flatten_list
            (map
              (fun '(x, y) => (bexp_to_fexp fns x, bexp_to_fexp fns y))
              (map
                (prod_map
                  (subst_env
                    (measure_list measure_exp el1 + measure_env env)
                    env)
                  (subst_env
                    (measure_list measure_exp el1 + measure_env env)
                    env))
                 el1)))
          (flatten_list vl1).
  Proof.
    (* #1 Intro: intro/subst/generalize *)
    itr - fns env e0 el1 el2 v0 vl1 v0' vl1' Heq_v Heq_vl Hlength Hwfm Hfs_nth.
    sbt.
    gen - vl1.
    (* #2 Induction: induction + destruct/simpl/congruence/constructor*)
    ind - el1 as [| e1 el1 IHel1] :> itr; des - vl1 as [| v1 vl1]; smp + Hlength
        :- con + cns.
    cns.
    * (* #3.1 Measure Reduction: clear/rewrite *)
      clr - IHel1 Hlength.
      rwr - mred_eel_e.
      (* #4.1 Prepare for Specialize: simpl/destruct/apply/assert *)
      smp - Hwfm.
      des - Hwfm as [[_ [Hwfm_v1 _]] _].
      app - fs_wfm_val_to_result in Hwfm_v1.
      ass > (1 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
      (* #5.1 Specialize: specialize *)
      spc - Hfs_nth as Hfs_v1:
        1 Hnlt fns (RValSeq [bval_to_fval fns v1]) Hwfm_v1.
      spe_rfl - Hfs_v1.
      (* #6.1 Prove by Hypothesis: simpl/assumption *)
      smp - Hfs_v1.
      asm.
    * (* #3.2 Measure Reduction: rewrite *)
      rwr - mred_eel_el.
      (* #4.2 Apply Indutive Hypothesis: apply + simpl/inversion/subst/tauto *)
      app - IHel1: smp; ivs - Hlength | smp + Hwfm; tau.
      (* #5.2 Destruct: clear/destruct/intro/inversion *)
      clr - IHel1 Hwfm fns.
      des - i; itr - Hnlt' fns r Hwfm_vi Hresult; ivc - Hresult.
      - (* #6.2.1 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        clr - Hnlt'.
        smp - Hwfm_vi.
        des - Hwfm_vi as [Hwfm_v0 _].
        app - fs_wfm_val_to_result in Hwfm_v0.
        ass > (0 < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        (* #7.2.1 Specialize: specialize *)
        spc - Hfs_nth as Hfs_v0: 
          0 Hnlt fns (RValSeq [bval_to_fval fns v0]) Hwfm_v0.
        spe_rfl - Hfs_v0.
        (* #8.2.1 Prove by Hypothesis: simpl/assumption *)
        smp + Hfs_v0.
        asm.
      - (* #6.2.2 Prepare for Specialize: clear/simpl/destruct/apply/assert *)
        smp + Hnlt' Hwfm_vi.
        ass > (S (S i) < Datatypes.length (e0 :: e1 :: el1)) as Hnlt: sli.
        clr - Hnlt'.
        (* #7.2.2 Specialize: specialize *)
        spc - Hfs_nth as Hfs_vi: (S (S i)) Hnlt fns
          (bres_to_fres fns (inl [nth (S (S i)) (v0 :: v1 :: vl1) ErrorValue])).
        smp - Hfs_vi.
        spc - Hfs_vi: Hwfm_vi.
        spe_rfl - Hfs_vi.
        (* #8.2.2 Prove by Hypothesis: assumption *)
        asm.
  Qed.
*)


End Equivalence_Help.









Section Equivalence_Atoms1.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_nil :
    forall fns r env,
        bres_to_fres fns (inl [VNil]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env ENil ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_lit :
    forall fns r env lit,
        bres_to_fres fns (inl [VLit lit]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELit lit) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env lit Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



End Equivalence_Atoms1.









Section Equivalence_Atoms2.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_var :
    forall fns r env var vs,
        get_value env (inl var) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EVar var) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env var vs Hget Hwfm Hresult.
    ufl - bexp_to_fexp_subst.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
    app - get_value_in in Hget as HIn.
    app - In_split in HIn as Heq_env.
    des - Heq_env as [env1]; ren - Heq_env: H.
    des - Heq_env as [env2]; ren - Heq_env: H.
    cwr - Heq_env; clr - env.
    ass - as Hnle: triv_nle_solver >
      (measure_val v <= measure_env (env1 ++ (inl var, v) :: env2)).
    psc - mred_val_min as Hmred_v: v
      (measure_env (env1 ++ (inl var, v) :: env2)) Hnle.
    cwr - Hmred_v; clr - env1 env2 var.
    (* #5 Well Formed Map: destruct/apply *)
    des - Hwfm as [Hwfm_v _].
    app - fs_wfm_val_to_forall in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' as Heq_v:
      (bval_to_fval fns v).
    (* #7 Pose Reduction: symmetry/pose *)
    bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



    (* Solved *)
  Theorem eq_bs_to_fs_su1_funid :
    forall fns r env fid vs,
        get_value env (inr fid) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env var vs Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
    app - get_value_in in Hget as HIn.
    app - In_split in HIn as Heq_env.
    des - Heq_env as [env1]; ren - Heq_env: H.
    des - Heq_env as [env2]; ren - Heq_env: H.
    cwr - Heq_env; clr - env.
    ass - as Hnle: triv_nle_solver >
      (measure_val v <= measure_env (env1 ++ (inr var, v) :: env2)).
    psc - mred_val_min as Hmred_v: v
      (measure_env (env1 ++ (inr var, v) :: env2)) Hnle.
    cwr - Hmred_v; clr - env1 env2 var.
    (* #5 Well Formed Map: destruct/apply *)
    des - Hwfm as [Hwfm_v _].
    app - fs_wfm_val_to_forall in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' as Heq_v:
      (bval_to_fval fns v).
    (* #7 Pose Reduction: symmetry/pose *)
    bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



  (* Admitted: modules own_module *)
  Theorem eq_bs_to_fs_su2_funid :
    forall fns r env fid id func varl_func body_func own_module modules,
        varl_func = varl func
    ->  body_func = body func
    ->  get_own_modfunc own_module fid.1 fid.2 (modules ++ stdlib) = Some func
    ->  get_value env (inr fid) = None
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VClos env [] id varl_func body_func None]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFunId fid) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env fid id func varl_func body_func own_module modules
          Hvarl Hbody Hmod Hget Hwfm Hresult.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    setoid_rewrite Hget.
    (* #3 Destruct Fid: cleardestruct/simpl *)
    clr - Hget Hwfm.
    des - fid.
    smp *.
    (* #4 FrameStack Proof: exists/split/step *)
    eei; spl.
    1: adm.
    framestack_step.
    {
      sbn.
      adm. (* 0 > fns (inr fid) : this probably false ? *)
    }
    (* Main Proof: extra modulo predicate *)
  Admitted.



End Equivalence_Atoms2.









Section Equivalence_Closures.



  (* Solved: except Scope *)
  Theorem eq_bs_to_fs_suc_fun :
    forall fns r env e vars id,
        bres_to_fres fns (inl [VClos env [] id vars e None]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EFun vars e) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e vars id Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn.
    (* rwr - mred_e_vars. *)
    (* #3 FrameStack Proof: scope/step *)
    eei; spl.
    1: adm. (* Scope *)
    framestack_step.
  Admitted.



  (* Admitted: add_fids needs to be implemented *)
  Theorem eq_bs_to_fs_suc_letrec :
    forall fns r env e l result id,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns result = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_funs_to_env l env id) e ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns result = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELetRec l e) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e l result id Hfs Hwfm Hresult.
    ivc - Hresult.
    (* #2 Simplify: cbn/unfold *)
    sbn.
    (* #3 Specalize *)
    spc - Hfs: fns (bres_to_fres fns result) Hwfm. (* fns? *)
    spe_rfl - Hfs.
    (* #4 Destruct *)
    des - Hfs as [k [Hscope Hstep]].
    (* #5 Rewrite Add Fids: rewrite/unfold *)
    (* rwr - bexp_to_fexp_add_fids in Hstep.
    ufl - bexp_to_fexp_subst measure_env_exp in *. *)
    (* #6 FrameStack Proof: scope/step *)
    framestack_scope - Hscope.
    framestack_step.
    (*framestack_step - Hstep. *)
  Admitted.



End Equivalence_Closures.









Section Equivalence_Doubles1.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_cons :
    forall fns r env e1 e2 v2 v1,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v2]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v1]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VCons v1 v2]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ECons e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 v2 v1 Hfs_v2 Hfs_v1 Hwfm Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e2
          mred_e1e2_e1.
    (* #3 Well Formed Map: destruct/apply *)
    des - Hwfm as [[Hwfm_v1 Hwfm_v2] _].
    app - fs_wfm_val_to_result in Hwfm_v2.
    app - fs_wfm_val_to_result in Hwfm_v1.
    (* #4 Remember Values: Remember Values *)
    rem - v2' v1' as Heq_v2 Heq_v1:
      (bval_to_fval fns v2)
      (bval_to_fval fns v1).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    cwl - Heq_v2 Heq_v1 in *; clr - v2 v1.
    spe_rfl - Hfs_v2 Hfs_v1.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    des - Hfs_v1 as [kv1 [Hscope_v1 Hstep_v1]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - v1' v2' Hscope_v1 Hscope_v2.
    framestack_step - Hstep_v2 / kv2 e2.
    framestack_step - Hstep_v1 / kv1 e1 env fns.
    framestack_step.
  Qed.



  (* Solved: only WFM asserted *)
  Theorem eq_bs_to_fs_ex1_cons :
    forall fns r env e1 e2 v2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v2]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ECons e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 v2 exc Hfs_v2 Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e2
          mred_e1e2_e1.
    (* #3 Well Formed Map: assert/apply/unfold *)
    ass > (fs_wfm_val (bval_to_fval fns v2)) as Hwfm_v2: adm.
    app - fs_wfm_val_to_result in Hwfm_v2.
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - v2' exc' as Heq_v2 Heq_exc:
      (bval_to_fval fns v2)
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v2: fns (RValSeq [v2']) Hwfm_v2.
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_v2 Heq_exc in *; clr - v2 exc.
    spe_rfl - Hfs_v2 Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v2 as [kv2 [_ Hstep_v2]].
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_v2 / kv2 e2.
    framestack_step - Hstep_exc / kexc e1 env fns.
    framestack_step.
  Admitted.



  (* Solved *)
  Theorem eq_bs_to_fs_ex2_cons :
    forall fns r env e1 e2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ECons e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 exc Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e2
          mred_e1e2_e1.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc e2.
    framestack_step.
  Qed.



  (* Solved: only WFM asserted *)
  Theorem eq_bs_to_fs_suc_seq :
    forall fns r env e1 e2 v1 v2,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v1]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ESeq e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 v1 v2 Hfs_v1 Hfs_v2 Hwfm_v2 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_val (bval_to_fval fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_val_to_result in Hwfm_v1.
    (* #4 Remember Values: Remember Values *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bval_to_fval fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    cwl - Heq_v1 Heq_v2 in *; clr - v1 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step - Hstep_v2 / kv2 e2 env fns v1'.
    framestack_step.
  Admitted.



  (* Solved *)
  Theorem eq_bs_to_fs_exc_seq :
    forall fns r env e1 e2 exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ESeq e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 exc Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc e1.
    framestack_step.
  Qed.



End Equivalence_Doubles1.









Section Equivalence_Doubles2.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_let :
    forall fns r env e1 e2 v1 v2 vars,
        (Datatypes.length vars = Datatypes.length v1)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl v1) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_vars_to_env vars v1 env) e2 ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELet vars e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 v1 v2 vars Hlength Hfs_v1 Hfs_v2 Hwfm_v2 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_valseq (bvs_to_fvs fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_valseq_to_result in Hwfm_v1.
    (* +4 Remember Values: remember *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bvs_to_fvs fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *; clr - Heq_v2 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 Rewrite Add Vars: rewrite/unfold *)
    ufl - bexp_to_fexp_subst in Hstep_v2.
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Heq_v1 in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #8 FrameStack Proof: scope/step + rewrite/pose/clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step: rwr - Heq_v1 Hlength; bse - bvs_to_fvs_length
      / Hlength Heq_v1 v1.
      admit.
    (* framestack_step - Hstep_v2. *)
  Admitted.



  (* Solved *)
  Theorem eq_bs_to_fs_exc_let :
    forall fns r env e1 e2 exc vars,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ELet vars e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 exc vars Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc e1.
    framestack_step.
  Qed.



  (* Solved: only WFM asserted *)
  (* Difference from Let: measure_reduction/ framestack tactic: auto - by *)
  Theorem eq_bs_to_fs_suc_try :
    forall fns r env e1 e2 e3 v1 v2 vars1 vars2,
        (Datatypes.length vars1 = Datatypes.length v1)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl v1) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_vars_to_env vars1 v1 env) e2 ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETry e1 vars1 e2 vars2 e3) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 e3 v1 v2 vars1 vars2 Hlength Hfs_v1 Hfs_v2 Hwfm_v2
          Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2e3_e1
          mred_e1e2e3_e2
          mred_e1e2e3_e3.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_valseq (bvs_to_fvs fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_valseq_to_result in Hwfm_v1.
    (* +4 Remember Values: remember *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bvs_to_fvs fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq v1') Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    rwl - Heq_v1 Heq_v2 in *; clr - Heq_v2 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 Rewrite Add Vars: rewrite/unfold *)
    ufl - bexp_to_fexp_subst in Hstep_v2.
    rwr - bexp_to_fexp_add_vars in Hstep_v2.
    rwl - Heq_v1 in Hstep_v2.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #8 FrameStack Proof: scope/step + rewrite/pose/clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step: rwr - Heq_v1 Hlength; ase - bvs_to_fvs_length
      / Hlength Heq_v1 v1 vars2 e3.
    (* framestack_step - Hstep_v2. *)
  Admitted.



  (* Solved: only WFM & Vars2 length asserted *)
  Theorem eq_bs_to_fs_exc_try :
    forall fns r env e1 e2 e3 exc v3 vars1 vars2,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v3 = r
        ->  ⟨ [], bexp_to_fexp_subst fns (append_try_vars_to_env vars2
              [exclass_to_value exc.1.1; exc.1.2; exc.2] env) e3 ⟩
              -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v3 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETry e1 vars1 e2 vars2 e3) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 e3 exc v3 vars1 vars2 Hfs_exc Hfs_v3 Hwfm_v3 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2e3_e1
          mred_e1e2e3_e2
          mred_e1e2e3_e3.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_exception (bexc_to_fexc fns exc)) as Hwfm_exc: adm.
    app - fs_wfm_exception_to_result in Hwfm_exc.
    (* #4 Remember Values: remember *)
    rem - exc' v3' as Heq_exc Heq_v3:
      (bexc_to_fexc fns exc)
      (bres_to_fres fns v3).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns exc' Hwfm_exc.
    spc - Hfs_v3: fns v3' Hwfm_v3.
    rwl - Heq_exc Heq_v3 in *; clr - Heq_v3 v3.
    spe_rfl - Hfs_exc Hfs_v3.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [_ Hstep_exc]].
    des - Hfs_v3 as [kv3 [Hscope_v3 Hstep_v3]].
    (* TMP FIX: *)
    (* #7 Assert Vars Length: assert/rewrite/simple + clear *)
    ass > (length vars2 = 3) as Hlength_vars2: adm.
    cwr - Hlength_vars2 in *.
    smp - Hstep_v3.
    (* #8 Rewrite Add Vars: rewrite/unfold *)
    ufl - bexp_to_fexp_subst in Hstep_v3.
    rwr - bexp_to_fexp_add_vars in Hstep_v3.
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #9 Translate Values: unfold/rewrite/clear/destruct/simpl/remember *)
    ufl - bvs_to_fvs in *.
    cwr - Heq_exc in *; clr - exc'.
    des - exc as [[ec vr] vd].
    smp *.
    rem - vr' vd' as Heq_vr Heq_vd:
      (bval_to_fval fns vr)
      (bval_to_fval fns vd);
      clr - Heq_vr Heq_vd vr vd.
    (* #10 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_v3.
    framestack_step.
    framestack_step - Hstep_exc / kexc e1.
    (* #11 Handle Error: constructor/unfold/destruct/simple + apply/clear *)
    ens : apply eval_cool_try_err |> clr - e2 vars1.
    ufl - exclass_to_value Syntax.exclass_to_value in *.
    des - ec; smp *.
    (* #12 FrameStack Proof 2: step *)
    (* * framestack_step - Hstep_v3.
    * framestack_step - Hstep_v3.
    * framestack_step - Hstep_v3. *)
  Admitted.



End Equivalence_Doubles2.









Section Equivalence_Lists1.



  (* Solved *)
  Theorem eq_bs_to_fs_nil_tuple :
    forall fns env vl,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple []) ⟩
          -->* bres_to_fres fns (inl [VTuple vl]).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env vl Hlength_vl.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved: only VALSCOPE asserted *)
  Theorem eq_bs_to_fs_suc_tuple :
    forall fns r env el vl,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VTuple vl]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl Hlength Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_tuple: fns env vl Hlength.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
    (* #5 Well Formed Map: assert/apply *)
    ass - as Hwfm_v: des - Hwfm as [[H _] _] >
      (fs_wfm_val (bval_to_fval fns v)).
    app - fs_wfm_val_to_result in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    pse - list_biforall_vtuple_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env [])
          el))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
  Admitted.



  (* Solved: only WFM asserted *)
  Theorem eq_bs_to_fs_exc_tuple :
    forall fns r env el vl exc j,
        j < Datatypes.length el
    ->  (Datatypes.length vl = j)
    ->  (forall i,
            i < j
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
         fs_wfm_result r
         → bres_to_fres fns (inr exc) = r
           → ⟨ [], bexp_to_fexp_subst fns env (nth j el ErrorExp) ⟩ -->* r
        )
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ETuple el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl exc j Hl_el Hlength_vl Hfs_nth Hfs_exc Hwfm_exc
          Hresult.
    ivc - Hresult.
    (* #2 Split List: pose/destruct/rewrite + clear *)
    pse - length_l_split as Hsplit_el: Value Expression vl el Hl_el.
    des - Hsplit_el as [el1 [el2 [Heq_el Hlength_vl]]].
    cwr - Heq_el in *; clr - el.
    (* #3 Destruct Lists: destruct + rewrite/lia/clear *)
    des - el2 as [| e2 el2]: rwr - app_nil_r in Hl_el; lia |> clr - Hl_el.
    des - vl as [| v vl].
    * (* #4.1 Formalize List: clear/apply/inversion/rewrite + subst/clear *)
      clr - Hfs_nth.
      app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
      ivc - Hempty_vl.
      rwr - app_nil_l in *.
      (* #5.1 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
          mred_eel_el.
      (* #6.1 Specialize Inductive Hypothesis: specialize/simpl + clear *)
      spc - Hfs_exc: fns (bres_to_fres fns (inr exc)) Hwfm_exc.
      spe_rfl - Hfs_exc.
      smp - Hfs_exc.
      (* #7.1 Remember Values: remember + clear *)
      rem - exc' as Heq_exc:
        (bexc_to_fexc fns exc);
        clr - Heq_exc exc.
      (* #8.1 Destruct Inductive Hypothesis: destruct *)
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #9.1 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
    * (* #4.2 Formalize List: destruct/rewrite + inversion/subst *)
      des - el1 as [| e1 el1]: ivs - Hlength_vl.
      rwl - Hlength_vl in *.
      (* #5.2 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
            mred_eel_el
            mred_exp_list_split.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      simpl bres_to_fres in Hfs_exc, Hwfm_exc.
      (* #6.2 Well Formed Map: assert/apply + destruct *)
      ass - as Hwfm_vvl : adm >
        (fs_wfm_result (bres_to_fres fns (inl [VTuple (v :: vl)]))).
      ass - as Hwfm_v: des - Hwfm_vvl as [[H _] _] >
        (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
      (* #7.2 Remember Values: remember *)
      rem - v' vl' exc' as Heq_v Heq_vl Heq_exc:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl)
        (bexc_to_fexc fns exc).
      (* #8.2 Pose Ident Theorem: pose + clear *)
      pse - list_biforall_vtuple_nth_le as Hbiforall:
        fns env e1 el1 (e2 :: el2) v vl v' vl'
        Heq_v Heq_vl Hlength_vl Hwfm_vvl Hfs_nth;
        clr - Heq_vl Hlength_vl Hwfm_vvl.
      pose proof framestack_ident_partial
        ITuple
        (map (bexp_to_fexp fns)
          (map
            (subst_env (measure_list measure_exp el1 + measure_env env) env [])
            el1))
        (bexp_to_fexp_subst fns env e2)
        (map (bexp_to_fexp fns)
          (map
            (subst_env (measure_list measure_exp el2 + measure_env env) env [])
            el2))
        vl' v' [] [] Hbiforall
        as Hfs_vl;
        clr - Hbiforall.
      (* #9.2 Specialize Inductive Hypothesis: assert/specialize/simpl/rewrite
        + clear *)
      ass - as Hnlt: sli >
        (0 < Datatypes.length (e1 :: el1)).
      ass - as Heq_nth: smp; rwr - Heq_v >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
        clr - Heq_v.
      spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
        clr - v vl.
      smp - Hfs_v.
      spc - Hfs_exc: fns exc' Hwfm_exc.
      cwl - Heq_exc in Hfs_exc; clr - exc.
      spe_rfl - Hfs_exc.
      rwr - nth_middle in Hfs_exc.
      (* #10.2 Destruct Inductive Hypothesis: destruct/simpl/rewrite + clear *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #11.2 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_v / kv e1.
      framestack_step - Hstep_vl / kvl el1.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
  Admitted.



  (* Solved *)
  Theorem eq_bs_to_fs_nil_values :
    forall fns env vl,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  ⟨ [], bexp_to_fexp_subst fns env (EValues []) ⟩
          -->* bres_to_fres fns (inl vl).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env vl Hlength_vl.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved: only VALSCOPE asserted *)
  Theorem eq_bs_to_fs_suc_values :
    forall fns r env el vl,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vl) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EValues el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl Hlength Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_values: fns env vl Hlength.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
    (* #5 Well Formed Map: assert/apply *)
    ass - as Hwfm_v: des - Hwfm as [H _] >
      (fs_wfm_val (bval_to_fval fns v)).
    app - fs_wfm_val_to_result in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (bvs_to_fvs fns vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_values as Hcreate: v' vl'.
    pse - list_biforall_values_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      IValues
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env [])
          el))
      (RValSeq (v' :: vl'))
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
  Admitted.



  (* Solved: only WFM asserted *)
  Theorem eq_bs_to_fs_exc_values :
    forall fns r env el vl exc j,
        j < Datatypes.length el
    ->  (Datatypes.length vl = j)
    ->  (forall i,
            i < j
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
         fs_wfm_result r
         → bres_to_fres fns (inr exc) = r
           → ⟨ [], bexp_to_fexp_subst fns env (nth j el ErrorExp) ⟩ -->* r
        )
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EValues el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl exc j Hl_el Hlength_vl Hfs_nth Hfs_exc Hwfm_exc
          Hresult.
    ivc - Hresult.
    (* #2 Split List: pose/destruct/rewrite + clear *)
    pse - length_l_split as Hsplit_el: Value Expression vl el Hl_el.
    des - Hsplit_el as [el1 [el2 [Heq_el Hlength_vl]]].
    cwr - Heq_el in *; clr - el.
    (* #3 Destruct Lists: destruct + rewrite/lia/clear *)
    des - el2 as [| e2 el2]: rwr - app_nil_r in Hl_el; lia |> clr - Hl_el.
    des - vl as [| v vl].
    * (* #4.1 Formalize List: clear/apply/inversion/rewrite + subst/clear *)
      clr - Hfs_nth.
      app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
      ivc - Hempty_vl.
      rwr - app_nil_l in *.
      (* #5.1 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
          mred_eel_el.
      (* #6.1 Specialize Inductive Hypothesis: specialize/simpl + clear *)
      spc - Hfs_exc: fns (bres_to_fres fns (inr exc)) Hwfm_exc.
      spe_rfl - Hfs_exc.
      smp - Hfs_exc.
      (* #7.1 Remember Values: remember + clear *)
      rem - exc' as Heq_exc:
        (bexc_to_fexc fns exc);
        clr - Heq_exc exc.
      (* #8.1 Destruct Inductive Hypothesis: destruct *)
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #9.1 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
    * (* #4.2 Formalize List: destruct/rewrite + inversion/subst *)
      des - el1 as [| e1 el1]: ivs - Hlength_vl.
      rwl - Hlength_vl in *.
      (* #5.2 Measure_Reduction: unfold/simpl/rewrite *)
      ufl - bexp_to_fexp_subst measure_env_exp.
      smp.
      rwr - mred_eel_e
            mred_eel_el
            mred_exp_list_split.
      smp.
      rwr - mred_eel_e
            mred_eel_el.
      simpl bres_to_fres in Hfs_exc, Hwfm_exc.
      (* #6.2 Well Formed Map: assert/apply + destruct *)
      ass - as Hwfm_vvl : adm >
        (fs_wfm_result (bres_to_fres fns (inl (v :: vl)))).
      ass - as Hwfm_v: des - Hwfm_vvl as [H _] >
        (fs_wfm_val (bval_to_fval fns v)).
      app - fs_wfm_val_to_result in Hwfm_v.
      (* #7.2 Remember Values: remember *)
      rem - v' vl' exc' as Heq_v Heq_vl Heq_exc:
        (bval_to_fval fns v)
        (map (bval_to_fval fns) vl)
        (bexc_to_fexc fns exc).
      (* #8.2 Pose Ident Theorem: pose + clear *)
      pse - list_biforall_values_nth_le as Hbiforall:
        fns env e1 el1 (e2 :: el2) v vl v' vl'
        Heq_v Heq_vl Hlength_vl Hwfm_vvl Hfs_nth;
        clr - Heq_vl Hlength_vl Hwfm_vvl.
      pose proof framestack_ident_partial
        IValues
        (map (bexp_to_fexp fns)
          (map
            (subst_env (measure_list measure_exp el1 + measure_env env) env [])
            el1))
        (bexp_to_fexp_subst fns env e2)
        (map (bexp_to_fexp fns)
          (map
            (subst_env (measure_list measure_exp el2 + measure_env env) env [])
            el2))
        vl' v' [] [] Hbiforall
        as Hfs_vl;
        clr - Hbiforall.
      (* #9.2 Specialize Inductive Hypothesis: assert/specialize/simpl/rewrite
        + clear *)
      ass - as Hnlt: sli >
        (0 < Datatypes.length (e1 :: el1)).
      ass - as Heq_nth: smp; rwr - Heq_v >
        (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
        clr - Heq_v.
      spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
        clr - v vl.
      smp - Hfs_v.
      spc - Hfs_exc: fns exc' Hwfm_exc.
      cwl - Heq_exc in Hfs_exc; clr - exc.
      spe_rfl - Hfs_exc.
      rwr - nth_middle in Hfs_exc.
      (* #10.2 Destruct Inductive Hypothesis: destruct/simpl/rewrite + clear *)
      des - Hfs_v as [kv [_ Hstep_v]].
      des - Hfs_vl as [kvl Hstep_vl].
      des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
      (* #11.2 FrameStack Proof: scope/step + clear *)
      framestack_scope - Hscope_exc.
      framestack_step - Hstep_v / kv e1.
      framestack_step - Hstep_vl / kvl el1.
      framestack_step - Hstep_exc / kexc e2.
      framestack_step.
  Admitted.



End Equivalence_Lists1.









Section Equivalence_Lists2.



  (* Solved *)
  Theorem eq_bs_to_fs_nil_map :
    forall fns env kvl vvl mkvl mvvl,
        (Datatypes.length ([] : list Expression) = Datatypes.length kvl)
    ->  (Datatypes.length ([] : list Expression) = Datatypes.length vvl)
    ->  (make_value_map kvl vvl = (mkvl, mvvl))
    ->  ⟨ [], bexp_to_fexp_subst fns env (EMap []) ⟩
          -->* bres_to_fres fns (inl [VMap (combine mkvl mvvl)]).
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env  kvl vvl mkvl mvvl Hlength_kvl Hlength_vvl Hmake_vl.
    smp - Hlength_kvl Hlength_vvl.
    sym - Hlength_kvl Hlength_vvl.
    app - length_zero_iff_nil as Hempty_kvl in Hlength_kvl.
    app - length_zero_iff_nil as Hempty_vvl in Hlength_vvl.
    ivc - Hempty_kvl.
    ivc - Hmake_vl.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Admitted: make_value_map*)
  Theorem eq_bs_to_fs_suc_map :
    forall fns r env el vl kvl vvl mkvl mvvl
           (mel := make_map_exps el : list Expression)
           (mvl := make_map_vals kvl vvl : list Value),
        (Datatypes.length el = Datatypes.length kvl)
    ->  (Datatypes.length el = Datatypes.length vvl)
    ->  (make_value_map kvl vvl = (mkvl, mvvl))
    ->  (combine mkvl mvvl = vl)
    ->  (forall i,
            i < Datatypes.length mel
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i mvl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i mel ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl [VMap vl]) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EMap el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion/subst + subst/clear *)
    itr - fns r env el vl kvl vvl mkvl mvvl mel mvl
          Hlength_kvl Hlength_vvl Hmake_vl Hcombine_vl Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    subst mel mvl.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [| [ke ve] el]:
      pse - eq_bs_to_fs_nil_map:  fns env kvl vvl mkvl mvvl
                                  Hlength_kvl Hlength_vvl Hmake_vl.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - kvl as [| kv kvl]: smp *; con.
    des - vvl as [| vv vvl]: smp *; con.
    ass - as Hlength: rwr - Hlength_kvl in Hlength_vvl; ivs - Hlength_vvl >
      (Datatypes.length kvl = Datatypes.length vvl).
    pse - make_value_map_cons as Hnot_empty:
      kv kvl vv vvl mkvl mvvl Hlength Hmake_vl.
    des - Hnot_empty as [Hnot_empty_mkvl Hnot_empty_mvvl].
    des - mkvl as [| mkv mkvl]: con.
    des - mvvl as [| mvv mvvl]: con.
    clr - Hnot_empty_mkvl Hnot_empty_mvvl.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_e1e2el_e1
          mred_e1e2el_e2
          mred_e1e2el_el.
    (* #5 Well Formed Map: destruct/simpl/assert/apply *)
    des - Hwfm as [[Hmake_vvl [[Hwfm_kv Hwfm_vv] Hwfm]] _].
    simpl map in Hmake_vvl.
    smp - Hwfm_kv Hwfm_vv.
    ass - as Hwfm_vl: app - make_val_map_cons in Hmake_vvl >
      (map
        (λ '(x, y), (bval_to_fval fns x, bval_to_fval fns y))
        (combine mkvl mvvl)
      =
      make_val_map
        (map
          (λ '(x, y), (bval_to_fval fns x, bval_to_fval fns y))
          (combine mkvl mvvl)));
      clr - Hwfm.
    app - fs_wfm_val_to_result in Hwfm_kv.
    app - fs_wfm_val_to_result in Hwfm_vv.
    (* #6 Remember Values: remember *)
    rem - kv' vv' vl' as Heq_kv Heq_vv Heq_vl:
      (bval_to_fval fns mkv)
      (bval_to_fval fns mvv)
      (map (λ '(x, y), (bval_to_fval fns x, bval_to_fval fns y))
        (combine mkvl mvvl)).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vmap as Hcreate: kv' vv' vl'.
    (* rwl - Hmake_vvl in Hcreate. *)
    (*
    pse - list_biforall_vtuple_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env)
          el))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
    *)
  Admitted.



(*
primop_eval_is_result
*)

(*
Lemma primop_create :
  forall fns env fname vl result eff1 eff2 eff3 r,
      primop_eval fname vl (last eff1 eff2) = (result, eff3)
  ->  create_result (IPrimOp fname) (bvs_to_fvs fns vl) = Some (RValSeq r, (beff_to_feff fns eff3)). 
*)

(* need some like:
  create_result (IPrimOp fname) vl = Some (e, eff)

maybe:
primop_eval fname vl (last eff1 eff2) = (result, eff3)
-> create_result (IPrimOp fname) vl = Some (e, eff3)
*)

Search "primop".

  (* Admitted: Some = None -> need create_result congruence *)
  Lemma primop_result :
    forall fns env fname,
      ⟨ [], bexp_to_fexp_subst fns env (EPrimOp fname []) ⟩ -->*
        bres_to_fres fns (inr (undef (VLit (Atom fname)))).
  Proof.
    itr.
    framestack_scope.
    framestack_step.
    ens.
    {
      eapply eval_cool_params_0.
      1: con.
      smp.
      ufl - Auxiliaries.primop_eval.
      des > (Auxiliaries.convert_primop_to_code fname).
      4-7: adm.
      1-2: des > (Auxiliaries.eval_primop_error fname []).
      2, 4: adm.
      3: trv.
      1-2: adm.
    }
    framestack_step.
  Admitted.



  (* Dependently Solved: primop_result *)
  Theorem eq_bs_to_fs_nil_primop :
    forall fns env vl fname result eff1 eff2 eff3,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  (Datatypes.length ([] : list Expression) = Datatypes.length eff1)
    ->  primop_eval fname vl (last eff1 eff2) = (result, eff3)
    ->  ⟨ [], bexp_to_fexp_subst fns env (EPrimOp fname []) ⟩
          -->* bres_to_fres fns result.
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env vl fname result eff1 eff2 eff3
          Hlength_vl Hlength_eff1 Hprimop.
    smp - Hlength_vl Hlength_eff1.
    sym - Hlength_vl Hlength_eff1.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    app - length_zero_iff_nil as Hempty_eff1 in Hlength_eff1.
    ivc - Hempty_vl.
    smp - Hprimop.
    ufl - primop_eval in Hprimop.
    des > (convert_primop_to_code fname); ivc - Hprimop.
    1-39: bse - primop_result: fns env fname.
  Qed.



  (* Admitted: create_result *)
  Theorem eq_bs_to_fs_suc_primop :
    forall fns r env el vl fname result eff1 eff2 eff3,
        (Datatypes.length el = Datatypes.length vl)
    ->  (Datatypes.length el = Datatypes.length eff1)
    ->  primop_eval fname vl (last eff1 eff2) = (result, eff3)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  fs_wfm_result r
    ->  bres_to_fres fns result = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EPrimOp fname el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl fname result eff1 eff2 eff3
          Hlength_vl Hlength_eff1 Hprimop Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]:
      pse - eq_bs_to_fs_nil_primop: fns env vl fname result eff1 eff2 eff3
                                    Hlength_vl Hlength_eff1 Hprimop.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
  Admitted.



End Equivalence_Lists2.









Section Equivalence_App.

(*
env : Environment
modules : list ErlModule
own_module : string
exp, body : Expression
res : ValueSequence + Exception
var_list : list Var
ref : Environment
ext : list (nat * FunctionIdentifier * FunctionExpression)
n : nat
eff1, eff2, eff3 : SideEffectList
eff : list SideEffectList
ids : list nat
id, id', id'' : nat
f : option FunctionIdentifier
H : Datatypes.length params = Datatypes.length vals
bs1 : | env, modules, own_module, id, exp, eff1 | -e> | id',
      inl [VClos ref ext n var_list body f], eff2 |
H0 : Datatypes.length var_list = Datatypes.length vals
H1 : Datatypes.length params = Datatypes.length eff
H2 : Datatypes.length params = Datatypes.length ids
H3 : ∀ i : nat,
       i < Datatypes.length params
       → | env, modules, own_module, nth_def ids id' 0 i, nth i params ErrorExp,
         nth_def eff eff2 [] i | -e> | nth_def ids id' 0 (S i), inl [nth i vals ErrorValue],
         nth_def eff eff2 [] (S i) |
H4 : ∀ i : nat,
       i < Datatypes.length params
       → ∀ (fns : name_sub) (r : Redex),
           fs_wfm_result r
           → bres_to_fres fns (inl [nth i vals ErrorValue]) = r
             → ⟨ [], bexp_to_fexp_subst fns env (nth i params ErrorExp) ⟩ -->* r
bs2 : | append_vars_to_env var_list vals (get_env ref ext), modules, own_module,
      last ids id', body, last eff eff2 | -e> | id'', res, eff3 |
IHbs1 : ∀ (fns : name_sub) (r : Redex),
          fs_wfm_result r
          → bres_to_fres fns (inl [VClos ref ext n var_list body f]) = r
            → ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r
IHbs2 : ∀ (fns : name_sub) (r : Redex),
          fs_wfm_result r
          → bres_to_fres fns res = r
            → ⟨ [],
              bexp_to_fexp_subst fns (append_vars_to_env var_list vals (get_env ref ext))
                body ⟩ -->* r
fns : name_sub
r : Redex
Hwfm : fs_wfm_result r
Hresult : bres_to_fres fns res = r
______________________________________(1/1)
⟨ [], bexp_to_fexp_subst fns env (EApp exp params) ⟩ -->* r

*)



(*
Hlength : Datatypes.length [] = Datatypes.length vl
Hfs_nth : ∀ i : nat,
            i < Datatypes.length []
            → ∀ (fns : name_sub) (r : Redex),
                fs_wfm_result r
                → bres_to_fres fns (inl [nth i vl ErrorValue]) = r
                  → ⟨ [], bexp_to_fexp_subst fns env (nth i [] ErrorExp) ⟩ -->* r
Hfs_exp : ∀ (fns : name_sub) (r : Redex),
            fs_wfm_result r
            → bres_to_fres fns (inl [VClos ref ext n vars body fid]) = r
              → ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r
Hfs_el : ∀ (fns : name_sub) (r : Redex),
           fs_wfm_result r
           → bres_to_fres fns result = r
             → ⟨ [],
               bexp_to_fexp_subst fns (append_vars_to_env vars vl (get_env ref ext)) exp
               ⟩ -->* r
Hwfm : fs_wfm_result (bres_to_fres fns result)
______________________________________(1/2)
⟨ [], bexp_to_fexp_subst fns env (ETuple []) ⟩ -->* bres_to_fres fns result
*)

Lemma append_vars_to_env_empty : 
  forall vars env,
    append_vars_to_env vars [] env
  = match vars with
   | [] => env
   | v :: vs => []
   end.
Proof.
  itr.
  ass - as Hunfold: des - vars; ufl - append_vars_to_env >
  (append_vars_to_env vars [] env =
  match vars with
   | [] => match ([] : list Value) with
           | [] => env
           | _ :: _ => []
           end
   | v :: vs =>
       match [] with
       | [] => []
       | e :: es => append_vars_to_env vs es (insert_value env (inl v) e)
       end
   end).
   bwr - Hunfold.
Qed.


  (* Solved *)
  Theorem eq_bs_to_fs_nil_app :
    forall fns env exp vl result ref ext n vars body fid,
        (Datatypes.length ([] : list Expression) = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length ([] : list Expression)
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i [] ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [VClos ref ext n vars body fid]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns result = r
        ->  ⟨ [], bexp_to_fexp_subst fns
              (append_vars_to_env vars vl (get_env ref ext)) body ⟩ -->* r)
    ->  ⟨ [], bexp_to_fexp_subst fns env (EApp exp []) ⟩
          -->* bres_to_fres fns result.
  Proof.
    (* #1 Rewrite Value List: inro/simpl/symmetry/apply/inversion
      + subst/clear *)
    itr - fns env exp vl result ref ext n vars body fid
          Hlength_vl Hfs_nth Hfs_exp Hfs_body.
    smp - Hlength_vl.
    sym - Hlength_vl.
    app - length_zero_iff_nil as Hempty_vl in Hlength_vl.
    ivc - Hempty_vl.
    (* #2 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    unfold measure_list.
    smp.
    rwr - Nat.add_0_r.
    rwr - append_vars_to_env_empty in Hfs_body.
    (* #3 Well Formed Map: assert/apply *)
    ass - as Hwfm_vclos: adm >
      (fs_wfm_result (bres_to_fres fns (inl [VClos ref ext n vars body fid]))).
    ass - as Hwfm_vl: adm >
      (fs_wfm_result (bres_to_fres fns result)).
    (* #4 Specialize Inductive Hypothesis: specialize + clear *)
    spc - Hfs_exp: fns
      (bres_to_fres fns (inl [VClos ref ext n vars body fid])) Hwfm_vclos.
    spc - Hfs_body: fns (bres_to_fres fns result) Hwfm_vl.
    spe_rfl - Hfs_exp Hfs_body.
    (* #5 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exp as [kexp [_ Hstep_exp]].
    des - Hfs_body as [kbody [Hscope_body Hstep_body]].
    (* #6 Rewrite Add Vars: rewrite/unfold *)
    (* rwr - bexp_to_fexp_add_vars in Hstep_vl. *)
    ufl - bexp_to_fexp_subst measure_env_exp in *.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope - Hscope_body.
    framestack_step - Hstep_exp / kexp.
    admit.
  Admitted.


  (* Solved: only VALSCOPE asserted *)
  Theorem eq_bs_to_fs_suc_app :
    forall fns r env exp el vl result ref ext n vars body fid,
        (Datatypes.length el = Datatypes.length vl)
    ->  (forall i,
            i < Datatypes.length el
        ->  (forall fns r,
                fs_wfm_result r
            ->  bres_to_fres fns (inl [nth i vl ErrorValue]) = r
            ->  ⟨ [], bexp_to_fexp_subst fns env (nth i el ErrorExp) ⟩ -->* r))
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [VClos ref ext n vars body fid]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns result = r
        ->  ⟨ [], bexp_to_fexp_subst fns
              (append_vars_to_env vars vl (get_env ref ext)) body ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns result = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EApp exp el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env exp el vl result ref ext n vars body fid
          Hlength Hfs_nth Hfs_exp Hfs_body Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el].
    
    1: adm.
    eei; spl.
    1: adm.
    
  Admitted.

(*

    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env el vl Hlength Hfs_nth Hwfm Hresult.
    ivc - Hresult.
    (* #2 Destruct Expression List: destruct + pose *)
    des - el as [|e el]: pse - eq_bs_to_fs_nil_tuple: fns env vl Hlength.
    (* #3 Fix Result: destruct + simpl/congruence *)
    des - vl: smp *; con.
    (* #4 Measure Reduction: unfold/simpl/rewrite *)
    ufl - bexp_to_fexp_subst measure_env_exp.
    smp.
    rwr - mred_eel_e
          mred_eel_el.
    (* #5 Well Formed Map: assert/apply *)
    ass - as Hwfm_v: des - Hwfm as [[H _] _] >
      (fs_wfm_val (bval_to_fval fns v)).
    app - fs_wfm_val_to_result in Hwfm_v.
    (* #6 Remember Values: remember *)
    rem - v' vl' as Heq_v Heq_vl:
      (bval_to_fval fns v)
      (map (bval_to_fval fns) vl).
    (* #7 Pose Ident Theorem: pose + clear *)
    pse - create_result_vtuple as Hcreate: v' vl'.
    pse - list_biforall_vtuple_nth_eq as Hbiforall:
      fns env e el v vl v' vl'
      Heq_v Heq_vl Hlength Hwfm Hfs_nth;
      clr - Hlength Hwfm Heq_vl.
    pose proof framestack_ident
      ITuple
      (map (bexp_to_fexp fns)
        (map (subst_env (measure_list measure_exp el + measure_env env) env)
          el))
      (RValSeq [Syntax.VTuple (v' :: vl')])
      vl' v' [] [] []
      Hcreate Hbiforall
      as Hfs_vl;
      clr - Hcreate Hbiforall.
    (* #8 Specialize Inductive Hypothesis: assert/specialize/simpl + clear *)
    ass - as Hnlt: sli >
      (0 < Datatypes.length (e :: el)).
    ass - as Heq_nth: smp; rwr - Heq_v >
      (bres_to_fres fns (inl [nth 0 (v :: vl) ErrorValue]) = RValSeq [v']);
      clr - Heq_v.
    spc - Hfs_nth as Hfs_v: 0 Hnlt fns (RValSeq [v']) Hwfm_v Heq_nth;
      clr - v vl.
    smp - Hfs_v.
    (* #9 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v as [kv [_ Hstep_v]].
    des - Hfs_vl as [kvl Hstep_vl].
    (* #10 FrameStack Proof: scope/step + clear *)
    eei; spl.
    1: admit. (*Needs to modify main proof, it need is_result r predicate *)
    framestack_step - Hstep_v / kv e.
    framestack_step - Hstep_vl.
*)


  (* Solved *) (* Almost same as ex2_cons *)
  Theorem eq_bs_to_fs_ex1_app :
    forall fns r env exp el exc,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inr exc) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env exp ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inr exc) = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (EApp exp el) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env exp el exc Hfs_exc Hwfm_exc Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_expel_exp
          mred_expel_el.
    (* #3 Well Formed Map: unfold *)
    ufl - bres_to_fres in Hwfm_exc.
    (* #4 Remember Values: Remember Values *)
    rem - exc' as Heq_exc:
      (bexc_to_fexc fns exc).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_exc: fns (RExc exc') Hwfm_exc.
    cwl - Heq_exc in *; clr - exc.
    spe_rfl - Hfs_exc.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_exc as [kexc [Hscope_exc Hstep_exc]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_exc.
    framestack_step - Hstep_exc / kexc exp.
    framestack_step.
  Qed.



End Equivalence_App.













Section Equivalence_Main.



  Theorem eq_bs_to_fs :
    forall env modules own_module id id' e e' eff eff',
        (eval_expr env modules own_module id e eff id' e' eff')
    ->  forall fns r,
          fs_wfm_result r
      ->  bres_to_fres fns e' = r
      ->  ⟨ [], (bexp_to_fexp_subst fns env e) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/induction *)
    itr - env modules own_module id id' e e' eff eff' bs.
    ind - bs; itr - fns r Hwfm Hresult.
    (* #2 Atoms #1: (Nil, Lit) {SAME} *)
    3:  bse - eq_bs_to_fs_suc_nil:    fns r env
                                      Hresult.
    3:  bse - eq_bs_to_fs_suc_lit:    fns r env l
                                      Hresult.
    (* #3 Atoms #2: (Var, FunId) {ALMOST} *)
    3:  bse - eq_bs_to_fs_suc_var:    fns r env s res
                                      H Hwfm Hresult.
    3:  bse - eq_bs_to_fs_su1_funid:  fns r env fid res
                                      H Hwfm Hresult.
    3:  bse - eq_bs_to_fs_su2_funid:  fns r env fid id func
                                      varl_func body_func own_module modules
                                      H1 H2 H0 H Hwfm Hresult.
    (* #4 Closures: (Fun, LetRec) {DIFFERENT} *)
    3:  bse - eq_bs_to_fs_suc_fun:    fns r env e vl id
                                      Hresult.
    12: bse - eq_bs_to_fs_suc_letrec: fns r env e l res id
                                      IHbs Hwfm Hresult.
    (* #5 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
    4:  bse - eq_bs_to_fs_suc_cons:   fns r env hd tl tlv hdv
                                      IHbs1 IHbs2 Hwfm Hresult.
    13: bse - eq_bs_to_fs_ex1_cons:   fns r env hd tl vtl ex
                                      IHbs1 IHbs2 Hwfm Hresult.
    12: bse - eq_bs_to_fs_ex2_cons:   fns r env hd tl ex
                                      IHbs Hwfm Hresult.
    10: bse - eq_bs_to_fs_suc_seq:    fns r env e1 e2 v1 v2
                                      IHbs1 IHbs2 Hwfm Hresult.
    27: bse - eq_bs_to_fs_exc_seq:    fns r env e1 e2 ex
                                      IHbs Hwfm Hresult.
    (* #6 Doubles #2: [e1;e2] (Let, Try) {SIMILIAR} *)
    9: bse - eq_bs_to_fs_suc_let:    fns r env e1 e2 vals res l
                                      H IHbs1 IHbs2 Hwfm Hresult.
    25: bse - eq_bs_to_fs_exc_let:    fns r env e1 e2 ex vl
                                      IHbs Hwfm Hresult.
    11: bse - eq_bs_to_fs_suc_try:    fns r env e1 e2 e3 vals res vl1 vl2
                                      H IHbs1 IHbs2 Hwfm Hresult.
    11: bse - eq_bs_to_fs_exc_try:    fns r env e1 e2 e3 ex res vl1 vl2
                                      IHbs1 IHbs2 Hwfm Hresult.
    (* #7 Lists #1: [el] (Tuple, Values) {ALMOST} *)
    3:  bse - eq_bs_to_fs_suc_tuple:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    9: bse - eq_bs_to_fs_exc_tuple:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
    1: bse - eq_bs_to_fs_suc_values:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    1: bse - eq_bs_to_fs_exc_values:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
    (* #6 Lists #2: [el] (Map, PrimOp) {ALMOST} *)
    6:  { 
      (* pse - eq_bs_to_fs_suc_map: fns r env l lv kvals vvals kvals' vvals' H0.
          smp - H9. 
          spe - *) adm. }
    18: { adm. }
    4: bse - eq_bs_to_fs_suc_primop:  fns r env params vals fname res
                                      eff eff1 eff2
                                      H H0 H4 H3 Hwfm Hresult.
    12: { adm. }
    (* #7 Applications: [e;el] (App) *)
    4:  { adm. }
    11: bse - eq_bs_to_fs_ex1_app: fns r env exp params ex IHbs Hwfm Hresult.
    11: { adm. }
    11: { adm. }
    11: { adm. }
    (* #8 Calls: [e1;e2;el] (Call) *)
    2:  { adm. }
    2:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    (* #9 Cases: [e;pattern] (Case) *)
    1:  { adm. }
    1:  { adm. }
    1:  { adm. }
  Admitted.

(* Admitted:
* FunId 2: modulo
* Fun & Letrec
* PrimOp
*)



End Equivalence_Main.








































































(* Version 2*)



(*
1 goal
fns : name_sub
bonds : list (Var + FunctionIdentifier)
env : Environment
var : Var
v : Value
Hget : get_value env (inl var) = Some [v]
Hwfm : fs_wfm_result (bres_to_fres fns (inl [v]))
Hin : existsb (λ k : Var + FunctionIdentifier, var_funid_eqb (inl var) k) bonds = true
______________________________________(1/1)
⟨ [], bexp_to_fexp fns (EVar var) ⟩ -->* [bval_to_fval fns v]
*)

Definition env_bonds_disjunct
  (env : Environment)
  (bonds : Bonds)
  : bool
  :=
  forallb
    (fun '(key, _) =>
      negb
        (existsb
          (fun k =>
            var_funid_eqb key k) 
          bonds))
    env.





Section Equivalence_Atoms12.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_nil2 :
    forall fns r bonds env,
        bres_to_fres fns (inl [VNil]) = r
    ->  ⟨ [], bexp_to_fexp fns
          (subst_env (measure_env_exp env ENil) env bonds ENil) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env bonds Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_lit2 :
    forall fns r bonds env lit,
        bres_to_fres fns (inl [VLit lit]) = r
    ->  ⟨ [], bexp_to_fexp fns
          (subst_env (measure_env_exp env (ELit lit)) env bonds (ELit lit)) ⟩
          -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r bonds env lit Hresult.
    ivc - Hresult.
    (* #2 FrameStack Proof: scope/step *)
    framestack_scope.
    framestack_step.
  Qed.



End Equivalence_Atoms12.





Section Equivalence_Atoms22.



  (* Solved *)
  Theorem eq_bs_to_fs_suc_var2 :
    forall fns r bonds env var vs,
        get_value env (inl var) = Some vs
    ->  fs_wfm_result r
    ->  bres_to_fres fns (inl vs) = r
    -> env_bonds_disjunct env bonds = true
    ->  ⟨ [], bexp_to_fexp fns
          (subst_env (measure_env_exp env (EVar var)) env bonds (EVar var)) ⟩
          -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r bonds env var vs Hget Hwfm Hresult Hbonds.
    ivc - Hresult.
    (* #2 Rewrite Get: cbn/rewrite *)
    sbn.
    rwr - Hget.
    (* #3 Destruct Match: destruct/simple + apply/simpl/congruence *)
    des - vs as [|v vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    des - vs as [|v0 vs]:
      app - get_value_singelton_length in Hget; smp - Hget; con.
    smp.
    
    (*tmp*)
    des > (in_bonds (inl var) bonds) as Hin.
    * ufl - in_bonds in Hin.
      ufl - env_bonds_disjunct in Hbonds.
      app - get_value_in in Hget as HIn.
      app - In_split in HIn as Heq_env.
      des - Heq_env as [env1]; ren - Heq_env: H.
      des - Heq_env as [env2]; ren - Heq_env: H.
      cwr - Heq_env in *; clr - env.
      Print app_comm_cons.
      ass - as Hrewrite: smp > 
        ((inl var, v) :: env2 = [(inl var, v)] ++ env2).
      cwr - Hrewrite in *.
      Search forallb.
      rwr - forallb_app in Hbonds.
      rwr - forallb_app in Hbonds.
      smp *.
      rem - tmp:
        (existsb
            (λ k : Var + FunctionIdentifier,
               match k with
               | inl s2 => (var =? s2)%string
               | inr _ => false
               end) bonds).
      Search forallb.
      des - tmp.
      - smp - Hbonds.
        rwr - andb_false_r in Hbonds.
        con.
      - con.
    * clr - Hin Hbonds.
      (* #4 Measure Reduction: apply/destruct/assert/pose/rewrite + clear/triv *)
      app - get_value_in in Hget as HIn.
      app - In_split in HIn as Heq_env.
      des - Heq_env as [env1]; ren - Heq_env: H.
      des - Heq_env as [env2]; ren - Heq_env: H.
      cwr - Heq_env; clr - env.
      ass - as Hnle: triv_nle_solver >
        (measure_val v <= measure_env (env1 ++ (inl var, v) :: env2)).
      psc - mred_val_min as Hmred_v: v
        (measure_env (env1 ++ (inl var, v) :: env2)) Hnle.
      cwr - Hmred_v; clr - env1 env2 var.
      (* #5 Well Formed Map: destruct/apply *)
      des - Hwfm as [Hwfm_v _].
      app - fs_wfm_val_to_forall in Hwfm_v.
      (* #6 Remember Values: remember *)
      rem - v' as Heq_v:
        (bval_to_fval fns v).
      (* #7 Pose Reduction: symmetry/pose *)
      bse - bs_to_fs_equivalence_reduction: v fns v' Hwfm_v Heq_v.
  Qed.



  (* Solved: except Scope *)
  Theorem eq_bs_to_fs_suc_fun2 :
    forall fns r bonds env e vars id,
        bres_to_fres fns (inl [VClos env [] id vars e None]) = r
    ->  ⟨ [], bexp_to_fexp fns
          (subst_env
            (measure_env_exp env (EFun vars e)) env bonds (EFun vars e)) ⟩
          -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r bonds env e vars id Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn.
    (* rwr - mred_e_vars. *)
    (* #3 FrameStack Proof: scope/step *)
    eei; spl.
    1: adm. (* Scope *)
    framestack_step.
    admit.
  Admitted.




  (* Solved: only WFM asserted *)
  Theorem eq_bs_to_fs_suc_seq2 :
    forall fns r env e1 e2 v1 v2,
        (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns (inl [v1]) = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e1 ⟩ -->* r)
    ->  (forall fns r,
            fs_wfm_result r
        ->  bres_to_fres fns v2 = r
        ->  ⟨ [], bexp_to_fexp_subst fns env e2 ⟩ -->* r)
    ->  fs_wfm_result r
    ->  bres_to_fres fns v2 = r
    ->  ⟨ [], bexp_to_fexp_subst fns env (ESeq e1 e2) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/inversion + subst/clear *)
    itr - fns r env e1 e2 v1 v2 Hfs_v1 Hfs_v2 Hwfm_v2 Hresult.
    ivc - Hresult.
    (* #2 Measure Reduction: cbn/rewrite *)
    sbn *.
    rwr - mred_e1e2_e1
          mred_e1e2_e2.
    (* #3 Well Formed Map: assert/apply *)
    ass > (fs_wfm_val (bval_to_fval fns v1)) as Hwfm_v1: adm.
    app - fs_wfm_val_to_result in Hwfm_v1.
    (* #4 Remember Values: Remember Values *)
    rem - v1' v2' as Heq_v1 Heq_v2:
      (bval_to_fval fns v1)
      (bres_to_fres fns v2).
    (* #5 Specialize Inductive Hypothesis: specialize/rewrite + clear *)
    spc - Hfs_v1: fns (RValSeq [v1']) Hwfm_v1.
    spc - Hfs_v2: fns v2' Hwfm_v2.
    cwl - Heq_v1 Heq_v2 in *; clr - v1 v2.
    spe_rfl - Hfs_v1 Hfs_v2.
    (* #6 Destruct Inductive Hypothesis: destruct *)
    des - Hfs_v1 as [kv1 [_ Hstep_v1]].
    des - Hfs_v2 as [kv2 [Hscope_v2 Hstep_v2]].
    (* #7 FrameStack Proof: scope/step + clear *)
    framestack_scope - Hscope_v2.
    framestack_step - Hstep_v1 / kv1 e1.
    framestack_step - Hstep_v2 / kv2 e2 env fns v1'.
    framestack_step.
  Admitted.


End Equivalence_Atoms22.




















Section Equivalence_Main2.



  Theorem eq_bs_to_fs2 :
    forall env modules own_module id id' e e' eff eff',
        (eval_expr env modules own_module id e eff id' e' eff')
    ->  forall fns r bonds,
          fs_wfm_result r
      ->  is_result r
      ->  bres_to_fres fns e' = r
      ->  env_bonds_disjunct env bonds = true
      ->  ⟨ [], bexp_to_fexp fns
            (subst_env (measure_env_exp env e) env bonds e) ⟩ -->* r.
  Proof.
    (* #1 Inversion Result: intro/induction *)
    itr - env modules own_module id id' e e' eff eff' bs.
    ind - bs; itr - fns r bonds Hwfm Hscope Hresult Hbonds.
    (* #2 Atoms #1: (Nil, Lit) {SAME} *)
    3:  bse - eq_bs_to_fs_suc_nil2:   fns r bonds env
                                      Hresult.
    3:  bse - eq_bs_to_fs_suc_lit2:   fns r bonds env l
                                      Hresult.
    (* #3 Atoms #2: (Var, FunId) {ALMOST} *)
    3:  bse - eq_bs_to_fs_suc_var2:    fns r bonds env s res
                                      H Hwfm Hresult Hbonds.
    3:  adm.
    3:  adm.
    
    (* #4 Closures: (Fun, LetRec) {DIFFERENT} *)
    3:  bse - eq_bs_to_fs_suc_fun:    fns r env e vl id
                                      Hresult.
    12: bse - eq_bs_to_fs_suc_letrec: fns r env e l res id
                                      IHbs Hwfm Hresult.
    (* #5 Doubles #1: [e1;e2] (Cons, Seq) {SIMILIAR}*)
    4:  bse - eq_bs_to_fs_suc_cons:   fns r env hd tl tlv hdv
                                      IHbs1 IHbs2 Hwfm Hresult.
    13: bse - eq_bs_to_fs_ex1_cons:   fns r env hd tl vtl ex
                                      IHbs1 IHbs2 Hwfm Hresult.
    12: bse - eq_bs_to_fs_ex2_cons:   fns r env hd tl ex
                                      IHbs Hwfm Hresult.
    10: bse - eq_bs_to_fs_suc_seq:    fns r env e1 e2 v1 v2
                                      IHbs1 IHbs2 Hwfm Hresult.
    27: bse - eq_bs_to_fs_exc_seq:    fns r env e1 e2 ex
                                      IHbs Hwfm Hresult.
    (* #6 Doubles #2: [e1;e2] (Let, Try) {SIMILIAR} *)
    9: bse - eq_bs_to_fs_suc_let:    fns r env e1 e2 vals res l
                                      H IHbs1 IHbs2 Hwfm Hresult.
    25: bse - eq_bs_to_fs_exc_let:    fns r env e1 e2 ex vl
                                      IHbs Hwfm Hresult.
    11: bse - eq_bs_to_fs_suc_try:    fns r env e1 e2 e3 vals res vl1 vl2
                                      H IHbs1 IHbs2 Hwfm Hresult.
    11: bse - eq_bs_to_fs_exc_try:    fns r env e1 e2 e3 ex res vl1 vl2
                                      IHbs1 IHbs2 Hwfm Hresult.
    (* #7 Lists #1: [el] (Tuple, Values) {ALMOST} *)
    3:  bse - eq_bs_to_fs_suc_tuple:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    9: bse - eq_bs_to_fs_exc_tuple:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
    1: bse - eq_bs_to_fs_suc_values:   fns r env exps vals
                                       H H3 Hwfm Hresult.
    1: bse - eq_bs_to_fs_exc_values:   fns r env exps vals ex i
                                       H H0 H4 IHbs Hwfm Hresult.
    (* #6 Lists #2: [el] (Map, PrimOp) {ALMOST} *)
    6:  { 
      (* pse - eq_bs_to_fs_suc_map: fns r env l lv kvals vvals kvals' vvals' H0.
          smp - H9. 
          spe - *) adm. }
    18: { adm. }
    4: bse - eq_bs_to_fs_suc_primop:  fns r env params vals fname res
                                      eff eff1 eff2
                                      H H0 H4 H3 Hwfm Hresult.
    12: { adm. }
    (* #7 Applications: [e;el] (App) *)
    4:  { adm. }
    11: bse - eq_bs_to_fs_ex1_app: fns r env exp params ex IHbs Hwfm Hresult.
    11: { adm. }
    11: { adm. }
    11: { adm. }
    (* #8 Calls: [e1;e2;el] (Call) *)
    2:  { adm. }
    2:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    4:  { adm. }
    (* #9 Cases: [e;pattern] (Case) *)
    1:  { adm. }
    1:  { adm. }
    1:  { adm. }
  Admitted.

(* Admitted:
* FunId 2: modulo
* Fun & Letrec
* PrimOp
*)



End Equivalence_Main2.