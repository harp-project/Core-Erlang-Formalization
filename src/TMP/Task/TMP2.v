From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.
Import ListNotations.





Section EraseNames.

Definition LiteralToLit (l : Literal) : Lit :=
match l with
 | BigStep.Syntax.Atom s => s
 | BigStep.Syntax.Integer x => x
end.

Fixpoint bpat_to_fpat (p : Pattern) : Pat :=
match p with
 | BigStep.Syntax.PVar v => PVar
 | BigStep.Syntax.PLit l => PLit (LiteralToLit l)
 | BigStep.Syntax.PCons hd tl => PCons (bpat_to_fpat hd) (bpat_to_fpat tl)
 | BigStep.Syntax.PTuple l => PTuple (map bpat_to_fpat l)
 | BigStep.Syntax.PMap l => PMap (map (fun '(x, y) => (bpat_to_fpat x, bpat_to_fpat y)) l)
 | BigStep.Syntax.PNil => PNil
end.


Definition NameSub {T} {dec : T -> T -> bool} := T -> nat.

Definition addName {T dec} (v : T) (σ : @NameSub _ dec) :=
  fun x => if dec x v
           then 0
           else S (σ x).

Definition addNames {T} {dec : T -> T -> bool} (vl : list T) (σ : NameSub) : NameSub :=
  fold_right (@addName _ dec) σ vl.

Definition varsOfPatternList (l : list Pattern) : list BigStep.Syntax.Var :=
  fold_right (fun x acc => variable_occurances x ++ acc) nil l
.

Definition sum_eqb {A B : Type} (eqbA : A -> A -> bool) (eqbB : B -> B -> bool) (a b : A + B) : bool :=
match a, b with
| inl a', inl b' => eqbA a' b'
| inr a', inr b' => eqbB a' b'
| _, _ => false
end.

Definition addVars (vl : list string) (σ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb)) :=
  addNames (map inl vl) σ.

Definition addFids (vl : list FunctionIdentifier) (σ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb)) :=
  addNames (map inr vl) σ.

Fixpoint bexp_to_fexp (σᵥ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) (* (: @NameSub (string * nat) (prod_eqb eqb Nat.eqb)) *)
  (e : Expression) : Exp :=
match e with
 | BigStep.Syntax.EValues el => EValues (map (bexp_to_fexp σᵥ) el)
 | ENil => ˝VNil
 | ELit l => ˝VLit (LiteralToLit l)
 | EVar v => ˝VVar (σᵥ (inl v))
 | EFunId f => ˝VFunId ((σᵥ (inr f)), snd f)
 | BigStep.Syntax.EFun vl e => EFun (length vl) (bexp_to_fexp (addVars vl σᵥ) e)
 | BigStep.Syntax.ECons hd tl => ECons (bexp_to_fexp σᵥ hd) (bexp_to_fexp σᵥ tl)
 | BigStep.Syntax.ETuple l => ETuple (map (bexp_to_fexp σᵥ) l)
 | BigStep.Syntax.ECall m f l => ECall (bexp_to_fexp σᵥ m) (bexp_to_fexp σᵥ f) (map (bexp_to_fexp σᵥ) l)
 | BigStep.Syntax.EPrimOp f l => EPrimOp f (map (bexp_to_fexp σᵥ) l)
 | BigStep.Syntax.EApp exp l => EApp (bexp_to_fexp σᵥ exp) (map (bexp_to_fexp σᵥ) l)
 | BigStep.Syntax.ECase e l => ECase (bexp_to_fexp σᵥ e) (map (fun '(pl, g, b) =>
                                     ((map bpat_to_fpat pl), bexp_to_fexp (addVars (varsOfPatternList pl) σᵥ) g, bexp_to_fexp (addVars (varsOfPatternList pl) σᵥ) b))
                                     l)
 | BigStep.Syntax.ELet l e1 e2 => ELet (length l) (bexp_to_fexp σᵥ e1) (bexp_to_fexp (addVars l σᵥ) e2)
 | BigStep.Syntax.ESeq e1 e2 => ESeq (bexp_to_fexp σᵥ e1) (bexp_to_fexp σᵥ e2)
 | BigStep.Syntax.ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) =>
                                           (length vl, bexp_to_fexp (addNames (map (inr ∘ fst) l ++ map inl vl) σᵥ) e)
                                         ) l)
                                          (bexp_to_fexp (addFids (map fst l) σᵥ) e)
 | BigStep.Syntax.EMap l => EMap (map (fun '(x, y) => (bexp_to_fexp σᵥ x, bexp_to_fexp σᵥ y)) l)
 | BigStep.Syntax.ETry e1 vl1 e2 vl2 e0 => ETry (bexp_to_fexp σᵥ e1)
                                                (length vl1) (bexp_to_fexp (addVars vl1 σᵥ) e2)
                                                (length vl2) (bexp_to_fexp (addVars vl1 σᵥ) e0)
end.

End EraseNames.




















From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.BigStep Require Import Environment.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
Require Import stdpp.list.


Import BigStep.


Section MesureTypes.


    Definition measure_list
      {A : Type}
      (f : A -> nat)
      (al : list A)
      : nat 
      :=
    list_sum (map f al).

    Definition measure_map
      {A : Type}
      (f : A -> nat)
      (aml : list (A * A))
      : nat
      :=
    list_sum (map (fun '(a1, a2) => (f a1) + (f a2)) aml).

    Definition measure_case
      (f : Expression -> nat)
      (cl : list ((list Pattern) * Expression * Expression))
      : nat
      :=
    list_sum (map (fun '(pl, g, b) => (f g) + (f b)) cl).

    Definition measure_letrec
      (f : Expression -> nat)
      (lrl : list (FunctionIdentifier * (list Var * Expression)))
      : nat
      :=
    list_sum (map (fun '(fid, (vl, b)) => (f b)) lrl).

    Definition measure_env
      (f : Value -> nat)
      (env : Environment)
      : nat
      :=
    list_sum (map (fun '(vf, v) => (f v)) env).









  Fixpoint measure_exp
    (e : Expression)
    : nat
    :=
  match e with
  | ENil => 1
  | ELit l => 1
  | EVar v => 1
  | EFunId f => 1

  | EFun vl e => 1
      + measure_exp e

  | ECons hd tl => 1
      + measure_exp hd
      + measure_exp tl

  | ESeq e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ELet l e1 e2 => 1
      + measure_exp e1
      + measure_exp e2

  | ETry e1 vl1 e2 vl2 e3 => 1
      + measure_exp e1
      + measure_exp e2
      + measure_exp e3

  | EValues el => 1
      + measure_list measure_exp el

  | EPrimOp f l => 1
      + measure_list measure_exp l

  | ETuple l => 1
      + measure_list measure_exp l

  | EMap l =>  1
      + measure_map measure_exp l

  | EApp exp l => 1
      + measure_exp exp
      + measure_list measure_exp l

  | ECall m f l => 1
      + measure_exp m
      + measure_exp f
      + measure_list measure_exp l

  | ECase e l => 1
      + measure_exp e
      + measure_case measure_exp l

  | ELetRec l e => 1
      + measure_exp e
      + measure_letrec measure_exp l
  end.



  Fixpoint measure_val
    (v : Value) 
    : nat
    :=
  match v with
  | VNil => 1
  | VLit l => 1

  | VCons hd tl => 1
      + measure_val hd
      + measure_val tl

  | VTuple l => 1
      + measure_list measure_val l

  | VMap l => 1
      + measure_map measure_val l

  | VClos env ext id vl e fid => 1
      + measure_exp e
      + measure_env measure_val env
  end.



  Definition measure_env_exp
    (env : Environment)
    (e : Expression)
    : nat
    :=
  measure_exp e
  + measure_env measure_val env.



End MesureTypes.
































Section Conv.


  Fixpoint bval_to_bexp (subst_env : Environment -> Expression -> Expression) 
                      (v : Value) 
                      : Expression :=

    let
      rem_from_env (env : Environment) 
                   (keys : list (Var + FunctionIdentifier)) 
                   : Environment :=

        fold_left (fun env' key => 
                      filter (fun '(k, v) => 
                                negb (var_funid_eqb k key)) 
                             env') 
                  keys 
                  env 
    in

    let
      rem_from_env_vl (env : Environment)
                      (vl : list Var)
                      : Environment :=

        rem_from_env env (map inl vl)
    in

    let
      rem_from_env_fids (env : Environment)
                        (ext : list (nat * FunctionIdentifier * FunctionExpression))
                        : Environment :=

        rem_from_env env (map inr (map snd (map fst ext)))
    in

    let
      map_ext (env : Environment) 
              (ext : list (nat * FunctionIdentifier * FunctionExpression)) 
              : list (FunctionIdentifier * (list Var * Expression)) :=

        map (fun '(n, fid, (vl, e)) => (fid, (vl, (subst_env (rem_from_env_vl env vl) e)))) ext
    in

    match v with

    | VNil => ENil
    | VLit l => ELit l

    | VClos env ext id vl e fid => 
        match ext, fid with
        | [], _ => EFun vl (subst_env (rem_from_env_vl env vl) e)
        | _, None => EFun vl (subst_env (rem_from_env_vl env vl) e) (*Todo: make it option ?*)
        | _, Some fid' => ELetRec (map_ext (rem_from_env_fids env ext) ext) (EFunId fid')
        end

    | VCons hd tl => ECons (bval_to_bexp subst_env hd) (bval_to_bexp subst_env tl)
    | VTuple l => ETuple (map (bval_to_bexp subst_env) l)
    | VMap l => EMap (map (prod_map (bval_to_bexp subst_env) (bval_to_bexp subst_env)) l)

    end.






  Definition bexp_to_fexp_subst f 
                              (subst_env : nat -> Environment -> Expression -> Expression) 
                              (e : Expression) 
                              (env : Environment) 
                              : Exp :=

    bexp_to_fexp f 
                (subst_env (measure_env_exp env 
                                             e) 
                           env 
                           e).







  Fixpoint fexp_to_fval (e : Exp) 
                           : option Val :=

    match e with
    | VVal v => Some v
    | EExp e' => 
        match e' with
        | Syntax.EFun vl e'' => Some (Syntax.VClos [] 0 vl e'')
        | Syntax.EValues el => 
            match (mapM fexp_to_fval el) with
            | Some el' => Some (Syntax.VTuple el')
            | None => None
            end
        | Syntax.ECons hd tl => 
            match (fexp_to_fval hd), 
                  (fexp_to_fval tl) with
            | Some hd', Some tl' => Some (Syntax.VCons hd' tl')
            | _, _ => None
            end
        | Syntax.ETuple l => 
            match (mapM fexp_to_fval l) with
            | Some l' => Some (Syntax.VTuple l')
            | None => None
            end
        | Syntax.EMap l => 
            match (mapM (fun '(x, y) => 
                          match (fexp_to_fval x), 
                                (fexp_to_fval y) with
                          | Some x', Some y' => Some (x', y')
                          | _, _ => None
                          end) l) with
            | Some l' => Some (Syntax.VMap l')
            | None => None
            end
        | Syntax.ECall m f l => None
            (*
            match (fexp_to_fval m), 
                  (fexp_to_fval f), 
                  (mapM fexp_to_fval l) with
            | Some m', Some f', Some l' => Some (Syntax.VTuple (m' :: f' :: l'))
            | _, _, _ => None
            end
            *)
        | Syntax.EPrimOp f l => None
            (*
            match (mapM fexp_to_fval l) with
            | Some l' => Some (Syntax.VTuple l')
            | None => None
            end
            *)
        | Syntax.EApp exp l =>  None
            (*
            match (fexp_to_fval exp), 
                  (mapM fexp_to_fval l) with
            | Some exp', Some l' => Some (Syntax.VTuple (exp' :: l'))
            | _, _ => None
            end
            *)
        | Syntax.ECase e' l => None
            (*
            match (fexp_to_fval e'), 
                  (mapM (fun '(pl, g, b) => 
                          match (fexp_to_fval g), 
                                (fexp_to_fval b) with
                          | Some g', Some b' => Some (pl, g', b')
                          | _, _ => None
                          end) l) with
            | Some e', Some l' => Some (Syntax.VTuple (e' :: l'))
            | _, _ => None
            end
            *)
        | Syntax.ELet l e1 e2 =>  None
            (*
            match (fexp_to_fval e1), 
                  (fexp_to_fval e2) with
            | Some e1', Some e2' => Some (Syntax.VTuple [e1'; e2'])
            | _, _ => None
            end
            *)
        | Syntax.ESeq e1 e2 =>  None
            (*
            match (fexp_to_fval e1), 
                  (fexp_to_fval e2) with
            | Some e1', Some e2' => Some (Syntax.VTuple [e1'; e2'])
            | _, _ => None
            end
            *)
        | Syntax.ELetRec l e =>  None
            (*
            match (mapM (fun '(fid, (vl, b)) => 
                          match (fexp_to_fval b) with
                          | Some b' => Some (fid, vl, b')
                          | None => None
                          end) l), 
                  (fexp_to_fval e) with
            | Some l', Some e' => Some (Syntax.VTuple (e' :: l'))
            | _, _ => None
            end
            *)
        | Syntax.ETry e1 vl1 e2 vl2 e0 =>  None
            (*
            match (fexp_to_fval e1), 
                  (fexp_to_fval e2), 
                  (fexp_to_fval e0) with
            | Some e1', Some e2', Some e0' => Some (Syntax.VTuple [e1'; e2'; e0'])
            | _, _, _ => None
            end
            *)
        end
    end.


  Definition bval_to_fval f 
                          (subst_env : nat -> Environment -> Expression -> Expression) 
                          (v : Value) 
                          : option Val :=

    fexp_to_fval (bexp_to_fexp f 
                                (bval_to_bexp (subst_env (measure_val v)) 
                                            v)).


  Definition bvs_to_fvs f 
                             (subst_env : nat -> Environment -> Expression -> Expression) 
                             (vs : ValueSequence) 
                             : option ValSeq :=

    mapM (bval_to_fval f subst_env) vs.


  Definition bex_to_fex f
                          (subst_env : nat -> Environment -> Expression -> Expression) 
                          (exc : Exception)
                          : option CoreErlang.Syntax.Exception :=
    match exc with

    | (excc, v1, v2) => 

        match (bval_to_fval f subst_env v1), 
              (bval_to_fval f subst_env v2) with

        | Some v1', Some v2' => 

            match excc with
            | Error => Some (CoreErlang.Syntax.Error, v1', v2')
            | Throw => Some (CoreErlang.Syntax.Throw, v1', v2')
            | Exit => Some (CoreErlang.Syntax.Exit, v1', v2')
            end

        | _, _ => None
        end
    end.



  Definition bres_to_fres f 
                          (subst_env : nat -> Environment -> Expression -> Expression)
                          (res : (ValueSequence + Exception))
                          : option Redex :=
    
    match res with

    | inl vs => 
        match (bvs_to_fvs f subst_env vs) with
        | Some vs' => Some (RValSeq vs')
        | None => None
        end

    | inr exc => 
        match (bex_to_fex f subst_env exc) with
        | Some exc' => Some (RExc exc')
        | None => None
        end
        
    end.

End Conv.




































Section Subst.



  Fixpoint subst_env (fuel : nat) 
                     (Γ : Environment) 
                     (e : Expression) 
                     : Expression :=

    let
      rem_from_env (env : Environment) 
                   (keys : list (Var + FunctionIdentifier)) 
                   : Environment :=

        fold_left (fun env' key => 
                      filter (fun '(k, v) => 
                                negb (var_funid_eqb k key)) 
                             env') 
                  keys 
                  env 
    in

    let
      rem_from_env_vl (env : Environment)
                      (vl : list Var)
                      : Environment :=

        rem_from_env env (map inl vl)
    in

    let
      rem_from_env_fids (env : Environment)
                        (l : list (FunctionIdentifier * (list Var * Expression)))
                        : Environment :=

        rem_from_env env (map inr (map fst l))
    in

    let
      rem_from_env_fids_vl (env : Environment)
                           (l : list (FunctionIdentifier * (list Var * Expression)))
                           (vl : list Var)
                           : Environment :=

        rem_from_env_fids (rem_from_env_vl env vl) l
    in

    match fuel with
    | O => e (*Todo: make it option?*)
    | S fuel' =>
        match e with

        | EValues el => EValues (map (subst_env fuel' Γ) el)
        | ENil => ENil
        | ELit l => ELit l

        | EVar v => 
            match (get_value Γ (inl v)) with
            | Some [v'] => bval_to_bexp (subst_env fuel') v'
            | Some vs => EValues (map (bval_to_bexp (subst_env fuel')) vs)
            | _ => EVar v
            end

        | EFunId f => 
            match (get_value Γ (inr f)) with
            | Some [f'] => bval_to_bexp (subst_env fuel') f'
            | _ => (EFunId f)
            end

        | EFun vl e => EFun vl (subst_env fuel' Γ e)

        | ECons hd tl => ECons (subst_env fuel' Γ hd) 
                               (subst_env fuel' Γ tl)

        | ETuple l => ETuple (map (subst_env fuel' Γ) l)
        
        | ECall m f l => ECall (subst_env fuel' Γ m) 
                               (subst_env fuel' Γ f) 
                               (map (subst_env fuel' Γ) l)

        | EPrimOp f l => EPrimOp f (map (subst_env fuel' Γ) l)

        | EApp exp l => EApp (subst_env fuel' Γ exp) 
                             (map (subst_env fuel' Γ) l)
        
        | ECase e l => ECase (subst_env fuel' Γ e) 
                             (map (fun '(pl, g, b) => (pl, (subst_env fuel' Γ g), (subst_env fuel' Γ b))) l)
        
        | ELet l e1 e2 => ELet l (subst_env fuel' Γ e1) 
                                 (subst_env fuel' (rem_from_env_vl Γ l) e2)
        
        | ESeq e1 e2 => ESeq (subst_env fuel' Γ e1) 
                             (subst_env fuel' Γ e2)
        
        | ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) => (fid, (vl, (subst_env fuel' (rem_from_env_fids_vl Γ l vl) b)))) l) 
                                 (subst_env fuel' (rem_from_env_fids Γ l) e)
        
        | EMap l => EMap (map (prod_map (subst_env fuel' Γ) (subst_env fuel' Γ)) l)
        
        | ETry e1 vl1 e2 vl2 e0 => ETry (subst_env fuel' Γ e1) 
                                        vl1 
                                        (subst_env fuel' Γ e2) 
                                        vl2 
                                        (subst_env fuel' Γ e0)
        end
    end.



End Subst.





























Section Eq.


  Ltac do_step := econstructor; [constructor;auto| simpl].






  Theorem equivalence_bigstep_framestack : 

    forall env modules own_module id id' e e' eff eff' f r,

      (eval_expr env modules own_module id e eff id' e' eff')

      ->

  	  Some r = bres_to_fres f subst_env e'

(* wellformed_map r (valseq,exc) later on top level *)

  	  ->

  	  ⟨ [], (bexp_to_fexp_subst f subst_env e env) ⟩
      	-->*
  	  r.

  Proof.
    intros. revert f r H0. induction H; intros.
    (* Values *)
    * admit.
    * admit.
    (* Nil *)
    * eexists. split; inv H0.
      - constructor. 
        scope_solver.
      - cbn.
        do_step.
        constructor.
    (* Lit *)
    * eexists. split; inv H0.
      - constructor.
        scope_solver.
      - do 1 do_step.
        constructor.
    (* Var *)
    * admit.
    (* FunId *)
    * admit.
    * admit.
    (* Fun *)
    * admit.
    (* Tuple*)
    * admit.
    (* Cons *)
    * admit.
    (* Case *)
    * admit.
    (* Call *)
    * admit.
    * admit.
    (* Primop *)
    * admit.
    (* App *)
    * admit.
    (* Let *)
    * admit.
    (* Seq *)
    * admit.
    (* LetRec *)
    * admit.
    (* Map *)
    * admit.
    (* Cons *)
    * admit.
    * admit.
    (* Tuple *)
    * admit.
    (* Try *)
    * admit.
    * admit.
    (* Case *)
    * admit.
    * admit.
    (* Call *)
    * admit.
    * admit.
    * admit.
    * admit.
    * admit.
    (* Primop *)
    * admit.
    (* App *)
    * admit.
    * admit.
    * admit.
    * admit.
    (* Let *)
    * admit.
    (* Seq *)
    * admit.
    (* Map *)
    * admit.
  Admitted.

End Eq.










(**
- Phase 1: Rename (SUCCESS!!!)
  - rename (Convert) to bexp_fval ...etc
  - rename (EraseNames)
  - remove dublicates (erasename -> bexp_to_fexp)
- Phase 2: Measure
  - Flip measure_env_exp [ERRROR]


*)



