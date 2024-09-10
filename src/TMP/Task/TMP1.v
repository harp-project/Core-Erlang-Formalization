From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.
Import ListNotations.





Section EraseNames.

Definition LiteralToLit (l : Literal) : Lit :=
match l with
 | BigStep.Syntax.Atom s => s
 | BigStep.Syntax.Integer x => x
end.

Fixpoint eraseNamesPat (p : Pattern) : Pat :=
match p with
 | BigStep.Syntax.PVar v => PVar
 | BigStep.Syntax.PLit l => PLit (LiteralToLit l)
 | BigStep.Syntax.PCons hd tl => PCons (eraseNamesPat hd) (eraseNamesPat tl)
 | BigStep.Syntax.PTuple l => PTuple (map eraseNamesPat l)
 | BigStep.Syntax.PMap l => PMap (map (fun '(x, y) => (eraseNamesPat x, eraseNamesPat y)) l)
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

Fixpoint eraseNames (σᵥ : @NameSub (string + FunctionIdentifier) (sum_eqb eqb (prod_eqb eqb Nat.eqb))) (* (: @NameSub (string * nat) (prod_eqb eqb Nat.eqb)) *)
  (e : Expression) : Exp :=
match e with
 | BigStep.Syntax.EValues el => EValues (map (eraseNames σᵥ) el)
 | ENil => ˝VNil
 | ELit l => ˝VLit (LiteralToLit l)
 | EVar v => ˝VVar (σᵥ (inl v))
 | EFunId f => ˝VFunId ((σᵥ (inr f)), snd f)
 | BigStep.Syntax.EFun vl e => EFun (length vl) (eraseNames (addVars vl σᵥ) e)
 | BigStep.Syntax.ECons hd tl => ECons (eraseNames σᵥ hd) (eraseNames σᵥ tl)
 | BigStep.Syntax.ETuple l => ETuple (map (eraseNames σᵥ) l)
 | BigStep.Syntax.ECall m f l => ECall (eraseNames σᵥ m) (eraseNames σᵥ f) (map (eraseNames σᵥ) l)
 | BigStep.Syntax.EPrimOp f l => EPrimOp f (map (eraseNames σᵥ) l)
 | BigStep.Syntax.EApp exp l => EApp (eraseNames σᵥ exp) (map (eraseNames σᵥ) l)
 | BigStep.Syntax.ECase e l => ECase (eraseNames σᵥ e) (map (fun '(pl, g, b) =>
                                     ((map eraseNamesPat pl), eraseNames (addVars (varsOfPatternList pl) σᵥ) g, eraseNames (addVars (varsOfPatternList pl) σᵥ) b))
                                     l)
 | BigStep.Syntax.ELet l e1 e2 => ELet (length l) (eraseNames σᵥ e1) (eraseNames (addVars l σᵥ) e2)
 | BigStep.Syntax.ESeq e1 e2 => ESeq (eraseNames σᵥ e1) (eraseNames σᵥ e2)
 | BigStep.Syntax.ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) =>
                                           (length vl, eraseNames (addNames (map (inr ∘ fst) l ++ map inl vl) σᵥ) e)
                                         ) l)
                                          (eraseNames (addFids (map fst l) σᵥ) e)
 | BigStep.Syntax.EMap l => EMap (map (fun '(x, y) => (eraseNames σᵥ x, eraseNames σᵥ y)) l)
 | BigStep.Syntax.ETry e1 vl1 e2 vl2 e0 => ETry (eraseNames σᵥ e1)
                                                (length vl1) (eraseNames (addVars vl1 σᵥ) e2)
                                                (length vl2) (eraseNames (addVars vl1 σᵥ) e0)
end.

End EraseNames.




















From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.BigStep Require Import Environment.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
Require Import stdpp.list.


Import BigStep.


Section MesureTypes.



  Fixpoint measure_exp (e : Expression) 
                      : nat :=
                      
    let 
      measure_exp_list (el : list Expression) 
                      : nat :=

        list_sum (map measure_exp el)
    in

    let 
      measure_exp_map (epl : list (Expression * Expression)) 
                     : nat :=

        list_sum (map (fun '(x, y) => (measure_exp x) + (measure_exp y)) epl)
    in

    let 
      measure_exp_case (l : list ((list Pattern) * Expression * Expression)) 
                      : nat :=

        list_sum (map (fun '(pl, g, b) => (measure_exp g) + (measure_exp b)) l)
    in 

    let
      measure_exp_letrec (l : list (FunctionIdentifier * (list Var * Expression))) 
                        : nat :=

        list_sum (map (fun '(fid, (vl, b)) => (measure_exp b)) l)
    in

    match e with

    | EValues el => 1 
        + (measure_exp_list el)

    | ENil => 1
    | ELit l => 1
    | EVar v => 1
    | EFunId f => 1

    | EFun vl e => 1 
        + (measure_exp e)

    | ECons hd tl => 1 
        + (measure_exp hd) 
        + (measure_exp tl)

    | ETuple l => 1 
        + (measure_exp_list l)

    | ECall m f l => 1 
        + (measure_exp m) 
        + (measure_exp f) 
        + (measure_exp_list l)

    | EPrimOp f l => 1 
        + (measure_exp_list l)

    | EApp exp l => 1 
        + (measure_exp exp) 
        + (measure_exp_list l)

    | ECase e l => 1 
        + (measure_exp e) 
        + (measure_exp_case l)

    | ELet l e1 e2 => 1 
        + (measure_exp e1) 
        + (measure_exp e2)

    | ESeq e1 e2 => 1 
        + (measure_exp e1) 
        + (measure_exp e2)

    | ELetRec l e => 1 
        + (measure_exp_letrec l) 
        + (measure_exp e)

    | EMap l => 1 
        + (measure_exp_map l)

    | ETry e1 vl1 e2 vl2 e0 => 1 
        + (measure_exp e1) 
        + (measure_exp e2) 
        + (measure_exp e0)

    end.



  Fixpoint measure_val (v : Value) 
                      : nat :=

    let
      measure_val_list (vl : list Value) 
                      : nat :=

        list_sum (map measure_val vl)
    in

    let 
      measure_val_map (vm : list (Value * Value)) 
                     : nat :=

        list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) vm)
    in

    let 
      measure_val_env (env : Environment) 
                     : nat :=

        list_sum (map (fun '(x, y) => (measure_val y)) env)
    in

    match v with

    | VNil => 1
    | VLit l => 1

    | VClos env ext id vl e fid => 1 
        + (measure_val_env env) 
        + (measure_exp e)

    | VCons hd tl => 1 
        + (measure_val hd) 
        + (measure_val tl)

    | VTuple l => 1 
        + (measure_val_list l) 

    | VMap l => 1 
        + (measure_val_map l)

    end.



  Definition measure_subst_env (env : Environment) 
                              (e : Expression) 
                              : nat :=
                            
    let 
      measure_env (env : Environment) 
                 : nat :=

        list_sum (map (fun '(x, y) => (measure_val y)) env)
    in

    (measure_exp e) + (measure_env env).



End MesureTypes.
































Section Conv.


  Fixpoint val_to_exp (subst_env : Environment -> Expression -> Expression) 
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

    | VCons hd tl => ECons (val_to_exp subst_env hd) (val_to_exp subst_env tl)
    | VTuple l => ETuple (map (val_to_exp subst_env) l)
    | VMap l => EMap (map (prod_map (val_to_exp subst_env) (val_to_exp subst_env)) l)

    end.



  Definition bs_to_fs_exp f 
                          (e : Expression) 
                          : Exp :=

    eraseNames f e.




  Definition bs_to_fs_exp_env f 
                              (subst_env : nat -> Environment -> Expression -> Expression) 
                              (e : Expression) 
                              (env : Environment) 
                              : Exp :=

    bs_to_fs_exp f 
                (subst_env (measure_subst_env env 
                                             e) 
                           env 
                           e).







  Fixpoint exp_to_val_fs (e : Exp) 
                           : option Val :=

    match e with
    | VVal v => Some v
    | EExp e' => 
        match e' with
        | Syntax.EFun vl e'' => Some (Syntax.VClos [] 0 vl e'')
        | Syntax.EValues el => 
            match (mapM exp_to_val_fs el) with
            | Some el' => Some (Syntax.VTuple el')
            | None => None
            end
        | Syntax.ECons hd tl => 
            match (exp_to_val_fs hd), 
                  (exp_to_val_fs tl) with
            | Some hd', Some tl' => Some (Syntax.VCons hd' tl')
            | _, _ => None
            end
        | Syntax.ETuple l => 
            match (mapM exp_to_val_fs l) with
            | Some l' => Some (Syntax.VTuple l')
            | None => None
            end
        | Syntax.EMap l => 
            match (mapM (fun '(x, y) => 
                          match (exp_to_val_fs x), 
                                (exp_to_val_fs y) with
                          | Some x', Some y' => Some (x', y')
                          | _, _ => None
                          end) l) with
            | Some l' => Some (Syntax.VMap l')
            | None => None
            end
        | Syntax.ECall m f l => None
            (*
            match (exp_to_val_fs m), 
                  (exp_to_val_fs f), 
                  (mapM exp_to_val_fs l) with
            | Some m', Some f', Some l' => Some (Syntax.VTuple (m' :: f' :: l'))
            | _, _, _ => None
            end
            *)
        | Syntax.EPrimOp f l => None
            (*
            match (mapM exp_to_val_fs l) with
            | Some l' => Some (Syntax.VTuple l')
            | None => None
            end
            *)
        | Syntax.EApp exp l =>  None
            (*
            match (exp_to_val_fs exp), 
                  (mapM exp_to_val_fs l) with
            | Some exp', Some l' => Some (Syntax.VTuple (exp' :: l'))
            | _, _ => None
            end
            *)
        | Syntax.ECase e' l => None
            (*
            match (exp_to_val_fs e'), 
                  (mapM (fun '(pl, g, b) => 
                          match (exp_to_val_fs g), 
                                (exp_to_val_fs b) with
                          | Some g', Some b' => Some (pl, g', b')
                          | _, _ => None
                          end) l) with
            | Some e', Some l' => Some (Syntax.VTuple (e' :: l'))
            | _, _ => None
            end
            *)
        | Syntax.ELet l e1 e2 =>  None
            (*
            match (exp_to_val_fs e1), 
                  (exp_to_val_fs e2) with
            | Some e1', Some e2' => Some (Syntax.VTuple [e1'; e2'])
            | _, _ => None
            end
            *)
        | Syntax.ESeq e1 e2 =>  None
            (*
            match (exp_to_val_fs e1), 
                  (exp_to_val_fs e2) with
            | Some e1', Some e2' => Some (Syntax.VTuple [e1'; e2'])
            | _, _ => None
            end
            *)
        | Syntax.ELetRec l e =>  None
            (*
            match (mapM (fun '(fid, (vl, b)) => 
                          match (exp_to_val_fs b) with
                          | Some b' => Some (fid, vl, b')
                          | None => None
                          end) l), 
                  (exp_to_val_fs e) with
            | Some l', Some e' => Some (Syntax.VTuple (e' :: l'))
            | _, _ => None
            end
            *)
        | Syntax.ETry e1 vl1 e2 vl2 e0 =>  None
            (*
            match (exp_to_val_fs e1), 
                  (exp_to_val_fs e2), 
                  (exp_to_val_fs e0) with
            | Some e1', Some e2', Some e0' => Some (Syntax.VTuple [e1'; e2'; e0'])
            | _, _, _ => None
            end
            *)
        end
    end.


  Definition bs_to_fs_val f 
                          (subst_env : nat -> Environment -> Expression -> Expression) 
                          (v : Value) 
                          : option Val :=

    exp_to_val_fs (bs_to_fs_exp f 
                                (val_to_exp (subst_env (measure_val v)) 
                                            v)).


  Definition bs_to_fs_valseq f 
                             (subst_env : nat -> Environment -> Expression -> Expression) 
                             (vs : ValueSequence) 
                             : option ValSeq :=

    mapM (bs_to_fs_val f subst_env) vs.


  Definition bs_to_fs_exc f
                          (subst_env : nat -> Environment -> Expression -> Expression) 
                          (exc : Exception)
                          : option CoreErlang.Syntax.Exception :=
    match exc with

    | (excc, v1, v2) => 

        match (bs_to_fs_val f subst_env v1), 
              (bs_to_fs_val f subst_env v2) with

        | Some v1', Some v2' => 

            match excc with
            | Error => Some (CoreErlang.Syntax.Error, v1', v2')
            | Throw => Some (CoreErlang.Syntax.Throw, v1', v2')
            | Exit => Some (CoreErlang.Syntax.Exit, v1', v2')
            end

        | _, _ => None
        end
    end.



  Definition bs_to_fs_res f 
                          (subst_env : nat -> Environment -> Expression -> Expression)
                          (res : (ValueSequence + Exception))
                          : option Redex :=
    
    match res with

    | inl vs => 
        match (bs_to_fs_valseq f subst_env vs) with
        | Some vs' => Some (RValSeq vs')
        | None => None
        end

    | inr exc => 
        match (bs_to_fs_exc f subst_env exc) with
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
            | Some [v'] => val_to_exp (subst_env fuel') v'
            | Some vs => EValues (map (val_to_exp (subst_env fuel')) vs)
            | _ => EVar v
            end

        | EFunId f => 
            match (get_value Γ (inr f)) with
            | Some [f'] => val_to_exp (subst_env fuel') f'
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

  	  Some r = bs_to_fs_res f subst_env e'

(* wellformed_map r (valseq,exc) later on top level *)

  	  ->

  	  ⟨ [], (bs_to_fs_exp_env f subst_env e env) ⟩
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
      - cbn.
        do 1 do_step.
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