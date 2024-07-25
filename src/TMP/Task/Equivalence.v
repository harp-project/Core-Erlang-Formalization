From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.BigStep Require Import Environment.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
From CoreErlang.TMP.Task Require Import EraseNames.

Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import stdpp.list.

Import BigStep.
Import ListNotations.






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






Section ConvertTypes.


  (* 
      BigStep
      Value -> Expression
  *)
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



  Fixpoint val_to_exp_opt (subst_env : Environment -> Expression -> option Expression) 
                          (v : Value) 
                          : option Expression :=

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
              : option (list (FunctionIdentifier * (list Var * Expression))) :=

        mapM (fun x => 
                match x with
                | (n, fid, (vl, e)) => 
                    match (subst_env (rem_from_env_vl env vl) e) with
                    | Some e' => Some (fid, (vl, e'))
                    | None => None
                    end
                end) 
            ext
    in

    let 
      map_map (x y : Value) 
              : option (Expression * Expression) :=

        match (val_to_exp_opt subst_env x), 
              (val_to_exp_opt subst_env y) with

        | Some x', Some y' => Some (x', y')
        | _, _ => None
        end
    in

    match v with

    | VNil => Some ENil
    | VLit l => Some (ELit l)

    | VClos env ext id vl e fid => 

        match ext, fid with

        | [], _ => 
            match (subst_env (rem_from_env_vl env vl) e) with
            | Some e' => Some (EFun vl e')
            | None => None
            end

        | _, None => None

        | _, Some fid' => 
            match (map_ext (rem_from_env_fids env ext) ext) with
            | Some ext' => Some (ELetRec ext' (EFunId fid'))
            | None => None
            end

        end

    | VCons hd tl => 
        match (val_to_exp_opt subst_env hd), 
              (val_to_exp_opt subst_env tl) with

        | Some hd', Some tl' => Some (ECons hd' tl')
        | _, _ => None
        end

    | VTuple l => 
        match (mapM (val_to_exp_opt subst_env) l) with
        | Some l' => Some (ETuple l')
        | None => None
        end

    | VMap l => 
        match (mapM (fun '(x, y) => map_map x y) l) with
        | Some l' => Some (EMap l')
        | None => None
        end

    end.


  (* 
      BigStep -> FrameStack
      Expression -> Exp
  *)
  Definition bs_to_fs_exp f 
                          (e : Expression) 
                          : Exp :=

    eraseNames f e.



  (* 
      BigStep -> FrameStack
      Expression -> Exp
      with environment substitution
  *)
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



  Definition bs_to_fs_exp_env_opt f 
                                  (subst_env : nat -> Environment -> Expression -> option Expression) 
                                  (e : Expression) 
                                  (env : Environment) 
                                  : option Exp :=

    match (subst_env (measure_subst_env env e) env e) with
    | Some e' => Some (bs_to_fs_exp f e')
    | None => None
    end.



  (*
      FrameStack
      Exp -> Val
  *)
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



  (*
      BigStep -> FrameStack
      Value -> Val
  *)
  Definition bs_to_fs_val f 
                          (subst_env : nat -> Environment -> Expression -> Expression) 
                          (v : Value) 
                          : option Val :=

    exp_to_val_fs (bs_to_fs_exp f 
                                (val_to_exp (subst_env (measure_val v)) 
                                            v)).



  Definition bs_to_fs_val_opt f 
                              (subst_env : nat -> Environment -> Expression -> option Expression) 
                              (v : Value) 
                              : option Val :=

    match (val_to_exp_opt (subst_env (measure_val v)) v) with
    | Some e => exp_to_val_fs (bs_to_fs_exp f e)
    | None => None
    end.



  (*
      BigStep -> FrameStack
      ValueSequence -> ValSeq
  *)
  Definition bs_to_fs_valseq f 
                             (subst_env : nat -> Environment -> Expression -> Expression) 
                             (vs : ValueSequence) 
                             : option ValSeq :=

    mapM (bs_to_fs_val f subst_env) vs.



  Definition bs_to_fs_valseq_opt f 
                                 (subst_env : nat -> Environment -> Expression -> option Expression) 
                                 (vs : ValueSequence) 
                                 : option ValSeq :=

    mapM (bs_to_fs_val_opt f subst_env) vs.



  (*
      BigStep -> FrameStack
      Exception -> Exception
  *)
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
  


  Definition bs_to_fs_exc_opt f
                              (subst_env : nat -> Environment -> Expression -> option Expression) 
                              (exc : Exception)
                              : option CoreErlang.Syntax.Exception :=
    match exc with

    | (excc, v1, v2) => 

        match (bs_to_fs_val_opt f subst_env v1), 
              (bs_to_fs_val_opt f subst_env v2) with

        | Some v1', Some v2' => 

            match excc with
            | Error => Some (CoreErlang.Syntax.Error, v1', v2')
            | Throw => Some (CoreErlang.Syntax.Throw, v1', v2')
            | Exit => Some (CoreErlang.Syntax.Exit, v1', v2')
            end

        | _, _ => None
        end
    end.


  (*
      BigStep -> FrameStack
      (ValueSequence + Exception) -> Redex
  *)
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



  Definition bs_to_fs_res_opt f 
                              (subst_env : nat -> Environment -> Expression -> option Expression)
                              (res : (ValueSequence + Exception))
                              : option Redex :=
    
    match res with

    | inl vs => 
        match (bs_to_fs_valseq_opt f subst_env vs) with
        | Some vs' => Some (RValSeq vs')
        | None => None
        end

    | inr exc => 
        match (bs_to_fs_exc_opt f subst_env exc) with
        | Some exc' => Some (RExc exc')
        | None => None
        end
        
    end.



End ConvertTypes.






Section SubstEnviroment.



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



  Fixpoint subst_env_opt (fuel : nat) 
                         (Γ : Environment) 
                         (e : Expression) 
                         : option Expression :=
    
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

    let
      subst_env_case (fuel : nat) 
                    (Γ : Environment)
                    (pl : list Pattern)
                    (g : Expression)
                    (b : Expression)
                    : option ((list Pattern) * Expression * Expression) :=
        
        match (subst_env_opt fuel Γ g),
              (subst_env_opt fuel Γ b) with

        | Some g', Some b' => Some (pl, g', b')
        | _, _ => None
        end
    in

    let 
      subst_env_letrec (fuel : nat) 
                       (Γ : Environment)
                       (fid : FunctionIdentifier)
                       (vl : list Var)
                       (b : Expression)
                       : option (FunctionIdentifier * (list Var * Expression)) :=

        match (subst_env_opt fuel Γ b) with
        | Some b' => Some (fid, (vl, b'))
        | None => None
        end
    in

    let 
      subst_env_map (fuel : nat) 
                    (Γ : Environment)
                    (x : Expression)
                    (y : Expression)
                    : option (Expression * Expression) :=

        match (subst_env_opt fuel Γ x), 
              (subst_env_opt fuel Γ y) with

        | Some x', Some y' => Some (x', y')
        | _, _ => None
        end
    in

    match fuel with
    | O => None
    | S fuel' =>
        match e with

        | EValues el => 
            match (mapM (subst_env_opt fuel' Γ) el) with
            | Some el' => Some (EValues el')
            | None => None
            end

        | ENil => Some ENil
        | ELit l => Some (ELit l)

        | EVar v => 
            match (get_value Γ (inl v)) with
            | Some [v'] => val_to_exp_opt (subst_env_opt fuel') v'
            | Some vs => match (mapM (val_to_exp_opt (subst_env_opt fuel')) vs) with
                         | Some vs' => Some (EValues vs')
                         | None => None
                        end
            | _ => Some (EVar v)
            end

        | EFunId f => 
            match (get_value Γ (inr f)) with
            | Some [f'] => val_to_exp_opt (subst_env_opt fuel') f'
            | _ => Some (EFunId f)
            end

        | EFun vl e => 
            match (subst_env_opt fuel' Γ e) with
            | Some e' => Some (EFun vl e')
            | None => None
            end

        | ECons hd tl => 
            match (subst_env_opt fuel' Γ hd), (subst_env_opt fuel' Γ tl) with
              | Some hd', Some tl' => Some (ECons hd' tl')
              | _, _ => None
            end

        | ETuple l => 
            match (mapM (fun x => subst_env_opt fuel' Γ x) l) with
            | Some l' => Some (ETuple l')
            | None => None
            end

        | ECall m f l => 
            match (subst_env_opt fuel' Γ m), 
                  (subst_env_opt fuel' Γ f), 
                  (mapM (fun x => subst_env_opt fuel' Γ x) l) with

            | Some m', Some f', Some l' => Some (ECall m' f' l')
            | _, _, _ => None
            end

        | EPrimOp f l => 
            match (mapM (fun x => subst_env_opt fuel' Γ x) l) with
            | Some l' => Some (EPrimOp f l')
            | None => None
            end

        | EApp exp l => 
            match (subst_env_opt fuel' Γ exp), 
                  (mapM (fun x => subst_env_opt fuel' Γ x) l) with

            | Some exp', Some l' => Some (EApp exp' l')
            | _, _ => None
            end

        | ECase e l => 
            match (subst_env_opt fuel' Γ e), 
                  (mapM (fun '(pl, g, b) => subst_env_case fuel' Γ pl g b) l) with

            | Some e', Some l' => Some (ECase e' l')
            | _, _ => None
            end

        | ELet l e1 e2 => 
            match (subst_env_opt fuel' Γ e1), 
                  (subst_env_opt fuel' (rem_from_env_vl Γ l) e2) with

            | Some e1', Some e2' => Some (ELet l e1' e2')
            | _, _ => None
            end

        | ESeq e1 e2 => 
            match (subst_env_opt fuel' Γ e1), 
                  (subst_env_opt fuel' Γ e2) with

            | Some e1', Some e2' => Some (ESeq e1' e2')
            | _, _ => None
            end

        | ELetRec l e => 
            match (mapM (fun '(fid, (vl, b)) => subst_env_letrec fuel' (rem_from_env_fids_vl Γ l vl) fid vl b) l), 
                  (subst_env_opt fuel' (rem_from_env_fids Γ l) e) with

            | Some l', Some e' => Some (ELetRec l' e')
            | _, _ => None
            end

        | EMap l => 
            match (mapM (fun '(x, y) => subst_env_map fuel' Γ x y) l) with
            | Some l' => Some (EMap l')
            | None => None
            end

        | ETry e1 vl1 e2 vl2 e0 => 
            match (subst_env_opt fuel' Γ e1), 
                  (subst_env_opt fuel' Γ e2), 
                  (subst_env_opt fuel' Γ e0) with

            | Some e1', Some e2', Some e0' => Some (ETry e1' vl1 e2' vl2 e0')
            | _, _, _ => None
            end
        end
    end.



End SubstEnviroment.






Section Test.



  (*
    env = []
    fun() -> 1
    fun() -> 1
  *)
  Lemma test_val_to_exp_1 : 
    val_to_exp (subst_env 10) 
               (VClos [] 
                      [] 
                      0 
                      [] 
                      (ELit (Integer 1)) 
                      None) 
    = 
    EFun [] (ELit (Integer 1)).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = []
    fun(x) -> y
    fun(x) -> y
  *)
  Lemma test_val_to_exp_2 : 
    val_to_exp (subst_env 10) 
               (VClos [] 
                      [] 
                      0 
                      ["x"] 
                      (EVar "y") 
                      None) 
    = 
    EFun ["x"] (EVar "y").
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [y = 1]
    fun(x) -> y
    fun(x) -> 1
  *)
  Lemma test_val_to_exp_3 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "y" , VLit (Integer 1))] 
                      [] 
                      0 
                      ["x"] 
                      (EVar "y") 
                      None) 
    = 
    EFun ["x"] (ELit (Integer 1)).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1]
    fun(x) -> x
    fun(x) -> x
  *)
  Lemma test_val_to_exp_4 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "x" , VLit (Integer 1))] 
                      [] 
                      0 
                      ["x"] 
                      (EVar "x") 
                      None) 
    = 
    EFun ["x"] (EVar "x").
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1; y = 1]
    fun(x) -> x , y
    fun(x) -> x , 1
  *)
  Lemma test_val_to_exp_5 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "x" , VLit (Integer 1));
                       (inl "y" , VLit (Integer 1))] 
                      [] 
                      0 
                      ["x"] 
                      (EValues [EVar "x"; EVar "y"])
                      None) 
    = 
    EFun ["x"] (EValues [EVar "x"; ELit (Integer 1)]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1; y = 1]
    fun(x) -> x + y
    fun(x) -> x + 1
  *)
  Lemma test_val_to_exp_6 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "x" , VLit (Integer 1));
                       (inl "y" , VLit (Integer 1))] 
                      [] 
                      0 
                      ["x"] 
                      (ECall (ELit (Atom "erlang")) 
                              (ELit (Atom "+")) 
                              [EVar "x"; EVar "y"])
                      None) 
    = 
    EFun ["x"] (ECall (ELit (Atom "erlang")) 
                      (ELit (Atom "+")) 
                      [EVar "x"; ELit (Integer 1)]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1; y = 1]
    fun(x,y) -> x + y
    fun(x,y) -> x + y
  *)
  Lemma test_val_to_exp_7 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "x" , VLit (Integer 1));
                       (inl "y" , VLit (Integer 1))] 
                      [] 
                      0 
                      ["x"; "y"] 
                      (ECall (ELit (Atom "erlang")) 
                              (ELit (Atom "+")) 
                              [EVar "x"; EVar "y"])
                      None) 
    = 
    EFun ["x"; "y"] (ECall (ELit (Atom "erlang")) 
                           (ELit (Atom "+")) 
                           [EVar "x"; EVar "y"]).
  Proof.
    cbn. reflexivity.
  Qed.



  (* -- Function param without FunId *)



  (*
    env = [y = fun(z) -> z]
    fun(x) -> y
    fun(x) -> (fun(z) -> z)
  *)
  Lemma test_val_to_exp_8 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "y" , (VClos [] 
                                         [] 
                                         0 
                                         ["z"] 
                                         (EVar "z") 
                                         None))] 
                      [] 
                      0 
                      ["x"] 
                      (EVar "y") 
                      None) 
    = 
    EFun ["x"] (EFun ["z"] (EVar "z")).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [y = fun(x) -> x; z = 1; x = 2]
    fun(x) -> z , y , x
    fun(x) -> 1 , (fun(x) -> x) , x
  *)
  Lemma test_val_to_exp_9 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "y" , (VClos [] 
                                         [] 
                                         0 
                                         ["x"] 
                                         (EVar "x") 
                                         None));
                       (inl "z" , VLit (Integer 1));
                       (inl "x" , VLit (Integer 2))] 
                    [] 
                    0 
                    ["x"] 
                    (EValues [EVar "z"; EVar "y"; EVar "x"]) 
                    None) 
    = 
    EFun ["x"] (EValues [ELit (Integer 1); 
                         EFun ["x"] (EVar "x"); 
                         EVar "x"]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [y = fun(x) -> (x , z); z = 1; x = 2]
    fun(x) -> z , y , x
    fun(x) -> 1 , (fun(x) -> (x , z)) , x
  *)
  Lemma test_val_to_exp_10 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "y" , (VClos [] 
                                         [] 
                                         0 
                                         ["x"] 
                                         (EValues [EVar "x"; EVar "z"]) 
                                         None));
                       (inl "z" , VLit (Integer 1));
                       (inl "x" , VLit (Integer 2))] 
                      [] 
                      0 
                      ["x"] 
                      (EValues [EVar "z"; EVar "y"; EVar "x"]) 
                      None) 
    = 
    EFun ["x"] (EValues [ELit (Integer 1); 
                         EFun ["x"] (EValues [EVar "x"; EVar "z"]); 
                         EVar "x"]).
  Proof.
    cbn. reflexivity.
  Qed.



  (* -- Function param with FunId *)



  (*
    env = [f/1 = fun(z) -> z]
    fun(x) -> f/1
    fun(x) -> (fun(z) -> z)
  *)
  Lemma test_val_to_exp_11 : 
    val_to_exp (subst_env 10) 
               (VClos [(inr ("f" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["z"] 
                                               (EVar "z") 
                                               None))] 
                      [] 
                      0 
                      ["x"] 
                      (EFunId ("f" , 1)) 
                      None) 
    = 
    EFun ["x"] (EFun ["z"] (EVar "z")).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [f/1 = fun(x) -> x; z = 1; x = 2]
    fun(x) -> z , f/1 , x
    fun(x) -> 1 , (fun(x) -> x) , x
  *)
  Lemma test_val_to_exp_12 : 
    val_to_exp (subst_env 10) 
               (VClos [(inr ("f" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["x"] 
                                               (EVar "x") 
                                               None));
                       (inl "z" , VLit (Integer 1));
                       (inl "x" , VLit (Integer 2))] 
                      [] 
                      0 
                      ["x"] 
                      (EValues [EVar "z"; EFunId ("f" , 1); EVar "x"]) 
                      None) 
    = 
    EFun ["x"] (EValues [ELit (Integer 1); 
                         EFun ["x"] (EVar "x"); 
                         EVar "x"]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [f/1 = fun(x) -> (x , z); z = 1; x = 2]
    fun(x) -> z , f/1 , x
    fun(x) -> 1 , (fun(x) -> (x , z)) , x
  *)
  Lemma test_val_to_exp_13 : 
    val_to_exp (subst_env 10) 
               (VClos [(inr ("f" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["x"] 
                                               (EValues [EVar "x"; EVar "z"]) 
                                               None));
                       (inl "z" , VLit (Integer 1));
                       (inl "x" , VLit (Integer 2))] 
                      [] 
                      0 
                      ["x"] 
                      (EValues [EVar "z"; EFunId ("f" , 1); EVar "x"]) 
                      None) 
    = 
    EFun ["x"] (EValues [ELit (Integer 1); 
                         EFun ["x"] (EValues [EVar "x"; EVar "z"]); 
                         EVar "x"]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [f/1 = fun(z,y) -> (z , y , x) [y = 1; x = 3]; z = 1; x = 2]
    fun(x) -> z , f/2 , x
    fun(x) -> 1 , (fun(z,y) -> (z , y , 3)) , x
  *)
  Lemma test_val_to_exp_14 : 
    val_to_exp (subst_env 10) 
               (VClos [(inr ("f" , 2) , (VClos [(inl "y" , VLit (Integer 1));
                                                (inl "x" , VLit (Integer 3))] 
                                               [] 
                                               0 
                                               ["z"; "y"] 
                                               (EValues [EVar "z"; EVar "y"; EVar "x"]) 
                                               None));
                       (inl "z" , VLit (Integer 1));
                       (inl "x" , VLit (Integer 2))] 
                      [] 
                      0 
                      ["x"] 
                      (EValues [EVar "z"; EFunId ("f" , 2); EVar "x"]) 
                      None) 
    = 
    EFun ["x"] (EValues [ELit (Integer 1); 
                         EFun ["z"; "y"] (EValues [EVar "z"; EVar "y"; ELit (Integer 3)]); 
                         EVar "x"]).
  Proof.
    cbn. reflexivity.
  Qed.



  (* -- Recurzive *)



  (*
    env = []
    f/1 = fun(x) -> x
    f/1 = fun(x) -> x
  *)
  Lemma test_val_to_exp_15 : 
    val_to_exp (subst_env 10) 
               (VClos [] 
                      [(1 , ("f" , 1) , (["x"] , (EVar "x")))]
                      0 
                      [] 
                      (ENil) 
                      (Some ("f" , 1))) 
    = 
    ELetRec [("f", 1, (["x"], EVar "x"))] (EFunId ("f", 1)).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = []
    f/1 = fun(x) -> x , i/1, f/2, f/1 , g/1
    g/1 = fun(x) -> y , x , g/1 , h/1
    h/1 = fun(x) -> y , x , f/1 , h/1
    -
    f/1 = fun(x) -> x , i/1, f/2, f/1 , g/1
    g/1 = fun(x) -> y , x , g/1 , h/1
    h/1 = fun(x) -> y , x , f/1 , h/1
  *)
  Lemma test_val_to_exp_16 : 
    val_to_exp (subst_env 10) 
               (VClos [] 
                      [(1 , ("f" , 1) , (["x"] , (EValues [EVar "x"; 
                                                           EFunId ("i" , 1);
                                                           EFunId ("f" , 2);
                                                           EFunId ("f" , 1);
                                                           EFunId ("g" , 1)])));
                       (2 , ("g" , 1) , (["x"] , (EValues [EVar "y"; 
                                                           EVar "x";
                                                           EFunId ("g" , 1);
                                                           EFunId ("h" , 1)])));
                       (3 , ("h" , 1) , (["y"] , (EValues [EVar "y";
                                                           EVar "x"; 
                                                           EFunId ("f" , 1);
                                                           EFunId ("h" , 1)])))]
                      0 
                      [] 
                      (ENil) 
                      (Some ("f" , 1))) 
    = 
    ELetRec [("f", 1, (["x"], EValues [EVar "x"; 
                                       EFunId ("i", 1);
                                       EFunId ("f", 2);
                                       EFunId ("f", 1); 
                                       EFunId ("g", 1)])); 
             ("g", 1, (["x"], EValues [EVar "y"; 
                                       EVar "x";
                                       EFunId ("g", 1); 
                                       EFunId ("h", 1)])); 
             ("h", 1, (["y"], EValues [EVar "y"; 
                                       EVar "x";
                                       EFunId ("f", 1); 
                                       EFunId ("h", 1)]))] 
           (EFunId ("f", 1)).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1; 
           y = 2; 
           z = 3;
           f/1 = fun(z) -> z; 
           g/1 = fun(z) -> z;
           h/1 = fun(z) -> z;
           i/1 = fun(z) -> z
           f/2 = fun(x,y) -> x , y , z]
    f/1 = fun(x) -> x , i/1, f/2, f/1 , g/1
    g/1 = fun(x) -> y , x , g/1 , h/1
    h/1 = fun(y) -> y , x , f/1 , h/1
    -
    f/1 = fun(x) -> x , (fun(z) -> z), (fun(x,y) -> x , y , z), f/1 , g/1
    g/1 = fun(x) -> 2 , x , g/1 , h/1
    h/1 = fun(y) -> y , 1 , f/1 , h/1
  *)
  Lemma test_val_to_exp_17 : 
    val_to_exp (subst_env 10) 
               (VClos [(inl "x" , VLit (Integer 1));
                       (inl "y" , VLit (Integer 2));
                       (inl "z" , VLit (Integer 3));
                       (inr ("f" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["z"] 
                                               (EVar "z") 
                                               None));
                       (inr ("g" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["z"] 
                                               (EVar "z") 
                                               None));
                       (inr ("h" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["z"] 
                                               (EVar "z") 
                                               None));
                       (inr ("i" , 1) , (VClos [] 
                                               [] 
                                               0 
                                               ["z"] 
                                               (EVar "z") 
                                               None));
                       (inr ("f" , 2) , (VClos [] 
                                               [] 
                                               0 
                                               ["x"; "y"] 
                                               (EValues [EVar "x"; EVar "y"; EVar "z"]) 
                                               None))] 
                      [(1 , ("f" , 1) , (["x"] , (EValues [EVar "x"; 
                                                           EFunId ("i" , 1);
                                                           EFunId ("f" , 2);
                                                           EFunId ("f" , 1);
                                                           EFunId ("g" , 1)])));
                       (2 , ("g" , 1) , (["x"] , (EValues [EVar "y"; 
                                                           EVar "x";
                                                           EFunId ("g" , 1);
                                                           EFunId ("h" , 1)])));
                       (3 , ("h" , 1) , (["y"] , (EValues [EVar "y";
                                                           EVar "x"; 
                                                           EFunId ("f" , 1);
                                                           EFunId ("h" , 1)])))]
                      0 
                      [] 
                      (ENil) 
                      (Some ("f" , 1))) 
    = 
    ELetRec [("f", 1, (["x"], EValues [EVar "x"; 
                                       EFun ["z"] (EVar "z");
                                       EFun ["x"; "y"] (EValues [EVar "x"; EVar "y"; EVar "z"]);
                                       EFunId ("f", 1); 
                                       EFunId ("g", 1)])); 
             ("g", 1, (["x"], EValues [ELit (Integer 2); 
                                       EVar "x";
                                       EFunId ("g", 1); 
                                       EFunId ("h", 1)])); 
             ("h", 1, (["y"], EValues [EVar "y"; 
                                       ELit (Integer 1);
                                       EFunId ("f", 1); 
                                       EFunId ("h", 1)]))] 
           (EFunId ("f", 1)).
  Proof.
    cbn. reflexivity.
  Qed.



  (* subst_env *)
  


  (*
    env = []
    x
    x
  *)
  Lemma test_subst_env_1 : 
    subst_env 10 
              [] 
              (EVar "x") 
    = 
    EVar "x".
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1]
    x
    1
  *)
  Lemma test_subst_env_2 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1))] 
              (EVar "x") 
    = 
    ELit (Integer 1).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1;
           y = 2;
           z = fun(x) -> x , y]
    <x , y , z>
    <1 , 2 , fun(x) -> x , y>
  *)
  Lemma test_subst_env_3 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1));
               (inl "y" , VLit (Integer 2));
               (inl "z" , VClos [] 
                                [] 
                                0 
                                ["x"] 
                                (EValues [EVar "x"; EVar "y"]) 
                                None)]
              (EValues [EVar "x"; EVar "y"; EVar "z"]) 
    = 
    (EValues [ELit (Integer 1); 
              ELit (Integer 2); 
              EFun ["x"] (EValues [EVar "x"; EVar "y"])]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1;
           y = 2;
           z = fun(x) -> x , y]
    x , y , app z [x]
    1 , 2 , app (fun(x) -> x , y) [1]
  *)
  Lemma test_subst_env_4 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1));
               (inl "y" , VLit (Integer 2));
               (inl "z" , VClos [] 
                                [] 
                                0 
                                ["x"] 
                                (EValues [EVar "x"; EVar "y"]) 
                                None)]
              (EValues [EVar "x"; EVar "y"; EApp (EVar "z") [EVar "x"]]) 
    = 
    EValues [ELit (Integer 1); 
             ELit (Integer 2); 
             EApp (EFun ["x"] 
                        (EValues [EVar "x"; EVar "y"])) 
                  [ELit (Integer 1)]].
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1;
           y = 2;
           z/1 = fun(x) -> x , y]
    x , y , app z/1 [x]
    1 , 2 , app (fun(x) -> x , y) [1]
  *)
  Lemma test_subst_env_5 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1));
               (inl "y" , VLit (Integer 2));
               (inr ("z" , 1) , VClos [] 
                                      [] 
                                      0 
                                      ["x"] 
                                      (EValues [EVar "x"; EVar "y"]) 
                                      None)]
              (EValues [EVar "x"; EVar "y"; EApp (EFunId ("z" , 1)) [EVar "x"]]) 
    = 
    EValues [ELit (Integer 1); 
             ELit (Integer 2); 
             EApp (EFun ["x"] 
                        (EValues [EVar "x"; EVar "y"])) 
                  [ELit (Integer 1)]].
  Proof.
    cbn. reflexivity.
  Qed.



  (* test bs_to_fs_res *)

  (*
    VNil 
      -> 
    Some [Syntax.VNil]
  *)
  Compute bs_to_fs_res (fun _ => 0) 
                        subst_env 
                        (inl [VNil]).
  
  (*
    VLit (Integer 1) 
      -> 
    Some [Syntax.VLit 1%Z]
  *)
  Compute bs_to_fs_res (fun _ => 0) 
                        subst_env 
                        (inl [VLit (Integer 1)]).

  (*
    VCons (VLit (Integer 1)) (VNil)
      -> 
    Some [Syntax.VCons (Syntax.VLit 1%Z) Syntax.VNil]
  *)
  Compute bs_to_fs_res (fun _ => 0) 
                        subst_env 
                        (inl [VCons (VLit (Integer 1)) (VNil)]).

  (*
    VTuple [VLit (Integer 1); VNil]
      -> 
    Some [Syntax.VTuple [Syntax.VLit 1%Z; Syntax.VNil]]
  *)
  Compute bs_to_fs_res (fun _ => 0) 
                        subst_env 
                        (inl [VTuple [VLit (Integer 1); VNil]]).

  (*
    VMap [(VLit (Integer 1) , VNil)]
      -> 
    Some [Syntax.VMap [(Syntax.VLit 1%Z, Syntax.VNil)]]

    Error!!!
  *)
  Compute bs_to_fs_res (fun _ => 0) 
                        subst_env 
                        (inl [VMap [(VLit (Integer 1) , VNil)]]).

  (*
    VClos [] [] 0 [] (ELit (Integer 1)) None
      -> 
    Some [Syntax.VClos [] 0 0 (˝ Syntax.VLit 1%Z)]

    Error!!!
  *)

  Compute bs_to_fs_res (fun _ => 0) 
                        subst_env 
                        (inl [VClos [] [] 0 [] (ELit (Integer 1)) None]).



  (* test bs_to_rs_valseq *)

  (*
    VNil 
      -> 
    Some [Syntax.VNil]
  *)
  Compute bs_to_fs_valseq (fun _ => 0) 
                          subst_env 
                          [VNil].

  (*
    VLit (Integer 1) 
      -> 
    Some [Syntax.VLit 1%Z]
  *)
  Compute bs_to_fs_valseq (fun _ => 0) 
                          subst_env 
                          [VLit (Integer 1)].

  (*
    VCons (VLit (Integer 1)) (VNil)
      -> 
    Some [Syntax.VCons (Syntax.VLit 1%Z) Syntax.VNil]
  *)

  Compute bs_to_fs_valseq (fun _ => 0) 
                          subst_env 
                          [VCons (VLit (Integer 1)) (VNil)].

  (*
    VTuple [VLit (Integer 1); VNil]
      -> 
    Some [Syntax.VTuple [Syntax.VLit 1%Z; Syntax.VNil]]

    Error!!!
  *)

  Compute bs_to_fs_valseq (fun _ => 0) 
                          subst_env 
                          [VTuple [VLit (Integer 1); VNil]].

  (*
    VMap [(VLit (Integer 1) , VNil)]
      -> 
    Some [Syntax.VMap [(Syntax.VLit 1%Z, Syntax.VNil)]]
  *)

  Compute bs_to_fs_valseq (fun _ => 0) 
                          subst_env 
                          [VMap [(VLit (Integer 1) , VNil)]].

  (*
    VClos [] [] 0 [] (ELit (Integer 1)) None
      -> 
    Some [Syntax.VClos [] 0 0 (˝ Syntax.VLit 1%Z)]
  *)

  Compute bs_to_fs_valseq (fun _ => 0) 
                          subst_env 
                          [VClos [] [] 0 [] (ELit (Integer 1)) None].
  
  
  
  (* test bs_to_fs_exp *)

  (*
    VNil 
      -> Theorem map_lambda :
  forall A B (f : A -> B) (l : list A),
    map f l = map (λ x, f x) l.
Proof.
  intros.
  reflexivity.
Qed.
    ˝ Syntax.VNil
  *)
  Compute bs_to_fs_exp (fun _ => 0) 
                       (val_to_exp (subst_env 100) 
                                   VNil).
  
  (*
    VLit (Integer 1) 
      -> 
    ˝ Syntax.VLit 1%Z
  *)
  Compute bs_to_fs_exp (fun _ => 0) 
                       (val_to_exp (subst_env 100) 
                                   (VLit (Integer 1))).

  (*
    VCons (VLit (Integer 1)) (VNil)
      -> 
    ° Syntax.ECons (˝ Syntax.VLit 1%Z) (˝ Syntax.VNil)
  *)
  Compute bs_to_fs_exp (fun _ => 0) 
                       (val_to_exp (subst_env 100) 
                                   (VCons (VLit (Integer 1)) VNil)).

  (*
    VTuple [VLit (Integer 1); VNil])
      -> 
    ° Syntax.ETuple [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]
  *)
  Compute bs_to_fs_exp (fun _ => 0) 
                       (val_to_exp (subst_env 100) 
                                   (VTuple [VLit (Integer 1); VNil])).

  (*
    VMap [(VLit (Integer 1) , VNil)]
      -> 
    ° Syntax.EMap [(˝ Syntax.VLit 1%Z, ˝ Syntax.VNil)]
  *)
  Compute bs_to_fs_exp (fun _ => 0) 
                       (val_to_exp (subst_env 100) 
                                   (VMap [(VLit (Integer 1) , VNil)])).

  (*
    VClos [] [] 0 [] (ELit (Integer 1)) None
      -> 
    ° Syntax.EFun 0 (˝ Syntax.VLit 1%Z)
  *)
  Compute bs_to_fs_exp (fun _ => 0) 
                       (val_to_exp (subst_env 100) 
                                   (VClos [] [] 0 [] (ELit (Integer 1)) None)).



  (* test exp_to_val_fs *)  

  (* VVal *)
  Compute exp_to_val_fs (˝ Syntax.VNil).
  Compute exp_to_val_fs (˝ Syntax.VLit 1%Z).
  Compute exp_to_val_fs (˝ Syntax.VPid 1).
  Compute exp_to_val_fs (˝ Syntax.VCons (Syntax.VLit 1%Z) (Syntax.VNil)).
  Compute exp_to_val_fs (˝ Syntax.VTuple [Syntax.VLit 1%Z; Syntax.VNil]).
  Compute exp_to_val_fs (˝ Syntax.VMap [(Syntax.VLit 1%Z, Syntax.VNil)]).
  Compute exp_to_val_fs (˝ Syntax.VVar 0).
  Compute exp_to_val_fs (˝ Syntax.VFunId (0 , 0)).
  Compute exp_to_val_fs (˝ Syntax.VClos [] 0 0 (˝ Syntax.VLit 1%Z)).

  (* VExp *)
  Compute exp_to_val_fs (° Syntax.EFun 0 (˝ Syntax.VLit 1%Z)).
  Compute exp_to_val_fs (° Syntax.EValues [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]).
  Compute exp_to_val_fs (° Syntax.ECons (˝ Syntax.VLit 1%Z) (˝ Syntax.VNil)).
  Compute exp_to_val_fs (° Syntax.ETuple [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]).
  Compute exp_to_val_fs (° Syntax.EMap [(˝ Syntax.VLit 1%Z, ˝ Syntax.VNil)]).
  Compute exp_to_val_fs (° Syntax.ECall (˝ Syntax.VLit 1%Z) (˝ Syntax.VLit 1%Z) [˝ Syntax.VNil]).
  Compute exp_to_val_fs (° Syntax.EPrimOp "" [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]).
  Compute exp_to_val_fs (° Syntax.EApp (˝ Syntax.VLit 1%Z) [˝ Syntax.VNil]).
  Compute exp_to_val_fs (° Syntax.ECase (˝ Syntax.VLit 1%Z) [([], ˝ Syntax.VLit 1%Z, ˝ Syntax.VLit 1%Z)]).
  Compute exp_to_val_fs (° Syntax.ELet 0 (˝ Syntax.VLit 1%Z) (˝ Syntax.VVar 0)).
  Compute exp_to_val_fs (° Syntax.ESeq (˝ Syntax.VLit 1%Z) (˝ Syntax.VLit 1%Z)).
  Compute exp_to_val_fs (° Syntax.ELetRec [(0, (˝ Syntax.VLit 1%Z))] (˝ Syntax.VVar 0)).
  Compute exp_to_val_fs (° Syntax.ETry (˝ Syntax.VLit 1%Z) 0 (˝ Syntax.VLit 1%Z) 0 (˝ Syntax.VLit 1%Z)).


  
  

  (* VExp *)               


End Test.






Section Eqvivalence_BigStep_to_FramStack.

  Ltac do_step := econstructor; [constructor;auto| simpl].

  Theorem measure_reduction : forall v n1 n2, 
    measure_val v <= n1 ->
    measure_val v <= n2 ->
    val_to_exp (subst_env n1) v = val_to_exp (subst_env n2) v.
  Proof.
  Admitted.

  Theorem measure_reduction_map :
    forall l v1 v2,
      list_sum (map measure_val l) <= measure_val v1 ->
      list_sum (map measure_val l) <= measure_val v2 ->
        map (val_to_exp (subst_env (measure_val v1))) l 
          =
        map (val_to_exp (subst_env (measure_val v2))) l.
  Proof.
  Admitted.

  Definition measure_val_pr 
    (v : Value * Value)  
    : nat :=
    
    match v with
    | (v1, v2) => 
      measure_val v1 +
      measure_val v2
    end.

  Theorem measure_reduction_prod_map :
    forall l v1 v2,
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) l) <= measure_val v1 ->
      list_sum (map (fun '(x, y) => (measure_val x) + (measure_val y)) l) <= measure_val v2 ->
        map (prod_map (val_to_exp (subst_env (measure_val v1))) 
                      (val_to_exp (subst_env (measure_val v1)))) 
            l
          =
        map (prod_map (val_to_exp (subst_env (measure_val v2))) 
                      (val_to_exp (subst_env (measure_val v2)))) 
            l.
  Proof.
  Admitted.

  Theorem measure_reduction_env :
    forall (env env' : list ((Var + FunctionIdentifier) * Value)) 
           (body : Expression) 
           (ref : list ((Var + FunctionIdentifier) * Value)) 
           (id : nat) 
           (params : list Var) 
           (funid : option FunctionIdentifier),
      (subst_env (list_sum (map (λ '(_, y), measure_val y) env)) env' body)
      =
      (subst_env (measure_val (VClos ref [] id params body funid)) env' body).
  Proof.
    (* Your proof here *)
  Admitted.

(*
  Theorem measure_reduction_env :
    forall env env' body ref id params funid,
      (subst_env (list_sum (map (λ '(_, y), measure_val y) env)) env' body)
      =
      (subst_env (measure_val (VClos ref [] id params body funid)) env' body).




⟨ [],
° Syntax.EFun (base.length params)
    (eraseNames (addVars params f)
       (subst_env (list_sum (map (λ '(_, y), measure_val y) env)) env' body)) ⟩ -->*
[Syntax.VClos [] 0 (base.length params)
   (eraseNames (addVars params f)
      (subst_env (measure_val (VClos ref [] id params body funid)) env' body))]
*)

  Theorem map_ite :
    forall {A B : Type} (f : A -> B) (a : A) (l : list A),
      map f (a :: l) = f a :: (map f l).
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Theorem mapM_ite : 
    forall {A B : Type} (f : A -> option B) (a : A) (l : list A),
      mapM f (a :: l) = match f a with
                        | None => None
                        | Some b => match mapM f l with
                                    | None => None
                                    | Some lb => Some (b :: lb)
                                    end
                        end.
  Proof.
    intros.
    simpl.
    reflexivity.
  Qed.

  Search mapM.

  Theorem mapM_ite1 : 
    forall {A B : Type} (f : A -> option B) (a : A) (l : list A) (b : B) (l' : list B),
      mapM f (a :: l) = Some (b :: l') ->
      f a = Some b /\ mapM f l = Some l'.
  Proof.
    intros.
    rewrite mapM_ite in H.
    remember (f a) as fa.
    remember (mapM f l) as fl.
    case_match. 2:
    {
      congruence.
    }
    case_match. 2:
    {
      congruence.
    }
    inversion H.
    split.
    * reflexivity.
    * reflexivity.
  Qed.

  Theorem refl_zero_step :
    forall Fs r k,
    ⟨ Fs, r ⟩ -[ k ]-> ⟨ Fs, r ⟩
    -> k = 0.
  Proof.
    intros.
    admit.
  Admitted.

 

  Theorem framestack_ident :
    forall ident el vl vl' r x eff Fs,
      create_result ident (vl ++ x :: vl') [] = Some (r , eff)
      -> list_biforall (fun e v => ⟨ [] , RExp e ⟩ -->* RValSeq [v]) el vl'
      -> exists k, ⟨ FParams ident vl el :: Fs, RValSeq [x] ⟩ -[ k ]-> ⟨ Fs, r ⟩.
  Proof.
    intros.
    generalize dependent r. generalize dependent vl'. revert vl. revert x.
    induction el; intros.
    {
      inv H0.
      exists 1. econstructor. econstructor. by symmetry.
      constructor.
    }
    {
      inv H0.
      destruct H3 as [khd [Hhd Dhd]].
      replace (vl ++ x :: hd' :: tl') with ((vl ++ [x]) ++ hd' :: tl') in H.
      2: {
        rewrite <- app_assoc.
        by rewrite <- app_cons_swap.
      }
      specialize (IHel _ _ _ H5 _ H). destruct IHel as [kIH DIH].
      eexists. econstructor. constructor.
      eapply transitive_eval.
      eapply frame_indep_core in Dhd. exact Dhd.
      simpl. exact DIH.
    }
  Qed.

  Theorem framestack_ident_rev :
    forall el ident vl e k r,
     ⟨ [FParams ident vl el], RExp e ⟩ -[ k ]-> ⟨ [], RValSeq r ⟩
     -> exists v vl' eff, 
          create_result ident (vl ++ v :: vl') [] = Some (RValSeq r, eff) /\ 
          list_biforall (λ (e0 : Exp) (v : Val), ⟨ [], RExp e0 ⟩ -->* RValSeq [v]) (e :: el) (v :: vl').
  Proof.
    induction el; intros.
    * Search step_rt.
      pose proof term_eval.
      pose proof terminates_in_k_eq_terminates_in_k_sem.
      unfold terminates_in_k_sem in H1.
      assert (is_result r).
      {
        constructor.
        admit. (*scope *)
      }
      pose proof conj H2 H.
      apply ex_intro with (x := RValSeq r) in H3.
      apply H1 in H3.
      apply H0 in H3. 2:
      {
        admit. (* scope *)
      }
      destruct H3 as [v [k0 [Hres [Hv Hk]]]].
      inv Hres.
      {
        pose proof transitive_eval_rev. (* H Hv *) (* inv H*)
        admit.
      }
      admit.
      
    * admit.
  Admitted.


  Theorem bs_to_fs_val_reduction :
    forall (v : Value) (f : NameSub) (env : Environment) (vs : ValSeq),
      bs_to_fs_val f subst_env v
        ≫= (λ y : Val, mret [y])
        = Some vs
      -> ⟨ [], eraseNames f
          (val_to_exp (subst_env (list_sum (map (λ '(_, y), measure_val y)
            env)))
          v) ⟩
         -->* vs.
  Proof.
    intros v f env.
    induction v using derived_Value_ind.
    * (* #1 VNil *)
      (* +1 Intro *)
      simpl.
      intros.
      inv H.
      (* +2 FrameStack Proof *)
      exists 1; split.
      - (* #1.1 Scope *)
        constructor.
        scope_solver.
      - (* #1.2 Step *)
        eapply step_trans.
        {
          constructor.
          scope_solver.
        }
        apply step_refl.
    * (* #2 VLit *)
      (* +1 Intro *)
      simpl.
      intros.
      inv H.
      (* +2 FrameStack Proof *)
      exists 1; split.
      - (* #2.1 Scope *)
        constructor.
        scope_solver.
      - (* #2.2 Step *)
        eapply step_trans.
        {
          constructor.
          scope_solver.
        }
        apply step_refl.
    * (* #3 VCons *)
      (* +1 Intro *)
      simpl.
      intros.
      (* rename [vs] *)
      rename H into Hvs.
      (* +2 Eliminate Cases *)
      (* case match [v1,v2] *)
      unfold bs_to_fs_val in *.
      remember 
        (subst_env (measure_val (VCons v1 v2))) 
        as _f_st.
      cbn in Hvs.
      (*v1*)
      case_match. 2:
      {
        cbn in Hvs.
        congruence.
      }
      (*v2*)
      case_match. 2:
      {
        cbn in Hvs.
        congruence.
      }
      (* inversion *)
      cbn in Hvs.
      inv Hvs.
      (* rename [v1',v2'] *)
      (*v1'*)
      rename v into v1'.
      rename H into Hv1'.
      (*v2'*)
      rename v0 into v2'.
      rename H0 into Hv2'.
      (* +3 Formalize Hypotheses *)
      (* measure reduction [v1,v2] *)
      (*v1*)
      rewrite measure_reduction 
        with (n2 := measure_val v1) 
        in Hv1'.
      2-3: slia.
      (*v2*)
      rewrite measure_reduction 
        with (n2 := measure_val v2) 
        in Hv2'.
      2-3: slia.
      (* +3 Specialize Hypotheses *)
      (* specialize [v1,v2] *)
      (*v1*)
      specialize (IHv1 [v1']).
      unfold bs_to_fs_exp in IHv1.
      rewrite Hv1' in IHv1.
      clear Hv1'.
      specialize (IHv1 eq_refl).
      (*v2*)
      specialize (IHv2 [v2']).
      unfold bs_to_fs_exp in IHv2.
      rewrite Hv2' in IHv2.
      clear Hv2'.
      specialize (IHv2 eq_refl).
      (* destruct hypothesis [v1,v2] *)
      destruct IHv1 as [kv1 [Hv1_res Hv1_step]].
      destruct IHv2 as [kv2 [Hv2_res Hv2_step]].
      (* +3 FrameStack Proof *)
      eexists; split. 
      + (* #3.1 Scope *)
        clear Hv1_step Hv2_step v1 v2 kv1 kv2 f env.
        constructor.
        inv Hv1_res.
        inv Hv2_res.
        destruct_foralls.
        scope_solver.
      + (* #3.2 Step *)
        clear Hv1_res Hv2_res.
        (*v2*)
        do 1 do_step.
        eapply transitive_eval.
        {
          eapply frame_indep_core in Hv2_step.
          exact Hv2_step.
        }
        simpl.
        clear Hv2_step v2 kv2.
        (*v1*)
        do 1 do_step.
        eapply transitive_eval.
        {
          eapply frame_indep_core in Hv1_step.
          exact Hv1_step.
        }
        simpl.
        clear Hv1_step v1 kv1.
        (*end*)
        clear f env.
        do 1 do_step.
        apply step_refl.
    * (* #4 VClos *)
      (* +1 Intro *)
      intros.
      clear H.
      (* rename [vs] *)
      rename H0 into Hvs.
      (* +2 Destruct Cases *)
      unfold bs_to_fs_val in *.
      remember 
        (subst_env (measure_val (VClos ref ext id params body funid)))
        as _f_st.
      remember
        (subst_env (list_sum (map (λ '(_, y), measure_val y) env)))
        as _f_st0.
      simpl in Hvs.
      remember
        (fold_left
          (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
             (key : Var + FunctionIdentifier),
             filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
          (map inl params) ref)
        as env'.
      (*ext*)
      destruct ext.
      - (* #4.1 [] *)
        cbn.
        inv Hvs.
        remember
          (fold_left
            (λ (env' : list ((Var + FunctionIdentifier) * Value)) 
               (key : Var + FunctionIdentifier),
               filter (λ '(k, _), negb (var_funid_eqb k key)) env') 
            (map inl params) ref)
          as env'.
        eexists; split.
        + constructor. 
          admit.
        + do 1 do_step.
          admit.
      - (* #4.2 _ :: _ *)
        (*funid*)
        destruct funid.
        + (* #4.2.1 Some *)
          cbn in Hvs.
          congruence.
        + (* #4.2.2 None *)
          cbn in Hvs.
          inv Hvs.
          admit.
      (* case match*)
    * (* #5 VTuple *)
      simpl.
      induction H.
      - (* #5.1 Base Step*)
        (* +1 Intro *)
        intros.
        cbn in *.
        clear f env.
        inv H.
        (* +2 FrameStack Proof *)
        exists 2. split. 
        + (* #5.1.1 Scope *)
          constructor.
          scope_solver.
        + (* #5.1.2 Step *)
          do 1 do_step.
          eapply step_trans.
          {
            econstructor.
            {
              congruence.
            }
            constructor.
          }
          apply step_refl.
      - (* #5.2 Inductive Step *)
        (* +1 Intro *)
        intros.
        clear H0.
        (* rename [v,vl,vs] *)
        (*v*)
        rename x into v.
        rename H into Hv.
        (*vl*)
        rename l into vl.
        rename IHForall into Hvl.
        (*vs*)
        rename H1 into Hvs.
        (* +2 Eliminate Cases *)
        (* case match [v] *)
        unfold bs_to_fs_val in *.
        remember 
          (subst_env (measure_val (VTuple (v :: vl))))
          as _f_st.
        simpl in Hvs.
        (*v*)
        case_match.
        2: {
          cbn in Hvs.
          congruence.
        }
        (* inversion *)
        cbn in Hvs.
        inv Hvs.
        (* rename [vl'] *)
        (*vl*)
        rename l into vl'.
        rename H into Hvl'.
        (* +3 Formalize Hypotheses *)
        (* measure reduction [v,vl] *)
        (*v*)
        rewrite measure_reduction 
          with (n2 := measure_val v) 
          in Hvl'.
        2-3: slia.
        (*vl*)
        rewrite measure_reduction_map 
          with (v2 := VTuple vl) 
          in Hvl'.
        2-3: slia.
        (* destruct expression [v,vl] *)
        (*v*)
        remember
          (exp_to_val_fs (bs_to_fs_exp f
            (val_to_exp (subst_env (measure_val v))
              v)))
          as _v_to_fs.
        destruct _v_to_fs as [v' |]. 2:
        {
          inversion Hvl'.
        }
        clear Heq_v_to_fs.
        (*v*)
        remember 
          (map (λ x : Expression, bs_to_fs_exp f x)
            (map (val_to_exp (subst_env (measure_val (VTuple vl))))
              vl))
          as _vl_to_fs.
        simpl in Hvl'.
        remember 
          (mapM exp_to_val_fs _vl_to_fs) 
          as _vl_to_el.
        destruct _vl_to_el as [vl'0 |]. 2:
        {
          inversion Hvl'.
        }
        (* inversion [vl'] *)
        simpl in Hvl'.
        inv Hvl'.
        (* rename [vl'] *)
        rename vl'0 into vl'.
        (* +4 Specialize Hypotheses *)
        (* specialize [v,vl] *)
        (*v*)
        specialize (Hv [v']).
        specialize (Hv eq_refl).
        (*vl*)
        specialize (Hvl [Syntax.VTuple vl']).
        remember 
          (subst_env (measure_val (VTuple vl)))
          as _f_st.
        simpl in Hvl.
        inv Heq_f_st.
        clear H.
        case_match. 2:
        {
          congruence.
        }
        clear H.
        symmetry in Heq_vl_to_el.
        inv Heq_vl_to_el.
        specialize (Hvl eq_refl).
        (* destruct hypothesis [v,vl] *)
        destruct Hv as [kv [Hv_res Hv_step]].
        destruct Hvl as [kvl [Hvl_res Hvl_step]].
        (* +5 Assert Theorem *)
        (* pose proof *)
        pose proof framestack_ident as Hident.
        remember
          (map (eraseNames f)
            (map (val_to_exp (subst_env (list_sum (map (λ '(_, y), measure_val y) env))))
              vl))
          as _el.
        remember
          (RValSeq [Syntax.VTuple (v' :: vl')])
          as _r.
        specialize (Hident ITuple _el [] vl' _r v' [] []).
        (* assert *)
        assert 
          (create_result ITuple ([] ++ v' :: vl') [] = 
          Some (_r, []))
          as Hr.
        {
          simpl.
          inv Heq_r.
          reflexivity.
        }
        (* apply *)
        inv Heq_r.
        clear H.
        apply Hident in Hr as Hvl. 2:
        {
          clear - Hvl_step.
          inv Hvl_step.
          inv H.
          inv H0.
          inv H. 2:
          {
            cbn. inv H8.
            inv H1.
            {
              apply biforall_nil.
            }
            inv H.
          }
          pose proof framestack_ident_rev _ _ _ _ _ _ H1.
          destruct H.
          destruct H.
          destruct H.
          destruct H.
          simpl in H.
          by inv H.
        }
        clear Hr Hident Hvl_step kvl.
        (* destruct hypothesis [vl] *)
        destruct Hvl as [kvl Hvl_step].
        (* +6 frame stack proof *)
        eexists. split.
        + (* #5.2.1 Scope *)
          clear Hvl_step kvl vl Hv_step kv v f env.
          constructor.
          inv Hv_res.
          inv Hvl_res.
          destruct_foralls.
          admit. (* scope_solver *)
        + (* #5.2.1 Scope *)
          clear Hvl_res Hv_res.
          do 2 do_step.
          (*v*)
          eapply transitive_eval.
          {
            eapply frame_indep_core in Hv_step.
            exact Hv_step.
          }
          clear Hv_step kv v.
          simpl.
          (*vl*)
          exact Hvl_step.
    * (* #6 VMap *)
      simpl.
      induction H.
      - (* #6.1 Base step *)
        (* +1 Intro *)
        intros.
        cbn in *.
        clear f env.
        inv H.
        (* +2 FrameStack Proof *)
        exists 1; split. 
        + (* #6.1.1 Scope *)
          constructor.
          scope_solver.
        + (* #6.1.2 Frame *)
          do 1 do_step.
          apply step_refl.
      - (* #6.2 Induction step *)
        (* +1 Intro *)
        intros.
        clear H0.
        (* destruct value [x] *)
        destruct x.
        simpl in H.
        (* destruct hypothesis [H] *)
        destruct H as [Hv1 Hv2].
        (* rename value [v1,v2,vl]*)
        rename v into v1.
        rename v0 into v2.
        rename l into vl.
        (* rename hypothesis [vl,vs]*)
        rename IHForall into Hvl.
        rename H1 into Hvs.
        (* +2 Eliminate Cases *)
        (* case match [v1,v2,vl] *)
        unfold bs_to_fs_val in *.
        remember
          (subst_env (measure_val (VMap ((v1, v2) :: vl)))) 
          as _f_st.
        simpl in Hvs.
        (*vl*)
        case_match. 2: {
          cbn in Hvs.
          congruence.
        }
        (* inversion *)
        cbn in Hvs.
        inv Hvs.
        (*v1*)
        case_match. 2:
        {
          inv H.
        }
        (*v2*)
        case_match. 2:
        {
          inv H.
        }
        (* rename [vl']*)
        rename l into vl'.
        rename H into Hvl'.
        (* rename [v1,v2]*)
        (*v1*)
        rename v into v1'.
        rename H0 into Hv1'.
        (*v2*)
        rename v0 into v2'.
        rename H1 into Hv2'.
        (* +3 Formalize Hypotheses *)
        (* - measure reduction [v1,v2,vl] *)
        (*v1*)
        rewrite measure_reduction with (n2 := measure_val v1) in Hv1'.
        2-3: slia.
        (*v2*)
        rewrite measure_reduction with (n2 := measure_val v2) in Hv2'.
        2-3: slia.
        (*vl*)
        rewrite measure_reduction_prod_map with (v2 := VMap vl) in Hvl'.
        2-3: slia.
        (* - clear cases with inversion [v1,v2,vl] *)
        (*v1*)
        remember 
          (exp_to_val_fs (bs_to_fs_exp f 
            (val_to_exp (subst_env (measure_val v1)) 
              v1))) 
          as _v1_to_fs.
        destruct _v1_to_fs as [v1'0 |]. 2:
        {
          inversion Hv1'.
        }
        inv Hv1'.
        clear Heq_v1_to_fs.
        (*v2*)
        remember 
          (exp_to_val_fs (bs_to_fs_exp f 
            (val_to_exp (subst_env (measure_val v2)) 
              v2))) 
          as _v2_to_fs.
        destruct _v2_to_fs as [v2'0 |]. 2:
        {
          inversion Hv2'.
        }
        inv Hv2'.
        clear Heq_v2_to_fs.
        (*vl*)
        remember (map (λ '(x, y0), (bs_to_fs_exp f x, bs_to_fs_exp f y0))
          (map
             (prod_map (val_to_exp (subst_env (measure_val (VMap vl))))
                (val_to_exp (subst_env (measure_val (VMap vl))))) vl)) 
          as _vl_to_fs.
        simpl in Hvl'.
        remember 
          (mapM
            (λ '(x, y),
              match exp_to_val_fs x with
                | Some x' => match exp_to_val_fs y with
                             | Some y' => Some (x', y')
                             | None => None
                             end
                | None => None
                end) _vl_to_fs)
          as _vl_to_el.
        destruct _vl_to_el as [vl'0 |]. 2:
        {
          inversion Hvl'.
        }
        simpl in Hvl'.
        inv Hvl'.
        (* rename [vl']*)
        rename vl'0 into vl'.
        (* +4 Specialize Hypotheses *)
        (* - specialize [v0,v1] *)
        (*v1*)
        specialize (Hv1 [v1']).
        specialize (Hv1 eq_refl).
        (*v2*)
        specialize (Hv2 [v2']).
        specialize (Hv2 eq_refl).
        (*vl*)
        specialize (Hvl [Syntax.VMap vl']).
        remember
          (subst_env (measure_val (VMap vl))) 
          as _f_st.
        simpl in Hvl.
        case_match. 2:
        {
          congruence.
        }
        symmetry in Heq_vl_to_el.
        inv Heq_vl_to_el.
        simpl in Hvl.
        specialize (Hvl eq_refl).
        clear H.
        (* - destruct hypothesis [v1,v2,vl] *)
        destruct Hv1 as [kv1 [Hv1_res Hv1_step]].
        destruct Hv2 as [kv2 [Hv2_res Hv2_step]].
        destruct Hvl as [kvl [Hvl_res Hvl_step]].
        (* +5 Assert Theorem *)
        (* pose proof *)
        pose proof framestack_ident as Hident.
        remember 
          ((map (λ '(x, y), (eraseNames f x, eraseNames f y))
            (map
               (prod_map
                  (val_to_exp (subst_env (list_sum (map (λ '(_, y), measure_val y) env))))
                  (val_to_exp (subst_env (list_sum (map (λ '(_, y), measure_val y) env)))))
               vl)))
          as _el.
        remember 
          (RValSeq [Syntax.VMap ((v1', v2') :: vl')]) 
          as _r.
        remember 
          (flatten_list _el)
          as _fel.
        remember 
          (flatten_list vl')
          as _fvl'.
        specialize (Hident IMap _fel [v1'] _fvl' _r v2' [] []).
        (* assert *)
        assert (create_result IMap ([v1'] ++ v2' :: _fvl') [] = Some (_r, [])) as Hr.
        {
          simpl.
          inv Heq_r.
          admit.
        }
        (* apply *)
        inv Heq_r.
        clear H.
        apply Hident in Hr as Hvl. 2:
        {
          clear - Hvl_step.
          inv Hvl_step.
          inv H.
          {
            admit.
          }
          admit.
        }
        clear Hr Hident Hvl_step kvl.
        (* destruct hypothesis [vl] *)
        destruct Hvl as [kvl Hvl_step].
        (* +6 FrameStack Proof *)
        eexists; split.
        + (* #6.2.1 Scope *)
          clear v1 kv1 Hv1_step v2 kv2 Hv2_step vl kvl Hvl_step.
          constructor.
          inv Hv1_res.
          inv Hv2_res.
          inv Hvl_res.
          destruct_foralls.
          admit. (* scope_solver *)
        + (* #6.2.2 Frame *)
          clear Hv1_res Hv2_res Hvl_res.
          do 1 do_step.
          (*v1*)
          eapply transitive_eval.
          {
            eapply frame_indep_core in Hv1_step.
            exact Hv1_step.
          }
          clear v1 kv1 Hv1_step.
          simpl.
          do 1 do_step.
          (*v2*)
          eapply transitive_eval.
          {
            eapply frame_indep_core in Hv2_step.
            exact Hv2_step.
          }
          clear v2 kv2 Hv2_step.
          simpl.
          (*vl*)
          exact Hvl_step.
  Admitted.


  (**
     induction H.
      - admit.
      - intros.
        admit.
      *)
      (**
      unfold bs_to_fs_val in H0.
      remember (subst_env (measure_val (VClos ref ext id params body funid))) as subst_env_clos.
      cbn in H0.
      cbn.
      rewrite Heqsubst_env_clos in H0.
      clear Heqsubst_env_clos.
      (* destruct both *)
      destruct ext.
      - admit.
      - destruct funid.
        + admit.
        + admit.
      *)

  (*Todo: restriction to f?*)
  (*Todo restriction to closed *)
  Theorem equivalence_bigstep_framestack : 

    forall env modules own_module id id' e e' eff eff' f r,

      (eval_expr env modules own_module id e eff id' e' eff')
      
      ->

  	  Some r = bs_to_fs_res f subst_env e'
  	  
  	  ->

  	  ⟨ [], (bs_to_fs_exp_env f subst_env e env) ⟩
      	-->*
  	  r.

  Proof.
    intros. revert f r H0. induction H; intros; cbn in *.
    (* Values *)
    * destruct (bs_to_fs_valseq f subst_env vals).
      - admit.
      - congruence.
    * destruct (bs_to_fs_exc f subst_env ex).
      - admit.
      - congruence.
    (* Nil *)
    * eexists. split; inv H0.
      - constructor. scope_solver.
      - do 1 do_step. constructor.
    (* Lit *)
    * eexists. split; inv H0.
      - constructor. scope_solver.
      - do 1 do_step. constructor.
    (* Var *)
    * rewrite H. destruct (bs_to_fs_valseq f subst_env res) eqn:Hr.
      - inv H0. destruct res; cbn in *. 
        + apply Environment.get_value_singelton_length in H. 
          cbn in H. congruence.
        + destruct res; cbn in *.
          ** apply bs_to_fs_val_reduction. assumption. 
          ** apply Environment.get_value_singelton_length in H. 
             cbn in H. congruence.
      - congruence.
    (* FunId *)
    * rewrite H. destruct (bs_to_fs_valseq f subst_env res) eqn:Hr. 
      - inv H0. destruct res; cbn in *. 
        + apply Environment.get_value_singelton_length in H. 
          cbn in H. congruence.
        + destruct res; cbn in *. 
          ** apply bs_to_fs_val_reduction. assumption. 
          ** apply Environment.get_value_singelton_length in H. 
             cbn in H. congruence.
      - congruence.
    * admit.
    (* Fun *)
    * admit.
    (* Tuple*)
    * admit.
    (* Cons *)
    * admit.
    (* Case *)
    * destruct (bs_to_fs_res f subst_env res).
      - admit.
      - congruence.
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



End Eqvivalence_BigStep_to_FramStack.