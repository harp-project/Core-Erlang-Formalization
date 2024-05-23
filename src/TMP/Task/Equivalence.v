From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.
From CoreErlang.TMP.Task Require Import EraseNames.

Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import stdpp.list.

Import BigStep.
Import ListNotations.






Section MesureTypes.



  Fixpoint mesure_exp (e : Expression) 
                      : nat :=
                      
    let 
      mesure_exp_list (el : list Expression) 
                      : nat :=

        list_sum (map mesure_exp el)
    in

    let 
      mesure_exp_map (epl : list (Expression * Expression)) 
                     : nat :=

        list_sum (map (fun '(x, y) => (mesure_exp x) + (mesure_exp y)) epl)
    in

    let 
      mesure_exp_case (l : list ((list Pattern) * Expression * Expression)) 
                      : nat :=

        list_sum (map (fun '(pl, g, b) => (mesure_exp g) + (mesure_exp b)) l)
    in 

    let
      mesure_exp_letrec (l : list (FunctionIdentifier * (list Var * Expression))) 
                        : nat :=

        list_sum (map (fun '(fid, (vl, b)) => (mesure_exp b)) l)
    in

    match e with

    | EValues el => 1 
        + (mesure_exp_list el)

    | ENil => 1
    | ELit l => 1
    | EVar v => 1
    | EFunId f => 1

    | EFun vl e => 1 
        + (mesure_exp e)

    | ECons hd tl => 1 
        + (mesure_exp hd) 
        + (mesure_exp tl)

    | ETuple l => 1 
        + (mesure_exp_list l)

    | ECall m f l => 1 
        + (mesure_exp m) 
        + (mesure_exp f) 
        + (mesure_exp_list l)

    | EPrimOp f l => 1 
        + (mesure_exp_list l)

    | EApp exp l => 1 
        + (mesure_exp exp) 
        + (mesure_exp_list l)

    | ECase e l => 1 
        + (mesure_exp e) 
        + (mesure_exp_case l)

    | ELet l e1 e2 => 1 
        + (mesure_exp e1) 
        + (mesure_exp e2)

    | ESeq e1 e2 => 1 
        + (mesure_exp e1) 
        + (mesure_exp e2)

    | ELetRec l e => 1 
        + (mesure_exp_letrec l) 
        + (mesure_exp e)

    | EMap l => 1 
        + (mesure_exp_map l)

    | ETry e1 vl1 e2 vl2 e0 => 1 
        + (mesure_exp e1) 
        + (mesure_exp e2) 
        + (mesure_exp e0)

    end.



  Fixpoint mesure_val (v : Value) 
                      : nat :=

    let
      mesure_val_list (vl : list Value) 
                      : nat :=

        list_sum (map mesure_val vl)
    in

    let 
      mesure_val_map (vm : list (Value * Value)) 
                     : nat :=

        list_sum (map (fun '(x, y) => (mesure_val x) + (mesure_val y)) vm)
    in

    let 
      mesure_val_env (env : Environment) 
                     : nat :=

        list_sum (map (fun '(x, y) => (mesure_val y)) env)
    in

    match v with

    | VNil => 1
    | VLit l => 1

    | VClos env ext id vl e fid => 1 
        + (mesure_val_env env) 
        + (mesure_exp e)

    | VCons hd tl => 1 
        + (mesure_val hd) 
        + (mesure_val tl)

    | VTuple l => 1 
        + (mesure_val_list l) 

    | VMap l => 1 
        + (mesure_val_map l)

    end.



  Definition mesure_subst_env (env : Environment) 
                              (e : Expression) 
                              : nat :=
                            
    let 
      mesure_env (env : Environment) 
                 : nat :=

        list_sum (map (fun '(x, y) => (mesure_val y)) env)
    in

    (mesure_exp e) + (mesure_env env).



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
                (subst_env (mesure_subst_env env 
                                             e) 
                           env 
                           e).



  Definition bs_to_fs_exp_env_opt f 
                                  (subst_env : nat -> Environment -> Expression -> option Expression) 
                                  (e : Expression) 
                                  (env : Environment) 
                                  : option Exp :=

    match (subst_env (mesure_subst_env env e) env e) with
    | Some e' => Some (bs_to_fs_exp f e')
    | None => None
    end.



  (*
      FrameStack
      Exp -> Val
  *)
  Definition exp_to_val_fs (e : Exp) 
                           : option Val :=

    match e with
    | VVal v => Some v
    | _ => None
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
                                (val_to_exp (subst_env (mesure_val v)) 
                                            v)).



  Definition bs_to_fs_val_opt f 
                              (subst_env : nat -> Environment -> Expression -> option Expression) 
                              (v : Value) 
                              : option Val :=

    match (val_to_exp_opt (subst_env (mesure_val v)) v) with
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
  Definition bs_to_rs_res f 
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



  Definition bs_to_rs_res_opt f 
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
    h/1 = fun(x) -> y , x , f/1 , h/1
    -
    f/1 = fun(x) -> x , (fun(z) -> z), (fun(x,y) -> x , y , z), f/1 , g/1
    g/1 = fun(x) -> 2 , x , g/1 , h/1
    h/1 = fun(x) -> y , 1 , f/1 , h/1
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



End Test.






Section Eqvivalence_BigStep_to_FramStack.



  Ltac do_step := econstructor; [constructor;auto| simpl].



  (*Todo: restriction to f?*)
  Theorem equivalence_bigstep_framestack : 

      forall env modules own_module id id' e e' eff eff' r f,

      | env , modules , own_module , id , e , eff | 
          -e> 
      | id' , e' , eff' |

      ->

      Some r = bs_to_rs_res f subst_env e'

      ->

      ⟨ [], (bs_to_fs_exp_env f subst_env e env) ⟩ 
          -->* 
      r.

  Proof.
    intros. revert f r H0. induction H; intros; cbn in *.
    (* Values *)
    * admit.
    * admit.
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
        + inv Hr. eexists. split.
          ** constructor. scope_solver.
          ** do 1 do_step. econstructor.
             {
                econstructor.
                {
                    congruence.
                }
                constructor.
             }
             constructor.
        + admit.
      - congruence.
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



End Eqvivalence_BigStep_to_FramStack.