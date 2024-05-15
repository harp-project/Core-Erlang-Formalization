From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.
From CoreErlang.TMP.Task Require Import EraseNames.

Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import stdpp.list.

Import BigStep.
Import ListNotations.






Module SubstEnviroment.



(*  # MESURE  *)



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






(*  # HELP  *)
(* TODO: Maybe put in Enviroment.v instead? *)
(*TODO: delete list*)



Fixpoint remove_value (env : Environment) 
                      (key : (Var + FunctionIdentifier)) 
                      : Environment :=

  match env with
  | [] => []
  | (k, v)::xs => 
      if (var_funid_eqb k key) 
        then (remove_value xs key)
        else (k, v)::(remove_value xs key)
  end.



Fixpoint remove_values (env : Environment) 
                       (keys : list (Var + FunctionIdentifier)) 
                       : Environment :=

  match keys with
  | [] => env
  | k::ks => remove_values (remove_value env k) ks
  end.



(*  # VAL TO EXP  *)



Fixpoint val_to_exp (subst_env : Environment -> Expression -> Expression) 
                    (v : Value) 
                    : Expression :=

  let
    map_ext (env : Environment) 
            (ext : list (nat * FunctionIdentifier * FunctionExpression)) 
            : list (FunctionIdentifier * (list Var * Expression)) :=

      map (fun '(n, fid, (vl, e)) => (fid, (vl, (subst_env env e)))) ext
  in

  match v with

  | VNil => ENil
  | VLit l => ELit l

  | VClos env ext id vl e fid => 
      match ext, fid with
      | [], _ => EFun vl (subst_env env e)
      | _, None => EFun vl (subst_env env e) (*Todo: make it option ?*)
      | _, Some fid' => ELetRec (map_ext env ext) (EFunId fid')
      end

  | VCons hd tl => ECons (val_to_exp subst_env hd) (val_to_exp subst_env tl)
  | VTuple l => ETuple (map (val_to_exp subst_env) l)
  | VMap l => EMap (map (prod_map (val_to_exp subst_env) (val_to_exp subst_env)) l)

  end.



Fixpoint val_to_exp_opt (subst_env : Environment -> Expression -> option Expression) 
                        (v : Value) 
                        : option Expression :=

  let
    map_ext (env : Environment) 
            (ext : list (nat * FunctionIdentifier * FunctionExpression)) 
            : option (list (FunctionIdentifier * (list Var * Expression))) :=

      mapM (fun x => 
              match x with
              | (n, fid, (vl, e)) => 
                  match (subst_env env e) with
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
          match (subst_env env e) with
          | Some e' => Some (EFun vl e')
          | None => None
          end

      | _, None => None

      | _, Some fid' => 
          match (map_ext env ext) with
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






(*  # SUBST ENV  *)



Fixpoint subst_env (fuel : nat) 
                   (Γ : Environment) 
                   (e : Expression) 
                   : Expression :=

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
                               (subst_env fuel' (remove_values Γ (map inl l)) e2)
      
      | ESeq e1 e2 => ESeq (subst_env fuel' Γ e1) 
                           (subst_env fuel' Γ e2)
      
      | ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) => (fid, (vl, (subst_env fuel' Γ b)))) l) 
                               (subst_env fuel' (remove_values Γ (map inr (map fst l))) e)
      
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
                (subst_env_opt fuel' (remove_values Γ (map inl l)) e2) with

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
          match (mapM (fun '(fid, (vl, b)) => subst_env_letrec fuel' Γ fid vl b) l), 
                (subst_env_opt fuel' (remove_values Γ (map inr (map fst l))) e) with

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



Module Converters.



Import SubstEnviroment.



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
                            (e : Expression) 
                            (env : Environment) 
                            : Exp :=

  bs_to_fs_exp f 
               (subst_env (mesure_subst_env env 
                                            e) 
                          env 
                          e).



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
Definition bs_to_fs_val f (v : Value) 
                          : option Val :=

  exp_to_val_fs (bs_to_fs_exp f 
                              (val_to_exp (subst_env (mesure_val v)) 
                                          v)).



(*
    BigStep -> FrameStack
    ValueSequence -> ValSeq
*)
Definition bs_to_fs_valseq f 
                           (vs : ValueSequence) 
                           : option ValSeq :=

  mapM (bs_to_fs_val f) vs.


End Converters.



Module FromBigStepToFramStack.

Import Converters.


Ltac do_step := econstructor; [constructor;auto| simpl].



(*Todo: restriction to f?*)
Theorem equivalence_bigstep_framestack : 
    forall env modules own_module id id' e e' eff eff' vs f,
    | env , modules , own_module , id , e , eff | 
        -e> 
     | id' , inl e' , eff' |
    ->
    Some vs = bs_to_fs_valseq f e'
    ->
    ⟨ [], (bs_to_fs_exp_env f e env) ⟩ 
        -->* 
    vs.
Proof.
  intros. revert vs H0 f. induction H; intros; cbn in *.
  * admit.
  * admit.
  * eexists. split.
    - scope_solver.
    -  do_step.
Admitted.


End FromBigStepToFramStack.