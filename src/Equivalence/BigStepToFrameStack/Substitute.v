From CoreErlang.Equivalence.BigStepToFrameStack Require Import EnvironmentLemmas.
From CoreErlang.Equivalence.BigStepToFrameStack Require Import Convert.
From CoreErlang.BigStep Require Import Environment.

Require Import stdpp.list.



(**

* Help
  - subst_env_case
  - subst_env_letrec
  - subst_env_map
* Main
  - subst_env

*)



Section Help.



  Definition subst_env_case
    (f : nat -> Environment -> Expression -> option Expression)
    (fuel : nat)
    (env : Environment)
    (pl : list Pattern)
    (g : Expression)
    (b : Expression)
    : option ((list Pattern) * Expression * Expression)
    :=
  match
    (f fuel env g),
    (f fuel env b)
  with
  | Some g', Some b' => Some (pl, g', b')
  | _, _ => None
  end.



  Definition subst_env_letrec
    (f : nat -> Environment -> Expression -> option Expression)
    (fuel : nat)
    (env : Environment)
    (fid : FunctionIdentifier)
    (vl : list Var)
    (b : Expression)
    : option (FunctionIdentifier * (list Var * Expression))
    :=
  match (f fuel env b) with
  | Some b' => Some (fid, (vl, b'))
  | None => None
  end.



  Definition subst_env_map
    (f : nat -> Environment -> Expression -> option Expression)
    (fuel : nat)
    (env : Environment)
    (x : Expression)
    (y : Expression)
    : option (Expression * Expression)
    :=
  match
    (f fuel env x),
    (f fuel env y)
  with
  | Some x', Some y' => Some (x', y')
  | _, _ => None
  end.



End Help.






Section Main.



  Fixpoint subst_env
    (fuel : nat)
    (env : Environment)
    (e : Expression)
    : option Expression
    :=
  match fuel with
  | O => None
  | S fuel' =>
    match e with

    | ENil => Some e

    | ELit l => Some e

    | EValues el => 
        match (mapM (subst_env fuel' env) el) with
        | Some el' => Some (EValues el')
        | None => None
        end


    | EFun vl e =>
        match (subst_env fuel' env e) with
        | Some e' => Some (EFun vl e')
        | None => None
        end

    | ECons hd tl =>
        match
          (subst_env fuel' env hd),
          (subst_env fuel' env tl)
        with
        | Some hd', Some tl' => Some (ECons hd' tl')
        | _, _ => None
        end

    | ETuple l =>
        match (mapM (subst_env fuel' env) l) with
        | Some l' => Some (ETuple l')
        | None => None
        end


    | ECall m f l =>
        match
          (subst_env fuel' env m),
          (subst_env fuel' env f),
          (mapM (subst_env fuel' env) l)
        with
        | Some m', Some f', Some l' => Some (ECall m' f' l')
        | _, _, _ => None
        end

    | EPrimOp f l =>
        match (mapM (subst_env fuel' env) l) with
        | Some l' => Some (EPrimOp f l')
        | None => None
        end

    | EApp exp l =>
        match
          (subst_env fuel' env exp),
          (mapM (subst_env fuel' env) l)
        with
        | Some exp', Some l' => Some (EApp exp' l')
        | _, _ => None
        end

    | ECase e l =>
        match
        (subst_env fuel' env e),
        (mapM
          (fun '(pl, g, b) =>
            subst_env_case subst_env fuel' env pl g b)
          l)
        with
        | Some e', Some l' => Some (ECase e' l')
        | _, _ => None
        end

    | ELet l e1 e2 =>
        match
          (subst_env fuel' env e1),
          (subst_env fuel' (env_rem_vars l env) e2)
        with
        | Some e1', Some e2 => Some (ELet l e1 e2)
        | _, _ => None
        end

    | ESeq e1 e2 =>
        match
          (subst_env fuel' env e1),
          (subst_env fuel' env e2)
        with
        | Some e1', Some e2 => Some (ESeq e1 e2)
        | _, _ => None
        end

    | ELetRec l e =>
        match
          (mapM
            (fun '(fid, (vl, b)) => 
              subst_env_letrec subst_env fuel' env fid vl b)
            l),
          (subst_env fuel' (env_rem_fids l env) e)
        with
        | Some l', Some e' => Some (ELetRec l' e')
        | _, _ => None
        end

    | EMap l =>
        match
          (mapM
            (fun '(x, y) =>
              subst_env_map subst_env fuel' env x y)
            l)
        with
        | Some l' => Some (EMap l')
        | None => None
        end

    | ETry e1 vl1 e2 vl2 e3 => 
        match
          (subst_env fuel' env e1),
          (subst_env fuel' env e2),
          (subst_env fuel' env e3)
        with
        | Some e1', Some e2', Some e3' => Some (ETry e1' vl1 e2' vl2 e3')
        | _, _, _ => None
        end

    | EVar var =>
        match (get_value env (inl var)) with
        | Some [v] => bval_to_bexp (subst_env fuel') v
        | Some vs =>
            match
              (mapM (bval_to_bexp (subst_env fuel')) vs)
            with
            | Some vs' => Some (EValues vs')
            | _ => Some e
            end
        | _ => Some e
        end

    | EFunId fid =>
        match (get_value env (inr fid)) with
        | Some [v] => bval_to_bexp (subst_env fuel') v
        | Some vs =>
            match
              (mapM (bval_to_bexp (subst_env fuel')) vs)
            with
            | Some vs' => Some (EValues vs')
            | _ => Some e
            end
        | _ => Some e
        end
    end
  end.



End Main.
