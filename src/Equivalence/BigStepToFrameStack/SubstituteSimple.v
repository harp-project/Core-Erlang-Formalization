From CoreErlang.Equivalence.BigStepToFrameStack Require Import EnvironmentRemove.
From CoreErlang.Equivalence.BigStepToFrameStack Require Import ConvertSimple.
From CoreErlang.BigStep Require Import Environment.

Require Import stdpp.list.



Fixpoint subst_env
  (fuel : nat)
  (env : Environment)
  (e : Expression)
  : Expression
  :=
match fuel with
(* This is None in option version *)
| O => e
| S fuel' =>
  match e with

  | ENil => e

  | ELit l => e

  | EValues el => EValues
      (map (subst_env fuel' env) el)

  | EFun vl e => EFun
    vl
    (subst_env fuel' env e)

  | ECons hd tl => ECons
      (subst_env fuel' env hd)
      (subst_env fuel' env tl)

  | ETuple l => ETuple
      (map (subst_env fuel' env) l)

  | ECall m f l => ECall
      (subst_env fuel' env m)
      (subst_env fuel' env f)
      (map (subst_env fuel' env) l)

  | EPrimOp f l => EPrimOp
    f
    (map (subst_env fuel' env) l)

  | EApp exp l => EApp
      (subst_env fuel' env exp)
      (map (subst_env fuel' env) l)

  | ECase e l => ECase
      (subst_env fuel' env e)
      (map
        (fun '(pl, g, b) =>
          (pl,
          (subst_env fuel' env g),
          (subst_env fuel' env b)))
        l)

  | ELet l e1 e2 => ELet
      l
      (subst_env fuel' env e1)
      (subst_env fuel' (env_rem_vars l env) e2)

  | ESeq e1 e2 => ESeq
      (subst_env fuel' env e1)
      (subst_env fuel' env e2)

  | ELetRec l e => ELetRec
      (map
        (fun '(fid, (vl, b)) =>
          (fid,
          (vl,
          (subst_env fuel' (env_rem_fids_vars l vl env) b))))
        l)
      (subst_env fuel' (env_rem_fids l env) e)

  | EMap l => EMap
      (map
        (prod_map
          (subst_env fuel' env)
          (subst_env fuel' env))
        l)

  | ETry e1 vl1 e2 vl2 e3 => ETry
      (subst_env fuel' env e1)
      vl1
      (subst_env fuel' env e2)
      vl2
      (subst_env fuel' env e3)

  | EVar var =>
      match (get_value env (inl var)) with
      | Some [v] => bval_to_bexp (subst_env fuel') v
      | Some vs => EValues
          (map (bval_to_bexp (subst_env fuel')) vs)
      | _ => e
      end

  | EFunId fid =>
      match (get_value env (inr fid)) with
      | Some [v] => bval_to_bexp (subst_env fuel') v
      | Some vs => EValues
          (map (bval_to_bexp (subst_env fuel')) vs)
      | _ => e
      end
  end
end.