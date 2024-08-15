From CoreErlang.Equivalence.BigStepToFrameStack Require Import Measure.
From CoreErlang.Equivalence.BigStepToFrameStack Require Import EraseNames.
From CoreErlang Require Import Syntax.
From CoreErlang.BigStep Require Import Environment.

Require Import stdpp.list.



(**

* Helpers
  - Environment
    + env_rem
    + env_rem_vars
    + env_rem_ext
  - Convert
    + bval_to_bexp_ext
* Main
  - bval_to_bexp
  - bexp_to_fexp
  - bexp_to_fexp_subst
  - fexp_to_fval
  - bval_to_fval
  - bvs_to_fvs
  - bexc_to_fexc
  - bres_to_fred
*)



Definition measure_env_exp
    (env : Environment)
    (e : Expression)
    : nat
    :=
  measure_env measure_val env
  + measure_exp e.



Section Help.



  Section Environment.

    Definition env_rem
      (keys : list (Var + FunctionIdentifier))
      (env : Environment)
      : Environment
      :=
    fold_left
      (fun env' key =>
        filter (fun '(k, v) =>
          negb (var_funid_eqb k key))
          env')
      keys
      env.

    Definition env_rem_vars
      (vars : list Var)
      (env : Environment)
      : Environment
      :=
    env_rem (map inl vars) env.

    Definition env_rem_ext
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      (env : Environment)
      : Environment
      :=
    env_rem (map inr (map snd (map fst ext))) env.

  End Environment.



  Section Convert.

    Definition bval_to_bexp_ext
      (f : Environment -> Expression -> Expression)
      (env : Environment)
      (ext : list (nat * FunctionIdentifier * FunctionExpression))
      : list (FunctionIdentifier * (list Var * Expression))
      :=
    map
      (fun '(n, fid, (vl, e)) =>
        (fid,
          (vl,
          (f (env_rem_vars vl env) e))))
      ext.

  End Convert.



End Help.






Section Main.



  Fixpoint bval_to_bexp
    (f : Environment -> Expression -> Expression)
    (v : Value)
    : Expression
    :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
      (bval_to_bexp f hd)
      (bval_to_bexp f tl)

  | VTuple l => ETuple
      (map (bval_to_bexp f) l)

  | VMap l => EMap
      (map
        (prod_map 
          (bval_to_bexp f)
          (bval_to_bexp f))
        l)

  | VClos env ext id vl e fid =>
      match ext, fid with
      | [], _ => EFun
          vl
          (f (env_rem_vars vl env) e)

      (* This is None in option version *)
      | _, None => EFun
          vl
          (f (env_rem_vars vl env) e)

      | _, Some fid' => ELetRec
          (bval_to_bexp_ext
            f
            (env_rem_ext ext env)
            ext)
          (EFunId fid')
      end
  end.



  Definition bexp_to_fexp
    f
    (e : Expression)
    : Exp
    :=
  erase_names_exp f e.



  Definition bexp_to_fexp_subst
    f
    (g : nat -> Environment -> Expression -> Expression)
    (env : Environment)
    (e : Expression)
    : Exp
    :=
  bexp_to_fexp
    f
    (g
      (measure_env_exp
        env
        e)
      env
      e).


  (*TODO: replace this and the next with erase_names_val
          WRONG for recursive closures
  *)
  Fixpoint fexp_to_fval
    (e : Exp)
    : option Val
    :=
  match e with
  | VVal v => Some v
  | EExp e' => 
      match e' with
      | Syntax.EFun vl e'' => 
          Some (Syntax.VClos [] 0 vl e'')

      | Syntax.EValues el =>
          match
            (mapM fexp_to_fval el)
          with
          | Some el' => Some (Syntax.VTuple el')
          | None => None
          end

      | Syntax.ECons hd tl =>
          match
            (fexp_to_fval hd),
            (fexp_to_fval tl)
          with
          | Some hd', Some tl' => Some (Syntax.VCons hd' tl')
          | _, _ => None
          end

      | Syntax.ETuple l =>
          match
            (mapM fexp_to_fval l)
          with
          | Some l' => Some (Syntax.VTuple l')
          | None => None
          end

      | Syntax.EMap l =>
          match
            (mapM
              (fun '(x, y) =>
                match
                  (fexp_to_fval x),
                  (fexp_to_fval y)
                with
                | Some x', Some y' => Some (x', y')
                | _, _ => None
                end)
              l)
          with
          | Some l' => Some (Syntax.VMap l')
          | None => None
          end

      | Syntax.ECall m f l => None
      | Syntax.EPrimOp f l => None
      | Syntax.EApp exp l =>  None
      | Syntax.ECase e' l => None
      | Syntax.ELet l e1 e2 =>  None
      | Syntax.ESeq e1 e2 =>  None
      | Syntax.ELetRec l e =>  None
      | Syntax.ETry e1 vl1 e2 vl2 e0 =>  None
      end
  end.



  Definition bval_to_fval
    f
    (g : nat -> Environment -> Expression -> Expression)
    (v : Value)
    : option Val
  :=
  fexp_to_fval
    (bexp_to_fexp
      f
      (bval_to_bexp
        (g (measure_val v))
        v)).



  Definition bvs_to_fvs
    f
    (g : nat -> Environment -> Expression -> Expression)
    (vs : ValueSequence)
    : option ValSeq
    :=
  mapM
    (bval_to_fval f g)
    vs.



  Definition bexc_to_fexc
    f
    (g : nat -> Environment -> Expression -> Expression)
    (exc : Exception)
    : option CoreErlang.Syntax.Exception
    :=
  match exc with
  | (excc, v1, v2) =>
      match
        (bval_to_fval f g v1),
        (bval_to_fval f g v2)
      with
      | Some v1', Some v2' =>
          match excc with
          | Error => Some (CoreErlang.Syntax.Error, v1', v2')
          | Throw => Some (CoreErlang.Syntax.Throw, v1', v2')
          | Exit => Some (CoreErlang.Syntax.Exit, v1', v2')
          end
      | _, _ => None
      end
  end.



  Definition bres_to_fred
    f
    (g : nat -> Environment -> Expression -> Expression)
    (res : (ValueSequence + Exception))
    : option Redex
    :=
  match res with
  | inl vs =>
      match (bvs_to_fvs f g vs) with
      | Some vs' => Some (RValSeq vs')
      | None => None
      end
  | inr exc => 
      match (bexc_to_fexc f g exc) with
      | Some exc' => Some (RExc exc')
      | None => None
      end
  end.



End Main.