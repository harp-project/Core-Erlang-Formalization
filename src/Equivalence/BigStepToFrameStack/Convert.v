From CoreErlang.Equivalence.BigStepToFrameStack Require Import EnvironmentLemmas.
From CoreErlang.Equivalence.BigStepToFrameStack Require Import EraseNames.
From CoreErlang.Equivalence.BigStepToFrameStack Require Import Measure.
Require Import stdpp.list.

Import BigStep.

(**
* Help
  - bval_to_bexp_ext
  - bval_to_bexp_pair
* Main
  - bval_to_bexp
  - bexp_to_fexp
  - bexp_to_fexp_subst
  - fexp_to_fval [Bad]
  - bval_to_fval [Bad]
  - bvs_to_fvs
  - bexc_to_fexc
  - bres_to_fred
*)

(*
TODO: fexp_to_fval & bexp_to_fval
      replace with erase_names_val
      WRONG for recursive closures
*)



Section Help.



  Definition bval_to_bexp_ext
    (f : Environment -> Expression -> option Expression)
    (env : Environment)
    (ext : list (nat * FunctionIdentifier * FunctionExpression))
    : option (list (FunctionIdentifier * (list Var * Expression)))
    :=
  mapM 
    (fun x => 
      match x with
      | (n, fid, (vl, e)) => 
          match (f (env_rem_vars vl env) e) with
          | Some e' => Some (fid, (vl, e'))
          | None => None
          end
      end)
    ext.



  Definition bval_to_bexp_pair
    (f : (Environment -> Expression -> option Expression) 
      -> Value
      -> option Expression)
    (g : Environment -> Expression -> option Expression)
    (x y : Value)
    : option (Expression * Expression)
    :=
  match
    (f g x), 
    (f g y) 
  with
  | Some x', Some y' => Some (x', y')
  | _, _ => None
  end.



End Help.






Section Main.



  Fixpoint bval_to_bexp
    (f : Environment -> Expression -> option Expression)
    (v : Value)
    : option Expression
    :=
  match v with
  | VNil => Some ENil

  | VLit l => Some (ELit l)

  | VCons hd tl =>
      match
        (bval_to_bexp f hd), 
        (bval_to_bexp f tl) 
      with
      | Some hd', Some tl' => Some (ECons hd' tl')
      | _, _ => None
      end

  | VTuple l =>
      match
        (mapM (bval_to_bexp f) l)
      with
      | Some l' => Some (ETuple l')
      | None => None
      end

  | VMap l =>
      match
        (mapM
          (fun '(x, y) =>
            bval_to_bexp_pair
              bval_to_bexp
              f
              x
              y)
          l)
      with
      | Some l' => Some (EMap l')
      | None => None
      end

  | VClos env ext id vl e fid =>
      match ext, fid with
      | [], _ =>
          match
            f
              (env_rem_vars vl env)
              e
          with
          | Some e' => Some (EFun vl e')
          | None => None
          end

      | _, None => None

      | _, Some fid' => 
          match
            (bval_to_bexp_ext
              f
              (env_rem_ext ext env)
              ext)
          with
          | Some ext' => Some (ELetRec ext' (EFunId fid'))
          | None => None
          end
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
    (g : nat -> Environment -> Expression -> option Expression)
    (env : Environment)
    (e : Expression)
    : option Exp
    :=
  match
    (g
      (measure_env_exp env e)
      env
      e)
  with
  | Some e' => Some (bexp_to_fexp f e')
  | None => None
  end.



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
    (g : nat -> Environment -> Expression -> option Expression)
    (v : Value)
    : option Val
    :=
  match
    (bval_to_bexp
      (g (measure_val v))
      v)
  with
  | Some e => fexp_to_fval (bexp_to_fexp f e)
  | None => None
  end.



  Definition bvs_to_fvs
    f
    (g : nat -> Environment -> Expression -> option Expression)
    (vs : ValueSequence)
    : option ValSeq
    :=
  mapM
    (bval_to_fval f g)
    vs.



  Definition bexc_to_fexc
    f
    (g : nat -> Environment -> Expression -> option Expression)
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
    (g : nat -> Environment -> Expression -> option Expression)
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