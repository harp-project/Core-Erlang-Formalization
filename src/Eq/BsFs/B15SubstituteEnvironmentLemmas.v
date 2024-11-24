From CoreErlang.Eq.BsFs Require Export B14SubstituteEnvironmentDefinitions.

Import BigStep.

(* STRUCTURE:
* Subst
  - subst_env_step
*)












Section Subst.



  Lemma subst_env_step :
    forall fuel env e,
      subst_env (1 + fuel) env e
    = match e with

      | ENil =>
        ENil

      | ELit lit =>
        ELit lit

      | ECons e1 e2 =>
        ECons
          (subst_env fuel env e1)
          (subst_env fuel env e2)

      | ESeq e1 e2 =>
        ESeq
          (subst_env fuel env e1)
          (subst_env fuel env e2)

      | EValues el =>
        EValues
          (map (subst_env fuel env) el)

      | ETuple el =>
        ETuple
          (map (subst_env fuel env) el)

      | EPrimOp s el =>
        EPrimOp s
          (map (subst_env fuel env) el)

      | EApp e el =>
        EApp
          (subst_env fuel env e)
          (map (subst_env fuel env) el)

      | ECall e1 e2 el =>
        ECall
          (subst_env fuel env e1)
          (subst_env fuel env e2)
          (map (subst_env fuel env) el)

      | EMap ell =>
        EMap
          (map
            (prod_map
              (subst_env fuel env)
              (subst_env fuel env))
            ell)

      | ECase e case =>
        ECase
          (subst_env fuel env e)
          (map
            (fun '(pl, e1, e2) =>
              (pl,
              (subst_env fuel env e1),
              (subst_env fuel env e2)))
            case)

      | EFun vars e =>
        EFun
          vars
          (subst_env fuel (rem_vars vars env) e)

      | ELet vars e1 e2 =>
        ELet
          vars
          (subst_env fuel env e1)
          (subst_env fuel (rem_vars vars env) e2)

      | ETry e1 vars1 e2 vars2 e3 =>
        ETry
          (subst_env fuel env e1)
          vars1
          (subst_env fuel (rem_vars vars1 env) e2)
          vars2
          (subst_env fuel (rem_vars vars2 env) e3)

      | ELetRec ext e =>
        ELetRec
          (map
            (fun '(fid, (vars, body)) =>
              (fid,
              (vars,
              (subst_env fuel (rem_exp_ext_both vars ext env) body))))
            ext)
          (subst_env fuel (rem_exp_ext_fids ext env) e)

      | EVar var =>
          match (get_value env (inl var)) with
          | Some [v] => bval_to_bexp (subst_env fuel) v
          | _ => e
          end

      | EFunId fid =>
          match (get_value env (inr fid)) with
          | Some [v] => bval_to_bexp (subst_env fuel) v
          | _ => e
          end

      end.
  Proof.
    trv.
  Qed.



End Subst.