From CoreErlang.Eq.BsFs Require Export B12MeasureDefinitions.

Import BigStep.

(* STRUCTURE:
* Inductive
  - bval_to_bexp_ext
* Main
  - bval_to_bexp
*)












Section Inductive.



  Definition bval_to_bexp_ext
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) => (fid, (vl, e)))
	  ext.



End Inductive.









Section Main.



  Fixpoint bval_to_bexp
	  (subst_env : Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with

  | VNil =>
    ENil

  | VLit lit =>
    ELit lit

  | VCons v1 v2 =>
    ECons
    	(bval_to_bexp subst_env v1)
    	(bval_to_bexp subst_env v2)

  | VTuple vl =>
    ETuple
  	  (map (bval_to_bexp subst_env) vl)

  | VMap vll =>
    EMap
    	(map
      	(prod_map
        	(bval_to_bexp subst_env)
        	(bval_to_bexp subst_env))
      	vll)

  | VClos env ext _ vars e fid =>
    match ext, fid with
    | _ :: _, Some fid' =>
      (subst_env
        env
        (ELetRec (bval_to_bexp_ext ext) (EFunId fid')))
    | _, _ =>
      (subst_env
        env
        (EFun vars e))
    end

  end.



End Main.