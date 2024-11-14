From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.


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
    	(f (rem_vars vl env) e))))
  ext.

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
      	(f (rem_vars vl env) e)

  	(* This is None in option version *)
  	| _, None => EFun
      	vl
      	(f (rem_vars vl env) e)

  	| _, Some fid' => ELetRec
      	(bval_to_bexp_ext
        	f
        	(rem_nfifes ext env)
        	ext)
      	(EFunId fid')
  	end
end.



  Fixpoint nest_env
    (fuel : nat)
	  (env : Environment)
	  (e : Expression)
	  : Expression
	  :=
	match fuel with(* This is None in option version *)
  | O => e
  | S fuel' =>
    match env with
    | [] => e
    | (k, v) :: env' =>
        match k with
        | inl var => ELet [var]
            (bval_to_bexp (nest_env fuel') v)
            (nest_env fuel' env' e)
        | inr funid => e
        end
    end
  end.