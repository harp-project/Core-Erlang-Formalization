From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.








Fixpoint remove_all
  (A B : Type) (f : A -> B -> bool) (keys : list A) (l : list B) : list B
  :=
match keys with
| [] => l
| k :: ks => remove_all A B f ks (filter (fun x => negb (f k x)) l)
end.

Definition remove_all'
  (A B : Type) (f : A -> B -> bool) (keys : list A) (l : list B) : list B
  :=
fold_left
  (fun l' k => filter (fun x => negb (f k x)) l')
  keys
  l.



Lemma remove_all_le :
  forall (A B : Type) (f : A -> B -> bool) (g : list B -> nat)
         (keys : list A) (l : list B),
  g (remove_all A B f keys l) <= g l.
Proof.
  itr.
  ind - keys as [| k keys IHkeys]: smp.
  smp.
Admitted.









(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: VALTOEXP /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Help
  - bval_to_bexp_ext
* Main
  - bval_to_bexp
*)






Section ValToExp_Help.



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



  Definition bval_to_bexp_ext'
	  (f : nat -> Environment -> Expression -> Expression)
	  (env : Environment)
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) =>
    	(fid,
      	(vl,
      	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e))))
	  ext.



  Definition bval_to_bexp_ext''
	  (f : nat -> Environment -> Expression -> Expression)
	  (n : nat)
	  (env : Environment)
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) =>
    	(fid,
      	(vl,
      	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e))))
	  ext.



  Definition bval_to_bexp_ext'''
    (g : Environment -> Expression -> Expression)
	  (f : nat -> Environment -> Expression -> Expression)
	  (env : Environment)
	  (ext : list (nat * FunctionIdentifier * FunctionExpression))
	  : list (FunctionIdentifier * (list Var * Expression))
	  :=
  map
	  (fun '(n, fid, (vl, e)) =>
    	(fid,
      	(vl,
      	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e))))
	  ext.



End ValToExp_Help.






Section ValToExp_Main.



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



  Fixpoint bval_to_bexp'
	  (f : nat -> Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
    	(bval_to_bexp' f hd)
    	(bval_to_bexp' f tl)

  | VTuple l => ETuple
  	  (map (bval_to_bexp' f) l)

  | VMap l => EMap
    	(map
      	(prod_map
        	(bval_to_bexp' f)
        	(bval_to_bexp' f))
      	l)

  | VClos env ext id vl e fid =>
    	match ext, fid with
    	| [], _ => EFun
        	vl
        	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e)

    	(* This is None in option version *)
    	| _, None => EFun
        	vl
        	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e)

    	| _, Some fid' => ELetRec
        	(bval_to_bexp_ext'
          	f
          	(rem_nfifes ext env)
          	ext)
        	(EFunId fid')
    	end
  end.



  Fixpoint bval_to_bexp''
	  (f : nat -> Environment -> Expression -> Expression)
	  (n : nat)
	  (v : Value)
	  : Expression
	  :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
    	(bval_to_bexp'' f n hd)
    	(bval_to_bexp'' f n tl)

  | VTuple l => ETuple
  	  (map (bval_to_bexp'' f n) l)

  | VMap l => EMap
    	(map
      	(prod_map
        	(bval_to_bexp'' f n)
        	(bval_to_bexp'' f n))
      	l)

  | VClos env ext id vl e fid =>
    	match ext, fid with
    	| [], _ => EFun
        	vl
        	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e)

    	(* This is None in option version *)
    	| _, None => EFun
        	vl
        	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e)

    	| _, Some fid' => ELetRec
        	(bval_to_bexp_ext''
          	f
          	n
          	(rem_nfifes ext env)
          	ext)
        	(EFunId fid')
    	end
  end.



  Fixpoint bval_to_bexp'''
	  (g : Environment -> Expression -> Expression)
	  (f : nat -> Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
    	(bval_to_bexp''' g f hd)
    	(bval_to_bexp''' g f tl)

  | VTuple l => ETuple
  	  (map (bval_to_bexp''' g f) l)

  | VMap l => EMap
    	(map
      	(prod_map
        	(bval_to_bexp''' g f)
        	(bval_to_bexp''' g f))
      	l)

  | VClos env ext id vl e fid =>
    	match ext, fid with
    	| [], _ => EFun
        	vl
        	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e)

    	(* This is None in option version *)
    	| _, None => EFun
        	vl
        	(f (measure_env_exp (rem_vars vl env) e) (rem_vars vl env) e)

    	| _, Some fid' => ELetRec
        	(bval_to_bexp_ext'''
          	g
          	f
          	(rem_nfifes ext env)
          	ext)
        	(EFunId fid')
    	end
  end.



End ValToExp_Main.













(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: SUBSTITUTE ///////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)



(**
* Main
  - subst_env
  - subst_env2
*)




Section Substitue.



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
          (subst_env fuel' (rem_vars l env) e2)

      | ESeq e1 e2 => ESeq
          (subst_env fuel' env e1)
          (subst_env fuel' env e2)

      | ELetRec l e => ELetRec
          (map
            (fun '(fid, (vl, b)) =>
              (fid,
              (vl,
              (subst_env fuel' (rem_both l vl env) b))))
            l)
          (subst_env fuel' (rem_fids l env) e)

      | EMap l => EMap
          (map
            (prod_map
              (subst_env fuel' env)
              (subst_env fuel' env))
            l)

      | ETry e1 vl1 e2 vl2 e3 => ETry
          (subst_env fuel' env e1)
          vl1
          (subst_env fuel' (rem_vars vl1 env) e2)
          vl2
          (subst_env fuel' (rem_vars vl2 env) e3)

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



  Fixpoint bval_to_bexp1
	  (f : Environment -> Expression -> Expression)
	  (v : Value)
	  : Expression
	  :=
  match v with
  | VNil => ENil

  | VLit l => ELit l

  | VCons hd tl => ECons
    	(bval_to_bexp1 f hd)
    	(bval_to_bexp1 f tl)

  | VTuple l => ETuple
  	  (map (bval_to_bexp1 f) l)

  | VMap l => EMap
    	(map
      	(prod_map
        	(bval_to_bexp1 f)
        	(bval_to_bexp1 f))
      	l)

  | VClos env ext id vl e fid =>
    	match ext, fid with
    	| [], _ => EFun
        	vl
        	((subst_env (measure_env_exp (rem_vars vl env) e))
        	  (rem_vars vl env)
        	  e)

    	(* This is None in option version *)
    	| _, None => EFun
        	vl
        	((subst_env (measure_env_exp (rem_vars vl env) e))
        	  (rem_vars vl env)
        	  e)

    	| _, Some fid' => ELetRec
        	(bval_to_bexp_ext
          	f
          	(rem_nfifes ext env)
          	ext)
        	(EFunId fid')
    	end
  end.



  Fixpoint subst_env1
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
          (map (subst_env1 fuel' env) el)

      | EFun vl e => EFun
          vl
          (subst_env1 fuel' env e)

      | ECons hd tl => ECons
          (subst_env1 fuel' env hd)
          (subst_env1 fuel' env tl)

      | ETuple l => ETuple
          (map (subst_env1 fuel' env) l)

      | ECall m f l => ECall
          (subst_env1 fuel' env m)
          (subst_env1 fuel' env f)
          (map (subst_env1 fuel' env) l)

      | EPrimOp f l => EPrimOp
          f
          (map (subst_env1 fuel' env) l)

      | EApp exp l => EApp
          (subst_env1 fuel' env exp)
          (map (subst_env1 fuel' env) l)

      | ECase e l => ECase
          (subst_env1 fuel' env e)
          (map
            (fun '(pl, g, b) =>
              (pl,
              (subst_env1 fuel' env g),
              (subst_env1 fuel' env b)))
            l)

      | ELet l e1 e2 => ELet
          l
          (subst_env1 fuel' env e1)
          (subst_env1 fuel' (rem_vars l env) e2)

      | ESeq e1 e2 => ESeq
          (subst_env1 fuel' env e1)
          (subst_env1 fuel' env e2)

      | ELetRec l e => ELetRec
          (map
            (fun '(fid, (vl, b)) =>
              (fid,
              (vl,
              (subst_env1 fuel' (rem_both l vl env) b))))
            l)
          (subst_env1 fuel' (rem_fids l env) e)

      | EMap l => EMap
          (map
            (prod_map
              (subst_env1 fuel' env)
              (subst_env1 fuel' env))
            l)

      | ETry e1 vl1 e2 vl2 e3 => ETry
          (subst_env1 fuel' env e1)
          vl1
          (subst_env1 fuel' (rem_vars vl1 env) e2)
          vl2
          (subst_env1 fuel' (rem_vars vl2 env) e3)

      | EVar var =>
          match (get_value env (inl var)) with
          | Some [v] => bval_to_bexp1 (subst_env1 fuel')  v
          | Some vs => EValues
              (map (bval_to_bexp (subst_env1 fuel')) vs)
          | _ => e
          end

      | EFunId fid =>
          match (get_value env (inr fid)) with
          | Some [v] => bval_to_bexp (subst_env1 fuel') v
          | Some vs => EValues
              (map (bval_to_bexp (subst_env1 fuel')) vs)
          | _ => e
          end
      end
  end.



  Fixpoint subst_env2
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
        	(map (subst_env2 fuel' env) el)

	    | EFun vl e => EFun
      	  vl
      	  (subst_env2 fuel' env e)

	    | ECons hd tl => ECons
        	(subst_env2 fuel' env hd)
        	(subst_env2 fuel' env tl)

	    | ETuple l => ETuple
        	(map (subst_env2 fuel' env) l)

	    | ECall m f l => ECall
        	(subst_env2 fuel' env m)
        	(subst_env2 fuel' env f)
        	(map (subst_env2 fuel' env) l)

	    | EPrimOp f l => EPrimOp
      	  f
      	  (map (subst_env2 fuel' env) l)

	    | EApp exp l => EApp
        	(subst_env2 fuel' env exp)
        	(map (subst_env2 fuel' env) l)

	    | ECase e l => ECase
        	(subst_env2 fuel' env e)
        	(map
          	(fun '(pl, g, b) =>
            	(pl,
            	(subst_env2 fuel' env g),
            	(subst_env2 fuel' env b)))
          	l)

	    | ELet l e1 e2 => ELet
        	l
        	(subst_env2 fuel' env e1)
        	(subst_env2 fuel' (rem_vars l env) e2)

	    | ESeq e1 e2 => ESeq
        	(subst_env2 fuel' env e1)
        	(subst_env2 fuel' env e2)

	    | ELetRec l e => ELetRec
        	(map
          	(fun '(fid, (vl, b)) =>
            	(fid,
            	(vl,
            	(subst_env2 fuel' (rem_both l vl env) b))))
          	l)
        	(subst_env2 fuel' (rem_fids l env) e)

	    | EMap l => EMap
        	(map
          	(prod_map
            	(subst_env2 fuel' env)
            	(subst_env2 fuel' env))
          	l)

	    | ETry e1 vl1 e2 vl2 e3 => ETry
        	(subst_env2 fuel' env e1)
        	vl1
        	(subst_env2 fuel' (rem_vars vl1 env) e2)
        	vl2
        	(subst_env2 fuel' (rem_vars vl2 env) e3)

	    | EVar var =>
        	match (get_value env (inl var)) with
        	| Some [v] =>
            	match v with
              | VNil => ENil

              | VLit l => ELit l

              | VCons hd tl => ECons
              	(bval_to_bexp (subst_env2 fuel') hd)
              	(bval_to_bexp (subst_env2 fuel') tl)

              | VTuple l => ETuple
              	(map (bval_to_bexp (subst_env2 fuel')) l)

              | VMap l => EMap
              	(map
                	(prod_map
                  	(bval_to_bexp (subst_env2 fuel'))
                  	(bval_to_bexp (subst_env2 fuel')))
                	l)

              | VClos env' ext id vl body fid =>
                	match ext, fid with
                	| [], _ => EFun
                	        vl
                	        (subst_env2 fuel' (rem_vars vl env') body)

                	(* This is None in option version *)
                	| _, None => EFun
                    	vl
                    	(subst_env2 fuel' (rem_vars vl env') body)

                	| _, Some fid' => ELetRec
                    	(bval_to_bexp_ext
                      	(subst_env2 fuel')
                      	(rem_nfifes ext env')
                      	ext)
                    	(EFunId fid')
                	end
              end
        	| _ => e
        	end

	    | EFunId fid =>
        	match (get_value env (inr fid)) with
        	| Some [v] =>
            	match v with
              | VNil => ENil

              | VLit l => ELit l

              | VCons hd tl => ECons
              	(bval_to_bexp (subst_env2 fuel') hd)
              	(bval_to_bexp (subst_env2 fuel') tl)

              | VTuple l => ETuple
              	(map (bval_to_bexp (subst_env2 fuel')) l)

              | VMap l => EMap
              	(map
                	(prod_map
                  	(bval_to_bexp (subst_env2 fuel'))
                  	(bval_to_bexp (subst_env2 fuel')))
                	l)

              | VClos env' ext id vl body fid =>
                	match ext, fid with
                	| [], _ => EFun
                	        vl
                	        (subst_env2 fuel' (rem_vars vl env') body)

                	(* This is None in option version *)
                	| _, None => EFun
                    	vl
                    	(subst_env2 fuel' (rem_vars vl env') body)

                	| _, Some fid' => ELetRec
                    	(bval_to_bexp_ext
                      	(subst_env2 fuel')
                      	(rem_nfifes ext env')
                      	ext)
                    	(EFunId fid')
                	end
              end
        	| _ => e
        	end
	    end
  end.



End Substitue.












