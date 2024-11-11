From CoreErlang.TMP.EqBF Require Export Base.

Import BigStep.




(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: MAKE_VALUE_Map /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)


Print make_value_map.

(*
Refactor needed: make_value_map
  uses to Value : list instead of (Value * Value) list
*)

Print map_insert.

Lemma map_insert_unfold :
  forall k v kl vl,
    map_insert k v kl vl
  = match kl with
    | [] => match vl with
            | [] => ([k], [v])
            | _ :: _ => ([], [])
            end
    | k' :: ks =>
        match vl with
        | [] => ([], [])
        | v' :: vs =>
            if Value_ltb k k'
            then (k :: k' :: ks, v :: v' :: vs)
            else
             if Value_eqb k k'
             then (k' :: ks, v' :: vs)
             else (k' :: (map_insert k v ks vs).1, v' :: (map_insert k v ks vs).2)
        end
    end.
Proof.
  itr.
  des - kl; des - vl :- trv.
Qed.

Fixpoint map_insert2
  (kv vv : Value)
  (vl : list (Value * Value))
  : list (Value * Value)
  :=
match vl with
| [] =>  [(kv, vv)]
| (kv', vv') :: vl' =>
    if Value_ltb kv kv'
    then ((kv, vv) :: (kv', vv') :: vl')
    else
      if Value_eqb kv kv'
      then ((kv', vv') :: vl')
      else ((kv', vv') :: (map_insert2 kv vv vl'))
end.

Lemma map_insert2_unfold :
  forall kv vv vl,
    map_insert2 kv vv vl
  = match vl with
    | [] =>  [(kv, vv)]
    | (kv', vv') :: vl' =>
        if Value_ltb kv kv'
        then ((kv, vv) :: (kv', vv') :: vl')
        else
          if Value_eqb kv kv'
          then ((kv', vv') :: vl')
          else ((kv', vv') :: (map_insert2 kv vv vl'))
    end.
Proof.
  itr.
  des - vl; trv.
Qed.

Definition combine_unfold :
  forall A B (l : list A) (l' : list B),
    combine l l'
  = match l with
    | [] => []
    | x :: tl => match l' with
                 | [] => []
                 | y :: tl' => (x, y) :: combine tl tl'
                 end
    end.
Proof.
  itr.
  des - l; des - l' :- trv.
Qed.

Print make_value_map.
Print combine.

Fixpoint make_value_map2
  (vl : list (Value * Value))
  : list (Value * Value)
  :=
match vl with
| [] => []
| (kv', vv') :: vl' => map_insert2 kv' vv' (make_value_map2 vl')
end.

Lemma combine_empty :
  forall A (kvl : list A) (vvl : list A),
      Datatypes.length kvl = Datatypes.length vvl
  ->  combine kvl vvl = []
  ->  kvl = [] /\ vvl = [].
Proof.
  itr - A kvl vvl Hlength Hcombine.
  rwr - combine_unfold in Hcombine.
  case_match.
  * smp - Hlength.
    sym - Hlength.
    app - length_zero_iff_nil as Hempty in Hlength.
    sbt; spl; trv.
  * case_match.
    - ivs - Hlength.
    - ivc - Hcombine.
Qed. 

Lemma map_insert_equal :
  forall kv vv kvl vvl kvl' vvl' vl vl',
      Datatypes.length kvl = Datatypes.length vvl
  ->  map_insert kv vv kvl vvl = (kvl', vvl')
  ->  combine kvl vvl = vl
  ->  combine kvl' vvl' = vl'
  ->  map_insert2 kv vv vl = vl'.
Proof.
  itr - kv vv kvl vvl kvl' vvl' vl vl' Hlength Hinsert Hcombine Hcombine'.
  ind - vl as [| v vl].
  * pse - combine_empty as Hempty: Value kvl vvl Hlength Hcombine.
    des - Hempty as [Hempty_kvl Hempty_vvl].
    sbt; clr - Hcombine.
    ivc - Hinsert.
    bmp.
  * admit.
Admitted.
  

  Theorem bs_map_insert_length1 :
    forall k v kl vl v0,
        Datatypes.length kl < Datatypes.length vl
    ->  length (map_insert k v kl vl).1
      = length (map_insert k v kl (v0 :: vl)).1.
  Proof.
    itr - k v kl vl v0 Hnle.
    rwr - map_insert_unfold.
    ind - kl as [| k1 kl IHkl]; des - vl as [| v1 vl] :- smp - Hnle; sli.
    ass - as Hnle0: smp + Hnle; lia >
      (Datatypes.length kl < Datatypes.length (v1 :: vl)).
    spc - IHkl: Hnle0.
    des > (Value_ltb k k1).
Admitted.

  Theorem bs_map_insert_length_nle :
    forall k v kl vl,
        Datatypes.length kl <= Datatypes.length vl
    ->  length kl <= length (map_insert k v kl vl).1.
  Proof.
    (* #1 Induction List: intro/induction + simpl/lia *)
    itr - k v kl vl Hnle.
    ind - kl as [| k' kl IHkl]: sli |> smp.
    (* #2 Specialize Induction: assert/specialze + simpl/lia/clear *)
    ass - as Hnle0: smp - Hnle; lia >
      (Datatypes.length kl ≤ Datatypes.length vl).
    spc - IHkl: Hnle0.
    (* #3 Case Elimination: destruct + simpl/lia *)
    des - vl as [| v' vl]: smp - Hnle; lia.
    (* #4 Destruct Key: destruct/apply + simpl/lia *)
    des > (Value_ltb k k'): sli.
    des > (Value_eqb k k'): sli |> smp + Hnle.
    app - le_n_S.
    
    rwr + map_insert_unfold in IHkl.
    des - kl as [| k'' kl]; des - vl as [| v'' vl].
    * sli.
    * sli.
    * smp - Hnle. sli.
    * 
    des > (Value_ltb k k''): sli.
    des > (Value_eqb k k''): sli |> smp + IHkl.
    cbn in IHkl.
  Admitted.

Lemma make_value_map_length :
  forall kvl vvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  Datatypes.length (make_value_map kvl vvl).1
    = Datatypes.length (make_value_map kvl vvl).2.
Proof.
  itr - kvl vvl Hlength.
  des - kvl as [| kv kvl]; des - vvl as [| vv vvl] :- smp - Hlength; con + smp.
  ivc - Hlength as Hlength: H0.
  rfl - make_value_map.
  rwr - map_insert_unfold.
  Search Datatypes.length.
  des > ((make_value_map kvl vvl).1); des > ((make_value_map kvl vvl).2).
  1-3: trv.
  des > (Value_ltb kv v); des > (Value_eqb kv v).
  1-3: smp; trv.
Admitted.
  
Lemma make_value_map_empty_keys1 :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  mvvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.
  des - kvl as [| kv kvl]; des - vvl as [| vv vvl] :- smp - Hlength; con.
  * bvs - Hmake.
  * ivc - Hlength as Hlength: H0.
    rfl - make_value_map map_insert in Hmake.
    rwr - map_insert_unfold in Hmake.
    des > ((make_value_map kvl vvl).1); des > ((make_value_map kvl vvl).2) :-
      ivs - Hmake.
    des > (Value_ltb kv v); des > (Value_eqb kv v) :- ivs - Hmake.
Qed.


Lemma make_value_map_empty_keys2 :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  kvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.  
  pse - make_value_map_empty_keys1 as Hmvvl: kvl vvl mvvl Hlength Hmake.
  cwr - Hmvvl in Hmake.
  des - kvl as [| kv kvl]; des - vvl as [| vv vvl] :- smp - Hlength; con.
  ivc - Hlength as Hlength: H0.
  rfl - make_value_map map_insert in Hmake.
  rwr - map_insert_unfold in Hmake.
  des > ((make_value_map kvl vvl).1); des > ((make_value_map kvl vvl).2) :-
    ivs - Hmake.
  des > (Value_ltb kv v); des > (Value_eqb kv v) :- ivs - Hmake.
Qed.

Lemma make_value_map_empty_keys :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  kvl = [] /\ vvl = [] /\ mvvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.
  ind - kvl as [| kv kvl IHkvl]; des - vvl as [| vv vvl] :- smp - Hlength; con.
  * clr - Hlength.
    spl; [trv | spl; [trv | idtac]].
    bvs - Hmake.
  * ivc - Hlength as Hlength: H0.
    smp - Hmake.
    rem - mkvl' mvvl' as Hmkvl Hmvvl:
      ((make_value_map kvl vvl).1)
      ((make_value_map kvl vvl).2).
    ufl - map_insert in Hmake.
  des - vvl as [| vv vvl] :- smp - Hlength; con.
    2: {  smp - Hlength; con.
    spl.
    1: rfl.
    smp - Hmake.
    des - vvl as [| vv vvl].
    - spl.
      1: rfl.
      bvs - Hmake.
    - 
  spl; try spl.
  * ind - kvl as [| kv kvl IHkvl].
    - rfl.
    - smp - Hmake.
Admitted.


Lemma make_value_map_empty_keys1' :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  mvvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.
  des - kvl as [| kv kvl]; des - vvl as [| vv vvl] :- smp - Hlength; con.
  * bvs - Hmake.
  * ivc - Hlength as Hlength: H0.
    rfl - make_value_map map_insert in Hmake.
    rwr - map_insert_unfold in Hmake.
    des > ((make_value_map kvl vvl).1); des > ((make_value_map kvl vvl).2) :-
      ivs - Hmake.
    des > (Value_ltb kv v); des > (Value_eqb kv v) :- ivs - Hmake.
Qed.


Lemma make_value_map_empty_keys2' :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  kvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.
  pse - make_value_map_empty_keys1 as Hmvvl: kvl vvl mvvl Hlength Hmake.
  cwr - Hmvvl in *.
  des - kvl as [| kv kvl]; des - vvl as [| vv vvl] :- smp - Hlength; con.
  ivc - Hlength as Hlength: H0.
  rfl - make_value_map map_insert in Hmake.
  rwr - map_insert_unfold in Hmake.
  psc - make_value_map_length as Hlength_make: kvl vvl Hlength.
  des > ((make_value_map kvl vvl).1).
  {
    smp - Hlength_make.
    sym - Hlength_make.
    app - length_zero_iff_nil as Hempty in Hlength_make.
    rwr - Hempty in *.
    ivs - Hmake.
  }
  des > ((make_value_map kvl vvl).2): ivs - Hlength_make.
  des > (Value_ltb kv v); des > (Value_eqb kv v) :- ivs - Hmake.
Qed.

Lemma make_value_map_empty_keys3' :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  vvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.
  pse - make_value_map_empty_keys1 as Hmvvl: kvl vvl mvvl Hlength Hmake.
  pse - make_value_map_empty_keys2 as Hkvl: kvl vvl mvvl Hlength Hmake.
  cwr - Hmvvl Hkvl in *.
  smp - Hlength.
  sym - Hlength.
  app - length_zero_iff_nil as Hempty in Hlength.
  bwr - Hempty.
Qed.

Lemma make_value_map_empty_keys' :
  forall kvl vvl mvvl,
      Datatypes.length kvl = Datatypes.length vvl
  ->  make_value_map kvl vvl = ([], mvvl)
  ->  kvl = [] /\ vvl = [] /\ mvvl = [].
Proof.
  itr - kvl vvl mvvl Hlength Hmake.
  pse - make_value_map_empty_keys1 as Hmvvl: kvl vvl mvvl Hlength Hmake.
  pse - make_value_map_empty_keys2 as Hkvl: kvl vvl mvvl Hlength Hmake.
  pse - make_value_map_empty_keys3 as Hvvl: kvl vvl mvvl Hlength Hmake.
  cwr - Hmvvl Hkvl Hvvl.
  spl; [trv | spl; trv].
Qed.








(*
////////////////////////////////////////////////////////////////////////////////
//// SECTION: REMOVE /////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

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












