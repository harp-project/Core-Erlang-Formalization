From CoreErlang.BigStep Require Import BigStep.

Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import stdpp.list.

Import BigStep.
Import ListNotations.



Module SubstEnviroment.

(*list_sum*)

Fixpoint mesure_exp (e : Expression) : nat :=
  let 
    mesure_exp_list (el : list Expression) : nat :=
      list_sum (map mesure_exp el)
  in
  let 
    mesure_exp_map (epl : list (Expression * Expression)) : nat :=
      list_sum (map (fun '(x, y) => (mesure_exp x) + (mesure_exp y)) epl)
  in
  let 
    mesure_exp_case (l : list ((list Pattern) * Expression * Expression)) : nat :=
      list_sum (map (fun '(pl, g, b) => (mesure_exp g) + (mesure_exp b)) l)
  in 
  let
    mesure_exp_letrec (l : list (FunctionIdentifier * (list Var * Expression))) : nat :=
      list_sum (map (fun '(fid, (vl, b)) => (mesure_exp b)) l)
  in
  match e with
  | EValues el => 1 + (mesure_exp_list el)
  | ENil => 0
  | ELit l => 1
  | EVar v => 1
  | EFunId f => 1
  | EFun vl e => 1 + (mesure_exp e)
  | ECons hd tl => 1 + (mesure_exp hd) + (mesure_exp tl)
  | ETuple l => 1 + mesure_exp_list l
  | ECall m f l => 1 + (mesure_exp m) + (mesure_exp f) + (mesure_exp_list l)
  | EPrimOp f l => 1 + (mesure_exp_list l)
  | EApp exp l => 1 + (mesure_exp exp) + (mesure_exp_list l)
  | ECase e l => 1 + (mesure_exp e) + (mesure_exp_case l)
  | ELet l e1 e2 => 1 + (mesure_exp e1) + (mesure_exp e2)
  | ESeq e1 e2 => 1 + (mesure_exp e1) + (mesure_exp e2)
  | ELetRec l e => 1 + (mesure_exp_letrec l) + (mesure_exp e)
  | EMap l => 1 + (mesure_exp_map l)
  | ETry e1 vl1 e2 vl2 e0 => 1 + (mesure_exp e1) + (mesure_exp e2) + (mesure_exp e0)
  end.



Fixpoint mesure_val (v : Value) : nat :=
  let
    mesure_val_list (vl : list Value) : nat :=
      list_sum (map mesure_val vl)
  in
  let 
    mesure_val_map (vm : list (Value * Value)) : nat :=
      list_sum (map (fun '(x, y) => (mesure_val x) + (mesure_val y)) vm)
  in
  let 
    mesure_val_env (env : Environment) : nat :=
      list_sum (map (fun '(x, y) => (mesure_val y)) env)
  in
  match v with
  | VNil => 0
  | VLit l => 1
  | VClos env ext id vl e fid => 1 + (mesure_val_env env) + (mesure_exp e)
  | VCons hd tl => 1 + (mesure_val hd) + (mesure_val tl)
  | VTuple l => 1 + (mesure_val_list l) 
  | VMap l => 1 + (mesure_val_map l)
  end.



Definition mesure_exp_env (e : Expression) (env : Environment) : nat :=
  let 
    mesure_val_env (env : Environment) : nat :=
      list_sum (map (fun '(x, y) => (mesure_val y)) env)
  in
  (mesure_exp e) + (mesure_val_env env).



Definition mesure_val_list (vl : list Value) : nat :=
  list_sum (map mesure_val vl).



Definition mesure_exp_list (el : list Expression) : nat :=
  let
    sum_nat (l : list nat) : nat :=
      fold_left Nat.add l 0
  in
  list_sum (map mesure_exp el).



(*{measure (mesure_val v)} *)


Fixpoint val_to_exp (v : Value) : option Expression :=
  (*
  let
    val_to_exp_map (x y : Value) : option (Expression * Expression) :=
      match (val_to_exp x), (val_to_exp y) with
      | Some x', Some y' => Some (x', y')
      | _, _ => None
      end
  in
  *)
  match v with
  | VNil => Some ENil
  | VLit l => Some (ELit l)
  (*TODO*)
  | VClos env ext id vl e fid => None (*match (subst_env (EFun vl e) env) with
                              | Some e' => Some (EFun vl e')
                              | None => None
                              end*)
  | VCons hd tl => match (val_to_exp hd), (val_to_exp tl) with
                  | Some hd', Some tl' => Some (ECons hd' tl')
                  | _, _ => None
                  end
  | VTuple l => match (mapM (fun (x : Value) => val_to_exp x : option Expression) l) with
                | Some l' => Some (ETuple l')
                | None => None
                end
  | VMap l =>  match (mapM (fun '(x, y) => match (val_to_exp x), (val_to_exp y) with
                                          | Some x', Some y' => Some (x', y')
                                          | _, _ => None
                                          end) l) with
              | Some l' => Some (EMap l')
              | None => None
              end
  end.

(*with *)

Fixpoint subst_env (e : Expression) (Γ : Environment) : option Expression :=
  let
    subst_env_case (pl : list Pattern) (g : Expression) (b : Expression) : option (list Pattern * Expression * Expression) :=
      match (subst_env g Γ), (subst_env b Γ) with
      | Some g', Some b' => Some (pl, g', b')
      | _, _ => None
      end
  in
  let
    subst_env_letrec (fid : FunctionIdentifier) (vl : list Var) (b : Expression) : option (FunctionIdentifier * (list Var * Expression)) :=
      match (subst_env b Γ) with
      | Some b' => Some (fid, (vl, b'))
      | None => None
      end
  in
  let
    subst_env_map (x y : Expression) : option (Expression * Expression) :=
      match (subst_env x Γ), (subst_env y Γ) with
      | Some x', Some y' => Some (x', y')
      | _, _ => None
      end
  in
  match e with
  | EValues el => match (mapM (fun x => subst_env x Γ) el) with
                  | Some el' => Some (EValues el')
                  | None => None
                  end
  | ENil => Some ENil
  | ELit l => Some (ELit l)
  | EVar v => match (get_value Γ (inl v)) with
              | Some [v'] => val_to_exp v'
              | _ => Some (EVar v)
              end
  | EFunId f =>  match (get_value Γ (inr f)) with
                | Some [f'] => val_to_exp f'
                | _ => Some (EFunId f)
                end
  | EFun vl e => match (subst_env e Γ) with
                | Some e' => Some (EFun vl e')
                | None => None
                end
  | ECons hd tl => match (subst_env hd Γ), (subst_env tl Γ) with
                  | Some hd', Some tl' => Some (ECons hd' tl')
                  | _, _ => None
                  end
  | ETuple l => match (mapM (fun x => subst_env x Γ) l) with
                | Some l' => Some (ETuple l')
                | None => None
                end
  | ECall m f l => match (subst_env m Γ), (subst_env f Γ), (mapM (fun x => subst_env x Γ) l) with
                  | Some m', Some f', Some l' => Some (ECall m' f' l')
                  | _, _, _ => None
                  end
  | EPrimOp f l => match (mapM (fun x => subst_env x Γ) l) with
                  | Some l' => Some (EPrimOp f l')
                  | None => None
                  end
  | EApp exp l => match (subst_env exp Γ), (mapM (fun x => subst_env x Γ) l) with
                  | Some exp', Some l' => Some (EApp exp' l')
                  | _, _ => None
                  end
  | ECase e l => match (subst_env e Γ), (mapM (fun '(pl, g, b) => subst_env_case pl g b) l) with
                | Some e', Some l' => Some (ECase e' l')
                | _, _ => None
                end
  | ELet l e1 e2 => match (subst_env e1 Γ), (subst_env e2 Γ) with
                    | Some e1', Some e2' => Some (ELet l e1' e2')
                    | _, _ => None
                    end
  | ESeq e1 e2 => match (subst_env e1 Γ), (subst_env e2 Γ) with
                  | Some e1', Some e2' => Some (ESeq e1' e2')
                  | _, _ => None
                  end
  | ELetRec l e => match (mapM (fun '(fid, (vl, b)) => subst_env_letrec fid vl b) l), (subst_env e Γ) with
                    | Some l', Some e' => Some (ELetRec l' e')
                    | _, _ => None
                    end
  | EMap l => match (mapM (fun '(x, y) => subst_env_map x y) l) with
              | Some l' => Some (EMap l')
              | None => None
              end
  | ETry e1 vl1 e2 vl2 e0 => match (subst_env e1 Γ), (subst_env e2 Γ), (subst_env e0 Γ) with
                              | Some e1', Some e2', Some e0' => Some (ETry e1' vl1 e2' vl2 e0')
                              | _, _, _ => None
                              end
  end.


(*
ELetRec (l : list (FunctionIdentifier * ((list Var) * Expression))) 
        (e : Expression)
(ext : list (nat * FunctionIdentifier * FunctionExpression))
FunctionExpression: (list Var) * Expression

(EFunId f)
  
VClos env ext id vl e fid
  ext ?= []:
  -> EFun vl e
  -> ELetRec ext (EFunId fid)

*)



















(*
Program Fixpoint val_to_exp2 (v : Value) {measure (mesure_val v)} : Expression :=
  match v with
  | VNil => ENil
  | VLit l => ELit l
  | VClos env ext id vl e fid => EFun vl e
  | VCons hd tl => ECons (val_to_exp2 hd) (val_to_exp2 tl)
  | VTuple l => ETuple (map (fun x => val_to_exp2 x) l)
  | VMap l =>  EMap (map (fun '(x, y) => (val_to_exp2 x, val_to_exp2 y)) l)
  end.
  Next Obligation.
    intros. rewrite <- Heq_v. simpl. lia.
  Qed.
  Next Obligation.
    intros. rewrite <- Heq_v. simpl. lia.
  Qed.
  Next Obligation.
    intros. induction l. intros. admit. (*mesure_val x < mesure_val v*)
  Admitted.
  Next Obligation.
    intro. induction l. admit.
  Admitted.
  Next Obligation.
    intro. induction l. admit.
  Admitted.
  Next Obligation.
    admit.
  Admitted.
*)

(*
Program Fixpoint val_to_exp2 (v : Value) {measure (mesure_val v)} : Expression :=
  let
    fix list_to_exp (vl : list Value) (el : list Expression) : list Expression :=
      match vl with 
      | [] => el
      | hd :: tl => list_to_exp tl (el ++ [val_to_exp2 hd])
      end
  in
  let
    fix map_to_exp (vl : list (Value * Value)) (el : list (Expression * Expression)) : list (Expression * Expression) :=
      match vl with 
      | [] => el
      | hd :: tl => map_to_exp tl (el ++ [(val_to_exp2 (fst hd), val_to_exp2 (snd hd))])
      end
  in
  match v with
  | VNil => ENil
  | VLit l => ELit l
  | VClos env ext id vl e fid => EFun vl e
  | VCons hd tl => ECons (val_to_exp2 hd) (val_to_exp2 tl)
  | VTuple l => ETuple (list_to_exp l [])
  | VMap l =>  EMap (map_to_exp l [])
  end.
  Next Obligation.
    intros. admit.
  Admitted.
  Next Obligation.
    intros. admit.
  Admitted.
  Next Obligation.
    intros. admit.
  Admitted.
  Next Obligation.
    intros. rewrite <- Heq_v. simpl. lia.
  Admitted.
  Next Obligation.
    intros. rewrite <- Heq_v. simpl. lia.
  Admitted.
  Next Obligation.
    intros. simpl. unfold well_founded. intros. constructor. intros. constructor. intros. admit.
  Admitted.


Fixpoint subst_env2 (e : Expression) (Γ : Environment) : Expression :=
  match e with
  | EValues el => map (fun x => subst_env2 x Γ) el
  | ENil => ENil
  | ELit l => ELit l
  | EVar v => match (get_value Γ (inl v)) with
              | Some [v'] => val_to_exp2 v'
              | _ => EVar v
              end
  | EFunId f =>  match (get_value Γ (inr f)) with
                | Some [f'] => val_to_exp2 f'
                | _ => EFunId f
                end
  | EFun vl e => EFun vl (subst_env2 e Γ)
  | ECons hd tl => ECons (subst_env2 hd Γ) (subst_env2 tl Γ)
  | ETuple l => ETuple (map (fun x => subst_env2 x Γ) l)
  | ECall m f l => ECall (subst_env2 m Γ) (subst_env2 f Γ) (map (fun x => subst_env2 x Γ) l)
  | EPrimOp f l => EPrimOp f (map (fun x => subst_env2 x Γ) l)
  | EApp exp l => EApp (subst_env2 exp Γ) (map (fun x => subst_env2 x Γ) l)
  | ECase e l => ECase (subst_env2 e Γ) (map (fun '(pl, g, b) => pl, (subst_env2 g Γ), (subst_env2 b Γ)) l)
  | ELet l e1 e2 => ELet l (subst_env2 e1 Γ) (subst_env2 e2 Γ(*/l*))
  | ESeq e1 e2 => ESeq (subst_env2 e1 Γ) (subst_env2 e2 Γ)
  | ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) => fid, (vl, (subst_env2 b Γ))) l) (subst_env2 e Γ)
  | EMap l => EMap (map (fun '(x, y) => (subst_env2 x Γ), (subst_env2 y Γ)) l)
  | ETry e1 vl1 e2 vl2 e0 => ETry (subst_env2 e1 Γ) vl1 (subst_env2 e2 Γ) vl2 (subst_env2 e0 Γ)
  end.



Definition mesure1 (v : Value) (vltuple : (list Value)) (eltuple : (list Expression)) : nat :=
  (mesure_val v) + (mesure_val_list vltuple) + (mesure_exp_list eltuple).

Program Fixpoint val_to_exp3 (v : Value) (vltuple : (list Value)) (eltuple : (list Expression)) {measure (mesure1 v vltuple eltuple)} : Expression :=
  match eltuple with
  | [] => match v with
          | VNil => ENil
          | VLit l => ELit l
          | VClos env ext id vl e fid => EFun vl e
          | VCons hd tl => ECons (val_to_exp3 hd [] []) (val_to_exp3 tl [] [])
          | VTuple l => ETuple []
          | VMap l =>  EMap []
          end
  | hd :: tl => match vltuple with
                | [] => ETuple (eltuple ++ [val_to_exp3 v [] []])
                | hd' :: tl' => val_to_exp3 hd' tl' (eltuple ++ [val_to_exp3 v [] []])
                end
  end.
  Next Obligation.
    intros. simpl. rewrite <- Heq_v. rewrite <- Heq_eltuple. simpl. admit.
  Admitted.
  Next Obligation.
    intros. simpl. rewrite <- Heq_v. rewrite <- Heq_eltuple. simpl. admit.
  Admitted.
  Next Obligation.
    intros. simpl. rewrite <- Heq_vltuple. rewrite <- Heq_eltuple. simpl.  admit.
  Admitted.
  Next Obligation.
    intros. simpl. rewrite <- Heq_vltuple. rewrite <- Heq_eltuple. simpl. admit.
  Admitted.
  Next Obligation.
    intros. simpl. admit.
  Admitted.
  Next Obligation.
    intros. simpl. admit.
  Admitted.
  (*
  match v with
  | VNil => ENil
  | VLit l => ELit l
  | VClos env ext id vl e fid => EFun vl e
  | VCons hd tl => ECons (val_to_exp3 hd [] []) (val_to_exp3 tl [] [])
  | VTuple l => match l with
                | [] => ETuple eltuple
                | hd :: tl => ENil
                end
  | VMap l =>  EMap []
  end.
  *)
  (*
  match vltuple with
  | [] => match v with
          | VNil => ENil
          | VLit l => ELit l
          | VClos env ext id vl e fid => EFun vl e
          | VCons hd tl => ECons (val_to_exp3 hd [] []) (val_to_exp3 tl [] [])
          | VTuple l => ETuple []
          | VMap l =>  EMap []
          end
  | hd :: tl => match v with
                | VTuple l => ENil
                | _ => ENil
                end
  end.
  *)

*)

End SubstEnviroment.