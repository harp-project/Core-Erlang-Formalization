From CoreErlang.BigStep Require Import BigStep.

Import BigStep.

Module SubstBigStep.


(*To do: valuetoExpreton (option expresion) *)

Fixpoint valueSequenceToExpression (vs : list Value) : Expression :=
match vs with
 | [] => ENil
 | v :: vs' => match v with
               | VNil => ENil
               | VLit l => ECons (ELit l) (valueSequenceToExpression vs')
               | VClos env ext id vl e => ENil
               | VCons hd tl => ECons (ECons (valueSequenceToExpression [hd]) (valueSequenceToExpression [tl])) (valueSequenceToExpression vs')
               | VTuple l => ECons (ETuple (map valueSequenceToExpression l)) (valueSequenceToExpression vs')
               | VMap l => ECons (EMap (map (fun '(x, y) => (valueSequenceToExpression [x], valueSequenceToExpression [y])) l)) (alueSequenceToExpression vs')
                end
end.

Fixpoint substB (e : Expression) (Γ : Environment) : Expression :=
match e with
  | EValues el => EValues (map (fun x => substB x Γ) el)
  | ENil => ENil
  | ELit l => ELit l
  | EVar v => match (get_value Γ (inl v)) with
              | Some n => valueSequenceToExpression n
              | None => EVar v
              end
  | EFunId f => match (get_value Γ f) with
                | Some n => n
                | None => EFunId f
                end
  | EFun vl e => EFun vl (substB e Γ)
  | ECons hd tl => ECons (substB hd Γ) (substB tl Γ)
  | ETuple l => ETuple (map (fun x => substB x Γ) l)
  | ECall m f l => ECall (substB m Γ) (substB f Γ) (map (fun x => substB x Γ) l)
  | EPrimOp f l => EPrimOp f (map (fun x => substB x Γ) l)
  | EApp exp l => EApp (substB exp Γ) (map (fun x => substB x Γ) l)
  | ECase e l => ECase (substB e Γ) (map (fun '(pl, g, b) =>
                                      (pl, substB g (addVars (varsOfPatternList pl) Γ), substB b (addVars (varsOfPatternList pl) Γ))
                                      ) l)
  | ELet l e1 e2 => ELet l (substB e1 Γ) (substB e2 (addVars l Γ))
  | ESeq e1 e2 => ESeq (substB e1 Γ) (substB e2 Γ)
  | ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) =>
                                            (vl, substB b (addNames (map (inr ∘ fst) l ++ map inl vl) Γ))
                                          ) l)
                                            (substB e (addFids (map fst l) Γ))
  | EMap l => EMap (map (fun '(x, y) => (substB x Γ, substB y Γ)) l)
  | ETry e1 vl1 e2 vl2 e0 => ETry (substB e1 Γ)
                                                  vl1 (substB e2 (addVars vl1 Γ))
                                                  vl2 (substB e0 (addVars vl1 Γ))
  end.
  
  End SubstBigStep.