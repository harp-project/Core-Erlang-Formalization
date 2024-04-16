From CoreErlang.BigStep Require Import BigStep.



Module SubstBigStep.


Import BigStep.
Import ListNotations.



Fixpoint mapOption {A B} (f : A -> nat -> option B) (l : list A) (fuel : nat) : option (list B) :=
  match fuel with
  | 0 => None
  | S fuel' =>  match l with
                | [] => Some []
                | x :: xs => match f x fuel' with
                            | Some y => match mapOption f xs fuel' with
                                        | Some ys => Some (y :: ys)
                                        | None => None
                                        end
                            | None => None
                            end
                end
  end.


(*Definition mapNone {A} (n : nat) : option (A) := None. *)



Fixpoint valueToExpression1 (v : Value) (fuel : nat) : option Expression :=
  match fuel with
  | 0 => None
  | S fuel' =>  match v with
                | VNil => Some ENil
                | VLit l => Some (ELit l)

                (*TODO*)
                | VClos env ext id vl e => None

                | VCons hd tl => match (valueToExpression1 hd fuel'), (valueToExpression1 tl fuel') with
                                | Some hd', Some tl' => Some (ECons hd' tl')
                                | _, _ => None
                                end
                
                (*TODO*)
                | VTuple l => None(* match (mapOption valueToExpression l fuel') with
                              | Some l' => Some (ETuple l')
                              | None => None
                              end *)
                    (*(ETuple (map valueToExpression l))*)

                (*TODO*)
                | VMap l =>  None (*match (mapOption (fun '(x, y) => match fuel' with
                                                              | 0 => mapNone 
                                                              | S fuel'' => match (valueToExpression x fuel'') with
                                                                            | Some x' => match (valueToExpression y fuel'') with
                                                                                        | Some y' => Some (x', y')
                                                                                        | None => None
                                                                                        end
                                                                            end
                                                              end

                                                              (* match (valueToExpression x fuel') with
                                                              | Some x' => match (valueToExpression y fuel') with
                                                                          | Some y' => Some (x', y')
                                                                          | None => None
                                                                          end
                                                              end *)

                                                              (*match (valueToExpression x fuel'), (valueToExpression y fuel') with
                                                              | Some x', Some y' => Some (x', y')
                                                              | _, _ => None
                                                              end *)
                                            ) l fuel') with
                            | Some l' => Some (EMap l')
                            | None => None
                            end
                            *)
                    (* EMap (map (fun '(x, y) => (valueToExpression x, valueToExpression y)) l) *)
                end
  end.



Fixpoint valueToExpression (v : Value) : option Expression :=
  match v with
  | VNil => Some ENil
  | VLit l => Some (ELit l)

  (*TODO*)
  | VClos env ext id vl e => None

  | VCons hd tl => match (valueToExpression hd), (valueToExpression tl) with
                  | Some hd', Some tl' => Some (ECons hd' tl')
                  | _, _ => None
                  end
  
  (*TODO*)
  | VTuple l => None
      (*(ETuple (map valueToExpression l))*)

  (*TODO*)
  | VMap l =>  None 
      (* EMap (map (fun '(x, y) => (valueToExpression x, valueToExpression y)) l) *)
  end.



Fixpoint substB (e : Expression) (Γ : Environment) : Expression :=
match e with
  | EValues el => EValues (map (fun x => substB x Γ) el)
  | ENil => ENil
  | ELit l => ELit l
  (*TODO*)
  | EVar v => EVar v(*match (get_value Γ (inl v)) with
              | Some n => match (map valueToExpression n) with
                          | Some e => e
                          | None => EVar v
                          end
              | None => EVar v
              end *)
  (*TODO*)
  | EFunId f => EFunId f (* match (get_value Γ (inr f)) with
                | Some n => match (map valueToExpression n) with
                          | Some e => e
                          | None => EFunId f
                          end
                | None => EFunId f
                end*)
  | EFun vl e => EFun vl (substB e Γ)
  | ECons hd tl => ECons (substB hd Γ) (substB tl Γ)
  | ETuple l => ETuple (map (fun x => substB x Γ) l)
  | ECall m f l => ECall (substB m Γ) (substB f Γ) (map (fun x => substB x Γ) l)
  | EPrimOp f l => EPrimOp f (map (fun x => substB x Γ) l)
  | EApp exp l => EApp (substB exp Γ) (map (fun x => substB x Γ) l)
  | ECase e l => ECase (substB e Γ) (map (fun '(pl, g, b) =>
                                      (pl, substB g Γ, substB b Γ)
                                    ) l)
  | ELet l e1 e2 => ELet l (substB e1 Γ) (substB e2 Γ)
  | ESeq e1 e2 => ESeq (substB e1 Γ) (substB e2 Γ)
  | ELetRec l e => ELetRec (map (fun '(fid, (vl, b)) =>
                                            ((fid, (vl, substB b Γ)))
                                          ) l)
                                            (substB e Γ)
  | EMap l => EMap (map (fun '(x, y) => (substB x Γ, substB y Γ)) l)
  | ETry e1 vl1 e2 vl2 e0 => ETry (substB e1 Γ)
                                                vl1 (substB e2 Γ)
                                                vl2 (substB e0 Γ)
  end.
  
  
  End SubstBigStep.