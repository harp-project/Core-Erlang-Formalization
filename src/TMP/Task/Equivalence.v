From CoreErlang.BigStep Require Import BigStep.
Require Import Coq.Lists.List.
Require Import stdpp.list.


Module subst_bigstepigStep.


Import BigStep.
Import ListNotations.


Search ((_ -> option _) -> _ -> _ option).
Search "map".
Search "mapM".
Check mapM.
(*Needed: {A B : Type} (f : A -> option B) (l : list A) : option (list B)*)

Fixpoint sequence {A : Type} (l : list (option A)) : option (list A) :=
  match l with
  | [] => Some []
  | hd :: tl => match hd with
              | Some x => match sequence tl with
                          | Some xs => Some (x :: xs)
                          | None => None
                          end
              | None => None
              end
  end.

Fixpoint value_to_expression (v : Value) : option Expression :=
  match v with
  | VNil => Some ENil
  | VLit l => Some (ELit l)
  (*TODO*)
  | VClos env ext id vl e fid => match (subst_bigstep (EFun vl e) env) with
                              | Some e' => Some (EFun vl e')
                              | None => None
                              end
  | VCons hd tl => match (value_to_expression hd), (value_to_expression tl) with
                  | Some hd', Some tl' => Some (ECons hd' tl')
                  | _, _ => None
                  end
  | VTuple l => match (mapM value_to_expression l) with
                | Some l' => Some (ETuple  l')
                | None => None
                end
  | VMap l =>  match (mapM (fun '(x, y) => match (value_to_expression x), (value_to_expression y) with
                                                    | Some x', Some y' => Some (x', y')
                                                    | _, _ => None
                                                    end
                                                    ) l) with
              | Some l' => Some (EMap l')
              | None => None
              end
  end.
(*with*) Fixpoint subst_bigstep (e : Expression) (Γ : Environment) : option Expression :=
match e with
  | EValues el => match (mapM (fun x => subst_bigstep x Γ) el) with
                  | Some el' => Some (EValues el')
                  | None => None
                  end
  | ENil => Some ENil
  | ELit l => Some (ELit l)
  | EVar v => match (get_value Γ (inl v)) with
              | Some [v'] => value_to_expression v'
              | _ => Some (EVar v)
              end
  | EFunId f =>  match (get_value Γ (inr f)) with
                | Some [f'] => value_to_expression f'
                | _ => Some (EFunId f)
                end
  | EFun vl e => match (subst_bigstep e Γ) with
                | Some e' => Some (EFun vl e')
                | None => None
                end
  | ECons hd tl => match (subst_bigstep hd Γ), (subst_bigstep tl Γ) with
                  | Some hd', Some tl' => Some (ECons hd' tl')
                  | _, _ => None
                  end
  | ETuple l => match (mapM (fun x => subst_bigstep x Γ) l) with
                | Some l' => Some (ETuple l')
                | None => None
                end
  | ECall m f l => match (subst_bigstep m Γ), (subst_bigstep f Γ), (mapM (fun x => subst_bigstep x Γ) l)) with
                  | Some m', Some f', Some l' => Some (ECall m' f' l')
                  | _, _, _ => None
                  end
  | EPrimOp f l => match (mapM (fun x => subst_bigstep x Γ) l) with
                  | Some l' => Some (EPrimOp f l')
                  | None => None
                  end
  | EApp exp l => match (subst_bigstep exp Γ), (mapM (fun x => subst_bigstep x Γ) l) with
                  | Some exp', Some l' => Some (EApp exp' l')
                  | _, _ => None
                  end
  | ECase e l => match (subst_bigstep e Γ) with
                | Some e' => match (mapM (fun '(pl, g, b) =>
                                      match (subst_bigstep g Γ), (subst_bigstep b Γ) with
                                      | Some g', Some b' => Some (pl, g', b')
                                      | _, _ => None
                                      end
                                    ) l) with
                            | Some l' => Some (ECase e' l')
                            | None => None
                            end
                | None => None
                end
  | ELet l e1 e2 => match (subst_bigstep e1 Γ), (subst_bigstep e2 Γ) with
                    | Some e1', Some e2' => Some (ELet l e1' e2')
                    | _, _ => None
                    end
  | ESeq e1 e2 => match (subst_bigstep e1 Γ), (subst_bigstep e2 Γ) with
                  | Some e1', Some e2' => Some (ESeq e1' e2')
                  | _, _ => None
                  end
  | ELetRec l e => match (mapM (fun '(fid, (vl, b)) =>
                                      match (subst_bigstep b Γ) with
                                      | Some b' => Some (fid, (vl, b'))
                                      | None => None
                                      end
                                    ) l), (subst_bigstep e Γ) with
                    | Some l', Some e' => Some (ELetRec l' e')
                    | _, _ => None
                    end
  | EMap l => match (mapM (fun '(x, y) => match (subst_bigstep x Γ), (subst_bigstep y Γ) with
                                                  | Some x', Some y' => Some (x', y')
                                                  | _, _ => None
                                                  end
                                                  ) l) with
              | Some l' => Some (EMap l')
              | None => None
              end
  | ETry e1 vl1 e2 vl2 e0 => match (subst_bigstep e1 Γ), (subst_bigstep e2 Γ), (subst_bigstep e0 Γ) with
                              | Some e1', Some e2', Some e0' => Some (ETry e1' vl1 e2' vl2 e0')
                              | _, _, _ => None
                              end
  end.
  
  
  End subst_bigstepigStep.