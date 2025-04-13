From CoreErlang.FrameStack Require Export Frames SubstSemantics.
From CoreErlang.Concurrent Require Export ProcessSemantics.

Import Coq.Lists.List.
Import ListNotations.

Fixpoint Exp_eqb_strict (e1 e2 : Exp) : bool :=
  match e1, e2 with
  | VVal a, VVal a' => Val_eqb_strict a a'
  | EExp (EValues l), EExp (EValues l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') 
                                 (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EFun vl e), EExp (EFun vl' e') => Nat.eqb vl vl' && Exp_eqb_strict e e'
  | EExp (ECons hd tl), EExp (ECons hd' tl') => Exp_eqb_strict hd hd' && Exp_eqb_strict tl tl'
  | EExp (ETuple l), EExp (ETuple l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (ECall m f l), EExp (ECall m' f' l') => Exp_eqb_strict f f' && Exp_eqb_strict m m' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EPrimOp f l), EExp (EPrimOp f' l') => String.eqb f f' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (EApp exp l), EExp (EApp exp' l') => Exp_eqb_strict exp exp' && 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Exp_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | EExp (ECase e l), EExp (ECase e' l') => Exp_eqb_strict e e' 
      && Nat.eqb (length l) (length l') 
      && (fix blist l l' := match l, l' with
        | [], [] => true
        | (pl,y,z)::xs, (pl',y',z')::xs' => andb (
          (fix blist l l' := match l, l' with
          | [], [] => true
          | x::xs, x'::xs' => andb (Pat_eqb x x') (blist xs xs')
          | _, _ => false
          end) pl pl') 
          (andb (Exp_eqb_strict y y') (andb (Exp_eqb_strict z z') (blist xs xs')))
                                           | _, _ => false
                                           end) l l' 
  | EExp (ELet l e1 e2), EExp (ELet l' e1' e2') => 
      Nat.eqb l l' && Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2'
  | EExp (ESeq e1 e2), EExp (ESeq e1' e2') => andb (Exp_eqb_strict e1 e1') (Exp_eqb_strict e2 e2')
  | EExp (ELetRec l e), EExp (ELetRec l' e') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Nat.eqb x x') (andb (Exp_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l' && Exp_eqb_strict e e'
  | EExp (EMap l), EExp (EMap l') => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Exp_eqb_strict x x') (andb (Exp_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l'
  | EExp (ETry e1 vl1 e2 vl2 e3), EExp (ETry e1' vl1' e2' vl2' e3') => 
      Nat.eqb vl1 vl1' && Nat.eqb vl2 vl2' &&
      Exp_eqb_strict e1 e1' && Exp_eqb_strict e2 e2' && Exp_eqb_strict e3 e3'
  | _, _ => false
  end
with Val_eqb_strict (v1 v2 : Val) : bool :=
  match v1, v2 with
  | VNil, VNil => true
  | VLit l, VLit l' => Lit_beq l l'
  | VPid p, VPid p' => Nat.eqb p p'
  | VCons hd tl, VCons hd' tl' => Val_eqb_strict hd hd' && Val_eqb_strict tl tl'
  | VTuple l, VTuple l' => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | x::xs, x'::xs' => andb (Val_eqb_strict x x') (blist xs xs')
        | _, _ => false
        end) l l'
  | VMap l, VMap l' => 
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (x,y)::xs, (x',y')::xs' => 
        andb (Val_eqb_strict x x') (andb (Val_eqb_strict y y') (blist xs xs'))
        | _, _ => false
        end) l l'
  | VVar v, VVar v' => Nat.eqb v v'
  | VFunId v, VFunId v' => funid_eqb v v'
  | VClos ext id vc e, VClos ext' id' vc' e' => 
      Nat.eqb id id' && Nat.eqb vc vc' && Exp_eqb_strict e e' &&
      (fix blist l l' := match l, l' with
        | [], [] => true
        | (n1,n2,e)::xs, (n1',n2',e')::xs' => 
        andb (Exp_eqb_strict e e') (andb (Nat.eqb n1 n1') (andb (Nat.eqb n2 n2') (blist xs xs')))
        | _, _ => false
        end) ext ext'
  | _, _ => false
  end.