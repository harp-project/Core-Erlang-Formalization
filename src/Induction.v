From CoreErlang Require Export Syntax Basics.
Import ListNotations.

Section CorrectPatInd.

Variables
  (P : Pat -> Prop)(Q : list Pat -> Prop)(R : list (Pat * Pat) -> Prop).

Hypotheses
 (H : P PNil)
 (H0 : forall (l : Lit), P (PLit l))
(*  (H0_2 : forall (p : PID), P (PPid p)) *)
 (H1 :  P PVar)
 (H2 : forall (hd : Pat), P hd -> forall (tl : Pat), P tl -> P (PCons hd tl))
 (H3 : forall (l:list Pat), Q l -> P (PTuple l))
 (H4 : forall (l:list (Pat * Pat)), R l -> P (PMap l))
 (H' : forall v : Pat, P v -> forall l:list Pat, Q l -> Q (v :: l))
 (H0' : forall (v1 : Pat), P v1 -> forall (v2 : Pat), P v2 -> forall l:list (Pat * Pat), R l -> R ((v1, v2) :: l))
 (H1' : Q [])
 (H2' : R []).

Fixpoint Pat_ind2 (v : Pat) : P v :=
  match v as x return P x with
  | PNil => H
  | PLit l => H0 l
(*   | PPid p => H0_2 p *)
  | PVar => H1
  | PCons hd tl => H2 hd (Pat_ind2 hd) tl (Pat_ind2 tl)
  | PTuple l => H3 l ((fix l_ind (l':list Pat) : Q l' :=
                       match l' as x return Q x with
                       | [] => H1'
                       | v::xs => H' v (Pat_ind2 v) xs (l_ind xs)
                       end) l)
  | PMap l => H4 l ((fix l_ind (l' : list (Pat * Pat)) : R l' :=
                      match l' as x return R x with
                      | [] => H2'
                      | (v1, v2)::xs => H0' v1 (Pat_ind2 v1) v2 (Pat_ind2 v2) xs (l_ind xs)
                      end) l)
  end.

End CorrectPatInd.


Section CorrectExpInd.

  Variables
    (P  : Exp -> Prop)
    (PV : Val -> Prop)
    (PE : NonVal -> Prop)
    (Q  : list Exp -> Prop)
    (QV : list Val -> Prop)
    (R  : list (Exp * Exp) -> Prop)
    (RV : list (Val * Val) -> Prop)
    (VV : list (nat * nat * Exp) -> Prop)
    (W : list ((list Pat) * Exp * Exp) -> Prop)
    (Z : list (nat * Exp) -> Prop).

  Hypotheses
   (HV : forall (e : Val), PV e -> P (VVal e))
   (HE : forall (e : NonVal), PE e -> P (EExp e))

   (HV1 : PV VNil)
   (HV2 : forall (l : Lit), PV (VLit l))
   (HV2_2 : forall p, PV (VPid p))
   (HV3 : forall (hd : Val), PV hd -> forall (tl : Val), PV tl ->  PV (VCons hd tl))
   (HV4 : forall (l : list Val), QV l -> PV (VTuple l))
   (HV5 : forall (l : list (Val * Val)), RV l -> PV (VMap l))
   (HV7 : forall (n : Var), PV(VVar n))
   (HV8 : forall (n : FunId), PV(VFunId n))
   (HV9 : forall (id : nat) (vl : nat) (ext : list (nat * nat * Exp)), VV ext -> forall (e : Exp), P e -> PV(VClos ext id vl e))

   (HE1 : forall (n : nat) (e : Exp), P e -> PE (EFun n e))
   (HE2 : forall (el : list Exp), Q el -> PE (EValues el))
   (HE3 : forall (hd : Exp), P hd -> forall (tl : Exp), P tl -> PE (ECons hd tl))
   (HE4 : forall (l : list Exp), Q l -> PE (ETuple l))
   (HE5 : forall (l : list (Exp * Exp)), R l -> PE (EMap l))
   (HE6 : forall (m f : Exp) (l : list Exp), P m -> P f -> Q l -> PE (ECall m f l))
   (HE7 : forall (f : string) (l : list Exp), Q l -> PE (EPrimOp f l))
   (HE8 : forall (e: Exp), P e -> forall (l : list Exp), Q l -> PE (EApp e l))
   (HE9 : forall (e : Exp), P e -> forall (l : list ((list Pat) * Exp * Exp)), W l -> PE (ECase e l) )
   (HE10 : forall (l : nat) (e1 : Exp), P e1 -> forall (e2 : Exp), P e2 -> PE (ELet l e1 e2))
   (HE11: forall (e1 : Exp), P e1 -> forall (e2 : Exp), P e2 -> PE (ESeq e1 e2))
   (HE12: forall (e : Exp), P e -> forall (l : list (nat * Exp)), Z l -> PE (ELetRec l e))
   (HE13: forall (e1 : Exp), P e1 -> forall (vl1 : nat) (e2 : Exp), P e2 -> 
   forall (vl2 : nat) (e3 : Exp), P e3 -> PE (ETry e1 vl1 e2 vl2 e3))
(*    (HE14 : forall l, W l -> PE (EReceive l)) *)
   
   (HQ1 : Q [])
   (HQ2 : forall (e : Exp), P e -> forall (el : list Exp), Q el -> Q (e::el))
   (HQV1: QV [])
   (HQV2: forall (e : Val), PV e -> forall (el : list Val), QV el -> QV (e::el))
   (HR1 : R [])
   (HR2 : forall (e1 : Exp), P e1 -> forall (e2 : Exp), P e2 -> 
   forall (el : list (Exp * Exp)), R el -> R ((e1,e2)::el))
   (HRV1: RV [])
   (HRV2: forall (e1 : Val), PV e1 -> forall (e2 : Val), PV e2 -> 
   forall (el : list (Val * Val)), RV el -> RV ((e1,e2)::el))
   (HVV1 : VV [])
   (HVV2 : forall (n : nat) (m : nat) (e : Exp), P e -> forall (el : list (nat * nat * Exp)), VV el -> VV ((n,m,e)::el))
   (HW1 : W [])
   (HW2 : forall (l : list Pat) (e1 : Exp), P e1 -> forall (e2 : Exp), P e2 ->
    forall (lv : list ((list Pat) * Exp * Exp)), W lv -> 
    W ((l,e1,e2)::lv))
   (HZ1 : Z [])
   (HZ2 : forall (n : nat) (e : Exp), P e -> forall (el : list (nat * Exp)), Z el -> Z ((n,e)::el))
   (*(HW2 : forall (e1 : Exp), P e1 -> forall (e2 : Exp), P e2 ->
    forall (lv : list ((list Pat) * Exp * Exp)), W lv -> 
    forall (l : list Pat), W ((l,e1,e2)::lv) ) *)
   .

  Fixpoint Exp_ind2 (e : Exp) : P e :=
  match e as x return P x with
  | VVal ve => HV ve (Val_ind2 ve)
  | EExp nve => HE nve (NVal_ind2 nve)
  end

  with NVal_ind2 (nve : NonVal) : PE nve :=
  match nve as x return PE x with
  | EFun vl e => HE1 vl e (Exp_ind2 e)
  | EValues el => HE2 el (list_ind Q HQ1 (fun e ls => HQ2 e (Exp_ind2 e) ls) el)
  | ECons hd tl => HE3 hd (Exp_ind2 hd) tl (Exp_ind2 tl)
  | ETuple l => HE4 l (list_ind Q HQ1 (fun e ls => HQ2 e (Exp_ind2 e) ls) l)
  | EMap l => HE5 l (list_ind R HR1 (fun '(e1,e2) ls => HR2 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2) ls) l)
  | ECall m f l => HE6 m f l (Exp_ind2 m) (Exp_ind2 f) (list_ind Q HQ1 (fun e ls => HQ2 e (Exp_ind2 e) ls) l)
  | EPrimOp f l => HE7 f l (list_ind Q HQ1 (fun e ls => HQ2 e (Exp_ind2 e) ls) l)
  | EApp exp l => HE8 exp (Exp_ind2 exp) l (list_ind Q HQ1 (fun e ls => HQ2 e (Exp_ind2 e) ls) l)
  | ECase e l => HE9 e (Exp_ind2 e) l 
  (list_ind W HW1 (fun '(lp, e1, e2) ls => (HW2 lp e1 (Exp_ind2 e1) e2 (Exp_ind2 e2) ls)) l)
  | ELet l e1 e2 => HE10 l e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ESeq e1 e2 => HE11 e1 (Exp_ind2 e1) e2 (Exp_ind2 e2)
  | ELetRec l e => HE12 e (Exp_ind2 e) l (list_ind Z HZ1 (fun '(n,e) ls => HZ2 n e (Exp_ind2 e) ls) l)
  | ETry e1 vl1 e2 vl2 e3 => HE13 e1 (Exp_ind2 e1) vl1 e2 (Exp_ind2 e2) vl2 e3 (Exp_ind2 e3)
(*   | EReceive l => HE14 l (list_ind W HW1 (fun '(lp, e1, e2) ls => (HW2 lp e1 (Exp_ind2 e1) e2 (Exp_ind2 e2) ls)) l) *)
  end
  
  with Val_ind2 (ve : Val) : PV ve :=
  match ve as x return PV x with
  | VNil => HV1
  | VLit l => HV2 l
  | VPid p => HV2_2 p
  | VCons hd tl => HV3 hd (Val_ind2 hd) tl (Val_ind2 tl)
  | VTuple l => HV4 l (list_ind QV HQV1 (fun e ls => HQV2 e (Val_ind2 e) ls) l)
  | VMap l => HV5 l (list_ind RV HRV1 (fun '(e1,e2) ls => HRV2 e1 (Val_ind2 e1) e2 (Val_ind2 e2) ls) l)
  | VVar n => HV7 n
  | VFunId n => HV8 n
  | VClos ext id vl e => HV9 id vl ext (list_ind VV HVV1 (fun '(n,m,e) ls => HVV2 n m e (Exp_ind2 e) ls) ext) e (Exp_ind2 e)
  end
  .
  Combined Scheme Exp_ind from Exp_ind2, NVal_ind2, Val_ind2.

End CorrectExpInd.

Section Val_ind_weakened.

Variables (P : Val -> Prop)
          (Q : list Val -> Prop)
          (R : list (Val * Val) -> Prop).
Hypotheses
  (HV1 : P VNil)
  (HV2 : forall l : Lit, P (VLit l))
  (HV2_2 : forall p : PID, P (VPid p))
  (HV3 : forall hd : Val, P hd -> forall tl : Val, P tl -> P (VCons hd tl))
  (HV4 : forall (l : list Val), Q l -> P (VTuple l))
  (HV5 : forall (l : list (Val * Val)), R l -> P (VMap l))
  (HV6 : forall n : Var, P (VVar n))
  (HV7 : forall n : FunId, P (VFunId n))
  (HV8 : forall (ext : list (nat * nat * Exp)) (id params : nat) (e : Exp),
  P (VClos ext id params e))
  (HQ1: Q [])
  (HQ2: forall (v : Val), P v -> forall (vl : list Val), Q vl -> Q (v::vl))
  (HR1: R [])
  (HR2: forall (v1 : Val), P v1 -> forall (v2 : Val), P v2 -> 
   forall (vl : list (Val * Val)), R vl -> R ((v1,v2)::vl)).

Fixpoint Val_ind_weakened (v : Val) : P v :=
  match v as x return P x with
  | VNil => HV1
  | VLit l => HV2 l
  | VPid p => HV2_2 p
  | VCons hd tl => HV3 hd (Val_ind_weakened hd) tl (Val_ind_weakened tl)
  | VTuple l => HV4 l (list_ind Q HQ1 (fun e ls => HQ2 e (Val_ind_weakened e) ls) l)
  | VMap l => HV5 l (list_ind R HR1 (fun '(e1,e2) ls => HR2 e1 (Val_ind_weakened e1) e2 (Val_ind_weakened e2) ls) l)
  | VVar n => HV6 n
  | VFunId n => HV7 n
  | VClos ext id vl e => HV8 ext id vl e
  end.

End Val_ind_weakened.

Ltac valinduction :=
  match goal with
  | |- forall v : Val, ?P =>
    let FP := fresh "FProp" in
    let v'  := fresh "v" in
      remember (fun v:Val => P) as FP;
      induction v using Val_ind_weakened with
        (Q := Forall FP)
        (R := Forall (PBoth FP)); subst FP
  end.
