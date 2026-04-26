From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.

Fixpoint isWellFormedList_n (n : nat) (v : Val) : Prop :=
  match n, v with
    | 0, VNil => True
    | S n0, VCons hd tl => isWellFormedList_n n0 tl
    | _, _ => False
  end.

Fixpoint isWellFormedNumberList_n (n : nat) (v : Val) : Prop :=
  match n, v with
    | 0, VNil => True
    | S n0, VCons (VLit (Integer _)) tl => isWellFormedNumberList_n n0 tl
    | _, _ => False
  end.

Fixpoint isWellFormed2TupleList_n (n : nat) (v : Val): Prop :=
match n, v with
  | 0, VNil => True
  | S n0, VCons (VTuple [_ ; _]) tl => isWellFormed2TupleList_n n0 tl
  | _, _ => False
end.

Fixpoint list_length (v : Val) :=
  match v with
  | VNil => 0
  | VCons hd tl => S (list_length tl)
  | _ => 0
  end.

(*Well formed list precondition could be alternatively defined by this inductive type*)
Inductive wellFormedListInd : nat -> Val -> Prop :=
 | WFNil : wellFormedListInd 0 VNil
 | WFCons : forall (n : nat) (hd tl : Val), wellFormedListInd n tl -> wellFormedListInd (S n) (VCons hd tl)
.