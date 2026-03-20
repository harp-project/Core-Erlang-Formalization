From CoreErlang.FrameStack Require Import SubstSemantics SubstSemanticsLemmas.

Fixpoint isWellFormedList_n (n : nat) (v : Val): Prop :=
  match n, v with
    | 0, VNil => True
    | S n0, VCons hd tl => isWellFormedList_n n0 tl
    | _, _ => False
  end.

Fixpoint isWellFormedNumberList_n (n : nat) (v : Val): Prop :=
  match n, v with
    | 0, VNil => True
    | S n0, VCons (VLit (Integer _)) tl => isWellFormedNumberList_n n0 tl
    | _, _ => False
  end.

Fixpoint list_length (v : Val) :=
  match v with
  | VNil => 0
  | VCons hd tl => S (list_length tl)
  | _ => 0
  end.