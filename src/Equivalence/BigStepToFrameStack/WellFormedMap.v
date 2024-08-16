From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.

Require Import stdpp.list.

Import BigStep.

Definition well_formed_map (v : Value) : Prop :=
    match v with
    | VMap vl => vl = 
      let (f , l) := (make_value_map (fst (split vl)) (snd (split vl)))
      in zip f l
    | _ => True
    end.

   Fixpoint well_formed_map_framestack (v : Val) : Prop :=
   match v with
   | Syntax.VNil => True
   | Syntax.VLit l => True
   | VPid p => True
   | Syntax.VCons hd tl => well_formed_map_framestack hd /\ well_formed_map_framestack tl
   | Syntax.VTuple l => foldr (fun v acc => well_formed_map_framestack v /\ acc) True l
   | Syntax.VMap l => l = make_val_map l 
      /\ foldr (fun v acc => PBoth well_formed_map_framestack v /\ acc) True l
   (* /\ Forall (PBoth well_formed_map_framestack) l *)
   | VVar n => True
   | VFunId n => True
   | Syntax.VClos ext id params e => True
  end.