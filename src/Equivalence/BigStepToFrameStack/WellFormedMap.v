From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.FrameStack Require Import SubstSemantics.
Require Import stdpp.list.

Import BigStep.

(**
* well_formed_map_bs
* well_formed_map_fs
*)

(**
NOTES:  Later change lists to maps in Syntax
*)



Definition well_formed_map_bs
  (v : Value)
  : Prop
  :=
match v with
| VMap vl =>
    vl
    =
    let (f , l) :=
      (make_value_map
        (fst (split vl)) 
        (snd (split vl)))
    in zip f l

| _ => True
end.






Fixpoint well_formed_map_fs
  (v : Val)
  : Prop
  :=
match v with
| Syntax.VCons hd tl =>
    well_formed_map_fs hd
    /\
    well_formed_map_fs tl

| Syntax.VTuple l =>
    foldr
      (fun v acc =>
        well_formed_map_fs v /\ acc)
      True 
      l

| Syntax.VMap l =>
    l = make_val_map l
    /\
    foldr
      (fun v acc =>
        PBoth well_formed_map_fs v /\ acc)
      True
      l

| _ => True
end.