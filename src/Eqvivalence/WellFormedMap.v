From CoreErlang.BigStep Require BigStep.
From CoreErlang Require SubstSemantics.
From CoreErlang Require Basics.
Require Import stdpp.list.

(** CONTENT:
* WELLFORMEDMAP_BIGSTEP
  - WellFormedMap_BigStep_Value
    + wfm_bs_val
* WELLFORMEDMAP_FRAMESTACK
  -WellFormedMap_FrameStack_Value
    + wfm_fs_val
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: WELLFORMEDMAP_BIGSTEP ////////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import BigStep.
Import Basics.






Section WellFormedMap_BigStep_Value.



  Fixpoint wfm_bs_val
      (v : Value)
      : Prop
      :=
    match v with
    | VCons hd tl =>
        wfm_bs_val hd
        /\
        wfm_bs_val tl

    | VTuple l =>
        fold_right
          (fun v acc =>
            wfm_bs_val v /\ acc)
          True
          l

    | VClos env _ _ _ _ =>
        fold_right
          (fun kv acc =>
            wfm_bs_val (snd kv) /\ acc)
          True
          env

    | VMap l =>
        (l =
        let (kl , vl) :=
          (make_value_map
            (fst (split l))
            (snd (split l)))
        in zip kl vl)
        /\
        fold_right
          (fun v acc =>
            PBoth wfm_bs_val v /\ acc)
          True
          l

    | _ => True
    end.



End WellFormedMap_BigStep_Value.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: WELLFORMEDMAP_FRAMESTACK /////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)

Import SubstSemantics.






Section WellFormedMap_FrameStack_Value.



  Fixpoint wfm_fs_val
      (v : Val)
      : Prop
      :=
    match v with

    | VCons hd tl =>
        wfm_fs_val hd
      /\
        wfm_fs_val tl

    | VTuple l =>
        fold_right
          (fun v acc => wfm_fs_val v /\ acc)
          True
          l

    | VMap l =>
        l = make_val_map l
      /\
        fold_right
          (fun v acc => PBoth wfm_fs_val v /\ acc)
          True
          l

    | _ => True

    end.



End WellFormedMap_FrameStack_Value.