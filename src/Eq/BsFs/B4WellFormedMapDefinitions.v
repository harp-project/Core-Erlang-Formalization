From CoreErlang.Eq.BsFs Require Export B3MakeValueMapLemmas.

Import SubstSemantics.

(* STRUCTURE:
* WellFormedMap
  - fs_wfm_val
  - fs_wfm_val_valseq
  - fs_wfm_val_exception
  - fs_wfm_val_result
*)












Section WellFormedMap.



  Fixpoint fs_wfm_val
    (v : Val)
    : Prop
    :=
  match v with

  | VCons hd tl =>
      fs_wfm_val hd
    /\
      fs_wfm_val tl

  | VTuple l =>
      foldr
        (fun v acc => fs_wfm_val v /\ acc)
        True
        l

  | VMap l =>
      l = make_val_map l
    /\
      foldr
        (fun v acc => PBoth fs_wfm_val v /\ acc)
        True
        l

  | _ => True

  end.



  Definition fs_wfm_valseq
    (vs : ValSeq)
    : Prop
    :=
  foldr (fun v acc => fs_wfm_val v /\ acc) True vs.



  Definition fs_wfm_exception
    (exc : Exception)
    : Prop
    :=
  match exc with
  | (excc, v1, v2) => fs_wfm_val v1 /\ fs_wfm_val v2
  end.



  Definition fs_wfm_result
    (res : Redex)
    : Prop
    :=
  match res with
  | RValSeq vs => fs_wfm_valseq vs
  | RExc exc => fs_wfm_exception exc
  | _ => True
  end.



End WellFormedMap.