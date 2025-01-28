From CoreErlang.Eqvivalence.Tactics Require Export T1ParamZero.
From CoreErlang.Eqvivalence.Tactics Require Export T2ParamSingle.
From CoreErlang.Eqvivalence.Tactics Require Export T3ParamMultiple.
From CoreErlang.Eqvivalence.Tactics Require Export T4Name.
From CoreErlang.Eqvivalence.Tactics Require Export T5Transform.
From CoreErlang.Eqvivalence Require Export Induction.
From CoreErlang.Eqvivalence Require Export WellFormedMap.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.

(* STRUCTURE:
* Lists
  - length_lt_split
  - cons_app
* Zips
  - zip_fst
  - zip_snd
* Extensions
  - ext_to_env_fst
*)












Section Lists.



  Lemma cons_app :
    forall T (x : T) (l : list T),
      x :: l = [x] ++ l.
  Proof.
    trv.
  Qed.



  Lemma length_lt_split :
    forall A B (al : list A) (bl : list B),
        length al < length bl
    ->  exists bl1 bl2 : list B,
            bl = bl1 ++ bl2
        /\  length bl1 = length al.
  Proof.
    (* #1 Exists: intro/exists/split *)
    itr - A B al bl Hl.
    exi - (firstn (length al) bl)
          (skipn (length al) bl).
    spl.
    * (* #2.1 Equality: rewrite *)
      by rewrite take_drop.
    * (* #2.2 Length: rewrite/reflexivity/lia *)
      rwr - firstn_length_le.
      - rfl.
      - lia.
  Qed.



End Lists.









Section Zips.



  Lemma zip_fst :
    forall A B (al : list A) (bl : list B),
    	length al = length bl
    ->  map fst (zip al bl) = al.
  Proof.
    itr - A B al bl Hlen_eq.
    ass > (length al <= length bl) as Hlen_le: lia.
    apply fst_zip.
    asm.
  Qed.



  Lemma zip_snd :
    forall A B (al : list A) (bl : list B),
    	length al = length bl
    ->  map snd (zip al bl) = bl.
  Proof.
    itr - A B al bl Hlen_eq.
    ass > (length bl <= length al) as Hlen_le: lia.
    apply snd_zip.
    asm.
  Qed.



End Zips.









Section Extension.

  Import BigStep.



  Lemma ext_to_env_fst :
    forall ext defext Γ,
      map
        fst
        (map
          (fun '(n, fid, (vars, e)) =>
            (inr fid : (Var + FunctionIdentifier), VClos Γ defext n vars e))
          ext)
    = map (inr ∘ snd ∘ fst) ext.
  Proof.
    itr - ext.
    ind - ext as [| [[n fid] [vars e]] ext IH]: smp.
    itr - defext Γ.
    smp.
    feq.
    spe - IH: defext Γ.
    exa - IH.
  Qed.



End Extension.