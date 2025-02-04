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
  - cons_app
  - length_lt_split
  - length_map_eq
  - map_single
* Zips
  - zip_fst
  - zip_snd
  - zip_empty
* Extensions
  - ext_to_env_fst
* Exception
  - exc_to_vals
  - exc_to_vals_eq
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
    ->  exists bl1 bl2,
            bl = bl1 ++ bl2
        /\  length al = length bl1.
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



  Lemma length_lt_split_middle :
    forall A B (al : list A) (bl : list B),
        length al < length bl
    ->  exists bl1 b bl2,
            bl = bl1 ++ [b] ++ bl2
        /\  length al = length bl1.
  Proof.
    itr - A B al bl Hlen'.
    (* #1 Pose Previous Lemma: pose/destruct *)
    pse - length_lt_split as Hsplit: A B al bl Hlen'.
    des - Hsplit as [bl1 [bl2 [Hbl Hlen]]].
    (* #2 Destruct List: destruct *)
    des - bl2.
    * (* #3.1 Congruence: rewrite/subst/lia *)
      rwr - app_nil_r in Hbl.
      sbt.
      lia.
    * (* #3.2 Exists & Assum: exists/split/assumption *)
      exi - bl1 b bl2.
      spl; asm.
  Qed.



  Lemma length_map_eq :
    forall A B (al : list A) (bl : list B) (f : A -> B),
        bl = map f al
    ->  length al = length bl.
  Proof.
    itr.
    pose proof length_map f al.
    sbt.
    bym.
  Qed.



  Lemma map_single :
    forall A B (f : A -> B) a,
      map f [a]
    = [f a].
  Proof.
    trv.
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



  Lemma zip_empty :
    forall A B (al : list A) (bl : list B),
    	length al = length bl
    ->  zip al bl = []
    ->  al = [] /\ bl = [].
  Proof.
    intros.
    destruct al.
    * simpl in H. symmetry in H. apply length_zero_iff_nil in H.
	    subst. auto.
    * destruct bl. inversion H.
	    simpl in H0. inversion H0.
  Qed.



  Lemma zip_equal :
    forall A B (l : list (A * B)) (al : list A) (bl : list B),
    	length al = length bl
    ->  l = zip al bl
    ->  al = (map fst l) /\ bl = (map snd l).
  Proof.
    induction l as [| [x y] l IH]; intros.
    * symmetry in H0. epose proof zip_empty _ _ _ _ H H0.
	  destruct H1. subst. auto.
    * destruct al; destruct bl; simpl in H0; inversion H0. subst.
	  inversion H. specialize (IH al bl H2 eq_refl). destruct IH.
	  simpl. split; f_equal; assumption.
  Qed.



  Lemma zip_combine_eq :
    forall A (l1 l2 : list A),
      combine l1 l2
    = zip l1 l2.
  Proof.
    itr.
    (* Unfold the definition of zip *)
    unfold zip.
    unfold zip_with.
    (* Induction on l1 *)
    gen - l2.
    ind - l1 as [| x1 l1' IH]; itr - l2.
    * (* Base case: l1 is empty *)
      bmp.
    * (* Inductive case: l1 is non-empty *)
      des - l2 as [| x2 l2'].
      - (* l2 is empty *)
        bmp.
      - (* l2 is non-empty *)
        smp.
        bwr - IH.
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









Section Exception.

  Import BigStep.



  Definition exc_to_vals
      (x : Exception)
      : list Value
      :=
    match x with
    | (c, vr, vd) => [exclass_to_value c; vr; vd]
    end.



  Lemma exc_to_vals_eq :
    forall x,
      [exclass_to_value x.1.1; x.1.2; x.2]
    = exc_to_vals x.
  Proof.
    itr.
    des - x as [[c vr] vd].
    bmp.
  Qed.



End Exception.