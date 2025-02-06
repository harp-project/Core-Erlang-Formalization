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



  Lemma map_single :
    forall A B (f : A -> B) a,
      map f [a]
    = [f a].
  Proof.
    trv.
  Qed.



  Lemma flatten_cons :
    forall A (x y : A) (ll : list (A * A)),
      flatten_list ((x, y) :: ll)
    = x :: y :: (flatten_list ll).
  Proof.
    trv.
  Qed.



  Lemma flatten_cons_app1 :
    forall A (x y : A) (ll : list (A * A)),
      flatten_list ((x, y) :: ll)
    = [x] ++ y :: (flatten_list ll).
  Proof.
    trv.
  Qed.



  Lemma nth_after_app :
    forall A a d (al1 al2 : list A),
      nth (length al1) (al1 ++ a :: al2) d
    = a.
  Proof.
    itr.
    ass > (length al1 = length al1 + 0) as Hlen: lia.
    rwr - Hlen.
    rwr - app_nth2_plus.
    bmp.
  Qed.



End Lists.









Section Length.



  Lemma length_empty_fst :
    forall A B (al : list A),
        length al = length ([]: list B)
    ->  al = [].
  Proof.
    itr - A B al Hlen.
    smp - Hlen.
    rwr - length_zero_iff_nil in Hlen.
    trv.
  Qed.



  Lemma length_empty_snd :
    forall A B (al : list A),
        length ([]: list B) = length al
    ->  al = [].
  Proof.
    itr - A B al Hlen.
    smp - Hlen.
    sym - Hlen.
    rwr - length_zero_iff_nil in Hlen.
    trv.
  Qed.



  Lemma length_match2 :
    forall A B C (al : list A) (bl : list B) (cl : list C),
        length al = length cl
    ->  length bl = length cl
    ->  length al = length bl.
  Proof.
    itr - A B C al bl cl Hlen1 Hlen2.
    bwr - Hlen1 Hlen2.
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



  Lemma length_map_inl :
    forall A B (l : list A),
      length l
    = (length (map inl l : list (A + B))).
  Proof.
    itr.
    bwr - length_map.
  Qed.



  Lemma length_map_inr :
    forall A B (l : list B),
      length l
    = (length (map inr l : list (A + B))).
  Proof.
    itr.
    bwr - length_map.
  Qed.



  (*?*)
  Lemma length_map_from_eq :
    forall A B (al : list A) (bl : list B) (f : A -> B),
        bl = map f al
    ->  length al = length bl.
  Proof.
    itr.
    pose proof length_map f al.
    sbt.
    bym.
  Qed.



  (*?*)
  Lemma length_map_from_eq_fst :
    forall A B (al : list A) (bl : list B) (f : A -> B) n,
        bl = map f al
    ->  (length al = n <-> length bl = n).
  Proof.
    itr - A B al bl f n Heq.
    pse - length_map_from_eq: A B al bl f Heq.
    spl; itr; lia.
  Qed.



  (*?*)
  Lemma length_map_from_eq_snd :
    forall A B (al : list A) (bl : list B) (f : A -> B) n,
        bl = map f al
    ->  (n = length al <-> n = length bl).
  Proof.
    itr - A B al bl f n Heq.
    pse - length_map_from_eq: A B al bl f Heq.
    spl; itr; lia.
  Qed.



  Lemma length_app_single_end :
    forall A B (al : list A) (bl : list B) a b,
        length al = length bl
    ->  length (al ++ [a]) = length (bl ++ [b]).
  Proof.
    itr - A B al bl a b Hlen.
    do 2 rewrite length_app.
    sli.
  Qed.



  Lemma length_flatten_both_eq :
    forall A B (all : list (A * A)) (bll : list (B * B)),
        length all = length bll
    <-> length (flatten_list all) = length (flatten_list bll).
  Proof.
    itr - A B all bll.
    spl.
    * itr - Hlen.
      do 2 rewrite length_flatten_list.
      lia.
    * itr - Hlen.
      do 2 rewrite length_flatten_list in Hlen.
      lia.
  Qed.



  Lemma length_app_le :
    forall A (l l' : list A) n,
        length (l ++ l') < n
    ->  length l < n.
  Proof.
    itr - A l l' n Hle.
    rewrite length_app in Hle.
    lia.
  Qed.



  Lemma length_add_end_le :
    forall A (l : list A) (a : A),
        length l < length l + length [a].
  Proof.
    itr - A l a.
    sli.
  Qed.



  Lemma length_add_end_eq :
    forall A (l l' : list A) (a : A) n,
        length (l ++ [a]) = S n
    ->  length l' = n
    ->  length l = length l'.
  Proof.
    itr - A l l' a n Hlen1 Hlen2.
    rewrite length_app in Hlen1.
    smp - Hlen1.
    inversion Hlen1 as [Hlen_eq].
    rwl - Hlen2 in Hlen_eq.
    rwr - Nat.add_1_r in *.
    lia.
  Qed.



  Lemma length_diff_plus1 :
    forall A (l l' : list A) n,
        length l = n + 1
    ->  length l' = n
    ->  exists l'' a,
            l = l'' ++ [a]
        /\  length l'' = length l'.
  Proof.
    itr - A l l' n Hlen1 Hlen2.
    sym - Hlen1.
    rwr - Nat.add_1_r in Hlen1.
    smp - Hlen1.
    epose proof last_element_exists l n Hlen1.
    sym - Hlen1.
    des - H as [l'' [a Hl]].
    rwr - Hl in *.
    exi - l'' a.
    spl. 1: rfl.
    clr - Hl.
    by pose proof length_add_end_eq A l'' l' a n Hlen1 Hlen2.
  Qed.



End Length.









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



  Lemma zip_self :
    forall A B (l : list (A * B)),
      l = zip (map fst l) (map snd l).
  Proof.
    itr.
    ind - l as [| [x1 x2] l IHl]: smp.
    smp.
    bwl - IHl.
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









Section Mods.



  Lemma kmod2list_is_either_empty_or_single :
    forall A (l : list A) k,
        length l = k mod 2
    ->  l = [] \/ exists v, l = [v].
  Proof.
    itr - A l k Hlen.
    rem - mod2 as Hmod2:
      (k mod 2).
    pse - modulo_2: k.
    sbt.
    des - H as [Heven | Hodd].
    * lft.
      cwr - Heven in Hlen.
      rwr - length_zero_iff_nil in Hlen.
      sbt.
      rfl.
    * rgt.
      cwr - Hodd in Hlen.
      des - l: ivs - Hlen.
      exi - a.
      des - l :- ivs - Hlen.
  Qed.



  Lemma kmod2length_combined :
    forall A (ll : list (A * A)) (l : list A) k,
        (length ll = k / 2)
    ->  (length l = k mod 2)
    ->  (length (flatten_list ll ++ l) = k).
  Proof.
    itr - A ll l k Hlen_ll Hlen_l.
    rewrite length_app.
    rewrite length_flatten_list.
    rwr - Nat.mul_comm.
    rewrite Hlen_ll.
    rewrite Hlen_l.
    sym.
    apply Nat.div_mod.
    con.
  Qed.



End Mods.









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