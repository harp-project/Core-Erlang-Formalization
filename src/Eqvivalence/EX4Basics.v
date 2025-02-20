From CoreErlang.Eqvivalence.Tactics Require Export Tactics.
From CoreErlang.Eqvivalence Require Export E1Induction.
From CoreErlang.Eqvivalence Require Export E2WellFormedMap.
From CoreErlang.Eqvivalence Require Export EX3Notations.
From CoreErlang Require Export Basics.
From CoreErlang.BigStep Require Export BigStep.
From CoreErlang.FrameStack Require Export SubstSemanticsLemmas.
Require Export stdpp.list.

Import EX3Notations.

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












Section Either.



  Lemma left_eq :
    forall A B (a1 a2 : A),
        (inl a1 : sum A B) = inl a2
    <-> a1 = a2.
  Proof.
    intros A B a1 a2.
    split.
    - intros H. inversion H. reflexivity.
    - intros H. subst. reflexivity.
  Qed.



  Lemma right_eq :
    forall A B (b1 b2 : B),
        (inr b1 : sum A B) = inr b2
    <-> b1 = b2.
  Proof.
    intros A B b1 b2.
    split.
    - intros H. inversion H. reflexivity.
    - intros H. subst. reflexivity.
  Qed.






  Lemma left_neq :
    forall A B (a1 a2 : A),
        (inl a1 : sum A B) <> inl a2
    <-> a1 <> a2.
  Proof.
    intros A B a1 a2.
    split.
    - intros H H_eq. apply H. subst. reflexivity.
    - intros H H_eq. inversion H_eq. apply H. assumption.
  Qed.



  Lemma right_neq :
    forall A B (b1 b2 : B),
        (inr b1 : sum A B) <> inr b2
    <-> b1 <> b2.
  Proof.
    intros A B b1 b2.
    split.
    - intros H H_eq. apply H. subst. reflexivity.
    - intros H H_eq. inversion H_eq. apply H. assumption.
  Qed.



End Either.









Section Lists.



  Lemma cons_app :
    forall T (x : T) (l : list T),
      x :: l = [x] ++ l.
  Proof.
    trv.
  Qed.



  Lemma map_nil :
    forall A B (f : A -> B),
      map f [] 
    = [].
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



  Lemma list_fst_eq :
    forall A B (l1 l2 : list (A * B)),
        l1 = l2
    ->  (map fst l1) = (map fst l2).
  Proof.
    itr.
    bwr - H.
  Qed.



  Lemma list_snd_eq :
    forall A B (l1 l2 : list (A * B)),
        l1 = l2
    ->  (map snd l1) = (map snd l2).
  Proof.
    itr.
    bwr - H.
  Qed.



  Lemma list_app_fst :
    forall A B (l l1 l2 : list (A * B)),
        l = l1 ++ l2
    ->  (map fst l) = (map fst l1) ++ (map fst l2).
  Proof.
    itr.
    rewrite H.
    apply map_app.
  Qed.



  Lemma list_app_snd :
    forall A B (l l1 l2 : list (A * B)),
        l = l1 ++ l2
    ->  (map snd l) = (map snd l1) ++ (map snd l2).
  Proof.
    itr.
    rewrite H.
    apply map_app.
  Qed.



  Lemma list_app_inl :
    forall A B (l l1 l2 : list A),
        l = l1 ++ l2
    ->  (map inl l : list (A + B))= (map inl l1) ++ (map inl l2).
  Proof.
    itr.
    rewrite H.
    apply map_app.
  Qed.



  Lemma list_app_inr :
    forall A B (l l1 l2 : list B),
        l = l1 ++ l2
    ->  (map inr l : list (A + B))= (map inr l1) ++ (map inr l2).
  Proof.
    itr.
    rewrite H.
    apply map_app.
  Qed.



End Lists.









Section Length.



  Lemma length_eq :
    forall A (l1 l2 : list A),
        l1 = l2
    ->  length l1 = length l2.
  Proof.
    itr.
    bwr - H.
  Qed.



  Lemma length_cons_eq :
    forall A B a (al : list A) b (bl : list B),
        length (a :: al) = length (b :: bl)
    ->  length al = length bl.
  Proof.
    itr - A B a al b bl Hlen.
    smp - Hlen.
    rwr - Nat.succ_inj_wd in Hlen.
    trv.
  Qed.



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



  Lemma length_lt_split_middle_app :
    forall A l1 l2 l1' l2' (a : A),
        l1 ++ l2 = l1' ++ [a] ++ l2'
    ->  (exists l,
            l1  = l1' ++ [a] ++ l
        /\  l2' = l ++ l2)
      \/
        (exists l,
            l1' = l1 ++ l
        /\  l2  = l ++ [a] ++ l2').
  Proof.
    itr.
    ass >
      (length l1' < length l1
      \/ length l1 = length l1'
      \/ length l1 < length l1'): lia.
    des - H0 as [Hle | [Heq | Hle]].
    * lft.
      pse - length_lt_split: A A l1' l1 Hle.
      des - H0 as [l11 [l12 [Happ Hlen]]].
      sbt.
      des - l12 as [|a' l12]:
            rwr - app_nil_r in Hle;
            lia.
      rwr - cons_app in H.
      do 2 rwl - app_assoc in H.
      sym - Hlen.
      epose proof app_inj_1
            l11 l1'
            ([a'] ++ l12 ++ l2) ([a] ++ l2')
            Hlen H.
      des - H0.
      sbt.
      ivc - H.
      ivc - H1.
      exi - l12.
      ato.
    * rgt.
      epose proof app_inj_1
            l1 l1'
            l2 ([a] ++ l2')
            Heq H.
      des - H0.
      sbt.
      exi - ([] : list A).
      rwr - app_nil_r.
      ato.
    * rgt.
      pse - length_lt_split: A A l1 l1' Hle.
      des - H0 as [l1'1 [l1'2 [Happ Hlen]]].
      sbt.
      do 1 rwl - app_assoc in H.
      epose proof app_inj_1
            l1 l1'1
            l2 (l1'2 ++ [a] ++ l2')
            Hlen H.
      des - H0.
      sbt.
      exi - (l1'2).
      ato.
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



  Lemma length_map_fst :
    forall A B (l : list (A * B)),
      length l
    = (length (map fst l)).
  Proof.
    itr.
    bwr - length_map.
  Qed.



  Lemma length_map_snd :
    forall A B (l : list (A * B)),
      length l
    = (length (map snd l)).
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



  Lemma length_flatten_both_lt :
    forall A B (all : list (A * A)) (bll : list (B * B)),
        length all < length bll
    <-> length (flatten_list all) < length (flatten_list bll).
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



  Lemma length_app_end_any :
    forall A B C (l : list A) (b : B) (c : C),
      length l + length [b]
    = length l + length [c].
  Proof.
    sli.
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



  Lemma length_succ_add_end :
    forall A B (al : list A) a (bl : list B) b,
        S (length al) = S (length bl)
    ->  length (al ++ [a]) = length (bl ++ [b]).
  Proof.
    itr - A B al a bl b Hlen.
    do 2 rewrite length_app.
    sli.
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



  Lemma length_eq_map :
    forall A B (f1 f2 : A -> B) (l1 l2 : list A),
        map f1 l1 = map f2 l2
    ->  length l1 = length l2.
  Proof.
    itr.
    rewrite <- (length_map f1 l1).
    rewrite <- (length_map f2 l2).
    bwr - H.
  Qed.



End Length.









Section List2.



  Lemma list_app_fst_split :
    forall A B (l : list (A * B)) (l1 l2 : list A),
        map fst l = l1 ++ l2
    ->  exists (l1' l2' : list (A * B)),
            l = l1' ++ l2'
        /\  (map fst l1') = l1
        /\  (map fst l2') = l2.
  Proof.
    itr.
    exi - (firstn (length l1) l) (skipn (length l1) l).
    do 2 try spl.
    * epose proof take_drop (base.length l1) l as Htake_drop.
      bym.
    * rwl - firstn_map.
      rwr - H.
      apply take_app_length.
    * rwl - skipn_map.
      rwr - H.
      apply drop_app_length.
  Qed.



  Lemma list_app_snd_split :
    forall A B (l : list (A * B)) (l1 l2 : list B),
        map snd l = l1 ++ l2
    ->  exists (l1' l2' : list (A * B)),
            l = l1' ++ l2'
        /\  map snd l1' = l1
        /\  map snd l2' = l2.
  Proof.
    itr.
    exi - (firstn (length l1) l) (skipn (length l1) l).
    do 2 try spl.
    * epose proof take_drop (base.length l1) l as Htake_drop.
      bym.
    * rwl - firstn_map.
      rwr - H.
      apply take_app_length.
    * rwl - skipn_map.
      rwr - H.
      apply drop_app_length.
  Qed.



  Lemma list_app_inl_split :
    forall A B (l : list A) (l1 l2 : list (A + B)),
        map inl l = l1 ++ l2
    ->  exists (l1' l2' : list A),
            l = l1' ++ l2'
        /\  map inl l1' = l1
        /\  map inl l2' = l2.
  Proof.
    itr.
    exi - (firstn (length l1) l) (skipn (length l1) l).
    do 2 try spl.
    * epose proof take_drop (base.length l1) l as Htake_drop.
      bym.
    * rwl - firstn_map.
      rwr - H.
      apply take_app_length.
    * rwl - skipn_map.
      rwr - H.
      apply drop_app_length.
  Qed.



  Lemma list_app_inr_split :
    forall A B (l : list B) (l1 l2 : list (A + B)),
        map inr l = l1 ++ l2
    ->  exists (l1' l2' : list B),
            l = l1' ++ l2'
        /\  map inr l1' = l1
        /\  map inr l2' = l2.
  Proof.
    itr.
    exi - (firstn (length l1) l) (skipn (length l1) l).
    do 2 try spl.
    * epose proof take_drop (base.length l1) l as Htake_drop.
      bym.
    * rwl - firstn_map.
      rwr - H.
      apply take_app_length.
    * rwl - skipn_map.
      rwr - H.
      apply drop_app_length.
  Qed.



  Lemma list_app_fst_split_other :
    forall A B (l : list (A * B)) (l1 l2 : list A),
        map fst l = l1 ++ l2
    ->  exists (l1' l2' : list (A * B)),
            map snd l = map snd l1' ++  map snd l2'
        /\  length l1' = length l1
        /\  length l2' = length l2.
  Proof.
    itr.
    pse - list_app_fst_split: A B l l1 l2 H.
    des - H0 as [l1' [l2' [Heq [Hl1 Hl2]]]].
    exi - l1' l2'.
    app - list_app_snd in Heq.
    spl; ato.
    do 2 rwr - length_map_fst.
    app - length_eq in Hl1.
    app - length_eq in Hl2.
    spl; ato.
  Qed.



  Lemma list_app_snd_split_other :
    forall A B (l : list (A * B)) (l1 l2 : list B),
        map snd l = l1 ++ l2
    ->  exists (l1' l2' : list (A * B)),
            map fst l = map fst l1' ++  map fst l2'
        /\  length l1' = length l1
        /\  length l2' = length l2.
  Proof.
    itr.
    pse - list_app_snd_split: A B l l1 l2 H.
    des - H0 as [l1' [l2' [Heq [Hl1 Hl2]]]].
    exi - l1' l2'.
    app - list_app_fst in Heq.
    spl; ato.
    do 2 rwr - length_map_snd.
    app - length_eq in Hl1.
    app - length_eq in Hl2.
    spl; ato.
  Qed.



  Lemma list_app_fst_split_middle :
    forall A B (l : list (A * B)) (l1 l2 : list A) a,
        map fst l = l1 ++ [a] ++ l2
    ->  exists (l1' l2' : list (A * B)) b,
            l = l1' ++ [(a, b)] ++ l2'
        /\  (map fst l1') = l1
        /\  (map fst l2') = l2.
  Proof.
    itr.
    pse - list_app_fst_split: A B l l1 ([a] ++ l2) H.
    des - H0 as [l1' [l2' [Heq [Hl1 Hl2]]]].
    des - l2' as [| [a' b] l2'];
          smp - Hl2;
          ivs - Hl2.
    exi - l1' l2' b.
    spl; ato.
  Qed.



  Lemma list_app_fst_split_middle_other :
    forall A B (l : list (A * B)) (l1 l2 : list A) a,
        map fst l = l1 ++ [a] ++ l2
    ->  exists (l1' l2' : list (A * B)) b,
            map snd l = map snd l1' ++ [b] ++ map snd l2'
        /\  length l1' = length l1
        /\  length l2' = length l2.
  Proof.
    itr.
    pse - list_app_fst_split_middle: A B l l1 l2 a H.
    des - H0 as [l1' [l2' [b [Heq [Hl1 Hl2]]]]].
    exi - l1' l2' b.
    app - list_app_snd in Heq.
    smp *.
    spl; ato.
    app - length_eq in Hl1.
    app - length_eq in Hl2.
    rwl - length_map_fst in Hl1.
    rwl - length_map_fst in Hl2.
    ato.
  Qed.



  Lemma list_app_fst_split_middle_both :
    forall A B (l : list (A * B)) (l1 l2 : list A) a,
        map fst l = l1 ++ [a] ++ l2
    ->  exists (l1' l2' : list (A * B)) b,
            l = l1' ++ [(a, b)] ++ l2'
        /\  map snd l = map snd l1' ++ [b] ++ map snd l2'
        /\  (map fst l1') = l1
        /\  (map fst l2') = l2
        /\  length l1' = length l1
        /\  length l2' = length l2.
  Proof.
    itr.
    pse - list_app_fst_split_middle: A B l l1 l2 a H.
    des - H0 as [l1' [l2' [b [Heq [Hl1 Hl2]]]]].
    exi - l1' l2' b.
    do 5 (try spl); ato.
    app - list_app_snd in Heq.
    smp *.
    ato.
    app - length_eq in Hl1.
    rwl - length_map_fst in Hl1.
    ato.
    app - length_eq in Hl2.
    rwl - length_map_fst in Hl2.
    ato.
  Qed.



End List2.









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
        length l = k % 2
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
    ->  (length l = k % 2)
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









Module ExcToValSeqNotation.



  Notation "z 'ᶻ⇒ᵛˢ'" := (exc_to_vals z)
    (at level 20,
      format "z  ᶻ⇒ᵛˢ").



End ExcToValSeqNotation.