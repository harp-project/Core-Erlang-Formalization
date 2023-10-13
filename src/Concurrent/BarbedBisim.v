From CoreErlang Require Export Concurrent.InductiveNodeSemantics
                               Concurrent.ProcessSemantics
                               FrameStack.CTX.

Import ListNotations.


Definition Srel (a b : Signal) :=
match a, b with
 | SMessage e, SMessage e' => forall n, Vrel n e e' /\ Vrel n e' e
 | SExit r b, SExit r' b' => b = b' /\ forall n, Vrel n r r' /\ Vrel n r' r
 | SLink, SLink => True
 | SUnlink, SUnlink => True
 | _, _ => False
end.

Fixpoint usedPidsExp (e : Exp) : list PID :=
match e with
 | VVal e => usedPidsVal e
 | EExp e => usedPidsNonVal e
end
with usedPidsVal (v : Val) : list PID :=
match v with
 | VNil => []
 | VLit l => []
 | VPid p => [p]
 | VCons hd tl => usedPidsVal hd ++ usedPidsVal tl
 | VTuple l => fold_right (fun x acc => usedPidsVal x ++ acc) [] l
 | VMap l =>
   fold_right (fun x acc => usedPidsVal x.1 ++ usedPidsVal x.2 ++ acc) [] l
 | VVar n => []
 | VFunId n => []
 | VClos ext id params e => 
   fold_right (fun x acc => usedPidsExp (snd x) ++ acc) (usedPidsExp e) ext
end

with usedPidsNonVal (n : NonVal) : list PID :=
match n with
 | EFun vl e => usedPidsExp e
 | EValues el => fold_right (fun x acc => usedPidsExp x ++ acc) [] el
 | ECons hd tl => usedPidsExp hd ++ usedPidsExp tl
 | ETuple l => fold_right (fun x acc => usedPidsExp x ++ acc) [] l
 | EMap l =>
   fold_right (fun x acc => usedPidsExp x.1 ++ usedPidsExp x.2 ++ acc) [] l
 | ECall m f l => fold_right (fun x acc => usedPidsExp x ++ acc)
                             (usedPidsExp m ++ usedPidsExp f) l
 | EPrimOp f l => fold_right (fun x acc => usedPidsExp x ++ acc) [] l
 | EApp exp l => fold_right (fun x acc => usedPidsExp x ++ acc) (usedPidsExp exp) l
 | ECase e l => fold_right (fun x acc => usedPidsExp x.1.2 ++ usedPidsExp x.2 ++ acc) (usedPidsExp e) l
 | ELet l e1 e2 => usedPidsExp e1 ++ usedPidsExp e2
 | ESeq e1 e2 => usedPidsExp e1 ++ usedPidsExp e2
 | ELetRec l e => fold_right (fun x acc => usedPidsExp x.2 ++ acc) (usedPidsExp e) l
 | ETry e1 vl1 e2 vl2 e3 => usedPidsExp e1 ++ usedPidsExp e2 ++ usedPidsExp e3
end.

Definition usedPidsRed (r : Redex) : list PID :=
match r with
 | RExp e => usedPidsExp e
 | RValSeq vs => fold_right (fun x acc => usedPidsVal x ++ acc) [] vs
 | RExc e => usedPidsVal e.1.2 ++ usedPidsVal e.2
 | RBox => []
end.

Definition usedPidsIdent (i : FrameIdent) : list PID :=
match i with
 | IValues => []
 | ITuple => []
 | IMap => []
 | ICall m f => usedPidsVal m ++ usedPidsVal f
 | IPrimOp f => []
 | IApp v => usedPidsVal v
end.

Definition usedPidsFrame (f : Frame) : list PID :=
match f with
 | FCons1 hd => usedPidsExp hd
 | FCons2 tl => usedPidsVal tl
 | FParams ident vl el => usedPidsIdent ident ++
                          fold_right (fun x acc => usedPidsVal x ++ acc) [] vl ++
                          fold_right (fun x acc => usedPidsExp x ++ acc) [] el
 | FApp1 l => fold_right (fun x acc => usedPidsExp x ++ acc) [] l
 | FCallMod f l => fold_right (fun x acc => usedPidsExp x ++ acc) (usedPidsExp f) l
 | FCallFun m l => fold_right (fun x acc => usedPidsExp x ++ acc) (usedPidsVal m) l
 | FCase1 l => fold_right (fun x acc => usedPidsExp x.1.2 ++ usedPidsExp x.2 ++ acc)
                          [] l
 | FCase2 lv ex le =>
   fold_right (fun x acc => usedPidsVal x ++ acc) [] lv ++
   fold_right (fun x acc => usedPidsExp x.1.2 ++ usedPidsExp x.2 ++ acc)
              (usedPidsExp ex) le
 | FLet l e => usedPidsExp e
 | FSeq e => usedPidsExp e
 | FTry vl1 e2 vl2 e3 => usedPidsExp e2 ++ usedPidsExp e3
end.

Definition usedPidsStack (fs : FrameStack) : list PID :=
  fold_right (fun x acc => usedPidsFrame x ++ acc) [] fs.

Definition usedPidsProc (p : Process) : list PID :=
match p with
| inl (fs, r, mb, links, flag) => 
    usedPidsStack fs ++
    usedPidsRed r ++
    links ++
    fold_right (fun x acc => usedPidsVal x ++ acc) [] mb.1 ++
    fold_right (fun x acc => usedPidsVal x ++ acc) [] mb.2
| inr links => (* TODO: should links should be considered? - Probably *)
    fold_right (fun x acc => x.1::usedPidsVal x.2 ++ acc) [] links
end.

(* Definition isUsed (ι : PID) (Π : ProcessPool) : Prop :=
  exists ι' p, Π ι' = Some p /\ In ι (usedPidsProc p). *)

(* Definition isUnTaken (ι : PID) (Π : ProcessPool) : Prop :=
  Π ι = None /\ isUsed ι Π. *)

Definition isUnTaken (ι : PID) (n : Node) : Prop :=
  n.2 ι = None /\ isUsed ι n.1.

(* This relation is not transitive unfortunately, since isUsed is not
   in the conclusion *)
Definition preCompatibleNodes (n1 n2 : Node) : Prop :=
  forall ι, isUnTaken ι n1 -> n2.2 ι = None.

Definition symClos {T : Type} (R : T -> T -> Prop) : T -> T -> Prop :=
  fun t1 t2 => R t1 t2 /\ R t2 t1.

Theorem compatibility_of_reduction :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι, isUnTaken ι n ->
      (isUnTaken ι n' \/ spawnPIDOf a = Some ι /\ exists p, n'.2 ι = Some p).
Proof.
  intros. inv H; unfold symClos, preCompatibleNodes.
  * left. destruct H0. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - simpl in *. now apply isUsed_etherAdd.
  * left. destruct H0. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - simpl in *. eapply isUsed_etherPop in H1 as [H1 | H1].
      + eassumption.
      + subst. unfold update in H. now rewrite Nat.eqb_refl in H.
      + assumption.
  * left. destruct H0. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - assumption.
  * clear H3 H4 H1. destruct H0. simpl in *.
    destruct (Nat.eq_dec ι0 ι').
    - subst. right. split; auto.
      eexists. unfold update. rewrite Nat.eqb_refl. reflexivity.
    - left. split.
      + simpl. unfold update in *.
        repeat break_match_goal; eqb_to_eq; subst; try congruence.
      + simpl. assumption.
Qed.


Corollary compatibility_of_reductions :
   forall n n' l, n -[l]ₙ->* n' ->
    forall ι, isUnTaken ι n ->
      (isUnTaken ι n' \/ In ι (PIDsOf spawnPIDOf l) /\ exists p, n'.2 ι = Some p).
Proof.
  intros n n' l H. induction H; intros; auto.
  apply (compatibility_of_reduction _ _ _ _ H) in H1 as [H1 | [H1_1 H1_2]].
  * apply IHclosureNodeSem in H1. destruct H1 as [? | [? ?]]; auto.
    right. simpl. break_match_goal; simpl; auto.
  * right. simpl. rewrite H1_1. split. now constructor.
    destruct H1_2. eapply processes_dont_die_Some in H1. eassumption.
    eauto.
Qed.



Theorem compatibility_of_reduction_rev :
  forall n n' a ι, n -[a | ι]ₙ-> n' ->
    forall ι,
      isUnTaken ι n' ->
      isUnTaken ι n \/
      (sendPIDOf a = Some ι /\ ~isUsed ι n.1 /\ n.2 ι = None).
(*       (spawnPIDOf a = Some ι /\ n.2 ι = None). *)
Proof.
  intros. inv H; unfold symClos, preCompatibleNodes.
  * destruct H0.
    destruct (Nat.eq_dec ι' ι0); simpl; subst.
    - simpl in *.
      destruct (isUsed_dec ι0 ether).
      + left. split. simpl. unfold update in *; now break_match_goal.
        now simpl.
      + right. split; simpl; auto.
        split; auto. unfold update in *; now break_match_goal.
    - left. split.
      + simpl in *. unfold update in *; now break_match_goal.
      + simpl in *. eapply isUsed_etherAdd_rev. eassumption. assumption.
  * destruct H0. left. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - simpl in *. eapply isUsed_etherPop_rev; eassumption.
  * destruct H0. left. split.
    - simpl in *. unfold update in *; now break_match_goal.
    - assumption.
  * clear H3 H4 H1. destruct H0. simpl in *.
    destruct (Nat.eq_dec ι0 ι').
    - subst. left. split.
      + now simpl.
      + now simpl.
    - left. split.
      + simpl. unfold update in *.
        repeat break_match_hyp; eqb_to_eq; subst; try congruence.
      + simpl. assumption.
Qed.

Corollary compatibility_of_reductions_rev :
   forall l n n', n -[l]ₙ->* n' ->
    forall ι,
      isUnTaken ι n' ->
      isUnTaken ι n \/
      (In ι (PIDsOf sendPIDOf l) /\ ~isUsed ι n.1 /\ n.2 ι = None).
Proof.
  induction l using list_length_ind.
  destruct (length l) eqn:Hl; intros.
  * apply length_zero_iff_nil in Hl; subst. inv H0. auto.
  * pose proof Hl.
    eapply eq_sym, last_element_exists in Hl as [l' [x Eq]]. subst.
    apply closureNodeSem_trans_rev in H0 as [n0' [D1 D2]].
    rewrite app_length in H2. simpl in *.
    inv D2. inv H7. eapply compatibility_of_reduction_rev in H5.
    2: eassumption.
    destruct H5. 2: destruct H0.
    - eapply H in D1. 2: lia. 2: eassumption.
      destruct D1; auto. destruct_hyps.
      right; split. 2: split; auto.
      unfold PIDsOf. rewrite flat_map_app. simpl.
      fold (PIDsOf spawnPIDOf l'). apply in_or_app. now left.
    - destruct_hyps. clear H H2 H1.
      unfold isUnTaken.
      eapply processes_dont_die_None in D1 as P3. 2: eassumption.
      destruct (isUsed_dec ι n0.1).
      + left. easy.
      + right. split. 2: easy.
        unfold PIDsOf. rewrite flat_map_app.
        apply in_or_app. simpl. right. rewrite H0. now constructor.
Qed.

Fixpoint overtakes {A : Type} (eq_dec :forall (a b : A), {a = b} + {a <> b}) (a b : A) (l : list A) : Prop :=
  match l with
  | [] => False
  | x :: xs =>
    match eq_dec a x with
    | left _ => True
    | right _ => match eq_dec b x with
                 | left _ => False
                 | right _ => overtakes eq_dec a b xs
                 end
    end
  end.

(* Lemma spawn_overtakes_send :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, In ι (PIDsOf sendPIDOf l) -> In ι (PIDsOf spawnPIDOf l) ->
      overtakes (ι, spawn) (ι, send) l. *)

(* What if a new PID is targeted by a message ->
   PID compatibility should also include sent messages 

   The following definition is sufficient, because if both spawn and send
   is present in the trace for some PID ι, then the spawn will happen first
   always. If there is no spawn (only send) for ι, then this should hold for
   the other trace.
*)
Definition reductionPreCompatibility (n1 n2 : Node) l l' :=
  Forall (fun x => ~isUnTaken x n2) (PIDsOf spawnPIDOf l) /\
  (forall ι, n1.2 ι = None ->
             In ι (PIDsOf sendPIDOf l) -> 
             ~In ι (PIDsOf spawnPIDOf l) ->
        n2.2 ι = None /\
        In ι (PIDsOf sendPIDOf l') /\
        ~In ι (PIDsOf spawnPIDOf l')).

Lemma no_spawn_unTaken :
  forall n n' l, n -[l]ₙ->* n' ->
    forall ι, isUnTaken ι n ->
      ~In ι (PIDsOf spawnPIDOf l).
Proof.
  intros n n' l H. induction H; intros; simpl.
  * congruence.
  * intro Hin. inv H; simpl in *.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + unfold update in *; break_match_goal; auto. congruence.
      + now apply isUsed_etherAdd.
    - apply IHclosureNodeSem in Hin. assumption.
      destruct H1. split; simpl in *.
      + unfold update in *; break_match_goal; auto. congruence.
      + eapply isUsed_etherPop in H2 as [H2 | H2]; try eassumption.
        subst. unfold update in H. now rewrite Nat.eqb_refl in H.
    - assert (isUnTaken ι0 (ether, ι ↦ p' ∥ Π)). {
        destruct H1; split; auto.
        simpl in *. unfold update in *; break_match_goal; auto. congruence.
      }
      apply IHclosureNodeSem in H. apply H.
      destruct a; auto. destruct H3 as [? | [? | ?]]; congruence.
    - destruct Hin.
      + clear H5. subst. destruct H1. simpl in *. congruence.
      + clear H5. assert (isUnTaken ι0 (ether, ι' ↦ inl ([], r, emptyBox, [], false) ∥ ι ↦ p' ∥ Π)). {
          destruct H1; split; auto.
          simpl in *. unfold update in *.
          repeat break_match_goal; auto; try congruence.
          eqb_to_eq. subst. break_match_hyp; try congruence.
        }
        apply IHclosureNodeSem in H5. now apply H5.
Qed.

Lemma included_spawn :
  forall (l : list (Action * PID)) (n n' : Node),
  n -[ l ]ₙ->* n' ->
    forall ι : PID, In ι (PIDsOf spawnPIDOf l) ->
      n'.2 ι <> None.
Proof.
  intros l n n' H. induction H; intros.
  * intro. inv H.
  * inv H; simpl in *; try assumption.
    1-3: apply IHclosureNodeSem; try assumption.
    - firstorder; now subst.
    - clear H5. destruct H1. 2: apply IHclosureNodeSem; try assumption.
      subst. apply processes_dont_die with (ι := ι0) in H0; auto.
      cbn. unfold update. now rewrite Nat.eqb_refl.
Qed.

Theorem reduction_preserves_preCompatibility :
  forall n1 n2, (* symClos *) preCompatibleNodes n1 n2 ->
    forall n1' n2' l l',
      n1 -[l]ₙ->* n1' ->
      n2 -[l']ₙ->* n2' ->
      (* Should not spawn incompatible processes: *)
      reductionPreCompatibility n1 n2 l l' ->
      reductionPreCompatibility n2 n1 l' l ->
        (* symClos *) preCompatibleNodes n1' n2'.
Proof.
  intros.
  unfold preCompatibleNodes in *. destruct H2 as [H2 H4], H3 as [H3 H5]. intros.
  eapply compatibility_of_reductions_rev in H0 as H0'. 2: eassumption.
  destruct H0'.
  * apply H in H7 as H7'.
    destruct (in_dec Nat.eq_dec ι (PIDsOf spawnPIDOf l')).
    - rewrite Forall_forall in H3. apply H3 in i. congruence.
    - eapply no_spawn_included in n. 2: eassumption. now rewrite n in H7'.
  * destruct_hyps.
    destruct (in_dec Nat.eq_dec ι (PIDsOf spawnPIDOf l)).
    - eapply included_spawn in H0. 2: eassumption. now destruct H6.
    - apply (H4 _ H9 H7) in n. destruct_hyps.
      apply (no_spawn_included _ _ _ H1) in H12. now apply H12.
Qed.

Corollary reduction_preserves_compatibility :
  forall n1 n2, symClos preCompatibleNodes n1 n2 ->
    forall n1' n2' l l',
      n1 -[l]ₙ->* n1' ->
      n2 -[l']ₙ->* n2' ->
      reductionPreCompatibility n1 n2 l l' ->
      reductionPreCompatibility n2 n1 l' l ->
        symClos preCompatibleNodes n1' n2'.
Proof.
  intros. destruct H; split.
  * eapply reduction_preserves_preCompatibility.
    2-3: eassumption. all: eassumption.
  * eapply reduction_preserves_preCompatibility.
    2-3: eassumption. all: eassumption.
Qed.

CoInductive barbedBisim (U : list PID) : Node -> Node -> Prop :=
| is_bisim (A B : Node) :
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
  (forall A' a ι,
      A -[a | ι]ₙ-> A' ->
        exists B' l,
          reductionPreCompatibility A B [(a,ι)] l /\
          reductionPreCompatibility B A l [(a,ι)] /\
          B -[l]ₙ->* B' /\ barbedBisim U A' B') ->
  (forall source dest,
      ~In dest U ->
      exists source' l B',
      B -[l]ₙ->* B' /\
      list_biforall Srel (A.1 source dest) (B'.1 source' dest)) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' ->
        exists A' l,
          reductionPreCompatibility B A [(a,ι)] l /\
          reductionPreCompatibility A B l [(a,ι)] /\
          A -[l]ₙ->* A' /\
      barbedBisim U A' B') ->
  (forall source dest,
      ~In dest U ->
      exists source' l A',
      A -[l]ₙ->* A' /\
      list_biforall Srel (B.1 source dest) (A'.1 source' dest)) ->
  barbedBisim U A B
.

Theorem reductionPreCompatibility_refl A A' a ι:
  A -[ a | ι ]ₙ-> A' ->
  reductionPreCompatibility A A [(a, ι)] [(a, ι)].
Proof.
  split; intros.
  * cbn. break_match_goal; auto. constructor; auto.
    intro. destruct H0. destruct a; inv Heqo. inv H.
    1: destruct H3 as [? | [? | ?]]; congruence.
    simpl in *. congruence.
  * cbn in H1. break_match_hyp; inv H1. 2: { inv H3. }
    destruct a; inv Heqo. split; auto. split; auto.
    now constructor.
Qed.

Corollary Srel_refl :
  forall s, SIGCLOSED s -> Srel s s.
Proof.
  destruct s; simpl; auto.
Qed.

(* Co-induction test, this probably can be proven without it *)
Theorem barbedBisim_refl :
  forall U A, ether_wf A.1 -> barbedBisim U A A.
Proof.
  cofix H. intros.
  constructor.
  * unfold symClos, preCompatibleNodes.
    split; intros ι H1; apply H1.
  * assumption.
  * assumption.
  * intros. exists A', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A A' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source, [], A.
    split. constructor. apply forall_biforall_refl.
    specialize (H0 source dest). rewrite Forall_forall in *.
    intros. apply Srel_refl. now apply H0.
  * intros. exists B', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A B' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source, [], A.
    split. constructor. apply forall_biforall_refl.
    specialize (H0 source dest). rewrite Forall_forall in *.
    intros. apply Srel_refl. now apply H0.
Qed.

Definition barbedExpansion (U : list PID) (S : Node -> Node -> Prop) :=
  forall (A B : Node), S A B ->
  (forall A' a ι, A -[a | ι]ₙ-> A' -> exists B' l, 
    reductionPreCompatibility A B [(a,ι)] l /\
    reductionPreCompatibility B A l [(a,ι)] /\
    length l <= 1 /\ B -[l]ₙ->* B' /\ S A' B')
/\
  (forall B' a ι, B -[a | ι]ₙ-> B' -> exists A' l,
    reductionPreCompatibility B A [(a,ι)] l /\
    reductionPreCompatibility A B l [(a,ι)] /\
    length l >= 1 /\ A -[l]ₙ->* A' /\ S A' B')
/\
  (forall source dest,
    ~In dest U ->
    exists source', list_biforall Srel (A.1 source dest) (B.1 source' dest))
/\
  (forall source dest,
    ~In dest U ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    list_biforall Srel (B.1 source dest) (A'.1 source' dest)).

Theorem barbedExpansion_transitive :
  forall U S, barbedExpansion U S ->
    forall A B C, S A B -> S B C -> S A C.
Proof.
  intros. apply H in H0. apply H in H1.
  clear H. destruct_hyps.
Qed.

Definition barbedBisimUpTo (U : list PID) (S : Node -> Node -> Prop) :=
 barbedExpansion U S /\
 forall A B, S A B ->
  (forall A' a ι, A -[a | ι]ₙ-> A' ->
     exists B' A'' B'' l,
       reductionPreCompatibility A B [(a,ι)] l /\
       reductionPreCompatibility B A l [(a,ι)] /\
       B -[l]ₙ->* B' /\
       S A' A'' /\ S B' B'' /\ S A'' B'') /\
  (forall source dest,
    ~In dest U ->
    exists source' l B',
    B -[l]ₙ->* B' /\
    list_biforall Srel (A.1 source dest) (B'.1 source' dest)) /\
  (forall B' a ι, B -[a | ι]ₙ-> B' ->
     exists A' B'' A'' l,
       reductionPreCompatibility B A [(a,ι)] l /\
       reductionPreCompatibility A B l [(a,ι)] /\
       A -[l]ₙ->* A' /\
       S A' A'' /\ S B' B'' /\ S A'' B'') /\
   (forall source dest,
    ~In dest U ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    list_biforall Srel (B.1 source dest) (A'.1 source' dest)).

Theorem barbedBisimUpTo_barbedBisim :
  forall U S, barbedBisimUpTo U S -> barbedBisim U S.
Proof.
  unfold barbedBisimUpTo, barbedBisim, symClos. intros.
  destruct_hyps. split.
  {
    intros.
    apply H3 in H1 as H1'. destruct_hyps.
    apply H in H1. destruct_hyps.
    clear H3 H10 H11 H8 H6.
    apply H1 in H4 as H4'. destruct H4' as [B' [l ?]]. destruct_hyps.
    apply H5 in H4 as H4'. destruct H4' as [B'2 [A'' [B'' [l2 ?]]]]. destruct_hyps.
    
    
    exists n2', l'. do 3 (split; auto).
      
    }
    {
    
    }
  }
Qed.


