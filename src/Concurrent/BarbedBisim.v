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

(* Definition isUntaken (ι : PID) (Π : ProcessPool) : Prop :=
  Π ι = None /\ isUsed ι Π. *)

Definition symClos {T : Type} (R : T -> T -> Prop) : T -> T -> Prop :=
  fun t1 t2 => R t1 t2 /\ R t2 t1.

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
  Forall (fun x => ~isUntaken x n2) (PIDsOf spawnPIDOf l) /\
  (forall ι, n1.2 ι = None ->
             In ι (PIDsOf sendPIDOf l) -> 
             ~In ι (PIDsOf spawnPIDOf l) ->
        n2.2 ι = None /\
        In ι (PIDsOf sendPIDOf l') /\
        ~In ι (PIDsOf spawnPIDOf l')).

(* This relation is not transitive unfortunately, since isUsed is not
   in the conclusion *)
Definition preCompatibleNodes (n1 n2 : Node) : Prop :=
  forall ι, isUntaken ι n1 -> n2.2 ι = None.

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
Notation "A ~ B 'using' U" := (barbedBisim U A B) (at level 70).

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

Theorem barbedBisim_refl :
  forall U A, ether_wf A.1 -> A ~ A using U.
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

Theorem barbedBisim_sym :
  forall U A B, A ~ B using U -> B ~ A using U.
Proof.
  cofix IH.
  intros. inv H. constructor; auto.
  * split; apply H0.
  * clear H6 H4. intros.
    apply H5 in H. destruct_hyps.
    do 2 eexists. split. 2: split. 3: split. 3: eassumption.
    1-2: auto.
    now apply IH.
  * clear H6 H4. intros.
    apply H3 in H. destruct_hyps.
    do 2 eexists. split. 2: split. 3: split. 3: eassumption.
    1-2: auto.
    now apply IH.
Qed.

(* Lemma preCompatibleNodes_trans :
  forall A B C, preCompatibleNodes A B -> preCompatibleNodes B C ->
    preCompatibleNodes A C.
Proof.
  intros. intros ι Hi. apply H in Hi.
Qed. *)

Lemma reductionPreCompatibility_app :
  forall As Bs A B,
    reductionPreCompatibility A B As Bs ->
    reductionPreCompatibility B A Bs As ->
    forall As' Bs' A' B' B'' (* B'' A'' *),
      A -[As]ₙ->* A' ->
      (* A' -[ys]ₙ->* A'' -> *)
      B -[Bs]ₙ->* B' ->
      B' -[Bs']ₙ->* B'' ->
      reductionPreCompatibility A' B' As' Bs' ->
      reductionPreCompatibility B' A' Bs' As' ->
      reductionPreCompatibility A B (As ++ As') (Bs ++ Bs').
Proof.
  intros As Bs A B C1 C2 As' Bs' A' B' B'' D1A D1 D2 C1' C2'.
  unfold reductionPreCompatibility in *.
  destruct C1 as [C1_1 C1_2]. destruct C2 as [C2_1 C2_2].
  destruct C1' as [C1_1' C1_2']. destruct C2' as [C2_1' C2_2'].
  split.
  * clear C2_2' C1_2' C1_2 C2_2.
    unfold PIDsOf. rewrite flat_map_app. fold (PIDsOf spawnPIDOf As).
    fold (PIDsOf spawnPIDOf As'). apply Forall_app; split; auto.
    (** Proof by contradiction :
        If ι ∈ (PIDsOf spawnPIDOf ys) 
        1) were used (isUsed ι B), then it couldn't be contained in
           this list (spawn could not happen on it).
        2) were assigned in B (B.2 ι = Some proc), then spawn could
           not happen on it
    *)
    rewrite Forall_forall in *. intros. apply C1_1' in H as H'. clear C1_1'.
    intro H0.
    eapply compatibility_of_reductions in H0 as H0'. 2: eassumption.
    destruct H0'. congruence. destruct_hyps.
    destruct H0. now pose proof (isUsed_no_spawn _ _ _ D1 _ H3).
  * intros ι Ha Hin1 Hin2. unfold PIDsOf in Hin1, Hin2.
    rewrite flat_map_app in *.
    fold (PIDsOf spawnPIDOf As) in *. fold (PIDsOf spawnPIDOf As') in *.
    fold (PIDsOf sendPIDOf As) in Hin1. fold (PIDsOf sendPIDOf As') in Hin1.
    apply not_in_app in Hin2 as [Hin2_1 Hin2_2].
    apply in_app_or in Hin1 as [Hin1 | Hin1].
    - specialize (C1_2 _ Ha Hin1 Hin2_1) as [H8_1 [H8_2 H8_3]]. split; auto.
      split.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now left.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply isUsed_no_spawn. exact D2.
        eapply isUsed_after_send; eauto.
    - eapply no_spawn_included in Hin2_1. 2: eassumption. rewrite Hin2_1 in Ha.
      specialize (C1_2' _ Ha Hin1 Hin2_2) as [H8_1 [H8_2 H8_3]]. split.
      2: split.
      + eapply processes_dont_die_None; eassumption.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now right.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply no_spawn_included_2. eassumption. assumption.
Qed.

Lemma barbedBisim_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ~ B using U ->
      exists B' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ~ B' using U.
Proof.
  intros A A' l IH. induction IH; rename n into A; intros.
  * exists B, []. split. 2: split. 3: split. 3: constructor. 3: assumption.
    1-2: split; constructor; auto.
    1-2: inv H1.
  * rename n' into A'. rename n'' into A''.
    inv H0. apply H4 in H as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    clear H4 H5 H6 H7. apply IHIH in H10. destruct H10 as [B'' [l'' H10]].
    destruct_hyps.
    exists B'', (l' ++ l''). split. 2: split. 3: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
Qed.

Axiom ff : False.

Theorem barbedBisim_trans :
  forall U A B C, A ~ B using U -> B ~ C using U -> A ~ C using U.
Proof.
  cofix IH. intros.
  inv H. pose proof (H0) as BC. inv H0. constructor; auto.
  * clear H4 H6. unfold symClos, preCompatibleNodes.
    split.
    - intros. destruct H1 as [H1 _]. apply H1 in H0.
      exfalso. apply ff.
    - exfalso. apply ff.
  * clear H7. intros. apply H4 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    pose proof (barbedBisim_many _ _ _ H14 _ _ BC).
    destruct H16 as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H15 H19). exists C', l'.
    split. 2: split. 3: split; auto.
    1-2: exfalso; apply ff.
  * intros.
  * exfalso. apply ff.
  * exfalso. apply ff.
Qed.

CoInductive barbedExpansion (U : list PID) : Node -> Node -> Prop :=
| is_expansion A B:
(*   symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 -> *)
  (forall A' a ι, A -[a | ι]ₙ-> A' -> exists B' l, 
    reductionPreCompatibility A B [(a,ι)] l /\
    reductionPreCompatibility B A l [(a,ι)] /\
    length l <= 1 /\ B -[l]ₙ->* B' /\ barbedExpansion U A' B')
  ->
  (forall B' a ι, B -[a | ι]ₙ-> B' -> exists A' l,
    reductionPreCompatibility B A [(a,ι)] l /\
    reductionPreCompatibility A B l [(a,ι)] /\
    length l >= 1 /\ A -[l]ₙ->* A' /\ barbedExpansion U A' B')
  ->
  (forall source dest,
    ~In dest U ->
    exists source', list_biforall Srel (A.1 source dest) (B.1 source' dest))
  ->
  (forall source dest,
    ~In dest U ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    list_biforall Srel (B.1 source dest) (A'.1 source' dest))
->
  barbedExpansion U A B.

Notation "A ⪯ B 'using' U" := (barbedExpansion U A B) (at level 70).

CoInductive barbedBisimUpTo (U : list PID) : Node -> Node -> Prop :=
| is_bisim_up_to A B:
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
  (forall A' a ι, A -[a | ι]ₙ-> A' ->
     exists B' A'' B'' l,
       reductionPreCompatibility A B [(a,ι)] l /\
       reductionPreCompatibility B A l [(a,ι)] /\
       B -[l]ₙ->* B' /\
       A' ⪯ A'' using U /\ B' ⪯ B'' using U /\ barbedBisimUpTo U A'' B'') ->
  (forall source dest,
    ~In dest U ->
    exists source' l B',
    B -[l]ₙ->* B' /\
    list_biforall Srel (A.1 source dest) (B'.1 source' dest)) ->
  (forall B' a ι, B -[a | ι]ₙ-> B' ->
     exists A' B'' A'' l,
       reductionPreCompatibility B A [(a,ι)] l /\
       reductionPreCompatibility A B l [(a,ι)] /\
       A -[l]ₙ->* A' /\
       A' ⪯ A'' using U /\ B' ⪯ B'' using U /\ barbedBisimUpTo U  A'' B'') ->
   (forall source dest,
    ~In dest U ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    list_biforall Srel (B.1 source dest) (A'.1 source' dest))
->
  barbedBisimUpTo U A B.

Notation "A ~⪯~ B 'using' U" := (barbedBisimUpTo U A B) (at level 70).

Theorem barbedBisimUpTo_barbedBisim :
  forall U A B, A ~⪯~ B using U -> A ~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * clear H4 H6 H5. intros. apply H3 in H as H'.
    destruct H' as [B' [A'' [B'' [l H']]]]. destruct_hyps.
    inv H7. inv H8. clear H15 H16 H14 H12 H13 H11.
    apply H10
    
    apply IH in H9.
    
Qed.


