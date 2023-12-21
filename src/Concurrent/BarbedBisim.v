From CoreErlang Require Export Concurrent.InductiveNodeSemantics
                               Concurrent.ProcessSemantics
                               FrameStack.CTX
                               Concurrent.PIDRenaming.

Import ListNotations.


Definition Srel (a b : Signal) :=
match a, b with
 | SMessage e, SMessage e' => forall n, Vrel n e e' /\ Vrel n e' e
 | SExit r b, SExit r' b' => b = b' /\ forall n, Vrel n r r' /\ Vrel n r' r
 | SLink, SLink => True
 | SUnlink, SUnlink => True
 | _, _ => False
end.
(* 
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
  fold_right (fun x acc => usedPidsFrame x ++ acc) [] fs. *)

Definition usedPIDsProc (p : Process) : list PID :=
match p with
| inl (fs, r, mb, links, flag) => 
    usedPIDsStack fs ++
    usedPIDsRed r ++
    links ++
    fold_right (fun x acc => usedPIDsVal x ++ acc) [] mb.1 ++
    fold_right (fun x acc => usedPIDsVal x ++ acc) [] mb.2
| inr links => (* TODO: should links should be considered? - Probably *)
    fold_right (fun x acc => (x.1::usedPIDsVal x.2) ++ acc) [] links
end.
Print usedPIDsProc.
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
  (forall ι, ι ∉ dom n1.2 ->
             In ι (PIDsOf sendPIDOf l) -> 
             ~In ι (PIDsOf spawnPIDOf l) ->
        ι ∉ dom n2.2 /\
        In ι (PIDsOf sendPIDOf l') /\
        ~In ι (PIDsOf spawnPIDOf l')).

(* This relation is not transitive unfortunately, since isUsed is not
   in the conclusion *)
Definition preCompatibleNodes (n1 n2 : Node) : Prop :=
  forall ι, isUntaken ι n1 -> (* n2.2 ι = None *)
    isUntaken ι n2.

Lemma preCompatibleNodes_trans :
  forall n1 n2 n3, preCompatibleNodes n1 n2 -> preCompatibleNodes n2 n3 ->
    preCompatibleNodes n1 n3.
Proof.
  unfold preCompatibleNodes. intros.
  apply H in H1. now apply H0 in H1.
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
    - eapply compatibility_of_reductions in H7' (* as [H7' | H7'] *).
      2: eassumption.
      assumption. (*  destruct_hyps. exfalso. now apply n. *)
  * destruct_hyps.
    destruct (in_dec Nat.eq_dec ι (PIDsOf spawnPIDOf l)).
    - eapply included_spawn in H0. 2: eassumption. now destruct H6.
    - apply not_elem_of_dom in H9.
      apply (H4 _ H9 H7) in n. destruct_hyps.
      apply not_elem_of_dom in H10.
      pose proof (isUsedEther_after_send _ _ _ H1 _ H11 H12 H10).
      split; try assumption.
      apply -> no_spawn_included; eauto.
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

Definition Signal_eqb (s1 s2 : Signal) : bool :=
match s1,  s2 with
 | SMessage m, SMessage m' => m =ᵥ m'
 | SExit r b, SExit r' b' => Bool.eqb b b' && (r =ᵥ r')
 | SLink, SLink => true
 | SUnlink, SUnlink => true
 | _, _ => false
end.

Notation "s1 ==ₛ s2" := (Signal_eqb s1 s2) (at level 69, no associativity).

Definition Signal_eq (s1 s2 : Signal) : Prop := s1 ==ₛ s2 = true.

Notation "s1 =ₛ s2" := (Signal_eq s1 s2) (at level 69, no associativity).

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
      dest ∉ dom A.2 ->
      exists source' l B',
      B -[l]ₙ->* B' /\
      dest ∉ dom B'.2 /\
      (* list_biforall Srel (A.1 source dest) (B'.1 source' dest) *)
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in *)
      (* A.1 source dest = B'.1 source' dest *)
      option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) ->
  (forall B' a ι,
      B -[a | ι]ₙ-> B' ->
        exists A' l,
          reductionPreCompatibility B A [(a,ι)] l /\
          reductionPreCompatibility A B l [(a,ι)] /\
          A -[l]ₙ->* A' /\
      barbedBisim U A' B') ->
  (forall source dest,
      ~In dest U ->
      dest ∉ dom B.2 ->
      exists source' l A',
      A -[l]ₙ->* A' /\
      dest ∉ dom A'.2 /\
      (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
      (* NOTE: this part could be adjusted based on the equivalence we are
               interested in, as far as this relation is reflexive,
               transitive and symmetric *)
      (* B.1 source dest = A'.1 source' dest *)
      option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest))) ->
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

Corollary Signal_eq_refl :
  forall s, s =ₛ s.
Proof.
  destruct s; cbn; try reflexivity.
  * cbn. unfold "=ₛ". simpl. apply Val_eqb_refl.
  * cbn. unfold "=ₛ". simpl. rewrite Val_eqb_refl.
    now destruct b.
Qed.

Corollary Signal_eq_sym :
  forall s s', s =ₛ s' -> s' =ₛ s.
Proof.
  destruct s eqn:ES1, s' eqn:ES2; unfold "=ₛ"; cbn; intro H; try reflexivity; try now inv H.
  * now rewrite Val_eqb_sym.
  * cbn. rewrite Val_eqb_sym.
    destruct b, b0; auto.
Qed.

Corollary Signal_eq_trans :
  forall s s' s'', s =ₛ s' -> s' =ₛ s'' -> s =ₛ s''.
Proof.
  destruct s eqn:ES1, s' eqn:ES2, s'' eqn:ES3;
    unfold "=ₛ"; cbn; intros H1 H2; try reflexivity; try now inv H1; try now inv H2.
  * erewrite Val_eqb_trans; eauto.
  * apply andb_true_iff in H1, H2. destruct_and!.
    rewrite (Val_eqb_trans _ _ _ H3 H0).
    now destruct b, b0, b1.
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
    split. constructor. split. assumption.
    apply option_biforall_refl.
    intros. apply Signal_eq_refl.
    (* (*  apply forall_biforall_refl. *) reflexivity. *)
    (* specialize (H0 source dest). rewrite Forall_forall in *.
    intros. apply Srel_refl. now apply H0. *)
  * intros. exists B', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A B' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source, [], A.
    split. constructor. split. assumption. (*  reflexivity. *) (* apply forall_biforall_refl.
    specialize (H0 source dest). rewrite Forall_forall in *.
    intros. apply Srel_refl. now apply H0. *)
    apply option_biforall_refl.
    intros. apply Signal_eq_refl.
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
    congruence. (* 
    destruct H0'. (* congruence. *) destruct_hyps.
    destruct H0. pose proof (isUsedEther_no_spawn _ _ _ D1 _ H3). *)
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
        eapply isUsedEther_no_spawn. exact D2.
        eapply isUsedEther_after_send; eauto.
        now apply not_elem_of_dom.
    - eapply no_spawn_included in Hin2_1. 2: eassumption.
      apply not_elem_of_dom in Ha.
      rewrite Hin2_1 in Ha.
      apply not_elem_of_dom in Ha.
      specialize (C1_2' _ Ha Hin1 Hin2_2) as [H8_1 [H8_2 H8_3]]. split.
      2: split.
      + apply not_elem_of_dom. eapply processes_dont_die_None; try eassumption.
        now apply not_elem_of_dom.
      + unfold PIDsOf. rewrite flat_map_app. eapply in_app_iff.
        now right.
      + unfold PIDsOf. rewrite flat_map_app.
        fold (PIDsOf spawnPIDOf Bs). fold (PIDsOf spawnPIDOf Bs').
        apply app_not_in; auto.
        eapply no_spawn_included_2. eassumption.
        apply not_elem_of_dom. assumption.
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

(* Theorem reductionPreCompatibility_trans :
  forall A C B As Bs Cs,
    reductionPreCompatibility A B As Bs ->
    reductionPreCompatibility B C Bs Cs ->
    reductionPreCompatibility A C As Cs.
Proof.
  intros. destruct H, H0. split.
  * rewrite Forall_forall in *. intros.
    apply H in H3 as H3'.
Qed. *)

(* Lemma Vrel_trans :
  forall n v1 v2, Vrel n v1 v2 -> forall v3, Vrel n v2 v3 -> Vrel n v1 v3.
Proof.
  intros n v1 v2 H.
  assert (VALCLOSED v1) by now apply Vrel_closed_l in H. revert H0.
  induction H using Vrel_ind; destruct v3; intros;
    try now (try rewrite Vrel_Fix_eq in H;
             try rewrite Vrel_Fix_eq in H1;
             simpl in *; destruct_hyps; auto).
  * rewrite Vrel_Fix_eq. simpl. split. 2: split.
    1: apply H0.
    1: now apply Vrel_closed_r in H.
    rewrite Vrel_Fix_eq in H. simpl in H. destruct_hyps. subst.
    split. 2: split. 1-2: auto.
Qed. *)

(* Corollary Srel_trans :
  forall s1 s2 s3, Srel s1 s2 -> Srel s2 s3 -> Srel s1 s3.
Proof.
  intros; destruct s1, s2, s3; simpl in *; try contradiction.
  * intros. split; apply CIU_Val_compat_closed_reverse.
    - specialize (H n) as [H _]. specialize (H0 n) as [H0 _].
      apply Erel_Val_compat_closed in H, H0.
      apply Rrel_exp_compat_closed in H, H0.
      apply CIU_iff_Rrel_closed in H, H0.
Qed. *)

(** NOTE: this theorem is needed separately to prove transitivity, because
    using symmetry in the proof for transitivity breaks the guardedness
    conditions! *)
Corollary barbedBisim_many_sym :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, B ~ A using U ->
      exists B' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ B' ~ A' using U.
Proof.
  intros.
  apply barbedBisim_sym in H0.
  pose proof (barbedBisim_many _ _ _ H _ _ H0).
  destruct_hyps. exists x, x0. do 3 (split; auto).
  now apply barbedBisim_sym.
Qed.

Theorem barbedBisim_trans :
  forall U A B C,
    (A ~ B using U -> B ~ C using U -> A ~ C using U).
Proof.
  (**)
  (* intros. apply barbedBisim_sym in H as Hsym.
  apply barbedBisim_sym in H0 as H0sym.
  generalize dependent A. generalize dependent B. revert U C. *)
  (**)
  cofix IH. intros.
  pose proof (H) as AB. inv H. pose proof (H0) as BC. inv H0. constructor; auto.
  * clear -H1 H. destruct H1, H. split.
    1-2: eapply preCompatibleNodes_trans; eassumption.
  * clear H7. intros. apply H4 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    pose proof (barbedBisim_many _ _ _ H14 _ _ BC).
    destruct H16 as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H15 H19). exists C', l'.
    split. 2: split. 3: split; auto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H20 in H25. intro.
        now apply H in H26.
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H1 in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto.
  * intros.
    epose proof (H5 source dest H0 H14). destruct H15 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    pose proof (barbedBisim_many _ _ _ H15 _ _ BC) as [C' [Cs ?]]. destruct_hyps.
    pose proof H21 as B'C'. inv H21.
    specialize (H26 sourceB _ H0 ltac:(assumption)).
    destruct H26 as [sourceC [Cs' [C'' ?]]].
    destruct_hyps.
    exists sourceC, (Cs ++ Cs'), C''.
    split. 2: split.
    - eapply closureNodeSem_trans; eassumption.
    - assumption.
    - clear -H29 H17. (* rewrite <- H29. assumption. *) (* transitivity is needed here! *)
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
  * clear H7. intros. rename B' into C'. apply H12 in H0 as H0'.
    destruct H0' as [B' [l [H0']]]. destruct_hyps.
    (* assert (B ~ A using U) as BA by now apply barbedBisim_sym. *)
    pose proof (barbedBisim_many_sym _ _ _ H14 _ _ AB).
    destruct H16 as [A' [l']]. destruct_hyps.
    (* apply barbedBisim_sym in H15. *)
    (* specialize (IH _ _ _ _ H15 H19). *)
    epose proof (IH _ _ _ _ H19 H15) as IH2. clear IH.
    exists A', l'.
    split. 2: split. 3: split; auto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H20 in H25. intro.
        now apply H1 in H26.
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto.
  * intros.
    epose proof (H13 source dest H0 H14). destruct H15 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    assert (B ~ A using U) as BA by now apply barbedBisim_sym.
    pose proof (barbedBisim_many _ _ _ H15 _ _ BA) as [A' [As ?]]. destruct_hyps.
    pose proof H21 as B'A'. inv H21.
    specialize (H26 sourceB _ H0 ltac:(assumption)).
    destruct H26 as [sourceA [As' [A'' ?]]].
    destruct_hyps.
    exists sourceA, (As ++ As'), A''.
    split. 2: split.
    - eapply closureNodeSem_trans; eassumption.
    - assumption.
    - (* rewrite <- H29. assumption. (* transitivity is needed here! *) *)
      clear -H29 H17.
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
Qed.

CoInductive barbedExpansion (U : list PID) : Node -> Node -> Prop :=
| is_expansion A B:
  symClos preCompatibleNodes A B ->
  ether_wf A.1 -> ether_wf B.1 ->
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
    dest ∉ dom A.2 ->
    exists source', (* list_biforall Srel (A.1 source dest) (B.1 source' dest) *)
    dest ∉ dom B.2 /\
    (* (A.1 source dest) = (B.1 source' dest) *)
    option_list_biforall Signal_eq (A.1 !! (source, dest)) (B.1 !! (source', dest)))
  ->
  (forall source dest,
    ~In dest U ->
    dest ∉ dom B.2 ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    dest ∉ dom A'.2 /\
    (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
    (* (B.1 source dest) = (A'.1 source' dest) *)
    option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))
->
  barbedExpansion U A B.

Notation "A ⪯ B 'using' U" := (barbedExpansion U A B) (at level 70).

Theorem barbedExpansion_implies_bisim :
  forall U A B, A ⪯ B using U -> A ~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * intros. apply H3 in H. destruct H as [B' [l H]]. destruct_hyps.
    apply IH in H10. exists B', l. now auto.
  * intros. apply (H5 source dest) in H. destruct_hyps.
    exists x, [], B. split; auto. now constructor. assumption.
  * intros. apply H4 in H. destruct H as [A' [l H]]. destruct_hyps.
    apply IH in H10. exists A', l. now auto.
Qed.

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
    dest ∉ dom A.2 ->
    exists source' l B',
    B -[l]ₙ->* B' /\
    dest ∉ dom B'.2 /\
    (* list_biforall Srel (A.1 source dest) (B'.1 source' dest) *)
    (* (A.1 source dest) = (B'.1 source' dest) *)
    option_list_biforall Signal_eq (A.1 !! (source, dest)) (B'.1 !! (source', dest))) ->
  (forall B' a ι, B -[a | ι]ₙ-> B' ->
     exists A' B'' A'' l,
       reductionPreCompatibility B A [(a,ι)] l /\
       reductionPreCompatibility A B l [(a,ι)] /\
       A -[l]ₙ->* A' /\
       A' ⪯ A'' using U /\ B' ⪯ B'' using U /\ barbedBisimUpTo U  A'' B'') ->
   (forall source dest,
    ~In dest U ->
    dest ∉ dom B.2 ->
    exists source' l A',
    A -[l]ₙ->* A' /\
    dest ∉ dom A'.2 /\
    (* list_biforall Srel (B.1 source dest) (A'.1 source' dest) *)
    (* (B.1 source dest) = (A'.1 source' dest) *)
    option_list_biforall Signal_eq (B.1 !! (source, dest)) (A'.1 !! (source', dest)))
->
  barbedBisimUpTo U A B.

Notation "A ~⪯~ B 'using' U" := (barbedBisimUpTo U A B) (at level 70).

Corollary diamond_trans :
  forall U A B A' B',
    A ~ A' using U -> B ~ B' using U -> A' ~ B' using U ->
    A ~ B using U.
Proof.
  intros ????? AA' BB' A'B'.
  eapply barbedBisim_trans. exact AA'.
  eapply barbedBisim_trans. exact A'B'.
  now apply barbedBisim_sym.
Qed.


Lemma barbedExpansion_refl :
  forall U A, ether_wf A.1 -> A ⪯ A using U.
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
    - split. slia. split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A A' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists B', [(a, ι)]. split. 2: split.
    - eapply reductionPreCompatibility_refl; eassumption.
    - eapply reductionPreCompatibility_refl; eassumption.
    - split. slia. split. econstructor. eassumption. constructor.
      apply H.
      now pose proof (ether_wf_preserved A B' [(a, ι)] ltac:(econstructor;[eassumption|constructor]) H0).
  * intros. exists source.
    split. assumption.
    apply option_biforall_refl. intros. apply Signal_eq_refl.
  * intros. exists source, [], A.
    split. constructor.
    split. assumption.
    apply option_biforall_refl. intros. apply Signal_eq_refl.
Qed.

Lemma barbedExpansion_is_expansion_up_to :
  forall U A B,
    A ⪯ B using U -> A ~⪯~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * intros. apply H3 in H as H'. destruct H' as [B' [l H']]. destruct_hyps.
    exists B', A', B', l. do 3 (split; auto).
    split. 2: split.
    1-2: apply barbedExpansion_refl.
    - now apply (ether_wf_preserved A A' [(a, ι)] ltac:(econstructor;[eassumption|constructor])).
    - now apply (ether_wf_preserved _ _ _ H10).
    - now apply IH.
  * intros. apply (H5 source) in H. destruct H as [sourceB H].
    exists sourceB, [], B. split. constructor. assumption. assumption.
  * intros. apply H4 in H as H'. destruct H' as [A' [l H']]. destruct_hyps.
    exists A', B', A', l. do 3 (split; auto).
    split. 2: split.
    1-2: apply barbedExpansion_refl.
    - now apply (ether_wf_preserved _ _ _ H10).
    - now apply (ether_wf_preserved B B' [(a, ι)] ltac:(econstructor;[eassumption|constructor])).
    - now apply IH.
Qed.


(* Lemma barbedBisimUpTo_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ~⪯~ B using U ->
      exists B' A'' B'' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ A'' using U /\ A'' ~⪯~ B'' using U /\ B' ⪯ B'' using U.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
Admitted.

Lemma barbedBisimUpTo_barbedBisim_helper :
  forall U A B A' B',
    A ⪯ A' using U -> A' ~⪯~ B' using U -> B ⪯ B' using U
    -> A ~⪯~ B using U.
Proof.
  cofix IH. intros. pose proof H as AA'. pose proof H1 as BB'.
  constructor; auto.
  * inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H0. eapply preCompatibleNodes_trans.
      apply H2. inv H1. apply H0.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H0. eapply preCompatibleNodes_trans.
      apply H2. inv H. apply H0.
  * now inv H.
  * now inv H1.
  * intros. rename A'0 into A0.
    inv H. apply H6 in H2 as [A'0 [l ?]]. destruct_hyps.
    clear H6 H7 H8 H9.
    eapply barbedBisimUpTo_many in H11. 2: eassumption.
    destruct H11 as [B'' [A''' [B''' [l'' H11]]]]. destruct_hyps.
    
Admitted.

Lemma barbedBisimUpTo_trans :
  forall U A B C,
    A ~⪯~ B using U -> B ~⪯~ C using U
    -> A ~⪯~ C using U.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [A'' [B'' [lB H1]]]].
    destruct_hyps.
    eapply barbedBisimUpTo_many in H9. 2: eassumption.
    destruct H9 as [C' [B''0 [C'' [lC H9]]]]. destruct_hyps.
    exists C', A'', C'', lC. split. 2: split. 3: split.
    3: assumption.
    (* - clear -H H1 H9 H13 H2 H0.
      destruct H, H1, H9, H13. split.
      + rewrite Forall_forall in *.
        intros. apply H in H9. intro.
        apply H5 in H10; auto.
        
      + intros. apply H21 in H27; eauto.
        destruct_hyps. apply H23 in H27; eauto.
    - destruct H0', H7, H16, H17. split.
      + rewrite Forall_forall in *.
        intros. apply H17 in H25. intro.
        now apply H1 in H26.
      + intros. apply H24 in H27; eauto.
        destruct_hyps. apply H22 in H27; eauto. *)
    1-2: admit.
    split. 2: split. 1-3: try assumption.
    eapply IH. 2: eassumption.
    apply barbedExpansion_implies_bisim in H15.
Abort. *)

Lemma barbedExpansion_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B, A ⪯ B using U ->
      exists B' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ B' using U /\ length l' <= length l.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
  * exists B, []. split. 2: split. 3: split. 4: split.
    3: constructor.
    3: assumption.
    1-2: split; constructor; auto.
    lia.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H3 in H4 as H'. destruct H' as [B' [l' H']]. destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl in H12. 2: eassumption.
    destruct H12 as [B'' [l'' H12]].
    destruct_hyps.
    exists B'', (l' ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l) by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Qed.

Lemma barbedExpansion_many_sym :
  forall B B' l', B -[l']ₙ->* B' ->
    forall U A, A ⪯ B using U ->
      exists A' l,
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        A -[ l ]ₙ->* A' /\ A' ⪯ B' using U /\ length l' <= length l.
Proof.
  intros B B' l'. revert B B'. induction l'; intros; inv H.
  * exists A, []. split. 2: split. 3: split. 4: split.
    3: constructor.
    3: assumption.
    1-2: split; constructor; auto.
    lia.
  * rename B' into B''. rename n' into B'.
    inv H0. apply H5 in H4 as H'. destruct H' as [A' [l H']]. destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl' in H12. 2: eassumption.
    destruct H12 as [A'' [l'' H12]].
    destruct_hyps.
    exists A'', (l ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Qed.

Lemma barbedExpansion_trans :
  forall U A B C,
    A ⪯ B using U -> B ⪯ C using U
    -> A ⪯ C using U.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedExpansion_many in H10. 2: eassumption.
    destruct H10 as [C' [lC H10]]. destruct_hyps.
    exists C', lC. split. 2: split. 3: split. 4: split.
    4: assumption.
    4: eapply IH; eassumption.
    - inv H0.
      clear -H H1 H10 H12 H2 H16.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H16 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H5 in H12; eauto.
    - inv H0.
      clear -H H1 H10 H12 H2 H16.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H6 in H8. intro.
        now apply H2 in H9.
      + intros. apply H7 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
    - lia.
  * intros. rename B' into C'.
    inv H0. apply H6 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedExpansion_many_sym in H10. 2: eassumption.
    destruct H10 as [A' [lA H10]]. destruct_hyps.
    exists A', lA. split. 2: split. 3: split. 4: split.
    4: assumption.
    4: eapply IH; eassumption.
    - inv H.
      clear -H0 H1 H10 H12 H2 H16.
      destruct H0, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H16 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H7 in H12; eauto.
    - inv H.
      clear -H0 H1 H10 H12 H2 H16.
      destruct H0, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H4 in H8. intro.
        now apply H2 in H9.
      + intros. apply H5 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
    - lia.
  * intros. inv H. inv H0. clear H7 H6 H13 H12 H9 H15.
    specialize (H8 source dest H1 H2) as [sourceB [H8_1 H8_2]].
    specialize (H14 sourceB dest H1 H8_1) as [sourceC [H14_1 H14_2]].
    eexists. split. assumption.
    eapply option_biforall_trans; eauto.
    intros. eapply Signal_eq_trans; eassumption.
  * intros. pose proof H as AB. pose proof H0 as BC.
    inv H. inv H0. clear H7 H6 H13 H12 H8 H14.
    specialize (H15 source dest H1 H2) as [sourceB [lB [B' H14]]]. destruct_hyps.
    eapply barbedExpansion_many_sym in H0. 2: exact AB.
    destruct H0 as [A' [lA H0]]. destruct_hyps.
    inv H13.
    specialize (H21 sourceB dest H1 H6) as [sourceA [lA' [A'' H21]]]. destruct_hyps.
    do 3 eexists. split. 2: split.
    3: {
      eapply option_biforall_trans; eauto.
      intros. eapply Signal_eq_trans; eassumption.
    }
    eapply closureNodeSem_trans; eassumption.
    assumption.
Qed.

Require Export PIDRenaming.

Definition isUsedPool (ι : PID) (Π : ProcessPool) :=
  ι ∉ map_fold (fun k v acc => usedPIDsProc v ++ acc) [] Π.

Definition barbedCongr (U V : list PID) (A B : Node) : Prop :=
  forall C : ProcessPool,
    Forall (fun p => ~isUsedPool p C) V ->
      (A.1, A.2 ∪ C) ~ (B.1, B.2 ∪ C) using U.

(* Lemma barbedBisimUpTo_many :
  forall A A' l, A -[l]ₙ->* A' ->
    forall U B A'' B'', A ⪯ A'' using U -> A'' ~⪯~ B'' using U -> B ⪯ B'' using U ->
      exists B' A''' B''' l',
        reductionPreCompatibility A B l l' /\
        reductionPreCompatibility B A l' l /\
        B -[ l' ]ₙ->* B' /\ A' ⪯ A''' using U /\ A''' ~⪯~ B''' using U /\ B' ⪯ B''' using U.
Proof.
  intros A A' l. revert A A'. induction l; intros; inv H.
  * exists B, A', B, []. split. 2: split. 3: split. 4: split. 5: split.
    3: constructor.
    1-2: split; constructor; auto.
    1-2: inv H3.
    2: { 
    1-2: apply barbedExpansion_refl; now inv H0.
  * rename A' into A''. rename n' into A'.
    inv H0. apply H3 in H4 as H'. destruct H' as [B' [A''0 [B'' [lB H']]]].
    destruct_hyps.
    clear H3 H5 H8 H7. eapply IHl in H6. Unshelve. 3: exact B'. 3: exact U.
    2: { clear -H6 H11 H12 H13.
    destruct H12 as [A'' [l'' H12]].
    destruct_hyps.
    exists A'', (l ++ l''). split. 2: split. 3: split. 4: split.
    4: assumption.
    3: eapply closureNodeSem_trans; eassumption.
    unfold symClos, preCompatibleNodes in H1.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - replace (_ :: _) with ([(a0, ι)] ++ l') by reflexivity.
      eapply reductionPreCompatibility_app; try eassumption.
      econstructor. eassumption. constructor.
    - rewrite app_length. slia.
Admitted. *)

(* Lemma barbedBisimUpTo_barbedBisim_helper_asd :
  forall U A B C,
    A ⪯ B using U -> B ~⪯~ C using U
    -> A ~⪯~ C using U.
Proof.
  cofix IH. intros.
  constructor; auto. 2-3: inv H; inv H0; auto.
  * inv H. inv H0. split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros. inv H. apply H5 in H1. destruct H1 as [B' [lB H1]].
    destruct_hyps.
    eapply barbedBisimUpTo_many in H10. 2: eassumption.
    destruct H10 as [C' [B''0 [C'' [lC H10]]]]. destruct_hyps.
    exists C', A', C'', lC. split. 2: split. 3: split.
    3: assumption.
    1-2: shelve.
    split. 2: split. 2: assumption.
    apply barbedExpansion_refl. now inv H11.
    apply (barbedExpansion_trans _ _ _ _ H11) in H14.
    eapply IH; eassumption.
    Unshelve.
    - inv H0.
      clear -H H1 H10 H12 H2 H17.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H in H8. intro.
        now apply H17 in H9.
      + intros. apply H0 in H10; eauto.
        destruct_hyps. apply H5 in H12; eauto.
    - inv H0.
      clear -H H1 H10 H12 H2 H17.
      destruct H, H1, H10, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H6 in H8. intro.
        now apply H2 in H9.
      + intros. apply H7 in H10; eauto.
        destruct_hyps. apply H3 in H12; eauto.
  * 
Qed. *)

Lemma barbedBisimUpTo_barbedBisim_helper :
  forall U A B C,
    A ~ B using U -> B ~⪯~ C using U
    -> A ~⪯~ C using U.
Proof.
  cofix IH. intros. pose proof H as AB. inv H.
  pose proof H0 as BC. inv H0.
  constructor; auto.
  * split.
    - eapply preCompatibleNodes_trans.
      inv H. apply H1. apply H.
    - eapply preCompatibleNodes_trans.
      inv H1. apply H. apply H1.
  * intros.
    clear H5 H6 H7 H11 H12 H13.
    apply H4 in H0. destruct H0 as [B' [l H0]]. destruct_hyps.
   (*  pose proof (barbedBisim_expansion_many _ _ _ H6 _ _ BC).
    destruct H11 as [C' [l']]. destruct_hyps.
    specialize (IH _ _ _ _ H7 H14). exists C', l'.
    split. 2: split. 3: split; auto.
    - destruct H0, H5, H11, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H0 in H19. intro.
        now apply H in H20.
      + intros. apply H15 in H21; eauto.
        destruct_hyps. apply H17 in H23; eauto.
    - destruct H0, H5, H11, H12. split.
      + rewrite Forall_forall in *.
        intros. apply H12 in H19. intro.
        now apply H1 in H20.
      + intros. apply H18 in H21; eauto.
        destruct_hyps. apply H16 in H23; eauto.
  * intros.
    epose proof (H5 source dest H0). destruct H14 as [sourceB [Bs [B' ?]]].
    destruct_hyps.
    pose proof (barbedBisim_expansion_many _ _ _ H14 _ _ BC) as [C' [Cs ?]]. destruct_hyps.
    pose proof H19 as B'C'. inv H19.
    specialize (H24 sourceB _ H0). destruct H24 as [sourceC [Cs' [C'' ?]]].
    destruct_hyps.
    exists sourceC, (Cs ++ Cs'), C''.
    split.
    - eapply closureNodeSem_trans; eassumption.
    - rewrite <- H24. assumption. (* transitivity is needed here! *)
  * 
  * *)
Admitted.

Lemma barbedBisimUpTo_barbedBisim_helper2 :
  forall U A B C,
    A ~⪯~ B using U -> B ~ C using U
    -> A ~⪯~ C using U.
Proof.
  
Admitted.

Theorem barbedBisimUpTo_barbedBisim :
  forall U A B, A ~⪯~ B using U -> A ~ B using U.
Proof.
  cofix IH. intros. inv H. constructor; auto.
  * clear H4 H6 H5. intros. apply H3 in H as H'.
    destruct H' as [B' [A'' [B'' [l H']]]]. destruct_hyps.
    apply barbedExpansion_implies_bisim in H7, H8.
    (* apply IH in H9.
    exists B', l. do 3 (split; auto).
    eapply barbedBisim_trans. exact H7.
    eapply barbedBisim_trans. exact H9.
    now apply barbedBisim_sym. *)
    exists B', l. do 3 (split; auto).
    eapply barbedBisimUpTo_barbedBisim_helper in H9. 2: eassumption.
    apply barbedBisim_sym in H8.
    eapply barbedBisimUpTo_barbedBisim_helper2 in H9. 2: eassumption.
    now apply IH.
    (* tricks needed to fix guardedness *)
    (* eapply diamond_trans; try eassumption.
    now apply IH. Guarded. *)
    (* inv H9. *)
  * admit.
Admitted.


