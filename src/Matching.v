(**
  This file contains the formal definition of pattern matching in Core Erlang.
*)

From CoreErlang Require Import ScopingLemmas Equalities Maps.
Import ListNotations.

(** This function decides whether a value matches a pattern, and gives back
    the result bindings.
    NOTE: PIDs are not patterns.
 *)
Fixpoint match_pattern (p : Pat) (e : Val) : option (list Val) :=
match p with
| PVar => Some [e]
(* | PPid x => match e with
            | VPid p => if Nat.eqb p x then Some [] else None
            | _      => None
            end *)
| PNil => match e with
          | VNil => Some []
          | _    => None
          end
| PLit l0 => match e with
              | VLit l => if Lit_beq l l0 then Some [] else None
              | _      => None
              end
| PCons p1 p2 => 
  match e with
  | VCons v1 v2 =>
    match match_pattern p1 v1, match_pattern p2 v2 with
    | Some l1, Some l2 => Some (l1 ++ l2)
    | _      , _       => None
    end
  | _           => None
  end
| PTuple pl => match e with
              | VTuple vl =>
                        (fix match_and_bind_elements pl vl :=
                        match pl with
                        | [] => 
                            match vl with
                            | [] => Some []
                            | _ => None
                            end
                        | p::ps => 
                            match vl with
                            | v::vs => 
                                match (match_pattern p v) with
                                | Some vl1 => 
                                    match (match_and_bind_elements ps vs) with
                                    | Some vl2 => Some (vl1 ++ vl2)
                                    | _        => None
                                    end
                                | _ => None
                                end
                            | _ => None
                            end 
                        end) pl vl
              | _ => None
              end
| PMap pl => match e with
              | VMap vl => (fix match_and_bind_elements pl vl :=
                          match pl with
                          | [] => 
                              match vl with
                              | []  => Some []
                              | _   => None
                              end
                          | (p1,p2)::ps => 
                              match vl with
                              | (v1,v2)::vs =>
                                  match (match_pattern p1 v1), (match_pattern p2 v2) with
                                  | Some vl1, Some vl1' =>
                                      match (match_and_bind_elements ps vs) with
                                      | Some vl2  => Some (vl1 ++ vl1' ++ vl2)
                                      | _         => None
                                      end
                                  | _, _ => None
                                  end
                              | _ => None
                              end
                          end) pl vl
              | _  => None
              end
end.

(** Pattern matching for pattern lists to value sequences *)
Fixpoint match_pattern_list (pl : list Pat) (vl : ValSeq) : option (list Val) :=
match pl,vl with
  | (p::ps), (v::vs) => match match_pattern p v with
                        | Some vs' => match match_pattern_list ps vs with
                                      | Some vs'' => Some (vs'++vs'')
                                      | None      => None
                                      end
                        | None => None
                        end
  | [], [] => Some []
  | _, _ => None
end.

(** The scope of pattern matching *)
Theorem match_pattern_scope : forall p v l Γ,
  VAL Γ ⊢ v -> match_pattern p v = Some l
->
  Forall (fun v => VAL Γ ⊢ v) l.
Proof.
  induction p using Pat_ind2 with
  (Q := Forall (fun p => forall v l Γ, 
                  VAL Γ ⊢ v -> match_pattern p v = Some l
                  -> Forall (fun v => VAL Γ ⊢ v) l))
  (R := Forall (fun '(p1, p2) => (forall v l Γ, 
  VAL Γ ⊢ v -> match_pattern p1 v = Some l
  -> Forall (fun v => VAL Γ ⊢ v) l) /\
  (forall v l Γ, 
  VAL Γ ⊢ v -> match_pattern p2 v = Some l
  -> Forall (fun v => VAL Γ ⊢ v) l))); try intros v l' Γ HΓ Hmatch; simpl in *; try now constructor.
  * destruct v; try congruence. now inversion Hmatch.
  * destruct v; try congruence.
    destruct Lit_beq in Hmatch; inversion Hmatch. auto.
  (* * destruct v; try congruence. break_match_hyp; now invSome. *)
  * inversion Hmatch. now constructor.
  * destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion Hmatch. inversion HΓ. subst. apply Forall_app. split.
    - eapply IHp1. exact H3. auto.
    - eapply IHp2. exact H4. auto.
  * destruct v; try congruence. inversion HΓ; subst. clear HΓ.
    apply indexed_to_forall in H1.
    generalize dependent l'; generalize dependent l; induction l0;
    intros l H l' Hmatch.
    - destruct l. 2: congruence. now inversion Hmatch.
    - inversion H1; subst; clear H1.
      destruct l. congruence.
      do 2 (break_match_hyp; try congruence).
      inversion H; subst; clear H.
      specialize (IHl0 H4 l H5 _ Heqo0). inversion Hmatch; subst. clear Hmatch.
      apply Forall_app; split; auto.
      clear IHl0 Heqo0. eapply H2 in Heqo; eauto.
  * destruct v; try congruence. inversion HΓ; subst. clear HΓ.
    generalize dependent l'; generalize dependent l; induction l0;
    intros l H l' Hmatch.
    - destruct l. 2: { destruct p; congruence. } now inversion Hmatch.
    - destruct l. congruence.
      do 5 (break_match_hyp; try congruence).
      inversion H; subst; clear H.
      inversion Hmatch; subst. clear Hmatch.
      destruct H4.
      apply Forall_app; split;[|apply Forall_app; split].
      3: {
        eapply IHl0.
        - intros. apply (H0 (S i)). simpl. lia.
        - intros. apply (H2 (S i)). simpl. lia.
        - apply H5.
        - assumption.
      }
      + eapply H. 2: eassumption. apply (H0 0). simpl. lia.
      + eapply H1. 2: eassumption. apply (H2 0). simpl. lia.
Qed.

Lemma match_pattern_list_scope Γ vs :
  forall lp vs', match_pattern_list lp vs = Some vs' ->
    Forall (fun v => VAL Γ ⊢ v) vs ->
    Forall (fun v => VAL Γ ⊢ v) vs'.
Proof.
  induction vs; destruct lp; intros vs' H Hall; inv H.
  * auto.
  * inv Hall. destruct_all_hyps. inv H1. apply IHvs in Heqo0; auto.
    apply Forall_app; split; auto.
    eapply match_pattern_scope; eassumption.
Qed.

Lemma match_pattern_list_sublist vs :
  forall lp vs', match_pattern_list lp vs = Some vs' ->
    incl vs' vs.
Proof.
  (* Does not hold! One pattern can contain any number of 
     variables. *)
Abort.

(** The result of pattern matching is as long as many variables are present in
    the pattern.
*)
Lemma match_pattern_length :
  forall p v l, match_pattern p v = Some l ->
    PatScope p = length l.
Proof.
  induction p using Pat_ind2 with
    (Q := Forall (fun p => forall v l, match_pattern p v = Some l ->
    PatScope p = length l))
    (R := Forall (fun '(p1, p2) => (forall v l, match_pattern p1 v = Some l ->
    PatScope p1 = length l) /\
    (forall v l, match_pattern p2 v = Some l ->
    PatScope p2 = length l))); simpl; intros.
  * destruct v; now inv H.
  * destruct v; inv H. break_match_hyp; now inv H1.
  (* * destruct v; inv H. break_match_hyp; now inv H1. *)
  * now inv H.
  * destruct_all_hyps. inv H. rewrite app_length. firstorder.
  * destruct_all_hyps. generalize dependent l0. revert l1.
    induction l; intros.
    - destruct_all_hyps. now inv H.
    - destruct_all_hyps. inv H. inv IHp. rewrite app_length.
      apply IHl in Heqo0; auto. cbn. erewrite Heqo0, H1.
      reflexivity. eassumption.
  * destruct_all_hyps. generalize dependent l0. revert l1.
    induction l; intros.
    - destruct_all_hyps. now inv H.
    - destruct_all_hyps. inv H. inv IHp. do 2 rewrite app_length.
      apply IHl in Heqo1; auto. cbn. erewrite Heqo1.
      destruct H1. erewrite H, H0. rewrite Nat.add_assoc. reflexivity.
      all: eassumption.
  * firstorder.
  * firstorder.
  * firstorder.
  * firstorder.
Qed.

Lemma match_pattern_list_length vs :
  forall lp vs', match_pattern_list lp vs = Some vs' ->
    PatListScope lp = length vs'.
Proof.
  induction vs; destruct lp; intros vs' H; inversion H.
  * reflexivity.
  * repeat break_match_hyp; try congruence.
    inv H1. apply IHvs in Heqo0. cbn. rewrite app_length.
    rewrite <- Heqo0. erewrite match_pattern_length. reflexivity.
    eassumption.
Qed.

(** Matching only variables against a value seq. gives back the value seq. *)
Lemma match_pattern_list_vars :
  forall l, match_pattern_list (repeat PVar (length l)) l = Some l.
Proof.
  induction l; simpl; auto.
  break_match_goal; congruence.
Qed.

(** Matching with variables inside a tuple, gives back the elements of the tuple *)
Lemma match_pattern_list_tuple_vars :
  forall l, match_pattern_list [PTuple (repeat PVar (length l))] [VTuple l] = Some l.
Proof.
  induction l; simpl; auto.
  break_match_goal; break_match_hyp; try congruence.
  - inversion Heqo. simpl in IHl.
    rewrite Heqo0 in IHl. inv IHl. reflexivity.
  - simpl in IHl. rewrite Heqo0 in IHl. congruence.
Qed.

(** Concrete consequence of the previous theorem for map. (map_length is needed) *)
Corollary match_pattern_list_tuple_vars_map :
  forall l (f : Val -> Val), match_pattern_list [PTuple (repeat PVar (length l))] [VTuple (map f l)] = Some (map f l).
Proof.
  intros.
  pose proof (match_pattern_list_tuple_vars (map f l)). rewrite map_length in H.
  assumption.
Qed.

(** The previous property expressed slightly strenghtened. *)
Lemma match_pattern_list_tuple_vars_length :
  forall m l0 vs, match_pattern_list [PTuple (repeat PVar m)] [VTuple l0] = Some vs ->
  m = length l0 /\ vs = l0.
Proof.
  induction m; destruct l0; intros; simpl in *; inv H; auto.
  break_match_hyp. 2: congruence.
  inv H1. rewrite app_nil_r in *.
  break_match_hyp. 2: congruence. inv Heqo.
  specialize (IHm l0 l1). break_match_hyp. 2: congruence.
  inv Heqo0. clear -IHm.
  rewrite app_nil_r in IHm. specialize (IHm eq_refl) as [IHm1 IHm2].
  split; subst; auto.
Qed.

(** Matching property for maps containing only pattern variables. *)
Lemma match_pattern_list_map_vars_length :
  forall m l0 vs, match_pattern_list [PMap (repeat (PVar, PVar) m)] [VMap l0] = Some vs ->
  m = length l0 /\ vs = flatten_list l0.
Proof.
  induction m; destruct l0; intros; simpl in *; inv H; auto.
  break_match_hyp. 2: congruence.
  inv H1. rewrite app_nil_r in *.
  do 2 break_match_hyp. 2: congruence. inv Heqo.
  specialize (IHm l0 l1). break_match_hyp. 2: congruence.
  inv Heqo0. clear -IHm.
  rewrite app_nil_r in IHm. specialize (IHm eq_refl) as [IHm1 IHm2].
  split; subst; auto.
Qed.

Lemma match_pattern_list_map_vars :
  forall l, match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap l] = Some (flatten_list l).
Proof.
  induction l; simpl; auto.
  break_match_goal; break_match_hyp; try congruence.
  - destruct a. inv Heqp. simpl in IHl. break_match_hyp. 2: congruence.
    inv Heqo. inv IHl. reflexivity.
  - destruct a. inv Heqp. simpl in IHl. break_match_hyp; congruence.
Qed.

Lemma match_pattern_list_map_vars_map :
  forall l (f : Val*Val -> Val*Val), match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap (map f l)] = Some (flatten_list (map f l)).
Proof.
  intros.
  pose proof (match_pattern_list_map_vars (map f l)). rewrite map_length in H.
  assumption.
Qed.
