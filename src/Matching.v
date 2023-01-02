From CoreErlang Require Import ScopingLemmas Equalities Basics.
Import ListNotations.

Fixpoint match_pattern (p : Pat) (e : Val) : option (list Val) :=
match p with
| PVar => Some [e]
(* | PPid x => match e with
            | EPid p => if Nat.eqb p x then Some [] else None
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

Fixpoint match_pattern_list (pl : list Pat) (vl : list Val) : option (list Val) :=
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


Theorem match_pattern_scoped : forall p v l Γ,
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
