Require Export SubstSemantics.
From Coq Require Export Logic.ProofIrrelevance Program.Equality.

Import ListNotations.

(** This theorem says that the semantics rules are deterministic. *)
Theorem semmantics_rules_determinism :
  forall fs fs1 fs2 e e1 e2,
  ⟨ fs , e ⟩ --> ⟨ fs1 , e1 ⟩ ->
  ⟨ fs , e ⟩ --> ⟨ fs2 , e2 ⟩
  -> (fs1 = fs2 /\ e1 = e2).
Proof.
intros. inversion H; subst; inversion H0; auto; subst.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H8. inversion H8. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H8. inversion H8. subst. auto.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H8. inversion H8. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H4. inversion H4.
* rewrite H1 in H4. inversion H4. subst. auto.
* rewrite H1 in H8. inversion H8.
* rewrite H1 in H8. inversion H8. subst. auto.
* auto.
* congruence.
* specialize (H3 ext id 0 e0). congruence.
* auto.
* congruence.
* specialize (H7 ext id (Datatypes.length vl + 1) e'). congruence.
* congruence.
* specialize (H4 ext id vc e0). congruence.
* congruence.
* specialize (H8 ext id vc e'). congruence.
* specialize (H1 ext id 0 e). congruence.
* specialize (H1 ext id vc e). congruence.
* specialize (H1 ext id (Datatypes.length vl + 1) e'). congruence.
* specialize (H1 ext id vc e'). congruence.
* rewrite H1 in H10. inversion H10. subst. auto.
* rewrite H1 in H10. inversion H10.
* rewrite H1 in H10. inversion H10.
* auto.
* specialize (H6 vl1 e0 3 e3). congruence.
* specialize (H1 vl1 e0 3 e3). congruence.
Qed.

(* TODO: Is this needed? *)
(* if there is two identical hip then this tac will clear one *)
Ltac proof_irr :=
match goal with
| [H1 : ?P, H2 : ?P |- _] => assert (H1 = H2) by apply proof_irrelevance; subst
end.
Ltac proof_irr_many := repeat proof_irr.


Theorem step_rt_determinism :
  forall e k fs fs1 fs2 r1 r2,
  ⟨fs, e⟩ -[k]-> ⟨fs1, r1⟩ ->
  ⟨fs, e⟩ -[k]-> ⟨fs2, r2⟩
  -> (fs1 = fs2 /\ r1 = r2).
Proof.
  intros. dependent induction H.
  * inversion H0. subst. auto.
  * inversion H1. subst.
    pose proof semmantics_rules_determinism.
    specialize (H2 fs fs' fs'0 e e' e'0 H H3). destruct H2. subst.
    apply IHstep_rt. auto.
Qed.


(*This lemma was stated incorrectl, but the proof only needs some fixing*)
(*
Lemma eval_is_closed : 
  forall f params eff res eff',
  Auxiliaries.eval f params eff = (inl res, eff') ->
  (forall i, i < length params -> VALCLOSED (nth i params VNil))
  -> 
  (forall i, i < length res -> VALCLOSED (nth i res VNil)).
Proof.
  intros. unfold Auxiliaries.eval in H.
  destruct (convert_string_to_code f) eqn:Hfname; simpl in H.
  all: try (unfold eval_arith, eval_logical, eval_equality,
             eval_transform_list, eval_list_tuple, eval_cmp,
             eval_hd_tl, eval_elem_tuple, eval_check, eval_error, eval_io in H; rewrite Hfname in H);
  destruct params;
(* B route *)
[
  inversion H |
  destruct v; try (destruct params; [inversion H | destruct params; inversion H])
]; try (destruct l; inversion H).
(*
try (destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    try (
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ])).
*)
(* try (destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ])). *)
  * subst. specialize (H0 i H1). auto.
  * destruct v; try (inversion H).
    - destruct l.
      + inversion H.
      + inversion H7. subst. destruct i.
        ** simpl. constructor.
        ** simpl in H1. lia.
  * destruct v; try (destruct params; inversion H).
    - destruct l; inversion H.
    - destruct l; inversion H.
  * subst. specialize (H0 i H1). destruct i.
    - simpl. constructor.
    - simpl in H1. lia.
  * destruct v; inversion H.
    - destruct l.
      + inversion H.
      + inversion H. subst. simpl in *. specialize (H0 i H1). inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + subst. specialize (H0 i H1). inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + destruct x0; inversion H.
        ** subst. specialize (H0 i H1). inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** subst. specialize (H0 i H1). inversion H1.
           -- subst. simpl. constructor.
           -- lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + destruct x0; inversion H.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + destruct x0; inversion H.
        ** subst. specialize (H0 i H1). inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** subst. specialize (H0 i H1). inversion H1.
           -- subst. simpl. constructor.
           -- lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + destruct x0; inversion H.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + destruct x0; inversion H.
        ** subst. specialize (H0 i H1). inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** subst. specialize (H0 i H1). inversion H1.
           -- subst. simpl. constructor.
           -- lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + destruct x0; inversion H.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + subst. specialize (H0 i H1). inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
  * destruct v; inversion H.
    - destruct l; inversion H.
      + subst. specialize (H0 i H1). inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; inversion H.
    - destruct l; inversion H.
  
  * subst. specialize (H0 i H1).  inversion H1.
    - subst. simpl. constructor.
    - lia.
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H; subst; unfold ok; inversion H1; [subst; simpl; constructor | lia ].
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. intros. destruct i.
      + simpl. constructor.
      + destruct i.
        ** simpl. admit. (* use H0 *) (* The problem is "i < Datatypes.length [VTuple [ok; v]]" -> i=0 and I need i=1 for VALCLOSED v*)
        ** simpl in H2. lia.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. intros. destruct i.
      + simpl. constructor.
      + destruct i.
        ** simpl. admit. (* I need i=1 in H0 but i=0*)
        ** simpl in H2. lia.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  * simpl in H. subst. unfold ok. inversion H1.
    - subst. simpl. constructor. admit.
    - lia.
  (* New bool evaluation method *)
  * unfold ttrue in *. unfold ffalse in *.
    destruct (Equalities.Value_eqb (VLit (Atom s)) (VLit (Atom "true"))).
    - destruct (Equalities.Value_eqb v (VLit (Atom "true"))).
      + inversion H. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + destruct (Equalities.Value_eqb v (VLit (Atom "false"))).
        ** inversion H. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** inversion H.
    - destruct (Equalities.Value_eqb (VLit (Atom s)) (VLit (Atom "false"))).
      + destruct (Equalities.Value_eqb v (VLit (Atom "true"))).
        ** inversion H. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** destruct (Equalities.Value_eqb v (VLit (Atom "false"))).
           -- inversion H. subst. inversion H1.
              ++ subst. simpl. constructor.
              ++ lia.
           -- inversion H.
       + inversion H.
  * unfold ttrue in *. unfold ffalse in *.
    destruct (Equalities.Value_eqb (VLit (Atom s)) (VLit (Atom "true"))).
    - destruct (Equalities.Value_eqb v (VLit (Atom "true"))).
      + inversion H. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + destruct (Equalities.Value_eqb v (VLit (Atom "false"))).
        ** inversion H. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** inversion H.
    - destruct (Equalities.Value_eqb (VLit (Atom s)) (VLit (Atom "false"))).
      + destruct (Equalities.Value_eqb v (VLit (Atom "true"))).
        ** inversion H. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** destruct (Equalities.Value_eqb v (VLit (Atom "false"))).
           -- inversion H. subst. inversion H1.
              ++ subst. simpl. constructor.
              ++ lia.
           -- inversion H.
       + inversion H.
  * unfold ttrue in *. unfold ffalse in *.
    destruct (Equalities.Value_eqb (VLit (Atom s)) (VLit (Atom "true"))).
    - inversion H. subst. inversion H1.
      + subst. simpl. constructor.
      + lia.
    - destruct (Equalities.Value_eqb (VLit (Atom s)) (VLit (Atom "false"))).
      + inversion H. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + inversion H.
  
  (* --------------------------Proof structure starts here----------------------------------- *)
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia]).
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia]).
    - destruct l.
      + destruct (Equalities.Value_eqb (VLit (Atom s))
        (VLit (Atom s0))).
        ** subst. inversion H. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** subst. inversion H. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
      + inversion H5. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia]).
    - destruct l.
      + subst. inversion H5. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + destruct (x =? x0)%Z.
        ** subst. inversion H5. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
        ** subst. inversion H5. subst. inversion H1.
           -- subst. simpl. constructor.
           -- lia.
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia]).
    - subst. destruct (Equalities.Value_eqb v1 v3 &&
        Equalities.Value_eqb v2 v4)%bool.
      + inversion H3. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + inversion H3. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia]).
    - subst. destruct l.
      + subst. simpl. inversion H5. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + subst. simpl. inversion H5. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia]).
    - destruct l0.
      + subst. inversion H5. subst. inversion H1.
        ** subst. simpl. constructor.
        ** lia.
      + destruct l.
        ** destruct l0.
           -- destruct (Equalities.Value_eqb v0 v && true)%bool.
              ++ subst. inversion H5. subst. inversion H1.
                 *** subst. simpl. constructor.
                 *** lia.
              ++ subst. inversion H5. subst. inversion H1.
                 *** subst. simpl. constructor.
                 *** lia.
           -- destruct (Equalities.Value_eqb v0 v && false)%bool.
              ++ subst. inversion H5. subst. inversion H1.
                 *** subst. simpl. constructor.
                 *** lia.
              ++ subst. inversion H5. subst. inversion H1.
                 *** subst. simpl. constructor.
                 *** lia.
        ** destruct l0.
           -- destruct (Equalities.Value_eqb v0 v && false)%bool.
              ++ subst. inversion H5. subst. inversion H1.
                 *** subst. simpl. constructor.
                 *** lia.
              ++ subst. inversion H5. subst. inversion H1.
                 *** subst. simpl. constructor.
                 *** lia.
           -- destruct l.
              ++ destruct l0.
                 *** destruct (Equalities.Value_eqb v0 v &&
                     (Equalities.Value_eqb v1 v2 && true))%bool.
                     --- subst. inversion H5. subst. inversion H1.
                         +++ subst. simpl. constructor.
                         +++ lia.
                     --- subst. inversion H5. subst. inversion H1.
                         +++ subst. simpl. constructor.
                         +++ lia.
                 *** destruct (Equalities.Value_eqb v0 v &&
                     (Equalities.Value_eqb v1 v2 && false))%bool.
                     --- subst. inversion H5. subst. inversion H1.
                         +++ subst. simpl. constructor.
                         +++ lia.
                     --- subst. inversion H5. subst. inversion H1.
                         +++ subst. simpl. constructor.
                         +++ lia.
              ++ admit.
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  (* * destruct v; inversion H3; subst; inversion H1; subst; try (lia); try (constructor). *)
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]).
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]).
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]).
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * destruct v; try (subst; inversion H3; subst; inversion H1; [subst; simpl; constructor | lia ]);
    subst; destruct (Equalities.Value_eqb _ _); [inversion H; subst; inversion H1; [ simpl;
    constructor | lia] | inversion H; subst; inversion H1; [ simpl; constructor | lia] ].
  * subst. admit. (* i=0 but it needs i=1. What to do? *)
  * subst. admit. (* seem too long too many destructs *)
  * subst. admit. (* What to do? *) (* destruct eval_subtract _ _ ? *) 
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit.
  * subst. admit. (* destruct transform_tuple _ ? *) 
  * subst. admit. (* destruct transform_tuple _ ? *) 
  * subst. inversion H1.
    - subst. simpl. constructor. intros. inversion H2.
    - lia.
  * destruct (transform_list (VCons v1 v2)); subst; inversion H; subst.
    - inversion H1.
      + simpl. constructor. admit. (* where is l ?*)
      + lia.
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _); inversion H; subst;
    try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_ltb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst. inversion H1.
    - subst. simpl. constructor.
    - lia.
  * subst. admit. (* destruct eval_length [VCons v1 v2] ?*)
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst. inversion H1.
    - subst. simpl. specialize (H0 0 ltac:(simpl;lia)). simpl in *.
      inversion H0. auto.
    - lia.
  * subst. inversion H1.
    - subst. simpl. specialize (H0 0 ltac:(simpl;lia)). simpl in *.
      inversion H0. auto.
    - lia.
  * subst. destruct v; inversion H.
    - destruct x; inversion H.
      + destruct (nth_error l (Init.Nat.pred (Pos.to_nat p))); inversion H.
        ** subst. admit. (*Where is v? *)
  * subst. destruct v; inversion H.
  * subst. destruct params; inversion H.
  * subst. destruct v; inversion H.
  * subst. destruct params; inversion H.
  * subst. destruct v; inversion H; subst; destruct params; inversion H.
    - destruct x; inversion H.
      + destruct (replace_nth_error l (Init.Nat.pred (Pos.to_nat p)) v0); inversion H.
        ** subst. inversion H1.
           -- subst. simpl. constructor.
              admit. (* Were is l0? *)
           -- lia.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * destruct params; inversion H.
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; inversion H1; [subst; simpl; constructor | lia].
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).
  * subst; destruct (Equalities.Value_eqb _ _ || Equalities.Value_eqb _ _)%bool;
    inversion H; subst; try (inversion H1; [simpl; constructor | lia]).

Admitted.
*)

Theorem convert_to_closlist_keeps_scope :
  forall ext Γ,
  (forall i, i < length ext -> 
  EXP Datatypes.length ext + (nth i (map snd (map fst ext)) 0) + Γ ⊢ nth i (map snd ext) (Val VNil))
  -> forall i, i < length ext -> VAL Γ ⊢ nth i (convert_to_closlist ext) VNil.
Proof.
  unfold convert_to_closlist. induction ext; intros. 
  * simpl in *. destruct i.
    - lia.
    - constructor.
  * destruct i.
    - destruct a. destruct p. constructor.
      + intros. destruct i.
        ** simpl in *. apply (H 0). lia.
        ** simpl. simpl in H1.
           specialize (H (S i) ltac:(simpl;lia)). simpl in H. auto.
      + simpl. apply (H 0). lia.
    - assert ((forall i : nat,
         i < Datatypes.length ext ->
         EXP Datatypes.length ext +
             nth i (map snd (map fst ext)) 0 + S Γ
         ⊢ nth i (map snd ext) (Val VNil))). {
           intros. Search plus S.  rewrite Nat.add_succ_r. apply (H (S i0)). simpl. lia.
         }
         simpl in H0.
         specialize (IHext _ H1 i ltac:(simpl;lia)). simpl.
         Search nth.
         
Admitted.


(* This needs the eval_is_closed Lemma*)
Theorem step_closedness : forall F p F' p',
   ⟨ F, p ⟩ --> ⟨ F', p' ⟩ -> FSCLOSED F -> PROGCLOSED p
->
  FSCLOSED F' /\ PROGCLOSED p'.
Proof.
  intros. inversion H; subst.
  * inversion H1. subst. split.
    - auto.
    - inversion H3. subst. constructor. intros. destruct i.
      + simpl. auto.
      + simpl in H2. lia.
  * inversion H1. subst. split.
    - auto.
    - constructor. intros. destruct i.
      + simpl. constructor.
      + simpl. constructor.
  * inversion H1. subst. inversion H0. subst. inversion H5. subst. split.
    - constructor.
      + constructor.
        ** Check indexed_to_forall. rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _). Check Forall_app. apply Forall_app. 
        split.
           -- rewrite (indexed_to_forall _ _ VNil). auto.
           -- rewrite (indexed_to_forall _ _ VNil). auto.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H8.
           replace (e :: el) with ([e] ++ el) in H8 by (simpl;auto).
           rewrite Forall_app in H8. destruct H8. auto.
      + auto.
    - constructor. specialize (H8 0 ltac:(simpl;lia)). simpl in H8. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _).
      rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H2.
      rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H3.
      apply Forall_app. auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst. 
    clear H2. split.
    - constructor.
      + constructor.
        ** intros. simpl in H1. lia.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H3.
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _).
           replace (e :: el) with ([e] ++ el) in H3 by (simpl;auto).
           rewrite Forall_app in H3. destruct H3. auto.
      + auto.
    - constructor. specialize (H3 0 ltac:(simpl;lia)). simpl in H3. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - constructor. 
      + constructor. specialize (H2 0 ltac:(simpl;lia)). simpl in H2. auto.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. intros. simpl in H0. specialize (H2 i ltac:(simpl;lia)).
      inversion H0.
      + subst. simpl in *. constructor.
        ** auto.
        ** auto.
      + lia.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor.
      + constructor. auto.
      + auto.
    - constructor. auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - auto.
    - constructor. intros. destruct i.
      + simpl. constructor. intros. simpl. destruct i.
        ** constructor.
        ** constructor.
      + simpl in H1. lia.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - constructor.
      + constructor.
        ** rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _).
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H2.
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H3.
           apply Forall_app. auto.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H6.
           replace (e :: el) with ([e] ++ el) in H6 by (simpl;auto).
           rewrite Forall_app in H6. destruct H6. auto.
      + auto.
    - constructor. rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H6.
      replace (e :: el) with ([e] ++ el) in H6 by (simpl;auto).
      rewrite Forall_app in H6. destruct H6. rewrite indexed_to_forall in H0.
      specialize (H0 0). simpl in H0. apply H0. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. destruct i.
      + simpl. intros. constructor.
        rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _).
        rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H2.
        rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H3.
        apply Forall_app. auto.
      + simpl. intros. lia.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor.
      + constructor.
        ** simpl. intros. lia.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H3.
           replace (e :: el) with ([e] ++ el) in H3 by (simpl;auto).
           rewrite Forall_app in H3. destruct H3. auto.
      + auto.
    - constructor. rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H3.
      replace (e :: el) with ([e] ++ el) in H3 by (simpl;auto).
      rewrite Forall_app in H3. destruct H3. inversion H1. subst. auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - auto.
    - constructor. intros. simpl in H1. destruct i.
      + simpl. constructor. 
        ** intros. simpl in H2. lia.
        ** intros. simpl in H2. lia.
      + lia.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - constructor.
      + constructor.
        ** auto.
        ** auto.
        ** auto.
        ** auto.
        ** specialize (H2 0). simpl in H2. apply H2. auto.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - assert (forall i, i < length vl -> VALCLOSED (fst (nth i vl (VNil, VNil)))) as H11.
      { clear H H2 H5 H7 H8 H9 H10. intros. specialize (H6 i H).
        replace VNil with (fst (VNil, VNil)) in H6 by auto.
        rewrite map_nth in H6. auto. } (* prooving the assert is correct based on H6 *)
      clear H6. rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (fst v)) _) in H11.
      
      assert (forall i, i < length vl -> VALCLOSED (snd (nth i vl (VNil, VNil)))) as H12.
      { clear H H2 H5 H8 H9 H10. intros. specialize (H7 i H).
        replace VNil with (snd (VNil, VNil)) in H7 by auto.
        rewrite map_nth in H7. auto. } (* prooving the assert is correct based on H7 *)
      clear H7. rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (snd v)) _) in H12.
      
      specialize (H2 0 ltac:(simpl;lia)). simpl in H2.
      
      assert (forall i, i < length ((fs', sn') :: el) -> 
      EXPCLOSED (fst (nth i ((fs', sn') :: el) (Val VNil, Val VNil)))) as H13.
      { intros. specialize (H8 i H0). replace (Val VNil) with (fst (Val VNil, Val VNil))
        in H8 by auto. rewrite map_nth in H8. auto. }
      clear H8. rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED (fst e)) _) in H13.
      
      assert (forall i, i < length ((fs', sn') :: el) -> 
      EXPCLOSED (snd (nth i ((fs', sn') :: el) (Val VNil, Val VNil)))) as H14.
      { intros. specialize (H9 i H0). replace (Val VNil) with (snd (Val VNil, Val VNil))
        in H9 by auto. rewrite map_nth in H9. auto. }
      clear H9. rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED (snd e)) _) in H14.
      
      replace ((fs', sn') :: el) with ([(fs', sn')] ++ el) in H13 by (simpl;auto).
      replace ((fs', sn') :: el) with ([(fs', sn')] ++ el) in H14 by (simpl;auto).
      rewrite Forall_app in H13. destruct H13. rewrite Forall_app in H14. destruct H14.
      
      constructor.
      
      + constructor.
        ** intros. replace VNil with (fst (VNil,VNil)) by auto.
           rewrite map_nth. revert H6. revert i.
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (fst v)) _).
           apply Forall_app. split.
           -- auto.
           -- constructor.
              ++ auto.
              ++ auto.
        ** intros. replace VNil with (snd (VNil,VNil)) by auto.
           rewrite map_nth. revert H6. revert i.
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (snd v)) _).
           apply Forall_app. split.
           -- auto.
           -- constructor.
              ++ auto.
              ++ auto.
        ** intros. replace (Val VNil) with (fst (Val VNil, Val VNil)) by auto.
           rewrite map_nth. revert H6. revert i.
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED (fst e)) _). auto.
        ** intros. replace (Val VNil) with (snd (Val VNil, Val VNil)) by auto.
           rewrite map_nth. revert H6. revert i.
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED (snd e)) _). auto.
        ** inversion H3. subst. simpl in H8. auto.
      + auto.
    - constructor. specialize (H8 0 ltac:(simpl;lia)). simpl in H8. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. intros. simpl in H0. destruct i.
      + simpl.
        
        assert (forall i, i < length vl -> VALCLOSED (fst (nth i vl (VNil, VNil)))) as H11.
        { intros. specialize (H6 i H1).
          replace VNil with (fst (VNil, VNil)) in H6 by auto.
          rewrite map_nth in H6. auto. } (* prooving the assert is correct based on H6 *)
        clear H6. rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (fst v)) _) in H11.
        
        assert (forall i, i < length vl -> VALCLOSED (snd (nth i vl (VNil, VNil)))) as H12.
        { intros. specialize (H7 i H1).
          replace VNil with (snd (VNil, VNil)) in H7 by auto.
          rewrite map_nth in H7. auto. } (* prooving the assert is correct based on H7 *)
        clear H7. rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (snd v)) _) in H12.
        
        constructor.
        ** intros. replace VNil with (fst (VNil,VNil)) by auto.
           rewrite map_nth. revert H1. revert i.
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (fst v)) _).
           rewrite Forall_app. split.
           -- auto.
           -- constructor.
              ++ simpl. auto.
              ++ auto.
        ** intros. replace VNil with (snd (VNil,VNil)) by auto.
           rewrite map_nth. revert H1. revert i.
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED (snd v)) _).
           rewrite Forall_app. split.
           -- auto.
           -- constructor.
              ++ simpl. specialize (H2 0 ltac:(simpl;lia)). simpl in H2. auto.
              ++ auto.
      + lia.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor.
      + constructor.
        ** intros. simpl. destruct i.
           -- constructor.
           -- constructor.
        ** intros. simpl. destruct i.
           -- constructor.
           -- constructor.
        ** replace (Datatypes.length ((fs, sn) :: el)) with
           (Datatypes.length (map fst ((fs, sn) :: el))) in H3 by
           (simpl;rewrite map_length; auto).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H3.
           
           replace (Datatypes.length el) with (Datatypes.length (map fst el)) by
           (simpl;rewrite map_length; auto).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _).
           
           (* Here this replace was a trickier step. *)
           replace (map fst ((fs, sn) :: el)) with ([fst (fs, sn)]++(map fst el)) in H3
           by (simpl;auto). apply Forall_app in H3. destruct H3. auto.
           
        ** clear H3. replace (Datatypes.length ((fs, sn) :: el)) with 
           (Datatypes.length (map snd ((fs, sn) :: el))) in H4 by
           (simpl;rewrite map_length; auto).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H4.
           
           replace (Datatypes.length el) with (Datatypes.length (map snd el)) by
           (simpl;rewrite map_length; auto).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _).
           
           replace (map snd ((fs, sn) :: el)) with ([snd (fs, sn)]++(map snd el)) in H4
           by (simpl;auto). apply Forall_app in H4. destruct H4. auto.
        
        ** clear H3. replace (Datatypes.length ((fs, sn) :: el)) with 
           (Datatypes.length (map snd ((fs, sn) :: el))) in H4 by
           (simpl;rewrite map_length; auto).
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H4.
           
           replace (map snd ((fs, sn) :: el)) with ([snd (fs, sn)]++(map snd el)) in H4
           by (simpl;auto). apply Forall_app in H4. destruct H4. simpl in H1.
           inversion H1. subst. auto.
      + auto.
    - constructor. replace (Datatypes.length ((fs, sn) :: el)) with
      (Datatypes.length (map fst ((fs, sn) :: el))) in H3 by
      (simpl;rewrite map_length; auto).
      rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H3.
      
      replace (map fst ((fs, sn) :: el)) with ([fst (fs, sn)]++(map fst el)) in H3
      by (simpl;auto). apply Forall_app in H3. destruct H3. simpl in H1.
      inversion H1. subst. auto.
  * inversion H1. subst. clear H1. inversion H4. subst. clear H4. inversion H3. subst.
    clear H3. split.
    - auto.
    - admit. (* unclear because of the eval *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - constructor.
      + constructor.
        ** rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _).
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H2.
           rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H3.
           rewrite Forall_app. auto.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H7.
           replace (e :: el) with ([e] ++ el) in H7 by (simpl;auto).
           rewrite Forall_app in H7. destruct H7.
           rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _). auto.
      + auto.
    - rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H7.
      replace (e :: el) with ([e] ++ el) in H7 by (simpl;auto).
      rewrite Forall_app in H7. destruct H7. inversion H0. subst. constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - auto.
    - admit. (* unclear because of the eval *)
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H5.
    replace (e :: el) with ([e] ++ el) in H5 by (simpl;auto).
    rewrite Forall_app in H5. destruct H5. split.
    - constructor.
      + constructor. 
        ** intros. simpl in H3. lia.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _). auto.
      + auto.
    - constructor. inversion H1. subst. auto.
  * inversion H1. subst. clear H1. inversion H4. subst. clear H4. inversion H3. subst.
    clear H3. split.
    - auto.
    - destruct exc. destruct p. constructor.
      + admit. (* unclear because of the eval *)
      + admit. (* unclear because of the eval *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H2. subst.
    clear H2. inversion H5. subst. clear H5. split.
    - auto.
    - destruct exc. destruct p. constructor.
      + admit. (* unclear because of the eval *)
      + admit. (* unclear because of the eval *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. Search subscoped list_subst.
      Search subst ExpScoped. apply (subst_preserves_scope_exp _ (length vs)). (* subst is closed, solved*)
      + auto.
      + Search subscoped list_subst. apply scoped_list_idsubst. 
        rewrite -> (indexed_to_forall _ (fun v => VALCLOSED v) VNil). auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor. 
      + constructor. replace (l + 0) with l in H7 by auto. auto.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor. 
      + constructor. auto.
      + auto.
    - constructor. auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - auto.
    - constructor. intros. simpl in H1. inversion H1.
      + subst. simpl. constructor.
        ** intros. simpl in H2. lia.
        ** simpl. auto.
      + lia.
  * inversion H1. subst. clear H1. inversion H4. subst. clear H4. inversion H3. subst.
    clear H3. split.
    - auto.
    - admit. (* unclear because of the eval *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4.
    rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H2.
    rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H3.
    rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H7.
    replace (e :: el) with ([e] ++ el) in H7 by (simpl;auto).
    rewrite Forall_app in H7. destruct H7. inversion H2. subst. split.
    - constructor.
      + constructor.
        ** rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _).
           rewrite Forall_app. auto.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _). auto.
      + auto.
    - constructor. inversion H0. subst. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - auto.
    - admit. (* unclear because of the eval *)
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2.
    rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H5.
    replace (e :: el) with ([e] ++ el) in H5 by (simpl;auto).
    rewrite Forall_app in H5. destruct H5. split.
    - constructor.
      + constructor.
        ** intros. simpl in H3. lia.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _). auto.
      + auto.
    - constructor. inversion H1. subst. auto.
  * inversion H1. subst. clear H1. inversion H4. subst. clear H4. inversion H3. subst.
    clear H3. split.
    - auto.
    - admit. (* unclear because of the eval *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - auto.
    - destruct exc. destruct p. constructor.
      + admit. (* unclear because of the eval *)
      + admit. (* unclear because of the eval *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. admit. (* subst is closed theorem needed. *) (* convert_to_closlist *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4.
    rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H1.
    replace (e :: el) with ([e] ++ el) in H1 by (simpl;auto).
    rewrite Forall_app in H1. destruct H1. split.
    - constructor.
      + constructor.
        ** intros. simpl in H3. lia.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _). auto.
        ** specialize (H2 0). simpl in H2. apply H2. auto.
      + auto.
    - constructor.  inversion H0. subst. auto.
  * inversion H1. subst. clear H1. inversion H0. subst. clear H0. inversion H4. subst.
    clear H4.
    rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H3.
    rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _) in H6.
    rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _) in H7.
    replace (e :: el) with ([e] ++ el) in H7 by (simpl;auto). rewrite Forall_app in H7.
    destruct H7. split.
    - constructor.
      + constructor.
        ** rewrite <- (indexed_to_forall _ (fun v => VALCLOSED v) _).
           rewrite Forall_app. auto.
        ** rewrite <- (indexed_to_forall _ (fun e => EXPCLOSED e) _). auto.
        ** auto.
      + auto.
    - constructor. inversion H0. subst. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. inversion H8. subst. clear H8. split.
    - auto.
    - constructor. Search subscoped list_subst.
      Search subst ExpScoped. apply (subst_preserves_scope_exp _ (Datatypes.length 
      (convert_to_closlist ext ++ vl ++ [v]))).
      + replace (Datatypes.length ext + (Datatypes.length vl + 1) + 0) with 
        (Datatypes.length (convert_to_closlist ext ++ vl ++ [v])) in H11.
        ** auto.
        ** clear. Search length. rewrite app_length. rewrite app_length. simpl.
           replace (Datatypes.length (convert_to_closlist ext)) with (Datatypes.length ext).
           -- auto.
           -- destruct ext.
              ++ simpl. auto.
              ++ simpl. rewrite map_length. auto.
      + Search subscoped list_subst. apply scoped_list_idsubst. rewrite Forall_app. split.
        ** rewrite -> (indexed_to_forall _ (fun v => VALCLOSED v) VNil).
           intros. specialize (H10 i). replace (Datatypes.length (convert_to_closlist ext)) with
           (Datatypes.length ext) in H0.
           -- clear H H5 H2 H6 H7 H11. specialize (H10 H0). unfold convert_to_closlist.
              admit. (* I do not see how this *) (* convert_to_closlist *)
           -- destruct ext.
              ++ simpl. auto.
              ++ simpl. rewrite map_length. auto.
           (* Might need a help teorem abaut: length convert_to_closlist ext = length ext *)
        ** rewrite Forall_app. split.
           -- rewrite -> (indexed_to_forall _ (fun v => VALCLOSED v) VNil). auto.
           -- rewrite -> (indexed_to_forall _ (fun v => VALCLOSED v) VNil). auto.
        (* subst is closed theorem needed. *)
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor.
      + constructor. auto.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - auto.
    - constructor.
      + constructor.
      + apply (H3 0 ltac:(simpl;lia)).
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. inversion H9. subst. clear H9. split.
    - auto.
    - constructor.
      + constructor.
      + constructor.
        ** auto.
        ** auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - auto.
    - constructor.
      + constructor.
      + specialize (H3 0). simpl in H3. apply H3. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - auto.
    - constructor.
      + constructor.
      + auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - constructor.
      + constructor.
        ** intros. apply (H1 (S i)). simpl. lia.
        ** intros. apply (H4 (S i)). simpl. lia.
        ** auto.
        ** admit. (* forall ... VALCLOSED vs -> match_pattern_list lp vs = Some vs' -> forall ... VALCLOSED vs', Something like this is needed here. *)
        ** clear H1 H3 H6 H2 H. specialize (H4 0 ltac:(simpl;lia)). simpl in H4. auto.
      + auto.
    - constructor. admit. (* subst is closed theorem needed. *) 
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H5. subst.
    clear H5. split.
    - constructor.
      + constructor.
        ** intros. apply (H1 (S i)). simpl. lia.
        ** intros. apply (H4 (S i)). simpl. lia.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    (* - constructor. apply (subst_preserves_scope_exp _ (patternListScope lp)).
      + auto.
      + Search subscoped list_subst. apply scoped_list_idsubst. *)
    - constructor. admit. (* subst is closed theorem needed. *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - constructor. 
      + constructor.
        ** auto.
        ** auto.
      + auto.
    - constructor. auto.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor.
      + constructor.
        ** clear H H0 H4 H7. intros. specialize (H5 i H).
           replace (patternListScope (nth i (map fst (map fst l)) []) + 0) with 
           (patternListScope (nth i (map fst (map fst l)) [])) in H5 by (simpl;auto).
           auto.
        ** clear H H0 H4 H5. intros. specialize (H7 i H).
           replace (patternListScope (nth i (map fst (map fst l)) []) + 0) with
           (patternListScope (nth i (map fst (map fst l)) [])) in H7 by (simpl;auto).
           auto.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H4. subst. clear H4. split.
    - auto.
    - constructor.
      + constructor.
      + constructor.
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - auto.
    (* - constructor. apply (subst_preserves_scope_exp _ (Datatypes.length l + 0)).
      + auto.
      + replace (Datatypes.length l + 0) with (Datatypes.length l) by auto.
        Search subscoped list_subst.
        remember (convert_to_closlist (map (fun '(x, y) => (0, x, y)) l)) as ls.
        replace (Datatypes.length l) with (Datatypes.length ls).
        ** apply scoped_list_idsubst.
           rewrite -> (indexed_to_forall _ (fun v => VALCLOSED v) VNil).
           subst. admit.
        ** subst. destruct l.
           -- auto.
           -- simpl. *)
    - constructor. admit. (* subst is closed theorem needed. *)
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    - constructor. apply (subst_preserves_scope_exp _ (Datatypes.length vs)).
      + auto.
      + apply scoped_list_idsubst. 
        rewrite -> (indexed_to_forall _ (fun v => VALCLOSED v) VNil). auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. inversion H4. subst.
    clear H4. split.
    - auto.
    (*- constructor. apply (subst_preserves_scope_exp _ (3)).
      + auto.
      + simpl. *)
    - constructor. admit. (* subst is closed theorem needed. *)
  * inversion H1. subst. clear H1. inversion H3. subst. clear H3. inversion H2. subst.
    clear H2. split.
    - constructor.
      + constructor.
        ** replace (vl1 + 0) with vl1 in H9 by auto. auto.
        ** replace (vl2 + 0) with vl2 in H10 by auto. auto.
      + auto.
    - constructor. auto.
  * inversion H0. subst. clear H0. inversion H1. subst. clear H1. split.
    - auto.
    - constructor.
      + auto.
      + auto.
Admitted.



Theorem result_VALCLOSED_any (fs : FrameStack) (e v : ProgResult) :
  ⟨ fs, e ⟩ -->* v -> PROGCLOSED v.
Proof.
  intros. destruct H.
  * destruct H. destruct H. destruct H. subst. constructor.
    intros. inversion H0.
    - subst. admit.
    - subst. admit.
  * admit.
Admitted.

Corollary step_any_closedness : forall F p v,
   ⟨ F, p ⟩ -->* v -> FSCLOSED F -> PROGCLOSED p
->
  PROGCLOSED v.
Proof.
  intros. destruct v.
  * inversion H1.
    - subst. inversion H.
      + destruct H3. destruct H3. destruct H3.
Admitted.

(*
Theorem step_closedness : forall F e F' e',
   ⟨ F, e ⟩ --> ⟨ F', e' ⟩ -> FSCLOSED F -> EXPCLOSED e
->
  FSCLOSED F' /\ EXPCLOSED e'.
Proof.
  intros F e F' e' IH. induction IH; intros.
  * inversion H0. subst. inversion H4. inversion H3. subst. split; auto.
    constructor; auto. constructor; auto.
  * inversion H. inversion H0. subst. split; auto. inversion H5. subst. cbn in H2.
    apply -> subst_preserves_scope_exp; eauto.
  * inversion H0. subst. inversion H5. inversion H9. subst. split; auto. constructor; auto.
    constructor; auto.
    apply Forall_app. split; auto.
  * inversion H1. inversion H6. split. auto. subst. inversion H11.
    apply -> subst_preserves_scope_exp; eauto. subst.
    rewrite Nat.add_0_r. replace (S (length vl)) with (length (EFun vl e :: vs ++ [v])).
    apply scoped_list_idsubst. constructor. auto. apply Forall_app. split; auto.
    simpl. rewrite H0, app_length. simpl. lia.
  * inversion H0. subst. inversion H4. inversion H3. subst. split; auto.
    constructor; auto. constructor; auto.
  * inversion H2. inversion H6. inversion H12.
    subst. split; auto.
    constructor; auto. constructor; auto.
    apply Forall_app. split; auto.
  * inversion H0. inversion H4. 
    subst. split; auto. apply -> subst_preserves_scope_exp; eauto.
  * inversion H1. inversion H5. subst. split; auto.
    apply -> subst_preserves_scope_exp; eauto.
    rewrite (match_pattern_length _ v l H0).
    apply scoped_list_idsubst. eapply match_pattern_scoped; eauto.
  * inversion H2. inversion H6. subst. split; auto.
  * inversion H0. inversion H4; subst. split; auto. constructor; auto.
    constructor. destruct v; inversion H; inversion H1; auto.
  * inversion H. inversion H3. subst. split; auto. constructor. constructor.
  * split; auto. inversion H0. 2: inversion H1. apply -> subst_preserves_scope_exp; eauto.
    subst. apply cons_scope; auto. constructor. auto.
  * inversion H0. inversion H4. subst. split; auto. repeat constructor; auto.
  * inversion H1. inversion H5. subst. split; auto. repeat constructor; auto.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    now constructor.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite indexed_to_forall. exact H4.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite indexed_to_forall. exact H4.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto. now constructor.
  * inversion H0. 2: inversion H1. subst. split; auto. constructor; auto.
    constructor. rewrite Nat.add_0_r in H6. auto. auto.
  * inversion H0; subst; split; auto. 1-2: constructor; auto; now constructor.
    now inversion H1.
Qed.

Theorem result_VALCLOSED_any (fs : FrameStack) (e v : Exp) :
  ⟨ fs, e ⟩ -->* v -> VALCLOSED v.
Proof.
  intros. destruct H. auto.
Qed.

Corollary step_any_closedness : forall F e v,
   ⟨ F, e ⟩ -->* v -> FSCLOSED F -> EXPCLOSED e
->
  VALCLOSED v.
Proof.
  intros. destruct H, H2. induction H2.
  * destruct e; try inversion H; now inversion H1.
  * apply step_closedness in H2; auto.
Qed.
*)
