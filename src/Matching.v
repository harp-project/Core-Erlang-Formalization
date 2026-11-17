(**
  This file contains the formal definition of pattern matching in Core Erlang.
*)

From CoreErlang Require Import ScopingLemmas Equalities Maps.
Import ListNotations.

(**
  Segment matching is based on:
  https://www.erlang.org/doc/system/expressions.html#bit-syntax-expressions

  In the segment: Value:Size/TypeSpecifierList
  
  - ``When used in a bit string matching, Value must be a variable, or an integer, float, or string.'' -> we suppose that strings are desugared by the compiler
  - ``When used in a bit string matching, Size must be a guard expression that evaluates to an integer. All variables in the guard expression must be already bound.''
*)

(** Decodes the bits of an integer segment according to its signedness and
    endianness (`NativeEndian` is treated as big-endian). It depends on
    the segment specifiers of the syntax, thus it is not in `Bitstrings.v`. *)
Definition decode_int (w : N) (sign : BinSign) (endi : BinEnd) (bits : bv w) : Z :=
  let raw :=
    match endi with
    | LittleEndian => Z_to_bv w (little_bv_to_Z w bits)
    | BigEndian | NativeEndian => bits
    end
  in
  match sign with
  | Signed   => bv_signed raw
  | Unsigned => bv_unsigned raw
  end.

(** The result of pattern matching: either a successful match (with the
    bindings), a failed match, or `NotSupported`, when matching would need a
    feature that is not formalised (e.g., floats or UTF segments of binaries).
    The latter is different from a failed match: the semantics gets stuck
    instead of trying the next clause. *)
Inductive Match A :=
| Matches (v : A)
| NotMatches
| NotSupported.

Arguments Matches {A} v.
Arguments NotMatches {A}.
Arguments NotSupported {A}.

(** Inverts an equality between two `Match` results built from constructors:
    it either solves the goal (different constructors), or substitutes the
    results (`Matches`). *)
Ltac invMatch :=
match goal with
| [ H : Matches _ = Matches _ |- _] => inv H
| [ H : Matches _ = NotMatches |- _] => inv H
| [ H : Matches _ = NotSupported |- _] => inv H
| [ H : NotMatches = Matches _ |- _] => inv H
| [ H : NotMatches = NotMatches |- _] => inv H
| [ H : NotMatches = NotSupported |- _] => inv H
| [ H : NotSupported = Matches _ |- _] => inv H
| [ H : NotSupported = NotMatches |- _] => inv H
| [ H : NotSupported = NotSupported |- _] => inv H
end.

(** Sequences a [Match] result into a function producing another [Match],
    short-circuiting on [NotMatches]/[NotSupported]. *)
Definition bind_match {A B} (r : Match A) (f : A -> Match B) : Match B :=
  match r with
  | Matches a    => f a
  | NotMatches   => NotMatches
  | NotSupported => NotSupported
  end.

(** Combines two independent [Match] results: [NotSupported] dominates
    (if either side is unsupported, the combination is too), then
    [NotMatches] dominates over [Matches]. *)
Definition match_and {A B C} (f : A -> B -> C) (r1 : Match A) (r2 : Match B) : Match C :=
  match r1, r2 with
  | Matches a, Matches b => Matches (f a b)
  | NotSupported, _ | _, NotSupported => NotSupported
  | _, _ => NotMatches
  end.

(** Decodes the bits of a segment into a value based on its type: integer
    segments are decoded as integers, binary and bitstring segments as
    bitstrings (for binaries, the size has to be a multiple of the unit).
    Float and UTF segments are not supported. *)
Definition decode_bits (bits : bvn) (type : BinType) (unit : N)
                                    (sign : BinSign) (endi : BinEnd) : Match Val :=
match type with
| IntType => Matches (VLit (decode_int (bvn_n bits) sign endi (bvn_val bits)))
| FloatType => NotSupported (* TODO - when floats are implemented *)
| BitstringType => Matches (VBitstring bits)
| BinaryType => if (N.modulo (bvn_n bits) unit =? 0)%N
                then Matches (VBitstring bits)
                else NotMatches
| Utf8Type => NotSupported (* TODO *)
| Utf16Type => NotSupported (* TODO *)
| Utf32Type => NotSupported (* TODO *)
end.

(** This function decides whether a value matches a pattern, and gives back
    the result bindings.
    NOTE: PIDs are not patterns.
 *)
Fixpoint match_pattern (p : Pat) (e : Val) {struct p} : Match (list Val) :=
match p with
| PVar => Matches [e]
| PNil => match e with
          | VNil => Matches []
          | _    => NotMatches
          end
| PLit l0 => match e with
              | VLit l => if Lit_beq l l0 then Matches [] else NotMatches
              | _      => NotMatches
              end
| PCons p1 p2 =>
  match e with
  | VCons v1 v2 =>
    match_and (fun l1 l2 => l1 ++ l2) (match_pattern p1 v1) (match_pattern p2 v2)
  | _           => NotMatches
  end
| PTuple pl => match e with
              | VTuple vl =>
                 (fix match_and_bind_elements pl vl :=
                        match pl with
                        | [] => 
                            match vl with
                            | [] => Matches []
                            | _  => NotMatches
                            end
                        | p::ps =>
                            match vl with
                            | v::vs =>
                                match_and (fun vl1 vl2 => vl1 ++ vl2)
                                          (match_pattern p v)
                                          (match_and_bind_elements ps vs)
                            | _ => NotMatches
                            end
                        end) pl vl
              | _ => NotMatches
              end
| PMap pl => match e with
              | VMap vl =>
                 (fix match_and_bind_elements pl vl :=
                          match pl with
                          | [] =>
                              match vl with
                              | []  => Matches []
                              | _   => NotMatches
                              end
                          | (p1,p2)::ps =>
                              match vl with
                              | (v1,v2)::vs =>
                                  match_and (fun vl12 vl2 => vl12 ++ vl2)
                                            (match_and (fun vl1 vl1' => vl1 ++ vl1')
                                                       (match_pattern p1 v1) (match_pattern p2 v2))
                                            (match_and_bind_elements ps vs)
                              | _ => NotMatches
                              end
                          end) pl vl
              | _  => NotMatches
              end
| PBin segs =>
  match e with
  | VBitstring bits => 
     (fix match_segs (l : list (Segment Pat Val)) (bits : bvn) {struct l} : Match (list Val) :=
      match l with
      | [] => if N.eqb (bvn_n bits) 0
              then Matches []
              else NotMatches
      | Build_Segment pv (VLit sz) u ty sg endi :: segs =>
        if null segs && Lit_beq sz (Atom "all"%string)
        then bind_match (decode_bits bits ty (N.of_nat u) sg endi) (match_pattern pv)
        else match sz with
        | Integer n =>
          let total := (Z.to_N n * N.of_nat u)%N in
          if (n <? 0)%Z || (bvn_n bits <? total)%N then NotMatches
          else
            let '(front, rest) := bvn_split total bits in
            match_and (fun pats restpats => pats ++ restpats)
                      (bind_match (decode_bits front ty (N.of_nat u) sg endi) (match_pattern pv))
                      (match_segs segs rest)
         | _ => NotMatches
         end
      | _ => NotMatches
      end) segs bits
  | _ => NotMatches
  end
end.

(** The following two goals show that the inline loops of tuple and map
    patterns in `match_pattern` are equivalent to formulations based on
    `foldr` and `zip_with` (with an additional length check). *)
Goal
  forall pl vl,
  (fix match_and_bind_elements pl vl :=
                        match pl with
                        | [] => 
                            match vl with
                            | [] => Matches []
                            | _  => NotMatches
                            end
                        | p::ps =>
                            match vl with
                            | v::vs =>
                                match_and (fun vl1 vl2 => vl1 ++ vl2)
                                          (match_pattern p v)
                                          (match_and_bind_elements ps vs)
                            | _ => NotMatches
                            end
                        end) pl vl = let res := foldr (match_and app) (Matches []) (zip_with match_pattern pl vl)
                in match res with
                   | Matches _ => if length pl =? length vl then res else NotMatches
                   | r => r
                   end.
Proof.
  induction pl; destruct vl; simpl; try reflexivity.
  rewrite IHpl.
  simpl. unfold match_and. simpl.
  repeat case_match; simpl; try reflexivity; try congruence.
Qed.

Goal forall pl vl,
     let res := foldr (match_and app) (Matches []) (zip_with (fun '(p1, p2) '(v1, v2) =>
                                                                 match_and app (match_pattern p1 v1)
                                                                   (match_pattern p2 v2)) pl vl)
                in match res with
                   | Matches _ => if length pl =? length vl then res else NotMatches
                   | r => r
                   end = (fix match_and_bind_elements pl vl :=
                          match pl with
                          | [] =>
                              match vl with
                              | []  => Matches []
                              | _   => NotMatches
                              end
                          | (p1,p2)::ps =>
                              match vl with
                              | (v1,v2)::vs =>
                                  match_and (fun vl12 vl2 => vl12 ++ vl2)
                                            (match_and (fun vl1 vl1' => vl1 ++ vl1')
                                                       (match_pattern p1 v1) (match_pattern p2 v2))
                                            (match_and_bind_elements ps vs)
                              | _ => NotMatches
                              end
                          end) pl vl.
Proof.
  induction pl; destruct vl; try destruct a, p; simpl; try reflexivity.
  rewrite <- IHpl.
  simpl. unfold match_and. simpl.
  repeat case_match; simpl; try reflexivity; try congruence.
Qed.

(** Pattern matching for pattern lists to value sequences. The results of the
    individual patterns are combined with `match_and` (similarly to the
    elements of tuple patterns), thus `NotSupported` dominates over
    `NotMatches`. *)
Fixpoint match_pattern_list (pl : list Pat) (vl : ValSeq) : Match (list Val) :=
match pl,vl with
  | (p::ps), (v::vs) => match_and (fun vs' vs'' => vs' ++ vs'')
                                  (match_pattern p v) (match_pattern_list ps vs)
  | [], [] => Matches []
  | _, _ => NotMatches
end.

(** The scope of pattern matching *)
Theorem match_pattern_scope : forall p v l Γ,
  VAL Γ ⊢ v -> match_pattern p v = Matches l
->
  Forall (fun v => VAL Γ ⊢ v) l.
Proof.
  induction p using Pat_ind_weakened with
  (Q := Forall (fun p => forall v l Γ, 
                  VAL Γ ⊢ v -> match_pattern p v = Matches l
                  -> Forall (fun v => VAL Γ ⊢ v) l))
  (R := Forall (fun '(p1, p2) => (forall v l Γ, 
  VAL Γ ⊢ v -> match_pattern p1 v = Matches l
  -> Forall (fun v => VAL Γ ⊢ v) l) /\
  (forall v l Γ, 
  VAL Γ ⊢ v -> match_pattern p2 v = Matches l
  -> Forall (fun v => VAL Γ ⊢ v) l)))
  (T := Forall (fun seg => forall v l Γ, VAL Γ ⊢ v -> match_pattern (seg_val seg) v = Matches l -> Forall (ValScoped Γ) l));
  try intros v l' Γ HΓ Hmatch; simpl in *; unfold match_and, bind_match in *; try now constructor.
  * destruct v; try congruence. now inversion Hmatch.
  * destruct v; try congruence.
    destruct Lit_beq in Hmatch; inversion Hmatch. auto.
  * inversion Hmatch. now constructor.
  * destruct v; try congruence.
    break_match_hyp; try congruence. break_match_hyp; try congruence. inversion Hmatch. inversion HΓ. subst. apply Forall_app. split.
    - eapply IHp1. exact H3. auto.
    - eapply IHp2. exact H4. auto.
    - case_match; try congruence.
  * destruct v; try congruence. inversion HΓ; subst. clear HΓ.
    apply indexed_to_forall in H1.
    generalize dependent l'; generalize dependent l; induction l0;
    intros l H l' Hmatch.
    - destruct l. 2: congruence. now inversion Hmatch.
    - inversion H1; subst; clear H1.
      destruct l. congruence.
      do 2 (break_match_hyp; try congruence).
      inversion H; subst; clear H.
      specialize (IHl0 H4 l H5 _ Heqm0). inversion Hmatch; subst. clear Hmatch.
      apply Forall_app; split; auto.
      clear IHl0 Heqm0. eapply H2 in Heqm; eauto.
  * destruct v; try congruence. inversion HΓ; subst. clear HΓ.
    generalize dependent l'; generalize dependent l.
    induction l0; intros l H l' Hmatch.
    - destruct l. 2: { destruct p; congruence. } now inversion Hmatch.
    - destruct l. congruence.
      do 6 (break_match_hyp; try congruence).
      inv H. destruct H4.
      apply Forall_app; split;[apply Forall_app; split|].
      3: {
        eapply IHl0.
        - intros. apply (H0 (S i)). simpl. lia.
        - intros. apply (H2 (S i)). simpl. lia.
        - apply H5.
        - assumption.
      }
      + eapply H. 2: eassumption. apply (H0 0). simpl. lia.
      + eapply H1. 2: eassumption. apply (H2 0). simpl. lia.
  * destruct v; try congruence. inversion HΓ; subst. clear HΓ.
    generalize dependent l'.
    generalize dependent bits.
    generalize dependent l.
    induction l; intros H bits l' Hmatch.
    - case_match; try congruence. by inv H0.
    - destruct a. inv H. specialize (IHl H3). clear H3.
      repeat (case_match; subst; try congruence).
      + apply andb_true_iff in H as [X1 X2].
        destruct l; inv X1.
        unfold decode_bits in H0.
        case_match; try congruence; inv H0; cbn in *; eapply H2 in Hmatch;
          try eassumption; try by constructor.
        case_match; try congruence. inv H3. by constructor.
      + specialize (IHl _ _ H3). clear H3 H H0.
        inv Hmatch.
        apply Forall_app; split. 2: assumption.
        eapply H2 in H1; try eassumption.
        unfold decode_bits in H4.
        case_match; try congruence; inv H4; cbn in *; try by constructor.
        case_match; try congruence. inv H3. by constructor.
Qed.

(** The scope of pattern list matching: the bindings are scoped in the same
    context as the matched values. *)
Lemma match_pattern_list_scope Γ vs :
  forall lp vs', match_pattern_list lp vs = Matches vs' ->
    Forall (fun v => VAL Γ ⊢ v) vs ->
    Forall (fun v => VAL Γ ⊢ v) vs'.
Proof.
  induction vs; destruct lp; intros vs' H Hall; simpl in H; try invMatch; auto.
  unfold match_and in H. repeat break_match_hyp; invMatch.
  inversion Hall; subst.
  apply Forall_app; split.
  - eapply match_pattern_scope; eassumption.
  - eauto.
Qed.

Lemma match_pattern_list_sublist vs :
  forall lp vs', match_pattern_list lp vs = Matches vs' ->
    incl vs' vs.
Proof.
  (* Does not hold! One pattern can contain any number of 
     variables. *)
Abort.

(** The result of pattern matching is as long as many variables are present in
    the pattern.
*)
Lemma match_pattern_length :
  forall p v l, match_pattern p v = Matches l ->
    PatVars p = length l.
Proof.
  induction p using Pat_ind_weakened with
    (Q := Forall (fun p => forall v l, match_pattern p v = Matches l ->
    PatVars p = length l))
    (R := Forall (fun '(p1, p2) => (forall v l, match_pattern p1 v = Matches l ->
    PatVars p1 = length l) /\
    (forall v l, match_pattern p2 v = Matches l ->
    PatVars p2 = length l)))
    (T := Forall (fun seg => forall v l, match_pattern (seg_val seg) v = Matches l ->
    PatVars (seg_val seg) = length l)); simpl; intros.
  * destruct v; now inv H.
  * destruct v; inv H. break_match_hyp; now inv H1.
  * now inv H.
  * unfold match_and in H; destruct_all_hyps. inv H. rewrite length_app.
    apply IHp1 in Heqm; apply IHp2 in Heqm0; lia.
  * destruct_all_hyps. generalize dependent l0. revert l1.
    induction l; intros.
    - destruct_all_hyps. now inv H.
    - unfold match_and in *. destruct_all_hyps. inv H. inv IHp.
      rewrite length_app.
      apply IHl in Heqm0; auto. cbn. erewrite Heqm0, H1.
      reflexivity. eassumption.
  * destruct_all_hyps. generalize dependent l0. revert l1.
    induction l; intros.
    - destruct_all_hyps. now inv H.
    - unfold match_and in *. destruct_all_hyps. inv H. inv IHp. do 2 rewrite length_app.
      destruct H1. specialize (IHl H2 _ _ Heqm0). clear H2 Heqm0. simpl.
      erewrite IHl, H, H0. 2-3: eassumption. reflexivity.
  * destruct_all_hyps. generalize dependent l0. revert bits.
    induction IHp; intros.
    - destruct_all_hyps. now inv H.
    - unfold match_and in *. destruct_all_hyps.
      + apply andb_true_iff in Heqb as [X1 X2].
        destruct l; inv X1.
        unfold decode_bits in H0.
        case_match; try congruence; inv H0; cbn in *.
        eapply H in H3; try eassumption; lia.
        case_match; try congruence. eapply H in H3; try eassumption; lia. by cbn in H3.
        eapply H in H3; try eassumption; lia.
      + specialize (IHIHp _ _ Heqm0). clear Heqm0. inv H0. simpl in *.
        rewrite IHIHp. rewrite length_app. f_equal.
        unfold decode_bits in Heqm.
        case_match; try congruence; inv Heqm; cbn in *.
        eapply H in H2; by eassumption.
        case_match; try congruence. eapply H in H2; by eassumption.
        by cbn in H2.
        eapply H in H2; by eassumption.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
  * by constructor.
Qed.

(** The number of bindings of pattern list matching is the number of
    variables in the patterns. *)
Lemma match_pattern_list_length vs :
  forall lp vs', match_pattern_list lp vs = Matches vs' ->
    PatListVars lp = length vs'.
Proof.
  induction vs; destruct lp; intros vs' H; simpl in H; try invMatch; auto.
  unfold match_and in H.
  destruct (match_pattern p a) eqn:Hp, (match_pattern_list lp vs) eqn:Hl; invMatch.
  cbn. rewrite length_app.
  apply IHvs in Hl. rewrite <- Hl.
  erewrite match_pattern_length; [reflexivity | eassumption].
Qed.

(** Matching only variables against a value seq. gives back the value seq. *)
Lemma match_pattern_list_vars :
  forall l, match_pattern_list (repeat PVar (length l)) l = Matches l.
Proof.
  induction l; simpl; auto.
  rewrite IHl. reflexivity.
Qed.

(** Matching a single pattern as a list is the same as matching the pattern. *)
Lemma match_pattern_list_single :
  forall p v, match_pattern_list [p] [v] = match_pattern p v.
Proof.
  intros. simpl. unfold match_and.
  destruct match_pattern; auto. by rewrite app_nil_r.
Qed.

(** Matching with variables inside a tuple, gives back the elements of the tuple *)
Lemma match_pattern_list_tuple_vars :
  forall l, match_pattern_list [PTuple (repeat PVar (length l))] [VTuple l] = Matches l.
Proof.
  intros. rewrite match_pattern_list_single.
  induction l; simpl; auto.
  simpl in IHl. rewrite IHl. reflexivity.
Qed.

(** Concrete consequence of the previous theorem for map. (length_map is needed) *)
Corollary match_pattern_list_tuple_vars_map :
  forall l (f : Val -> Val), match_pattern_list [PTuple (repeat PVar (length l))] [VTuple (map f l)] = Matches (map f l).
Proof.
  intros.
  pose proof (match_pattern_list_tuple_vars (map f l)). rewrite length_map in H.
  assumption.
Qed.

(** The previous property expressed slightly strengthened. *)
Lemma match_pattern_list_tuple_vars_length :
  forall m l0 vs, match_pattern_list [PTuple (repeat PVar m)] [VTuple l0] = Matches vs ->
  m = length l0 /\ vs = l0.
Proof.
  intros m l0 vs H. rewrite match_pattern_list_single in H.
  revert l0 vs H. induction m; destruct l0; intros; simpl in *; try (invMatch; auto; fail).
  unfold match_and in H. break_match_hyp; invMatch.
  edestruct IHm as [? ?]; [eassumption |].
  subst. auto.
Qed.

(** Matching property for maps containing only pattern variables. *)
Lemma match_pattern_list_map_vars_length :
  forall m l0 vs, match_pattern_list [PMap (repeat (PVar, PVar) m)] [VMap l0] = Matches vs ->
  m = length l0 /\ vs = flatten_list l0.
Proof.
  intros m l0 vs H. rewrite match_pattern_list_single in H.
  revert l0 vs H. induction m; destruct l0; intros; simpl in *; try (invMatch; auto; fail).
  destruct p. unfold match_and in H. break_match_hyp; invMatch.
  edestruct IHm as [? ?]; [eassumption |].
  subst. auto.
Qed.

(** Matching a map pattern containing only variables gives back the keys and
    values of the map. *)
Lemma match_pattern_list_map_vars :
  forall l, match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap l] = Matches (flatten_list l).
Proof.
  intros. rewrite match_pattern_list_single.
  induction l; simpl; auto. destruct a.
  simpl in IHl. rewrite IHl. reflexivity.
Qed.

(** Consequences of the previous lemma for mapped maps. *)
Corollary match_pattern_list_map_vars_map :
  forall l (f : Val*Val -> Val*Val), match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap (map f l)] = Matches (flatten_list (map f l)).
Proof.
  intros.
  pose proof (match_pattern_list_map_vars (map f l)). rewrite length_map in H.
  assumption.
Qed.

Corollary match_pattern_list_map_vars_prod_map :
  forall l (f : Val -> Val), match_pattern_list [PMap (repeat (PVar , PVar) (length l))] [VMap (map (prod_map f f) l)] = Matches (flatten_list (map (prod_map f f) l)).
Proof.
  intros.
  pose proof (match_pattern_list_map_vars (map (prod_map f f) l)). rewrite length_map in H.
  assumption.
Qed.

(** Mapping both components of a pair with a pattern-matching lambda is
    `prod_map`. *)
Lemma map_prod_map {A B} (f : A -> B) :
  (fun '(a, b) => (f a, f b)) = prod_map f f.
Proof.
  extensionality x. by destruct x.
Qed.
