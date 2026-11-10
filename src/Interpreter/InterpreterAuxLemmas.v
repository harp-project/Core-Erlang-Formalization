From CoreErlang.Concurrent  Require Export NodeSemanticsLemmas.
From CoreErlang.Interpreter Require Export InterpreterAux.

(** This file contains equivalence lemmas about the wrapper functions and
    swapped functions found in "InterpreterAux.v". For more information
    about why these were swapped in the interpreter, see the comments in
    the "InterpreterAux.v" file.
*)

Lemma eval_logical_equiv: forall (mname fname : string) (params : list Val),
  eval_logical mname fname params = eval_logical_Interp mname fname params.
Proof.
  intros. unfold eval_logical_Interp.
  unfold eval_logical.
  destruct (convert_string_to_code (mname, fname)) eqn:Hcstc; try reflexivity.
  all: try destruct params; try reflexivity; try destruct params; try reflexivity; try destruct params; 
       try reflexivity; repeat setoid_rewrite Val_eqb_strict_lit_eqb; reflexivity.
Qed.

Lemma eval_check_equiv: forall (mname fname : string) (params : list Val),
  eval_check mname fname params = eval_check_Interp mname fname params.
Proof.
  intros. unfold eval_check_Interp.
  unfold eval_check.
  destruct (convert_string_to_code (mname, fname)) eqn:Hcstc; try reflexivity.
  destruct params; try reflexivity; destruct params; try reflexivity;
  repeat setoid_rewrite Val_eqb_strict_lit_eqb; reflexivity.
Qed.

Lemma eval_funinfo_equiv: forall (params : list Val),
  eval_funinfo params = eval_funinfo_Interp params.
Proof.
  intros. unfold eval_funinfo_Interp.
  destruct params; try reflexivity.
  destruct v; try destruct params; try destruct params; try reflexivity.
  setoid_rewrite Val_eqb_strict_lit_eqb. reflexivity.
Qed.

Lemma eval_equiv: forall (mname : string) (fname : string) (params : list Val),
  eval mname fname params = eval_Interp mname fname params.
Proof.
  intros. unfold eval_Interp.
  rewrite <- eval_logical_equiv.
  rewrite <- eval_funinfo_equiv.
  rewrite <- eval_check_equiv.
  reflexivity.
Qed.

Lemma create_result_equiv: forall (ident : FrameIdent) (vl : list Val),
  create_result ident vl = create_result_Interp ident vl.
Proof.
  intros. unfold create_result_Interp.
  destruct ident; try reflexivity.
  destruct m; try reflexivity. destruct l; try reflexivity. destruct f; try reflexivity.
  destruct l; try reflexivity. rewrite <- eval_equiv. reflexivity.
Qed.

Lemma usedPIDsExp_equiv: forall (e : Exp), usedPIDsExp e = usedPIDsExp_Interp e.
Proof.
  intros. unfold usedPIDsExp_Interp.
  induction e using Exp_ind2 with
  (PV := fun v => usedPIDsVal v = usedPIDsVal_Interp v)
  (PE := fun e => usedPIDsNVal e = usedPIDsNVal_Interp e)
  (PP := fun p => usedPIDsPat p = usedPIDsPat_Interp p)
  (Q  := Forall (fun e => usedPIDsExp e = usedPIDsExp_Interp e))
  (QV := Forall (fun v => usedPIDsVal v = usedPIDsVal_Interp v))
  (R  := Forall (PBoth (fun e => usedPIDsExp e = usedPIDsExp_Interp e)))
  (RV := Forall (PBoth (fun v => usedPIDsVal v = usedPIDsVal_Interp v)))
  (VV := Forall (fun e => usedPIDsExp e.2 = usedPIDsExp_Interp e.2))
  (W  := Forall (fun '(e1, e2, e3) => flat_union usedPIDsPat e1 = flat_union_Interp usedPIDsPat_Interp e1
                                      /\ usedPIDsExp e2 = usedPIDsExp_Interp e2
                                      /\ usedPIDsExp e3 = usedPIDsExp_Interp e3))
  (Z  := Forall (fun e => usedPIDsExp e.2 = usedPIDsExp_Interp e.2))
  (PQ := Forall (fun p => usedPIDsPat p = usedPIDsPat_Interp p))
  (PR := Forall (PBoth (fun p => usedPIDsPat p = usedPIDsPat_Interp p)))
  (PT := Forall (fun seg => usedPIDsPat (val seg) = usedPIDsPat_Interp (val seg)
                            /\ usedPIDsVal (Syntax.size seg) = usedPIDsVal_Interp (Syntax.size seg))); auto.
  * simpl. unfold pids_union. rewrite IHe. rewrite IHe0. reflexivity.
  * simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. inv H1. rewrite H. rewrite H0.
      apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe0. simpl.
    unfold pids_union. unfold flat_union. unfold flat_union_Interp. unfold pids_empty.
    rewrite IHe0.
    induction ext.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1.
      apply IHext in H2. unfold pids_union.
      assert (usedPIDsExp_Interp e ∪ (usedPIDsExp_Interp a.2
       ∪ foldr (λ (x : nat * nat * Exp) (acc : gset PID), usedPIDsExp x.2 ∪ acc) ∅ ext) =
       usedPIDsExp_Interp a.2 ∪ (usedPIDsExp_Interp e
       ∪ foldr (λ (x : nat * nat * Exp) (acc : gset PID), usedPIDsExp x.2 ∪ acc) ∅ ext) ) as Hhelp1.
       { set_solver. }
      rewrite Hhelp1. rewrite H2. set_solver.
  * simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction el.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHel in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe1, IHe2. simpl. rewrite IHe1. rewrite IHe2. unfold pids_union. reflexivity.
  * simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. inv H1. rewrite H, H0. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe1, IHe2. simpl. unfold pids_union. rewrite IHe1, IHe2.
    assert 
      (usedPIDsExp_Interp e1 ∪ (usedPIDsExp_Interp e2 ∪ flat_union_Interp usedPIDsExp_Interp l) =
       usedPIDsExp_Interp e1 ∪ usedPIDsExp_Interp e2 ∪ flat_union_Interp usedPIDsExp_Interp l) 
       as Hhelp.
    { set_solver. }
    rewrite Hhelp. clear Hhelp.
    unfold flat_union. unfold flat_union_Interp. unfold pids_empty. unfold pids_union.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe3. rewrite H1. apply IHl in H2.
      assert 
        (usedPIDsExp_Interp e1 ∪ usedPIDsExp_Interp e2
         ∪ (usedPIDsExp_Interp a ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l) =
         usedPIDsExp_Interp a ∪ (usedPIDsExp_Interp e1
         ∪ usedPIDsExp_Interp e2 ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l)) 
         as Hhelp.
      { set_solver. } rewrite Hhelp.
      rewrite H2. set_solver.
  * simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe. simpl. 
    unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    rewrite IHe. f_equal.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe0. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe. simpl.
    unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    rewrite IHe. f_equal.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe0. destruct a, p. simpl. destruct H1 as [Hp [H H0]].
      unfold flat_union, flat_union_Interp, pids_union, pids_empty in Hp.
      rewrite Hp, H, H0. f_equal.
      apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe1, IHe2. simpl. rewrite IHe1, IHe2. reflexivity.
  * fold usedPIDsExp_Interp in IHe1, IHe2. simpl. rewrite IHe1, IHe2. reflexivity.
  * fold usedPIDsExp_Interp in IHe. simpl.
    unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    rewrite IHe. f_equal.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe0. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * fold usedPIDsExp_Interp in IHe1, IHe2, IHe3. simpl.
    unfold pids_union. rewrite IHe1, IHe2, IHe3. set_solver.
  * (* EBin *)
    simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * (* ESeg *)
    fold usedPIDsExp_Interp in IHe, IHe0. simpl in IHe, IHe0. simpl.
    unfold pids_union. rewrite IHe, IHe0. reflexivity.
  * (* PCons *)
    simpl. unfold pids_union. rewrite IHe, IHe0. reflexivity.
  * (* PTuple *)
    simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * (* PMap *)
    simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. inv H1. rewrite H, H0. apply IHl in H2. rewrite H2. reflexivity.
  * (* PBin *)
    simpl. unfold flat_union. unfold flat_union_Interp. unfold pids_union. unfold pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHe. destruct H1. rewrite H, H0. apply IHl in H2. rewrite H2. reflexivity.
  * (* clauses of ECase *)
    constructor; [|assumption].
    fold usedPIDsExp_Interp in IHe2, IHe3.
    split; [|split]; [| exact IHe2 | exact IHe3].
    unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction l.
    + reflexivity.
    + simpl. inv IHe1. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
Qed.

Lemma usedPIDsRed_equiv : forall (r : Redex), usedPIDsRed r = usedPIDsRed_Interp r.
Proof.
  intros. destruct r.
  * cbn. apply usedPIDsExp_equiv.
  * cbn. unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction vs.
    + simpl. reflexivity.
    + simpl. rewrite IHvs.
      assert (usedPIDsVal a = usedPIDsVal_Interp a) by (apply (usedPIDsExp_equiv (VVal a))).
      rewrite H. reflexivity.
  * cbn. unfold pids_union.
    assert (usedPIDsVal e.1.2 = usedPIDsVal_Interp e.1.2) by (apply (usedPIDsExp_equiv (VVal e.1.2))).
    assert (usedPIDsVal e.2   = usedPIDsVal_Interp e.2  ) by (apply (usedPIDsExp_equiv (VVal e.2  ))).
    rewrite H, H0. reflexivity.
  * reflexivity.
Qed.

Lemma usedPIDsFrameId_equiv : forall (i : FrameIdent), 
  usedPIDsFrameId i = usedPIDsFrameId_Interp i.
Proof.
  intros. destruct i; auto.
  * simpl. unfold pids_union.
    assert (usedPIDsVal m = usedPIDsVal_Interp m) by (apply (usedPIDsExp_equiv (VVal m))).
    assert (usedPIDsVal f = usedPIDsVal_Interp f) by (apply (usedPIDsExp_equiv (VVal f))).
    rewrite H, H0. reflexivity.
  * simpl.
    exact (usedPIDsExp_equiv (VVal v)).
Qed.

Lemma usedPIDsPat_equiv : forall (p : Pat), usedPIDsPat p = usedPIDsPat_Interp p.
Proof.
  induction p using Pat_ind_weakened with
    (Q := Forall (fun p => usedPIDsPat p = usedPIDsPat_Interp p))
    (R := Forall (PBoth (fun p => usedPIDsPat p = usedPIDsPat_Interp p)))
    (T := Forall (fun seg => usedPIDsPat (val seg) = usedPIDsPat_Interp (val seg))); auto.
  * simpl. unfold pids_union. rewrite IHp1, IHp2. reflexivity.
  * simpl. unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHp. rewrite H1. apply IHl in H2. rewrite H2. reflexivity.
  * simpl. unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHp. inv H1. rewrite H, H0. apply IHl in H2. rewrite H2. reflexivity.
  * simpl. unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. inv IHp.
      assert (usedPIDsVal (Syntax.size a) = usedPIDsVal_Interp (Syntax.size a))
        by (apply (usedPIDsExp_equiv (VVal (Syntax.size a)))).
      rewrite H1, H. apply IHl in H2. rewrite H2. reflexivity.
Qed.

Lemma usedPIDsPats_equiv : forall (l : list Pat),
  foldr (λ (x : Pat) (acc : gset PID), usedPIDsPat x ∪ acc) ∅ l =
  foldr (λ (x : Pat) (acc : gset PID), usedPIDsPat_Interp x ∪ acc) ∅ l.
Proof.
  induction l; simpl; try reflexivity.
  rewrite usedPIDsPat_equiv, IHl. reflexivity.
Qed.

Lemma usedPIDsFrame_equiv : forall (f : Frame), usedPIDsFrame f = usedPIDsFrame_Interp f.
Proof.
  intros. destruct f; simpl.
  * exact (usedPIDsExp_equiv hd).
  * exact (usedPIDsExp_equiv (VVal tl)).
  * unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    rewrite (usedPIDsFrameId_equiv ident).
    assert (usedPIDsFrameId_Interp ident ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
            ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el =
            usedPIDsFrameId_Interp ident ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
            ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el)).
    { set_solver. }
    rewrite H. f_equal. clear H.
    induction vl.
    + simpl. f_equal.
      induction el.
      - simpl. reflexivity.
      - simpl.
        rewrite (usedPIDsExp_equiv a), IHel. reflexivity.
    + simpl.
      assert (usedPIDsVal a = usedPIDsVal_Interp a) by (apply (usedPIDsExp_equiv (VVal a))).
      rewrite H.
      assert (usedPIDsVal_Interp a ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
              ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el =
              usedPIDsVal_Interp a ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ vl
              ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ el)).
      { set_solver. } rewrite H0. rewrite IHvl. set_solver.
  * unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction l.
    + simpl. reflexivity.
    + simpl. rewrite (usedPIDsExp_equiv a), IHl. reflexivity.
  * unfold flat_union, flat_union_Interp, pids_union, pids_empty. induction l.
    + simpl. rewrite (usedPIDsExp_equiv f). reflexivity.
    + simpl.
      assert (usedPIDsExp f ∪ 
              (usedPIDsExp a ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l) =
              usedPIDsExp a ∪ 
              (usedPIDsExp f ∪ foldr (λ (x : Exp) (acc : gset PID), usedPIDsExp x ∪ acc) ∅ l)) by set_solver.
      rewrite H. rewrite IHl, (usedPIDsExp_equiv a). set_solver.
  * unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    assert (usedPIDsVal m = usedPIDsVal_Interp m) by (apply (usedPIDsExp_equiv (VVal m))).
    rewrite H. f_equal.
    induction l.
    + reflexivity.
    + simpl. rewrite (usedPIDsExp_equiv a), IHl. reflexivity.
  * unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    induction l.
    + reflexivity.
    + simpl. rewrite (usedPIDsPats_equiv a.1.1), (usedPIDsExp_equiv a.1.2), (usedPIDsExp_equiv a.2), IHl. reflexivity.
  * unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    rewrite (usedPIDsExp_equiv ex).
    assert (usedPIDsExp_Interp ex ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ lv
            ∪ foldr (λ (x : list Pat * Exp * Exp) (acc : gset PID),
              foldr (λ (x0 : Pat) (acc0 : gset PID), usedPIDsPat x0 ∪ acc0) ∅ x.1.1 ∪
              usedPIDsExp x.1.2 ∪ usedPIDsExp x.2 ∪ acc) ∅ le =
            usedPIDsExp_Interp ex ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ lv
            ∪ foldr (λ (x : list Pat * Exp * Exp) (acc : gset PID),
              foldr (λ (x0 : Pat) (acc0 : gset PID), usedPIDsPat x0 ∪ acc0) ∅ x.1.1 ∪
              usedPIDsExp x.1.2 ∪ usedPIDsExp x.2 ∪ acc) ∅ le)) by set_solver.
    rewrite H. f_equal. clear H. f_equal.
    + induction lv.
      - reflexivity.
      - simpl. rewrite IHlv.
        assert (usedPIDsVal a = usedPIDsVal_Interp a) by (apply (usedPIDsExp_equiv (VVal a))).
        rewrite H. reflexivity.
    + induction le.
      - reflexivity.
      - simpl. rewrite (usedPIDsPats_equiv a.1.1), (usedPIDsExp_equiv a.1.2), (usedPIDsExp_equiv a.2), IHle. reflexivity.
  * exact (usedPIDsExp_equiv e).
  * exact (usedPIDsExp_equiv e).
  * unfold pids_union. rewrite (usedPIDsExp_equiv e2), (usedPIDsExp_equiv e3). reflexivity.
  * (* FSeg1 *)
    exact (usedPIDsExp_equiv _).
  * (* FSeg2 *)
    exact (usedPIDsExp_equiv (VVal _)).
Qed.

Lemma usedPIDsStack_equiv : forall (fs : FrameStack), usedPIDsStack fs = usedPIDsStack_Interp fs.
Proof.
  intros. induction fs.
  + reflexivity.
  + simpl. rewrite (usedPIDsFrame_equiv a), IHfs. reflexivity.
Qed.

Instance LeibnizEquiv_gset_pid : LeibnizEquiv (gset (gset PID)) := _.

Lemma usedPIDsProc_equiv : forall (p : Process), usedPIDsProc p = usedPIDsProc_Interp p.
Proof.
  intros. destruct p; simpl.
  * destruct l, p, p, p. unfold flat_union, flat_union_Interp, pids_union, pids_empty.
    assert (usedPIDsStack f ∪ usedPIDsRed r ∪ g
            ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.1
            ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.2 =
            usedPIDsStack f ∪ (usedPIDsRed r ∪ (g
            ∪ (foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.1
            ∪ foldr (λ (x : Val) (acc : gset PID), usedPIDsVal x ∪ acc) ∅ m.2)))) by set_solver.
    rewrite H. clear H.
    rewrite (usedPIDsStack_equiv f), (usedPIDsRed_equiv r). do 4 f_equal.
    + destruct m. simpl. induction l.
      - reflexivity.
      - simpl. assert (usedPIDsVal a = usedPIDsVal_Interp a) by (apply (usedPIDsExp_equiv (VVal a))).
        rewrite H, IHl. reflexivity.
    + destruct m. simpl. induction l0.
      - reflexivity.
      - simpl. assert (usedPIDsVal a = usedPIDsVal_Interp a) by (apply (usedPIDsExp_equiv (VVal a))).
        rewrite H, IHl0. reflexivity.
  * unfold pids_map_set_union, pids_insert. f_equal.
    induction d using map_first_key_ind.
    + unfold map_to_set. setoid_rewrite map_to_list_empty. simpl. reflexivity.
    + unfold map_to_set.
      assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
      { apply map_to_list_insert_first_key; assumption. }
      setoid_rewrite H1. clear H1. simpl. f_equal.
      - assert (usedPIDsVal x = usedPIDsVal_Interp x) by (apply (usedPIDsExp_equiv (VVal x))).
        rewrite H1. f_equal. set_solver.
      - exact IHd.
Qed.

Lemma allPIDsPool_equiv: forall (p : ProcessPool), allPIDsPool p = allPIDsPool_Interp p.
Proof.
  intros. unfold allPIDsPool. unfold allPIDsPool_Interp.
  unfold flat_union, flat_union_Interp, pids_union, pids_empty, pool_toList, pids_insert.
  induction p using map_first_key_ind.
  * setoid_rewrite map_to_list_empty. simpl. reflexivity.
  * assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
    { apply map_to_list_insert_first_key; assumption. }
    setoid_rewrite H1. clear H1. simpl.
    assert ({[i]} ∪ usedPIDsProc x = usedPIDsProc_Interp x ∪ {[i]}).
    { assert (usedPIDsProc x = usedPIDsProc_Interp x) by (apply (usedPIDsProc_equiv x)). 
      rewrite H1. set_solver. }
    rewrite H1. f_equal. exact IHp.
Qed.

Lemma usedPIDsSignal_equiv: forall (s : Signal), usedPIDsSignal s = usedPIDsSignal_Interp s.
Proof.
  intros.
  destruct s; auto; simpl.
  * exact (usedPIDsExp_equiv (VVal e)).
  * exact (usedPIDsExp_equiv (VVal r)).
Qed.

Lemma allPIDsEther_equiv : forall (eth : Ether), allPIDsEther eth = allPIDsEther_Interp eth.
Proof.
  intros. unfold allPIDsEther, allPIDsEther_Interp.
  unfold flat_union, flat_union_Interp, pids_insert, pids_union, pids_empty, pids_singleton, ether_toList.
  induction eth using map_first_key_ind.
  * setoid_rewrite map_to_list_empty. simpl. reflexivity.
  * assert ((map_to_list (<[i:=x]> m) = ((i, x) ::map_to_list m))).
    { apply map_to_list_insert_first_key; assumption. }
    setoid_rewrite H1. clear H1. simpl. f_equal.
    + destruct i. f_equal.
      - set_solver.
      - clear. induction x.
        ** simpl. reflexivity.
        ** simpl. rewrite (usedPIDsSignal_equiv a), IHx. reflexivity.
    + exact IHeth.
Qed.

Lemma usedInPool_equiv: forall (pid : PID) (p : ProcessPool), usedInPool pid p = usedInPool_Interp pid p.
Proof.
  intros. unfold usedInPool, usedInPool_Interp, pids_member.
  rewrite allPIDsPool_equiv.
  destruct (gset_elem_of_dec _ _); reflexivity.
Qed.

Lemma usedInEther_equiv: forall (pid : PID) (eth : Ether), usedInEther pid eth = usedInEther_Interp pid eth.
Proof.
  intros. unfold usedInEther, usedInEther_Interp, pids_member.
  rewrite allPIDsEther_equiv.
  destruct (gset_elem_of_dec _ _); reflexivity.
Qed.

Lemma etherAdd_equiv: forall (source dest : PID) (m : Signal) (n : Ether),
  etherAdd source dest m n = etherAdd_Interp source dest m n.
Proof.
  intros. unfold etherAdd_Interp, etherAdd, ether_lookup, ether_insert. reflexivity.
Qed.

Lemma etherPop_equiv: forall (source dest : PID) (n : Ether),
  etherPop source dest n = etherPop_Interp source dest n.
Proof.
  intros. unfold etherPop, etherPop_Interp, ether_lookup, ether_insert. reflexivity.
Qed.
