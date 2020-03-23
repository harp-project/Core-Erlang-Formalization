Load Core_Erlang_Induction.

Module Core_Erlang_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
(* Import Core_Erlang_Closures. *)
Import Core_Erlang_Helpers.
Import Core_Erlang_Equalities.
Import Core_Erlang_Induction.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.

Proposition plus_comm_basic {e1 e2 : Value} : eval "plus"%string [e1 ; e2] = eval "plus"%string [e2; e1].
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  all: try(reflexivity).
  all: try(destruct l); try(destruct l0); try(reflexivity).
  * rewrite <- Z.add_comm. reflexivity.
Qed.

(* Proposition and_comm_basic (e1 e2 : Value) : eval "and"%string [e1 ; e2] = eval "and"%string [e2 ; e1].
Proof.
  simpl. case_eq e1; case_eq e2; intros.
  1-144: try(reflexivity).
  1-23: try(destruct l); try(destruct l0); try(reflexivity).
  * pose (eqf := string_dec s "false"); pose (eqf2 := string_dec s0 "false"); pose (eqt := string_dec s "true"); pose (eqt2 := string_dec s0 "true"); destruct eqf, eqf2, eqt, eqt2; subst; try(reflexivity).
    - admit.
Admitted. *)

Lemma in_combined_list : forall {P : Prop}, 
                         forall {l : list Expression} {l' : list Value} {a : Expression} {b : Value},

  (forall e : Expression, forall e' : Value,
    In (e, e') ((a, b) :: combine l l') -> P) -> 
  (forall e : Expression, forall e' : Value,
    In (e, e') (combine l l') -> P).
Proof.
  intros. pose (IN_C := in_cons (a, b) (e, e') (combine l l') H0). pose (H e e' IN_C). assumption.
Qed.

Import Omega.


Proposition nat_ge_or : forall {n m : nat}, n >= m <-> n = m \/ n > m.
Proof.
intros. omega.
Qed.

Proposition determinism_hypo {env : Environment} {exp : Expression} {v1 : Value} {v2 : Value} : 
 |env, exp| -e> inl v1 ->
 (forall v2 : Value, |env, exp| -e> inl v2 -> v1 = v2)
  ->
  |env, exp| -e> inl v2
->
  v1 = v2
.
Proof.
  intros. apply (H0 v2 H1).
Qed.

Lemma index_case_equality {env : Environment} {patterns : list Pattern} {guards bodies : list Expression} {v : Value} (i i0 : nat) (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env, gg | -e> v2 -> inl ffalse = v2)
  ->
  (forall j : nat,
     j < i0 ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     | add_bindings bb env, gg | -e> inl ffalse)
  ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings)
  ->
  match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0)
  ->
  |add_bindings bindings0 env, guard0| -e> inl ttrue
  ->
  |add_bindings bindings env, guard| -e> inl ttrue
  ->
  (forall v2 : Value + Exception, |add_bindings bindings env, guard| -e> v2 -> inl ttrue = v2)
->
  i = i0.
Proof.
  intros. pose (D := Nat.lt_decidable i i0). destruct D.
  * pose (P1 := H0 i H6 guard exp bindings H1). pose (P2 := H5 (inl ffalse) P1). inversion P2.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (P3 := H i0 H7 guard0 exp0 bindings0 H2 (inl ttrue) H3). inversion P3.
Qed.

Lemma list_equality {env : Environment} {exps : list Expression}  : 
forall vals vals0 : list Value,
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> |env, exp| -e> inl val) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals) -> forall v2 : Value, |env, exp| -e> inl v2 -> val = v2) ->
  (forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps vals0) -> |env, exp| -e> inl val) ->
  Datatypes.length exps = Datatypes.length vals ->
  Datatypes.length exps = Datatypes.length vals0
->
  vals = vals0.
Proof.
  induction exps.
  * intros. inversion H3. inversion H2. apply eq_sym in H6. apply eq_sym in H5. apply length_zero_iff_nil in H6. apply length_zero_iff_nil in H5. subst. reflexivity.
  * intros. inversion H3. inversion H2. 
  
  (* first elements are the same *)
    pose (EE1 := element_exist Value (Datatypes.length exps) vals (eq_sym H6)).
    pose (EE2 := element_exist Value (Datatypes.length exps) vals0 (eq_sym H5)).
    inversion EE1. inversion EE2. inversion H4. inversion H7. subst.
    pose (IN_EQ1 := in_eq (a, x) (combine (exps) (x1))).
    pose (IN_EQ2 := in_eq (a, x0) (combine (exps) (x2))).
    pose (P1 := H1 a x0 IN_EQ2).
    pose (P2 := H0 a x IN_EQ1 x0 P1). rewrite <- P2 in *.
  (* remaining lists are the same *)
  
  (* These three asserts ensure, that if something states for every element in a (b::l) list, then it states
  for every element in l too*)
    assert (
      forall (exp : Expression) (val : Value),
       In (exp, val) (combine exps x1) ->
       forall v2 : Value, |env, exp| -e> inl v2 -> val = v2
    ).
    {
      intros. pose (IN_C := in_cons (a, x) (exp, val) (combine exps x1) H8). pose (P3 := H0 exp val IN_C v2 H9). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
    In (exp, val) (combine exps x1) -> |env, exp| -e> inl val
    ).
    {
      intros. pose (IN_C := in_cons (a, x) (exp, val) (combine exps x1) H9). pose (P3 := H exp val IN_C). assumption.
    }
    assert (
      forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps x2) -> |env, exp| -e> inl val
    ).
    {
      intros. pose (IN_C := in_cons (a, x0) (exp, val) (combine exps x2) H10). pose (P3 := H1 exp val IN_C). assumption.
    }
    (* simpl list lengths *)
    inversion H2.
    inversion H3.
    pose (IH := IHexps x1 x2 H9 H8 H10 H12 H13). rewrite IH.
    reflexivity.
Qed.



Lemma exception_equality {env : Environment} {exps : list Expression} (i i0 : nat) (vals vals0 : list Value) (ex ex0 : Exception) :
(forall j : nat,
     j < i ->
     forall v2 : Value + Exception,
     | env, nth j exps ErrorExp | -e> v2 -> inl (nth j vals ErrorValue) = v2) ->
(forall j : nat, j < i0 -> | env, nth j exps ErrorExp | -e> inl (nth j vals0 ErrorValue)) ->
(forall v2 : Value + Exception, | env, nth i exps ErrorExp | -e> v2 -> inr ex = v2) ->
| env, nth i0 exps ErrorExp | -e> inr ex0 ->
i = i0.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (P1 := H0 (i) l0). pose (P2 := H1 (inl (nth i vals0 ErrorValue)) P1). inversion P2.
    - intros. assumption.
  * pose (P1 := H i0 g (inr ex0) H2). inversion P1.
Qed.

Proposition nth_In_combined_list {exps : list Expression} (vals vals0 : list Value) :
length exps = length vals ->
length vals0 < length exps ->
In (nth (length vals0) exps ErrorExp, nth (length vals0) vals ErrorValue) (combine exps vals).
Proof.
  intros. rewrite <- combine_nth.
    * apply nth_In. rewrite combine_length. rewrite <- H. rewrite Nat.min_id. assumption. 
    * assumption.
Qed.

Proposition nth_to_nth {env : Environment} {exps : list Expression} (vals vals0 : list Value) :
  (forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps vals0) -> | env, exp | -e> inl val) ->
  Datatypes.length exps = Datatypes.length vals0 ->
  Datatypes.length vals < Datatypes.length exps
->
  | env, nth (Datatypes.length vals) exps ErrorExp | -e>
   inl (nth (Datatypes.length vals) vals0 ErrorValue).
Proof.
  intros. apply H. rewrite <- combine_nth. 2: assumption. apply nth_In. rewrite combine_length. rewrite <- H0. rewrite Nat.min_id. assumption.
Qed.

Proposition restrict_union {env : Environment} {exps : list Expression} {vals : list Value} :
  (forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps vals) ->
     forall v2 : Value + Exception, | env, exp | -e> v2 -> inl val = v2)
->
  (forall (exp : Expression) (val : Value),
     In (exp, val) (combine exps vals) ->
     forall v2 : Value, | env, exp | -e> inl v2 -> val = v2).
Proof.
  intros. pose (P1 := H exp val H0). pose (P2 := P1 (inl v2) H1). inversion P2. reflexivity.
Qed.

Proposition nth_to_nth_case {env : Environment} {v : Value} {patterns : list Pattern} {guards bodies : list Expression} (i i0 : nat) (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) (ex : Exception):
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env, gg | -e> v2 -> inl ffalse = v2) ->
(forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v patterns guards bodies j = Some (gg, ee, bb) -> | add_bindings bb env, gg | -e> inl ffalse) ->
(forall v2 : Value + Exception,
      | add_bindings bindings env, guard | -e> v2 -> inl ttrue = v2) ->
| add_bindings bindings0 env, guard0 | -e> inr ex ->
match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0) ->
match_clause v patterns guards bodies i = Some (guard, exp, bindings)
->
False.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (P1 := H0 i l0 _ _ _ H4). pose (P2 := H1 (inl ffalse) P1). inversion P2.
    - intros. subst. rewrite H3 in H4. inversion H4. subst. pose (P1 := H1 (inr ex) H2). inversion P1.
  * pose (P1 := H i0 g guard0 exp0 bindings0 H3 (inr ex) H2). inversion P1.
Qed.

Proposition nth_to_nth_case_ex {env : Environment} {v : Value} {patterns : list Pattern} {guards bodies : list Expression} (i i0 : nat) (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) (ex : Exception):
(forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env, gg | -e> v2 -> inl ffalse = v2) ->
(forall j : nat,
      j < i0 ->
      forall (gg ee : Expression) (bb : list (Var * Value)),
      match_clause v patterns guards bodies j = Some (gg, ee, bb) -> | add_bindings bb env, gg | -e> inl ffalse) ->
(forall v2 : Value + Exception,
               | add_bindings bindings env, guard | -e> v2 -> inr ex = v2) ->
| add_bindings bindings0 env, guard0 | -e> inl ttrue ->
| add_bindings bindings env, guard | -e> inr ex ->
match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0) ->
match_clause v patterns guards bodies i = Some (guard, exp, bindings)
->
False.
Proof.
  intros. destruct (le_gt_dec i i0).
  * case_eq (le_lt_or_eq i i0 l).
    - intros. pose (P1 := H0 i l0 _ _ _ H5). pose (P2 := H1 (inl ffalse) P1). inversion P2.
    - intros. subst. rewrite H4 in H5. inversion H5. subst. pose (P1 := H1 (inl ttrue) H2). inversion P1.
  * pose (P1 := H i0 g guard0 exp0 bindings0 H4 (inl ttrue) H2). inversion P1.
Qed.

Lemma index_case_equality_ex {env : Environment} {v : Value} {patterns : list Pattern} {guards bodies : list Expression} (i i0 : nat) (guard guard0 exp exp0 : Expression) (bindings bindings0 : list (Var * Value)) (ex ex0 : Exception) : 
  (forall j : nat,
     j < i ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     forall v2 : Value + Exception, | add_bindings bb env, gg | -e> v2 -> inl ffalse = v2)
  ->
  (forall j : nat,
     j < i0 ->
     forall (gg ee : Expression) (bb : list (Var * Value)),
     match_clause v patterns guards bodies j = Some (gg, ee, bb) ->
     | add_bindings bb env, gg | -e> inl ffalse)
  ->
  match_clause v patterns guards bodies i = Some (guard, exp, bindings)
  ->
  match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0)
  ->
  |add_bindings bindings0 env, guard0| -e> inr ex0
  ->
  |add_bindings bindings env, guard| -e> inr ex
  ->
  (forall v2 : Value + Exception, |add_bindings bindings env, guard| -e> v2 -> inr ex = v2)
->
  i = i0.
Proof.
  intros. pose (P1 := Nat.lt_decidable i i0). destruct P1.
  * pose (P2 := H0 i H6 guard exp bindings H1). pose (P3 := H5 (inl ffalse) P2). inversion P3.
  * apply not_lt in H6. apply (nat_ge_or) in H6. inversion H6.
    - assumption.
    - pose (P3 := H i0 H7 guard0 exp0 bindings0 H2 (inr ex0) H3). inversion P3.
Qed.

Lemma map_helper {env : Environment} {kl vl : list Expression} {kvals vvals : list Value} {j : nat} :
  (forall i : nat,
     i < j ->
     | env, nth i kl ErrorExp | -e> inl (nth i kvals ErrorValue) /\
     | env, nth i vl ErrorExp | -e> inl (nth i vvals ErrorValue))
->
  (forall i : nat,
     i < j ->
     | env, nth i kl ErrorExp | -e> inl (nth i kvals ErrorValue)) /\
  (forall i : nat,
     i < j ->
     | env, nth i vl ErrorExp | -e> inl (nth i vvals ErrorValue)).
Proof.
  intros. split; intros; pose (P1 := H i H0); inversion P1; assumption.
Qed.

Proposition indexed_list_equality {env : Environment} {kl : list Expression}:
forall  kvals kvals0 : list Value,
  (forall i : nat,
      i < Datatypes.length kl -> | env, nth i kl ErrorExp | -e> inl (nth i kvals ErrorValue)) ->
  (forall i : nat,
     i < Datatypes.length kl ->
     forall v2 : Value + Exception,
     | env, nth i kl ErrorExp | -e> v2 -> inl (nth i kvals ErrorValue) = v2) ->
  (forall i : nat,
      i < Datatypes.length kl -> | env, nth i kl ErrorExp | -e> inl (nth i kvals0 ErrorValue)) ->
  length kl = length kvals ->
  length kl = length kvals0
->
  kvals0 = kvals.
Proof.
  induction kl; intros.
  * simpl in *. apply eq_sym, length_zero_iff_nil in H2. apply eq_sym, length_zero_iff_nil in H3. subst. reflexivity.
  * inversion H2. inversion H3. 
    pose (EE1 := element_exist Value (length kl) kvals (eq_sym H5)).
    pose (EE2 := element_exist Value (length kl) kvals0 (eq_sym H6)).
    inversion EE1. inversion EE2. inversion H4. inversion H7.
    subst.
    (* FIRST ELEMENTS ARE EQUAL *)
    assert (0 < length (a::kl)). { simpl. omega. }
    pose (P1 := H 0 H8).
    pose (P2 := H0 0 H8).
    pose (P3 := H1 0 H8).
    simpl in P1, P2, P3.
    pose (P4 := P2 (inl x0) P3). inversion P4. subst.
    (* OTHER ELEMENTS ARE EQUAL *)
    assert ((forall i : nat,
        i < Datatypes.length kl -> | env, nth i kl ErrorExp | -e> inl (nth i x1 ErrorValue))).
    {
      intros.
      assert ((S i) < Datatypes.length (a :: kl)). { omega. }
      pose (O1 := H (S i) H10). simpl in *. assumption.
    }
    assert ((forall i : nat,
        i < Datatypes.length kl ->
        forall v2 : Value + Exception,
        | env, nth i kl ErrorExp | -e> v2 -> inl (nth i x1 ErrorValue) = v2)).
    {
      intros.
      assert ((S i) < Datatypes.length (a :: kl)). { omega. }
      pose (O1 := H0 (S i) H12). simpl in O1.
      pose (P' := True).
      apply (O1 v2). assumption.
    }
    assert ((forall i : nat,
        i < Datatypes.length kl -> | env, nth i kl ErrorExp | -e> inl (nth i x2 ErrorValue))).
    {
      intros.
      assert ((S i) < Datatypes.length (a :: kl)). { omega. }
      pose (O1 := H1 (S i) H12). assumption.
    }
    inversion H2. inversion H3.
    pose (IH := IHkl x1 x2 H9 H10 H11 H13 H14). rewrite IH. reflexivity. 
Qed.

Proposition indexed_nth_to_nth {env : Environment} {kl : list Expression} (kvals kvals0 : list Value):
(forall i : nat,
      i < Datatypes.length kl -> | env, nth i kl ErrorExp | -e> inl (nth i kvals ErrorValue)) ->
  Datatypes.length kl = Datatypes.length kvals ->
  Datatypes.length kvals0 < Datatypes.length kl
->
  | env, nth (length kvals0) kl ErrorExp | -e> inl (nth (length kvals0) kvals ErrorValue).
Proof.
  intros. pose (P1 := H _ H1). assumption.
Qed.

Theorem determinism : forall {env : Environment} {e : Expression} {v1 : Value + Exception} , |env, e| -e> v1 -> (forall v2, |env, e| -e> v2 -> v1 = v2).
Proof.
  intro. intro. intro. intro H. induction H using eval_expr_ind_extended.
  (* LITERAL, VARIABLE, FUNCTION SIGNATURE, FUNCTION DEFINITION *)
  1-4: intros; inversion H; reflexivity.
  * intros. inversion H. reflexivity.

  (* TUPLE *)
  * intros. inversion H2; subst. 
    - pose (LEQ := list_equality vals vals0 H0 (restrict_union H1) H6 H H4). rewrite LEQ. reflexivity.
   - pose (P1 := H1 (nth (Datatypes.length vals0) exps ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list vals vals0 H H5)  (inr ex) H8). inversion P1.

  (* LIST *)
  * intros. inversion H1. 
    - subst. pose (IH1 := IHeval_expr1 (inl hdv0) H5). pose (IH2 := IHeval_expr2 (inl tlv0) H7). inversion IH1. inversion IH2. reflexivity.
    - subst. pose (IH1 := IHeval_expr1 (inr ex) H6). inversion IH1.
    - subst. pose (IH2 := IHeval_expr2 (inr ex) H7). inversion IH2.

  (* CASE *)
  * intros. inversion H8.
    - subst.
      (* determinism of initial expression *)
      pose (IH1 := IHeval_expr1 (inl v0) H13). inversion IH1. subst.
      pose (ICE := index_case_equality i i0 guard guard0 exp exp0 bindings bindings0 H5 H20 H3 H18 H21 H6 IHeval_expr2).
     (* Coq Hacking for possible rewrites *)
     pose (H18' := H18). pose (H3' := H3). rewrite ICE in H3'. rewrite H3' in H18'. inversion H18'. rewrite H10, H11, H12 in *.
     (* clause evaluation *)
    pose (IH3 := IHeval_expr3 v2 H22). assumption.
    - subst. pose (IH1 := IHeval_expr1 (inr ex) H17). inversion IH1.
    - subst. pose (IH1 := IHeval_expr1 (inl v0) H16). inversion IH1. rewrite <- H10 in *. pose (N_N := nth_to_nth_case i i0 guard guard0 exp exp0 bindings bindings0 ex H5 H19 IHeval_expr2 H20 H18 H3). inversion N_N.

  (* CALL *)
  * intros. inversion H3.
    - subst.
      pose (LEQ := list_equality vals vals0 H0 (restrict_union H1) H8 H H6). rewrite LEQ. reflexivity.
    - subst. pose (P1 := H1 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list vals vals0 H H7) (inr ex) H11). inversion P1.

  (* APPLY *)
  * intros. inversion H5.
    - subst. pose (LEQ := list_equality vals vals0 H2 (restrict_union H3) H12 H H8). rewrite LEQ in *.
      (* The equality of the var lists *)
      pose (IH1 := IHeval_expr1 (inl (VClosure ref0 ext0 var_list0 body0)) H9). inversion IH1. rewrite H7, H11, H13, H15 in *.
      (* equality of the expressions *)
      pose (IH2 := IHeval_expr2 v2 H14). assumption.
    - subst. pose (IH1 := IHeval_expr1 (inr ex) H10). inversion IH1.
    - subst. pose (P1 := H3 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list vals vals0 H H9) (inr ex) H14). inversion P1.
    - subst. pose (IH1 := IHeval_expr1 (inl v0) H11). inversion IH1. rewrite <- H7 in H13. pose (P1 := H13 ref ext var_list body). unfold not in P1. assert (VClosure ref ext var_list body = VClosure ref ext var_list body). { auto. } pose (P2 := P1 H6). inversion P2.
    - subst. pose (IH1 := IHeval_expr1 (inl (VClosure ref0 ext0 var_list0 body0)) H9). inversion IH1. subst. rewrite H1 in *. rewrite <- H, H8 in *. unfold not in H13. assert (length vals0 = length vals0). { auto. } pose (P1 := H13 H6). inversion P1.

  (* LET *)
  * intros. inversion H3. subst.
   - pose (LEQ := list_equality vals vals0 H0 (restrict_union H1) H10 (eq_sym H) (eq_sym H8)). rewrite LEQ in *.
     pose (IH1 := IHeval_expr v2 H11). assumption.
   - subst. pose (P1 := H1 (nth (Datatypes.length vals0) exps ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) (nth_In_combined_list vals vals0 (eq_sym H) H9) (inr ex) H12). inversion P1.

  (* LETREC *)
  * intros. inversion H2. 
    - subst. pose (IH2 := IHeval_expr v2 H11). assumption.

  (* MAP *)
  * intros. inversion H6.
    - pose (MH := map_helper H3). inversion MH.
      pose (MH2 := map_helper H15). inversion MH2.
      rewrite H9 in *.
      pose (LEQ1 := indexed_list_equality kvals kvals0 H16 H4 H18 H1 H11).
      rewrite <- H9 in *.
      pose (LEQ2 := indexed_list_equality vvals vvals0 H17 H5 H19 H0 H10).
      rewrite LEQ1, LEQ2 in *. rewrite H2 in H13. inversion H13. reflexivity.
    - pose (IH := H4 i H12 (inr ex) H16). inversion IH.
    - pose (IH := H5 i H12 (inr ex) H17). inversion IH.

  (* LIST HEAD EXCEPTION *)
  * intros. inversion H0; subst.
    - pose (IH := IHeval_expr (inl hdv) H4). inversion IH.
    - apply IHeval_expr. assumption.
    - pose (IH := IHeval_expr (inl vhd) H4). inversion IH.

  (* LIST TAIL EXCEPTION *)
  * intros. inversion H1; subst.
    - pose (IH2 := IHeval_expr2 (inl tlv) H7). inversion IH2.
    - pose (IH1 := IHeval_expr1 (inr ex0) H6). inversion IH1.
    - apply IHeval_expr2. assumption.

  (* TUPLE EXCEPTION *)
  * intros. inversion H4.
    - subst.
      pose (IH := IHeval_expr (inl (nth (Datatypes.length vals) vals0 ErrorValue)) (nth_to_nth vals vals0 H8 H6 H0)). inversion IH.
    - apply IHeval_expr. pose (EEQ := exception_equality i i0 vals vals0 ex ex0 H2 H8 IHeval_expr H10).
      rewrite EEQ. assumption.
  
  (* CORECT TRY *)
  * intros. inversion H1.
    - subst. apply IHeval_expr2. pose (IH1 := IHeval_expr1 (inl val'0) H11). inversion IH1. subst. assumption.
    - subst. pose (IH1 := IHeval_expr1 (inr ex) H11). inversion IH1.
  
  (* CORRECT CATCH *)
  * intros. inversion H1.
    - subst. pose (IH1 := IHeval_expr1 (inl val') H11). inversion IH1.
    - subst. apply IHeval_expr2. pose (IH1 := IHeval_expr1 (inr ex0) H11). inversion IH1. subst. assumption.

  (* CASE EXCEPTIONS *)
  (** binding expression exception *)
  * intros. inversion H2.
    - subst. pose (IH := IHeval_expr (inl v) H7). inversion IH.
    - subst. apply IHeval_expr. assumption.
    - subst. pose (IH := IHeval_expr (inl v) H10). inversion IH.

  (** ith guard exception *)
  * intros. inversion H6.
    - pose (IH1  := IHeval_expr1 (inl v0) H11). inversion IH1. rewrite <- H22 in *. pose (N_N := nth_to_nth_case_ex i i0 guard guard0 exp exp0 bindings bindings0 ex H4 H18 IHeval_expr2 H19 H5 H16 H2). inversion N_N.
    - pose (IH1 := IHeval_expr1 (inr ex0) H15). inversion IH1.
    - pose (IH1 := IHeval_expr1 (inl v0) H14). inversion IH1. rewrite <- H20 in *.
    assert (match_clause v patterns guards bodies i0 = Some (guard0, exp0, bindings0)). { assumption. } 
    assert (match_clause v patterns guards bodies i = Some (guard, exp, bindings)). { assumption. }
    assert (| add_bindings bindings0 env, guard0 | -e> inr ex0). { assumption. }
    pose (ICE := index_case_equality_ex i i0 guard guard0 exp exp0 bindings bindings0 ex ex0 H4 H17 H2 H16 H18 H5 IHeval_expr2).
    rewrite <- ICE in H19. rewrite H19 in H21. inversion H21. rewrite H24, H25, H26 in *. pose (IH2 := IHeval_expr2 (inr ex0) H22). assumption.

  (* CALL EXCEPTION *)
  * intros. inversion H4.
    - subst.
      pose (IH := IHeval_expr (inl (nth (Datatypes.length vals) vals0 ErrorValue)) (nth_to_nth vals vals0 H9 H7 H0)). inversion IH.
    - apply IHeval_expr. pose (EEQ := exception_equality i i0 vals vals0 ex ex0 H2 H10 IHeval_expr H12).
      rewrite EEQ. assumption.

  (* APPLY EXCEPTION *)
  (* name evaluates to an exception *)
  * intros. inversion H0.
    - subst. pose (IH := IHeval_expr (inl (VClosure ref ext var_list body)) H4). inversion IH.
    - subst. apply IHeval_expr. assumption.
    - subst. pose (IH := IHeval_expr (inl v) H5). inversion IH.
    - subst. pose (IH := IHeval_expr (inl v) H6). inversion IH.
    - subst. pose (IH := IHeval_expr (inl _) H4). inversion IH.

  (* parameter exception *)
  * intros. inversion H5.
    - subst. pose (N_N := nth_to_nth vals vals0 H12 H8 H0). pose (IH2 := IHeval_expr2 (inl (nth (Datatypes.length vals) vals0 ErrorValue)) N_N). inversion IH2.
    - subst. pose (IH1 := IHeval_expr1 (inr _) H10). inversion IH1.
    - pose (EEQ := exception_equality i i0 vals vals0 ex ex0 H3 H12 IHeval_expr2 H14). rewrite EEQ in *.
      apply IHeval_expr2. rewrite EEQ. assumption.
    - subst. pose (N_N := nth_to_nth vals vals0 H9 H8 H0). pose (IH2 := IHeval_expr2 (inl (nth (Datatypes.length vals) vals0 ErrorValue)) N_N). inversion IH2.
    - subst. pose (N_N := nth_to_nth vals vals0 H11 H8 H0). pose (IH2 := IHeval_expr2 (inl (nth (Datatypes.length vals) vals0 ErrorValue)) N_N). inversion IH2.

  (* name evaluate to a non-closure value *)
  * intros. inversion H4.
    - subst. pose (IH := IHeval_expr (inl (VClosure ref ext var_list body)) H8). inversion IH. pose (P1 := H3 ref ext var_list body H6). inversion P1.
    - subst. pose (IH := IHeval_expr (inr ex) H9). inversion IH.
    - subst. pose (NIC := nth_In_combined_list vals vals0 H H8). pose (P1 := H1 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) NIC (inr ex) H13). inversion P1.
    - subst. reflexivity. (* More information is needed about the specific location *)
    - subst. pose (IH := IHeval_expr (inl (VClosure ref ext var_list body)) H8). inversion IH. pose (P1 := H3 ref ext var_list body H6). inversion P1.

  (* paramlist is too short/long *)
  * intros. inversion H4.
    - subst. pose (IH := IHeval_expr (inl (VClosure ref0 ext0 var_list0 body0)) H8). inversion IH. subst.
      rewrite <- H, H7 in *. pose (P1 := H3 H9). inversion P1.
    - subst. pose (IH := IHeval_expr (inr ex) H9). inversion IH.
    - subst. pose (NIC := nth_In_combined_list vals vals0 H H8). pose (P1 := H2 (nth (Datatypes.length vals0) params ErrorExp) (nth (Datatypes.length vals0) vals ErrorValue) NIC (inr ex) H13). inversion P1.
    - subst. pose (IH := IHeval_expr (inl v) H10). inversion IH. pose (P1 := H12 ref ext var_list body (eq_sym H6)). inversion P1.
    - reflexivity. (* More information is needed about the location *)
  
  (* LET EXCEPTION *)
  * intros. inversion H4.
    - subst. pose (IH := IHeval_expr (inl (nth (Datatypes.length vals) vals0 ErrorValue)) (nth_to_nth vals vals0 H11 (eq_sym H9) H0)). inversion IH.
    - apply IHeval_expr. pose (EEQ := exception_equality i i0 vals vals0 ex ex0 H2 H12 IHeval_expr H13).
      rewrite EEQ. assumption.

  (* MAP KEY EXCEPTION *)
  * intros. inversion H7.
    - pose (P1 := H16 i H2). inversion P1.
      pose (IH := IHeval_expr _ H17). inversion IH.
    - pose (MH := map_helper H15). inversion MH.
      pose (MH2 := map_helper H3). inversion MH2.
      assert (| env, nth i0 kl ErrorExp | -e> inr ex0). { auto. }
      pose (EE1 := exception_equality i i0 kvals kvals0 ex ex0 H4 H18 IHeval_expr H17).
      apply IHeval_expr. rewrite <- EE1 in H22. assumption.
    - pose (MH := map_helper H14). inversion MH.
      pose (MH2 := map_helper H3). inversion MH2.
      assert (i = i0).
      {
         pose (P1 := Nat.lt_decidable i i0). destruct P1.
         * pose (P2 := H19 i H23). pose (IH2 := IHeval_expr (inl (nth i kvals0 ErrorValue)) P2). inversion IH2.
         * apply not_lt in H23. apply (nat_ge_or) in H23. inversion H23.
           - assumption.
           - pose (P4 := H5 i0 H24 (inr ex0) H18). inversion P4.
      }
      rewrite H23 in *.
      pose (P5 := IHeval_expr (inl val) H16). inversion P5.
  * intros. inversion H8.
    - pose (P1 := H17 i H2). inversion P1.
      pose (IH := IHeval_expr2 _ H19). inversion IH.
    - pose (MH := map_helper H16). inversion MH.
      pose (MH2 := map_helper H3). inversion MH2.
      assert (i = i0).
      {
        pose (P1 := Nat.lt_decidable i i0). destruct P1.
         * pose (P2 := H20 i H23). pose (IH2 := IHeval_expr2 (inl (nth i vvals0 ErrorValue)) P2). inversion IH2.
         * apply not_lt in H23. apply (nat_ge_or) in H23. inversion H23.
           - assumption.
           - pose (P4 := H4 i0 H24 (inr ex0) H18). inversion P4.
      }
      rewrite H23 in *.
      pose (P5 := IHeval_expr1 (inr ex0) H18). inversion P5.
    - pose (MH := map_helper H15). inversion MH.
      pose (MH2 := map_helper H3). inversion MH2.
      assert (| env, nth i0 vl ErrorExp | -e> inr ex0). { auto. }
      pose (EE1 := exception_equality i i0 vvals vvals0 ex ex0 H5 H21 IHeval_expr2 H19).
      apply IHeval_expr2. rewrite <- EE1 in H24. assumption.
Qed.

Ltac unfold_list exprs2 n H1 name :=
subst; simpl in H1; pose (name := element_exist Expression n exprs2 (eq_sym H1)); inversion name; inversion H0.

(* Theorem env_permutation env env' cl e t:
(env, cl, e) -e> t -> length env = length env' ->
(forall elem, In elem env -> In elem env') ->
(env', cl, e) -e> t.
Proof.


Admitted.*)

Theorem uequal_eq v0 v:
  uequal v0 v = true <-> v0 = v.
Proof.
  intros. split; intros.
  { destruct v0, v.
    * inversion H. apply eqb_eq in H1. subst. reflexivity.
    * inversion H.
    * inversion H.
    * inversion H. destruct f, f0. inversion H1. apply Bool.andb_true_iff in H2. inversion H2. apply eqb_eq in H0. apply Nat.eqb_eq in H3. subst. reflexivity.
  }
  { destruct v, v0.
    * inversion H. subst. simpl. apply eqb_refl.
    * inversion H.
    * inversion H.
    * inversion H. simpl. destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
  }
Qed.

Theorem uequal_neq v0 v:
  uequal v0 v = false <-> v0 <> v.
Proof.
  split; intros.
  { destruct v0, v.
    * simpl in *. apply eqb_neq in H. unfold not in *. intros. apply H. inversion H0. reflexivity.
    * unfold not. intro. inversion H0.
    * unfold not. intro. inversion H0.
    * destruct f, f0. simpl in H. Search andb. apply Bool.andb_false_iff in H. inversion H.
      - apply eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
      - apply Nat.eqb_neq in H0. unfold not in *. intro. apply H0. inversion H1. reflexivity.
  }
  { destruct v0, v.
    * simpl in *. apply eqb_neq. unfold not in *. intro. apply H. subst. reflexivity.
    * simpl. reflexivity.
    * simpl. reflexivity.
    * simpl. destruct f, f0. simpl. apply Bool.andb_false_iff. unfold not in H. case_eq ((s =? s0)%string); intros.
      - right. apply eqb_eq in H0. apply Nat.eqb_neq. unfold not. intro. apply H. subst. reflexivity.
      - left. reflexivity.
  }
Qed.

Proposition uequal_refl var :
uequal var var = true.
Proof.
  destruct var.
  * simpl. apply eqb_refl.
  * destruct f. simpl. rewrite eqb_refl, Nat.eqb_refl. simpl. reflexivity.
Qed.

Proposition uequal_sym v1 v2 :
  uequal v1 v2 = uequal v2 v1.
Proof.
  destruct v1, v2.
  * simpl. rewrite eqb_sym. reflexivity.
  * simpl. reflexivity.
  * simpl. reflexivity.
  * simpl. destruct f, f0. simpl. rewrite eqb_sym, Nat.eqb_sym. reflexivity.
Qed.

Theorem env_app_get env var val:
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (uequal s var).
    - intros. simpl. rewrite uequal_refl. reflexivity.
    - intros. simpl. rewrite uequal_sym in H. rewrite H. exact IHenv.
Qed.

Proposition list_variables_not_in x exps :
~ In x ((flat_map variables exps)) ->
(forall exp : Expression, In exp exps -> ~ In x (variables exp)).
Proof.
  intros. induction exps.
  * inversion H0.
  * simpl in H. assert (~ In x (variables a) /\ ~ In x (flat_map variables exps)).
    {
      unfold not in *. split; intros.
      * apply H. apply in_or_app. left. assumption.
      * apply H. apply in_or_app. right. assumption.
    }
    inversion H1. inversion H0.
    - subst. assumption.
    - apply IHexps.
      + assumption.
      + assumption.
Qed.

(* Proposition clause_variables x cs:
  ~ (In x (flat_map clause_variables cs)) ->
(forall p gg ee, In (CCons p gg ee) cs -> ~(In x (variables gg)) /\ ~ (In x (variables ee))).
Proof.
  intros. unfold not in *. split; intros; apply H.
  * induction cs.
    - inversion H0.
    - simpl. apply in_or_app. inversion H0.
      + left. subst. simpl. apply in_or_app. left. assumption.
      + right. apply IHcs.
        ** simpl in H. intros. apply H. apply in_or_app. right. assumption.
        ** assumption.
  * induction cs.
    - inversion H0.
    - simpl. apply in_or_app. inversion H0.
      + left. subst. simpl. apply in_or_app. right. assumption.
      + right. apply IHcs.
        ** simpl in H. intros. apply H. apply in_or_app. right. assumption.
        ** assumption.
Qed. *)

Proposition var_not_in_neq (var s : Var):
  ~(In var (variables (EVar s))) ->
  s <> var.
Proof.
  intros. unfold not in *. intro. apply H. rewrite H0. simpl. left. reflexivity.
Qed.

Proposition var_neq_not_in (var s : Var) :
  s <> var -> 
  ~(In var (variables (EVar s))).
Proof.
  intros. unfold not in *. intro. destruct (string_dec s var).
  * exact (H e).
  * apply H. inversion H0.
    - assumption.
    - inversion H1.
Qed.

Proposition irrelevant_append env s t var val:
  s <> var ->
  get_value env (inl s) = t <->
  get_value (append_vars_to_env [var] [val] env) (inl s) = t.
Proof.
  intros; split; intro.
  * simpl. induction env.
    - simpl in *. subst. apply eqb_neq in H. rewrite H. reflexivity.
    - destruct a. assert (get_value ((s0, v) :: env) (inl s) = t). { auto. } unfold get_value in H0. case_eq (uequal (inl s) s0).
      + intro. rewrite H2 in H0. subst. inversion H2. destruct s0.
        ** apply eqb_eq in H3. subst. simpl. apply eqb_neq in H. rewrite H. simpl. rewrite eqb_refl. reflexivity.
        ** inversion H3.
      + intros. simpl in H1. destruct s0.
        ** inversion H2. rewrite H4 in H1. simpl. destruct ((v0 =? var)%string).
          ++ simpl. apply eqb_neq in H. rewrite H. assumption.
          ++ simpl. rewrite H4. apply eqb_neq in H. simpl. exact (IHenv H1).
        ** simpl. exact (IHenv H1).
  * simpl in H0. induction env.
    - simpl in H0. apply eqb_neq in H. rewrite H in H0. subst. simpl. reflexivity.
    - destruct a. simpl in *. case_eq (uequal s0 (inl var)).
      + intro. destruct s0.
        ** inversion H1. apply eqb_eq in H3. rewrite H3. apply eqb_neq in H. rewrite H. rewrite H1 in H0. simpl in H0. rewrite H in H0. assumption.
        **  rewrite H1 in H0. simpl in H0. apply eqb_neq in H. rewrite H in H0. assumption.
      + intro. destruct s0.
        ** inversion H1. case_eq ((s =? v0)%string); intro.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. assumption.
          -- rewrite H1 in H0. simpl in H0. rewrite H2 in H0. exact (IHenv H0).
        ** rewrite H1 in H0. simpl in H0. exact (IHenv H0).
Qed.

Proposition irrelevant_append_eq env s var val:
  s <> var ->
  get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s).
Proof.
  intros. pose (IRA := irrelevant_append env s (get_value env (inl s)) var val H). assert (get_value env (inl s) = get_value env (inl s)). reflexivity. inversion IRA. pose (P1 := H1 H0). apply eq_sym. assumption.
Qed.

(* Theorem variable_irrelevancy (env: Environment) (cl : Closures) (e : Expression) (t val : Value) (var : Var) :
  ~(In var (variables e)) -> (forall env' a b, t <> VClosure env' a b) ->
  |env, cl, e| -e> t <->
  |append_vars_to_env [var] [val] env, cl, e| -e> t.
Proof.
  intro. split; intro. 
  * induction H1 using eval_expr_ind_extended.
    - apply eval_lit.
    - assert (get_value env (inl s) = get_value (append_vars_to_env [var] [val] env) (inl s)). { apply (var_not_in_neq) in H. pose (irrelevant_append_eq env s var val H). assumption. } rewrite H1. apply eval_var.
    - admit.
    - pose (H0 (inl env) vl e).  unfold not in n. assert (VClosure (inl env) vl e = VClosure (inl env) vl e). reflexivity. pose (n H1). inversion f.
    - apply eval_tuple.
      + assumption.
      + intros. apply H3; try(assumption).
        ** simpl in H. apply (list_variables_not_in) with (exps := exps). assumption. apply in_combine_l in H4. assumption.
        ** intros.
Qed.*)

Proposition get_value_here env var val:
get_value (insert_value env var val) var = inl val.
Proof.
  induction env.
  * simpl. rewrite uequal_refl. reflexivity.
  * simpl. destruct a. case_eq (uequal s var); intro.
    - simpl. rewrite uequal_refl. reflexivity.
    - simpl. rewrite uequal_sym, H. assumption.
Qed.

Proposition get_value_there env var var' val:
var <> var' ->
get_value (insert_value env var val) var' = get_value env var'.
Proof.
  intro. induction env.
  * simpl. apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. reflexivity.
  * simpl. destruct a. case_eq (uequal s var); intro.
    - apply uequal_eq in H0. assert (var <> var'). auto. rewrite <- H0 in H. apply uequal_neq in H. rewrite uequal_sym in H. rewrite H. simpl. apply uequal_neq in H1. rewrite uequal_sym in H1. rewrite H1. reflexivity.
    - simpl. case_eq (uequal var' s); intros.
      + reflexivity.
      + apply IHenv.
Qed.

End Core_Erlang_Proofs.