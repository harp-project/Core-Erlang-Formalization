Require Core_Erlang_Equalities.

From Coq Require Program.Equality.
From Coq Require Classes.EquivDec.


Module Expression_Eq_Dec.

Export Core_Erlang_Equalities.Equalities.

Import Program.Equality.
Import Classes.EquivDec.

Import ListNotations.

Set Implicit Arguments.

Section exp_rect.
  Variable P : Expression -> Type.

      Variable P_list_expr : list Expression -> Type.
      Variable P_list_expr_expr : list (Expression * Expression) -> Type.
      Variable P_list_var_expr : list (Var * Expression) -> Type.
      Variable P_list_expr_var : list (Expression * Var) -> Type.
      Variable P_list_pat_expr_expr : list (list Pattern * Expression * Expression) -> Type.
      Variable P_list_funid_var_expr : list (FunctionIdentifier * ((list Var) * Expression)) -> Type. 
      
      
      Hypothesis P_list_expr_nil : P_list_expr [].
      Hypothesis P_list_expr_cons : forall e l, P e -> P_list_expr l -> P_list_expr (e :: l).
      
      Hypothesis P_list_expr_expr_nil : P_list_expr_expr [].
      Hypothesis P_list_expr_expr_cons : forall e1 e2 l, P e1 -> P e2 -> P_list_expr_expr l -> P_list_expr_expr ((e1, e2) :: l).
      
      Hypothesis P_list_var_expr_nil : P_list_var_expr [].
      Hypothesis P_list_var_expr_cons : forall v e l, P e -> P_list_var_expr l -> P_list_var_expr ((v,e) :: l).
      
      Hypothesis P_list_expr_var_nil : P_list_expr_var [].
      Hypothesis P_list_expr_var_cons : forall v e l, P e -> P_list_expr_var l -> P_list_expr_var ((e, v) :: l).
      
      Hypothesis P_list_pat_expr_expr_nil : P_list_pat_expr_expr [].
      Hypothesis P_list_pat_expr_expr_cons : forall (p : list Pattern) e1 e2 l, P e1 -> P e2 -> P_list_pat_expr_expr l -> P_list_pat_expr_expr ((p, e1, e2) :: l).
      
      Hypothesis P_list_funid_var_expr_nil : P_list_funid_var_expr [].
      Hypothesis P_list_funid_var_expr_cons : forall f vl e l, P e -> P_list_funid_var_expr l -> P_list_funid_var_expr ((f,(vl,e)) :: l).
      
      Hypothesis P_empty_list : P ENil.
      Hypothesis P_literal : forall l, P (ELit l).
      Hypothesis P_var : forall v, P (EVar v).
      Hypothesis P_funid : forall f, P (EFunId f).
      Hypothesis P_fun : forall vl e, P e -> P (EFun vl e).
      Hypothesis P_list : forall e1 e2, P e1 -> P e2 -> P (ECons e1 e2).
      Hypothesis P_tuple : forall l, P_list_expr l -> P (ETuple l).
      Hypothesis P_call : forall f l, P_list_expr l -> P (ECall f l).
      Hypothesis P_apply : forall exp l, P exp -> P_list_expr l -> P (EApp exp l).
      Hypothesis P_case : forall el l, P_list_expr el -> P_list_pat_expr_expr l -> P (ECase el l).
      
      Hypothesis P_let : forall e l, P e -> P_list_var_expr l -> P (ELet l e).
      Hypothesis P_seq : forall e1 e2, P e1 -> P e2 -> P (ESeq e1 e2).
      
      Hypothesis P_letrec : forall l e, P e -> P_list_funid_var_expr l ->  P (ELetRec l e).
      
      Hypothesis P_map : forall l, P_list_expr_expr l -> P (EMap l).
      Hypothesis P_try : forall el e1 e2 vex1 vex2 vex3, P_list_expr_var el -> P e1 -> P e2 -> P (ETry el e1 e2 vex1 vex2 vex3).
      
     (*  Hypothesis P_map : forall l, P (EMap l). *)
      
   (*    Hypothesis P_arr : forall l, P_list l -> P (Arr l). *)
   (*    Hypothesis P_obj : forall l, P_list' l -> P (Obj l). *)

      Fixpoint expr_rect (e : Expression) : P e :=
        let fix go_list_tuple (l : list Expression) : P_list_expr l :=
            match l with
            | [] => P_list_expr_nil
            | e :: l => P_list_expr_cons (expr_rect e) (go_list_tuple l)
            end in
        let fix go_list_case (l : list (list Pattern * Expression * Expression)) : P_list_pat_expr_expr l :=
            match l with
            | [] => P_list_pat_expr_expr_nil
            | (p,e1,e2) :: l => P_list_pat_expr_expr_cons p (expr_rect e1) (expr_rect e2) (go_list_case l)
            end in
        let fix go_list_let (l : list (Var * Expression)) : P_list_var_expr l :=
            match l with
            | [] => P_list_var_expr_nil
            | (v,e) :: l => P_list_var_expr_cons v (expr_rect e) (go_list_let l)
            end in
        let fix go_list_try (l : list (Expression * Var)) : P_list_expr_var l :=
            match l with
            | [] => P_list_expr_var_nil
            | (e, v) :: l => P_list_expr_var_cons v (expr_rect e) (go_list_try l)
            end in
        let fix go_list_letrec ( l : list (FunctionIdentifier * ((list Var) * Expression))) : P_list_funid_var_expr l :=
            match l with
            | [] => P_list_funid_var_expr_nil
            | (f,(vl,e)) :: l => P_list_funid_var_expr_cons f vl (expr_rect e) (go_list_letrec l)
            end in
        let fix go_list_map (l : list (Expression * Expression)) : P_list_expr_expr l :=
            match l with
            | [] => P_list_expr_expr_nil
            | (e,e0) :: l => P_list_expr_expr_cons (expr_rect e) (expr_rect e0) (go_list_map l)
            end in
        match e with
        | ENil => P_empty_list
        | ELit l => P_literal l
        | EVar v => P_var v
        | EFunId f => P_funid f
        | EFun vl e => P_fun vl (expr_rect e)
        | ECons e1 e2 => P_list (expr_rect e1) (expr_rect e2)
        | ETuple l => P_tuple (go_list_tuple l)
        | ECall f l => P_call f (go_list_tuple l)
        | EApp exp l => P_apply (expr_rect exp) (go_list_tuple l)
        | ECase el l => P_case (go_list_tuple el) (go_list_case l)
        | ELet l e => P_let (expr_rect e) (go_list_let l)
        | ESeq e1 e2 => P_seq (expr_rect e1) (expr_rect e2)
        | ELetRec l e => P_letrec (expr_rect e) (go_list_letrec l)
        | EMap l => P_map (go_list_map l)
        | ETry el e1 e2 vex1 vex2 vex3 => P_try vex1 vex2 vex3 (go_list_try el) (expr_rect e1) (expr_rect e2)
        end.
End exp_rect.

Section expr_ind.
  Axiom expr_ind_ext: 
    forall
         P : Expression -> Prop,
       P ENil ->
       (forall l : Literal, P (ELit l)) ->
       (forall v : Var, P (EVar v)) ->
       (forall f2 : FunctionIdentifier,
        P (EFunId f2)) ->
       (forall (vl : list Var) (e : Expression),
        P e -> P (EFun vl e)) ->
       (forall hd : Expression,
        P hd ->
        forall tl : Expression,
        P tl -> P (ECons hd tl)) ->
       (forall 
          l : list Expression,
       (forall i, i < length l -> P (nth i l ENil)) -> P (ETuple l)) ->
       (forall (f : string)
          (l : list Expression),
       (forall i, i < length l -> P (nth i l ENil)) -> P (ECall f l)) ->
       (forall (exp : Expression) 
          (l : list Expression),
       (forall i, i < length l -> P (nth i l ENil)) -> P exp -> P (EApp exp l)) ->
       (forall el : list Expression,
        forall
          l : list (list Pattern * Expression * Expression),
          (forall i,  i < length el -> P (nth i el ENil)) ->
          (forall i, i < length l -> P (nth i (snd (split (fst (split l)))) ENil)) -> 
          
          (forall i, i < length l -> P (nth i (snd (split l)) ENil)) ->
        P (ECase el l)) ->
       (forall (l : list (Var * Expression))
          (e : Expression), (forall i, i < length l -> P (nth i (snd (split l)) ENil)) -> P e -> P (ELet l e)) ->
       (
        forall e1 : Expression,
        P e1 ->
        forall e2 : Expression,
        P e2 -> P (ESeq e1 e2)
       ) ->
       (forall
          (l : list
                 (FunctionIdentifier *
                  (list Var * Expression)))
          (e : Expression), (forall i, i < length l -> P (nth i (snd (split (snd (split l)))) ENil)) ->
        P e -> P (ELetRec l e)) ->
       (forall
          l : list
                (Expression *
                 Expression),
        (forall i, i < length l -> P (nth i (fst (split l)) ENil))  -> (forall i, i < length l -> P (nth i (snd (split l)) ENil)) -> P (EMap l)) ->
        (forall el : list (Expression * Var),
        (forall i, i < length el -> P (nth i (fst (split el)) ENil)) ->
        forall e1 : Expression,
        P e1 ->
        forall e2 : Expression,
        P e2 ->
        forall (vl : list Var) (vex1 vex2 vex3 : Var),
        P (ETry el e1 e2 vex1 vex2 vex3)) ->
       forall e : Expression,
       P e.
End expr_ind.

Definition funid_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec.
Definition list_var_eq_dec := list_eq_dec string_dec.

Lemma list_expr_expr_eq_dec: forall l l0 : list (Expression * Expression), 
  (forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (fst (split l)) ENil = e' \/
    nth i (fst (split l)) ENil <> e') ->
  (forall i : nat,
     i < Datatypes.length l ->
     forall e' : Expression,
     nth i (snd (split l)) ENil = e' \/
     nth i (snd (split l)) ENil <> e')
      -> l = l0 \/ l <> l0 .
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in H, H0. pose (H_0th := H 0 (Nat.lt_0_succ _)). pose (H0_0th := H0 0 (Nat.lt_0_succ _)). simpl in H_0th, H0_0th. destruct a, (split l). simpl in H_0th, H0_0th. destruct p. pose (H_0th' := H_0th e4). pose (H0_0th' := H0_0th e5). destruct H_0th', H0_0th'; try(right; congruence).
  assert(l = l0 \/ l <> l0). {eapply IHl; intros. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H (S i) H4 e'). simpl in P. simpl. assumption. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H0 (S i) H4 e'). simpl in P. simpl. assumption. } destruct H3.
  * left. now subst.
  * right. congruence.
Qed.

Lemma list_expr_eq_dec: forall l l0 : list Expression,
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i l ENil = e' \/ nth i l ENil <> e' ) ->
    l = l0 \/ l <> l0.
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  remember H as H'. simpl in H. pose (H_0th := H 0 (Nat.lt_0_succ _)). simpl in H_0th. pose (H_0th' := H_0th e). destruct H_0th'.
    * assert(l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < Datatypes.length (a :: l)). { simpl. omega. } pose (P := H' (S i) H2 e'). simpl in P. assumption. } destruct H1.
      - left. now subst.
      - right. congruence.
    * right. congruence.
Qed.

Lemma list_var_expr_eq_dec: forall l l0 : list (Var * Expression),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (snd (split l)) ENil = e' \/
    nth i (snd (split l)) ENil <> e')
     -> l = l0 \/ l <> l0.
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in *. pose (H_0th := H 0 (Nat.lt_0_succ _)). destruct a, (split l). simpl in H_0th. destruct p. pose (H_0th' := H_0th e0). destruct H_0th', (string_dec v v0); try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < S(Datatypes.length (l))). { omega. } pose (P := H (S i) H2 e'). simpl in P. assumption. } destruct H1.
    * left. now subst.
    * right. congruence.
Qed.

Lemma list_expr_var_eq_dec: forall l l0 : list (Expression * Var),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (fst (split l)) ENil = e' \/
    nth i (fst (split l)) ENil <> e')
     -> l = l0 \/ l <> l0.
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in *. pose (H_0th := H 0 (Nat.lt_0_succ _)). destruct a, (split l). simpl in H_0th. destruct p. pose (H_0th' := H_0th e0). destruct H_0th', (string_dec v v0); try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < S(Datatypes.length (l))). { omega. } pose (P := H (S i) H2 e'). simpl in P. assumption. } destruct H1.
    * left. now subst.
    * right. congruence.
Qed.

Lemma list_pat_expr_expr_eq_dec : forall l l0 : list (list Pattern * Expression * Expression),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (snd (split (fst (split l)))) ENil = e' \/
    nth i (snd (split (fst (split l)))) ENil <>
    e') -> 
(forall i : nat,
     i < Datatypes.length l ->
     forall e' : Expression,
     nth i (snd (split l)) ENil = e' \/
     nth i (snd (split l)) ENil <> e') 
-> l = l0 \/ l <> l0. 
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in H,H0. pose (H_0th := H 0 (Nat.lt_0_succ _)). pose (H0_0th := H0 0 (Nat.lt_0_succ _)). simpl in H_0th,H0_0th. destruct a, (split l). simpl in H_0th,H0_0th. destruct p. simpl in *. destruct p0, (split l1). simpl in H_0th,H0_0th. destruct p.  pose (H_0th' := H_0th e5). pose (H0_0th' := H0_0th e0). destruct H_0th', H0_0th'; try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl; intros. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H (S i) H4 e'). simpl in P. assumption. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H0 (S i) H4 e'). simpl in P. assumption. } destruct H3.
  * destruct (list_eq_dec (Pattern_eq_dec) l3 l6).
    - left. now subst.
    - right. congruence.
  * right. congruence.
Qed.

Lemma list_funid_listvar_expr_eq_dec : forall l l0 : list (FunctionIdentifier * ((list Var) * Expression)),
(forall i : nat,
    i < Datatypes.length l ->
    forall e' : Expression,
    nth i (snd (split (snd (split l))))
      ENil = e' \/
    nth i (snd (split (snd (split l))))
      ENil <> e')
-> l = l0 \/ l <> l0. 
Proof.
  intros.
  dependent induction l; destruct l0; try(auto; now right).
  simpl in H. pose (H_0th := H 0 (Nat.lt_0_succ _)). simpl in H_0th. destruct a, (split l). simpl in *. destruct p0, (split l2). simpl in H_0th. destruct p. destruct p. pose (H_0th' := H_0th e0). destruct H_0th', (funid_eq_dec f f0),(list_var_eq_dec l3 l6); try(right; congruence).
  assert (l = l0 \/ l <> l0). { eapply IHl. intros. assert (S i < S (Datatypes.length l)). { omega. } pose (P := H (S i) H2 e'). simpl in P. assumption. } destruct H1.
  * left. now subst.
  * right. congruence.
Qed.

Lemma Expression_eq_dec_with_axiom : forall e e' : Expression, e = e' \/ e <> e'.
Proof using.
  intros.
  dependent induction e using expr_ind_ext; destruct e'; try(right; congruence).
  * left. reflexivity.
  * destruct (Literal_eq_dec l l0).
    - left. now subst.
    - right. congruence.
  * destruct (string_dec v v0).
    - left. now subst.
    - right. congruence.
  * destruct (funid_eq_dec f f2).
    - left. now subst.
    - right. congruence.
  * destruct (IHe e'), (list_var_eq_dec vl vl0); try(right;congruence).
    - left. now subst.
  * destruct (IHe1 e'1), (IHe2 e'2); try(right;congruence).
    - left. now subst.
  * destruct (list_expr_eq_dec l l0 H).
    - rewrite H0. auto.
    - right. congruence.
  * destruct (list_expr_eq_dec l l0 H).
    - rewrite H0. destruct (string_dec f f0).
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (list_expr_eq_dec l l0 H).
    - rewrite H0. destruct (IHe e').
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (list_expr_eq_dec el el0 H).
    - destruct (list_pat_expr_expr_eq_dec l l0 H0 H1).
      + subst. auto.
      + right. congruence.
    - right. congruence.
  * destruct (list_var_expr_eq_dec l l0 H).
    - rewrite H0. destruct (IHe e').
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (IHe1 e'1), (IHe2 e'2); try(right;congruence).
    - left. now subst.
  * destruct (list_funid_listvar_expr_eq_dec l l0 H).
    - destruct (IHe e').
      + left. now subst.
      + right. congruence.
    - right. congruence.
  * destruct (list_expr_expr_eq_dec l l0 H H0).
    - rewrite H1. auto.
    - right. congruence.
  * destruct (IHe1 e'1), (IHe2 e'2), (string_dec vex1 vex0), (string_dec vex2 vex4), (string_dec vex3 vex5); try(right;congruence).
    subst. destruct (list_expr_var_eq_dec el el0).
    - intros. apply H. assumption.
    - subst. left. reflexivity.
    - right. congruence.
Qed.

Fixpoint Expression_eq_dec (e1 e2 : Expression) : {e1 = e2} + {e1 <> e2}.
Proof.
  set (var_eq_dec := string_dec).
  set (literal_eq_dec := Literal_eq_dec).
  set (pattern_eq_dec := Pattern_eq_dec).
  set (explist_eq_dec := list_eq_dec Expression_eq_dec).
  set (varlist_eq_dec := list_eq_dec string_dec).  (* for function signatures: *)
  set (funsig_eq_dec := prod_eq_dec string nat string_dec Nat.eq_dec).  set (patlist_eq_dec := list_eq_dec pattern_eq_dec).
  (* for letrec *)
  set (listvarexp_eq_dec := list_eq_dec (prod_eqdec (list_eq_dec string_dec) Expression_eq_dec)).
    (* for fnames *)
  set (listfunsig_eq_dec := list_eq_dec funsig_eq_dec).
  set (listlistvar_eq_dec := list_eq_dec (list_eq_dec string_dec)).
  set (list_eq_dec (prod_eqdec (prod_eqdec (list_eq_dec Pattern_eq_dec) Expression_eq_dec) Expression_eq_dec)).
  set (list_eq_dec (prod_eqdec string_dec Expression_eq_dec)).
  set (list_eq_dec (prod_eqdec funsig_eq_dec (prod_eqdec (list_eq_dec string_dec) Expression_eq_dec))).
  set (list_eq_dec (prod_eqdec Expression_eq_dec Expression_eq_dec)).
  set (list_eq_dec (prod_eqdec Expression_eq_dec string_dec)).
  decide equality.
Defined.

End Expression_Eq_Dec.