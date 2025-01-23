(**
  This file show a general property about the evaluation of list transformation.
*)
From CoreErlang.BigStep Require Import SemanticsProofs
                                       Tactics.

Import ListNotations.

(* TODO: move these *)
Fixpoint mk_exp_cons (l : list Expression) : Expression :=
match l with
| [] => ENil
| e :: es => ECons e (mk_exp_cons es)
end.

Fixpoint mk_val_cons (l : list Value) : Value :=
match l with
| [] => VNil
| e :: es => VCons e (mk_val_cons es)
end.

Lemma match_value_bind_pattern_var :
  forall x v,
    match_value_bind_pattern v (PVar x) = [(x, v)].
Proof.
  intros. destruct v; reflexivity.
Qed.

Section seq_map_eval.
Context {l : list Expression}
        {f : Value -> Value}
        {f_body : Expression}
        {f_var : Var}
        {modules : list ErlModule}
        {own_module : string}
        {vs : list Value}.

(* This hypothesis could be enough for values in vs, not for necessarily all values *)
Hypothesis f_simulates :
  forall i id eff Γ, i < length vs ->
    | insert_value Γ (inl f_var) (nth i vs VNil), modules, own_module, id, f_body, eff | -e> | id, inl [f (nth i vs VNil)] , eff |.
Hypothesis param_eval :
  forall i env id eff, i < length l ->
    | env, modules, own_module, id, nth i l ENil, eff | -e> |id, inl [nth i vs VNil], eff|.
Hypothesis length_eq : length l = length vs.

Local Definition L : Var := "L"%string.
Local Definition F : Var := "F"%string.
Local Definition H : Var := "H"%string.
Local Definition T : Var := "T"%string.

Definition map_body : Expression :=
  ECase (EVar L) [
      ([PNil], ELit (Atom "true"%string), ENil);
      ([PCons (PVar H) (PVar T)], ELit (Atom "true"%string), ECons (EApp (EVar F) [EVar H])
                                        (EApp (EFunId ("map"%string, 2)) [EVar F;EVar T])
      )
    ].

Definition map_exp : Expression :=
  ELetRec [(("map"%string, 2), ([F; L], map_body))] (EApp (EFunId ("map"%string, 2)) [EFun [f_var] f_body; mk_exp_cons l]).

Theorem map_correct :
  | [], modules, own_module, 0, map_exp, [] | -e> | 2, inl [mk_val_cons (map f vs)], []|.
Proof.
  apply eval_letrec. (* cbn. *)
  cbn. unfold insert_value.
  (* remember (VClos _ _ _ _ _) as map_clos. *)
  remember [(_, _)] as Γ.
  eapply eval_app with (vals := [VClos Γ [] 1 [f_var] f_body; mk_val_cons vs])
                       (eff := [[]; []])
                       (ids := [2; 2]).
  all: simpl; try reflexivity.
  * subst Γ. solve.
  * reflexivity.
  * intros. destruct i. 2: destruct i. 3: lia.
    subst Γ. cbn. solve.
    cbn.
    { (* separate thm *)
      clear-param_eval length_eq. revert vs param_eval length_eq. induction l; simpl; intros.
      * apply eq_sym, length_zero_iff_nil in length_eq. subst. solve.
      * pose proof (param_eval 0 Γ 2 [] ltac:(lia)) as Ha0. simpl in Ha0.
        destruct vs. inversion length_eq. simpl in *.
        epose proof (IHl0 l1 _ ltac:(lia)) as Rest. clear IHl0.
        Unshelve. 2: {
          intros. apply (param_eval (S i)). lia.
        }
        clear -Ha0 Rest.
        eapply eval_cons. exact Rest. exact Ha0.
    }
  * cbn.
    { (* separate thm *)
      clear param_eval length_eq l. subst Γ. induction vs.
      * simpl. eapply eval_case with (i := 0) (vals := [VNil]);
                  simpl; try lia; try reflexivity; solve.
      * epose proof (IHl _) as Rest.
        Unshelve. 2: {
          intros. apply (f_simulates (S i)). simpl. lia.
        }
        clear IHl.
        simpl.
        eapply eval_case with (i := 1) (vals := [VCons a (mk_val_cons l)]); simpl; try lia.
        2: {
          destruct a, l; reflexivity.
        }
        - solve.
        - destruct j. 2: lia. intros. inversion H1.
        - solve.
        - repeat rewrite match_value_bind_pattern_var. simpl.
          eapply eval_cons.
          + 
            eapply eval_app with (vals := [VClos
      [(inr ("map"%string, 2),
        VClos [] [(0, ("map"%string, 2), ([F; L], map_body))] 0 [
          F; L] map_body)] [] 1 [f_var] f_body; mk_val_cons l])
                       (eff := [[]; []])
                       (ids := [2; 2]); try reflexivity.
            ** solve.
            ** reflexivity.
            ** simpl. intros. destruct i. 2: destruct i. 3: lia.
               -- simpl. solve.
               -- simpl. solve.
            ** simpl. exact Rest.
          + eapply eval_app with (vals := [a]) (eff := [[]]) (ids := [2]); try reflexivity.
            ** simpl. solve.
            ** reflexivity.
            ** simpl. destruct i. 2: lia. intros. simpl. solve.
            ** simpl.
               (* epose proof (f_simulates 0 2 [] [(inr ("map"%string, 2),
    VClos [] [(0, ("map"%string, 2), ([F; L], map_body))] 0 [F; L] map_body);
   (inl f_var, a)] ltac:(simpl; lia)) as FF. simpl in FF. *)
               epose proof (f_simulates 0 2 [] [(inr ("map"%string, 2),
    VClos [] [(0, ("map"%string, 2), ([F; L], map_body))] 0 [F; L] map_body)] ltac:(simpl; lia)) as FF. simpl in FF.
               unfold get_env. unfold get_env_base. assumption.
    }
Qed.

End seq_map_eval.

Goal
  | [], stdlib, "main"%string, 0, (@map_exp [ELit (Integer 1); ELit (Integer 2)] (ECall (ELit (Atom "erlang"%string)) (ELit (Atom "+"%string)) [EVar "X"%string; ELit (Integer 1)]) "X"%string) , [] | -e> | 2, inl [VCons (VLit (Integer 2)) (VCons (VLit (Integer 3)) VNil) ], [] |.
Proof.
  epose proof (@map_correct [ELit (Integer 1); ELit (Integer 2)]
                 (fun v =>
                   match eval_arith "erlang" "+" [v; VLit (Integer 1)] with
                   | inl [v] => v
                   | _ => VLit (Integer 0)
                   end)
                (ECall (ELit (Atom "erlang"%string)) (ELit (Atom "+"%string)) [EVar "X"%string; ELit (Integer 1)])
                "X"%string stdlib "main"%string
                [VLit (Integer 1); VLit (Integer 2)] _ _ eq_refl).
  now cbn in H0.
Unshelve.
  (* f_simulates *)
  * intros. simpl in *. destruct i. 2: destruct i. 3: lia.
    - simpl.
      eapply eval_call with (vals := [VLit (Integer 1); VLit (Integer 1)]) (eff := [eff; eff]) (ids := [id;id]); try reflexivity.
      + solve.
      + solve.
      + destruct i; simpl. 2: destruct i. 3: lia.
        ** intros. apply eval_var.
           now rewrite get_value_here.
        ** intros. solve.
      + reflexivity.
      + reflexivity.
    - simpl.
      eapply eval_call with (vals := [VLit (Integer 2); VLit (Integer 1)]) (eff := [eff; eff]) (ids := [id;id]); try reflexivity.
      + solve.
      + solve.
      + destruct i; simpl. 2: destruct i. 3: lia.
        ** intros. apply eval_var.
           now rewrite get_value_here.
        ** intros. solve.
      + reflexivity.
      + reflexivity.
  (* param_eval *)
  * intros. simpl in *. destruct i. 2: destruct i. 3: lia.
    - solve.
    - solve.
Qed.
