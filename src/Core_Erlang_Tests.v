Require Core_Erlang_Semantics.

Module Tests.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Omega.

Import Core_Erlang_Syntax.Syntax.
Import Core_Erlang_Environment.Environment.
Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Helpers.Helpers.
Import Core_Erlang_Side_Effects.Side_Effects.

(** This is an edless recursion *)
Example eval_letrec1 : 
  |[], 0, ELetRec [(("x"%string, 1), (["X"%string], EApp (EFunId ("x"%string, 1)) [EVar "X"%string])) ]
            (EApp (EFunId ("x"%string, 1)) [EEmptyTuple]), []|
-e> 
  |1, inl ErrorValue, []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := [VEmptyTuple]) 
                                  (body := (EApp (EFunId ("x"%string, 1)) [EVar "X"%string])) (n := 0)
                                  (ids := [1])
                                  (var_list := ["X"%string]) 
                                  (ref := [])
                                  (ext := [(0, ("x"%string, 1), 
                                        (["X"%string], EApp (EFunId ("x"%string, 1)) [EVar "X"%string]))]) 
                                  (eff := [[]]); try (reflexivity).
    - unfold append_funs_to_env. simpl. eapply eval_funid.
    - intros. inversion H.
      + unfold append_funs_to_env, EEmptyTuple. simpl. eapply eval_tuple with (eff := []) (vals := [])
                      (ids := []); try(reflexivity). 
        ** intros. inversion H0.
      + inversion H1.
    - simpl. reflexivity.
    - eapply eval_apply with (vals := [VEmptyTuple]) 
                             (body := (EApp (EFunId ("x"%string, 1)) [EVar "X"%string])) 
                             (var_list := ["X"%string]) 
                             (ref := []) (ids := [1])
                             (ext := [(0, ("x"%string, 1),
                                     (["X"%string], EApp (EFunId ("x"%string, 1)) [EVar "X"%string]))]) (n := 0)
                             (eff := [[]]); try (reflexivity).
    + apply eval_funid.
    + intros. inversion H.
      ** apply eval_var.
      ** inversion H1.
    + simpl. reflexivity.
    + eapply eval_apply with (vals := [VEmptyTuple]) 
                             (body := (EApp (EFunId ("x"%string, 1)) [EVar "X"%string])) (n := 0)
                             (var_list := ["X"%string]) 
                             (ref := []) (ids := [1])
                             (ext := [(1, ("x"%string, 1), 
                                     (["X"%string], EApp (EFunId ("x"%string, 1)) [EVar "X"%string]))]) 
                             (eff := [[]]); try (reflexivity).
Admitted.

(* This is not accepted by the compiler in Core Erlang *)
Example eval_letrec2 : 
  |[], 0, ELet [("F"%string, EFun ["X"%string] 
         (EApp (EVar "F"%string) [EVar "X"%string]))] 
            (EApp (EVar "F"%string) [EEmptyTuple]), []| 
-e>
|1, inr novar, []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 ["X"%string] (EApp (EVar "F"%string) [EVar "X"%string])]) 
                       (ids := [1])
                       (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := [VEmptyTuple]) (n := 0)
                                  (var_list := ["X"%string]) (ids := [1])
                                  (body := (EApp (EVar "F"%string) [EVar "X"%string])) 
                                  (ref := []) (ext := []) (eff := [[]]); try(reflexivity).
    - apply eval_var.
    - intros. inversion H.
      + eapply eval_tuple with (eff := []) (ids := []); try(reflexivity).
        ** intros. inversion H0.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_apply_ex_closure_ex.
      + reflexivity.
      + apply eval_var.
Qed.

(* Top level functions, and their closures must be added initially *)
Example multiple_top_level_funs : |[(inr ("fun1"%string, 0), VClos [] [
    (0, ("fun1"%string, 0), ([], (EApp (EFunId ("fun3"%string, 0)) [])));
    (1, ("fun2"%string, 0), ([], (ELit (Integer 42))));
    (2, ("fun3"%string, 0), ([], (EApp (EFunId ("fun2"%string, 0)) [])))
  ] 0 [] (EApp (EFunId ("fun3"%string, 0)) [])) ; 
                                      (inr ("fun2"%string, 0), VClos [] [
    (0, ("fun1"%string, 0), ([], (EApp (EFunId ("fun3"%string, 0)) [])));
    (1, ("fun2"%string, 0), ([], (ELit (Integer 42))));
    (2, ("fun3"%string, 0), ([], (EApp (EFunId ("fun2"%string, 0)) [])))
  ] 1 [] (ELit (Integer 42))) ;
                                      (inr ("fun3"%string, 0), VClos [] [
    (0, ("fun1"%string, 0), ([], (EApp (EFunId ("fun3"%string, 0)) [])));
    (1, ("fun2"%string, 0), ([], (ELit (Integer 42))));
    (2, ("fun3"%string, 0), ([], (EApp (EFunId ("fun2"%string, 0)) [])))
  ] 2 [] (EApp (EFunId ("fun2"%string, 0)) []))], 3
                                      , EApp (EFunId ("fun1"%string,0)) [], []| 
-e> 
  |3, inl (VLit (Integer 42)), []|.
Proof.
  remember [
  (0, ("fun1"%string, 0), ([], (EApp (EFunId ("fun3"%string, 0)) [])));
  (1, ("fun2"%string, 0), ([], (ELit (Integer 42))));
  (2, ("fun3"%string, 0), ([], (EApp (EFunId ("fun2"%string, 0)) [])))
] as ext.
  eapply eval_apply with (vals := []) (ref := []) (ext := ext) (eff := [])
                         (body := (EApp (EFunId ("fun3"%string, 0)) [])) 
                         (var_list := []) (n := 0) (ids := []); auto.
  * apply eval_funid.
  * simpl. intros. inversion H.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (n := 2) (ref := []) (ext := ext) (eff := [])
                                 (body := (EApp (EFunId ("fun2"%string, 0)) [])) 
                                 (var_list := []) (ids := []); auto.
    - rewrite Heqext. simpl. apply eval_funid.
    - intros. inversion H.
    - simpl. reflexivity.
    - simpl. eapply eval_apply with (vals := []) (n := 1) (ref := []) (ext := ext) (eff := [])
                                    (body := (ELit (Integer 42))) (var_list := []) (ids := []); auto.
      + rewrite Heqext. apply eval_funid.
      + intros. inversion H.
      + reflexivity.
      + apply eval_lit.
Qed.

Example multiple_top_level_funs2 :
  | [], 0, ELetRec [(("fun1"%string,0), ([], EApp (EFunId ("fun3"%string, 0)) [])); 
                    (("fun2"%string,0), ([], ELit (Integer 42))); 
                    (("fun3"%string,0), ([], EApp (EFunId ("fun2"%string, 0)) []))]
     (EApp (EFunId ("fun1"%string,0)) []), [] |
-e>
  |3, inl (VLit (Integer 42)), []|.
Proof.
  eapply eval_letrec; try(reflexivity).
  unfold append_funs_to_env. simpl.
  (*remember [
     (2, ("fun3"%string, 0), ([], EApp (EFunId ("fun2"%string, 0)) []));
     (1, ("fun2"%string, 0), ([], ELit (Integer 42)));
     (0, ("fun1"%string, 0), ([], EApp (EFunId ("fun3"%string, 0)) []))
  ] as ext.*)
  eapply eval_apply with (vals := []) (ref := []) 
                         (ext := [
     (2, ("fun3"%string, 0), ([], EApp (EFunId ("fun2"%string, 0)) []));
     (1, ("fun2"%string, 0), ([], ELit (Integer 42)));
     (0, ("fun1"%string, 0), ([], EApp (EFunId ("fun3"%string, 0)) []))
  ])
                         (eff := [])
                         (body := (EApp (EFunId ("fun3"%string, 0)) [])) 
                         (var_list := []) (n := 0) (ids := []); auto.
  * apply eval_funid.
  * simpl. intros. inversion H.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (n := 2) (ref := []) 
                                  (ext := [
     (2, ("fun3"%string, 0), ([], EApp (EFunId ("fun2"%string, 0)) []));
     (1, ("fun2"%string, 0), ([], ELit (Integer 42)));
     (0, ("fun1"%string, 0), ([], EApp (EFunId ("fun3"%string, 0)) []))
  ]) 
                                 (eff := [])
                                 (body := (EApp (EFunId ("fun2"%string, 0)) [])) 
                                 (var_list := []) (ids := []); auto.
    - simpl. apply eval_funid.
    - intros. inversion H.
    - simpl. reflexivity.
    - simpl. eapply eval_apply with (vals := []) (n := 1) (ref := [])
                                    (ext := [
     (2, ("fun3"%string, 0), ([], EApp (EFunId ("fun2"%string, 0)) []));
     (1, ("fun2"%string, 0), ([], ELit (Integer 42)));
     (0, ("fun1"%string, 0), ([], EApp (EFunId ("fun3"%string, 0)) []))
  ]) 
                                    (eff := [])
                                    (body := (ELit (Integer 42))) (var_list := []) (ids := []); auto.
      + apply eval_funid.
      + intros. inversion H.
      + reflexivity.
      + apply eval_lit.
Qed.

Example weird_apply : |[], 0, ELetRec [(("f"%string, 1), (["X"%string],
   ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]
   ))]
   (ELet [("X"%string, EFun ["F"%string]
       (ELetRec [(("f"%string, 1), (["X"%string], ELit (Integer 0)))] 
          (EApp (EVar "F"%string) [ELit (Integer 2)])
       ))
     ]
    (EApp (EVar "X"%string) [EFunId ("f"%string, 1)])
   ), []|
-e> 
  |3, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_letrec; auto.
  simpl. eapply eval_let with (vals := [
 VClos 
  [(inr ("f"%string, 1),
   VClos []
     [(0, ("f"%string, 1),
      (["X"%string],
      ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))] 0 ["X"%string]
     (ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))
  ]
  [] 1
  ["F"%string]
  (ELetRec [(("f"%string, 1), (["X"%string], ELit (Integer 0)))]
        (EApp (EVar "F"%string) [ELit (Integer 2)]))
 ]
  ) (eff := [[]]) (ids := [2]); auto.
  * intros. inversion H; inversion H1. unfold append_funs_to_env. simpl. apply eval_fun.
  * simpl. eapply eval_apply with (var_list := ["F"%string]) (n := 1) (eff := [[]]) (ids := [2])
  (vals := [VClos []
     [(0, ("f"%string, 1),
      (["X"%string],
      ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))] 0 ["X"%string]
     (ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])])])
  (body := (ELetRec [(("f"%string, 1), (["X"%string], ELit (Integer 0)))]
       (EApp (EVar "F"%string) [ELit (Integer 2)])))
  (ext := [])
  (ref := [(inr ("f"%string, 1),
     VClos []
       [(0, ("f"%string, 1),
        (["X"%string],
        ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"), ELit (Integer 5));
          (PLit (Integer 1), ELit (Atom "true"),
          EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
          (PVar "A"%string, ELit (Atom "true"),
          EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))] 0 ["X"%string]
       (ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"), ELit (Integer 5));
          (PLit (Integer 1), ELit (Atom "true"),
          EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
          (PVar "A"%string, ELit (Atom "true"),
          EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))]); auto.
    - apply eval_var.
    - intros. inversion H; inversion H1. simpl. apply eval_funid.
    - simpl. eapply eval_letrec; auto. simpl.
      eapply eval_apply with (var_list := ["X"%string]) (eff := [[]])
        (vals := [VLit (Integer 2)])
        (ref := []) (n := 0) (ids := [3])
        (body := ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])])
        (ext := [(0, ("f"%string, 1),
     (["X"%string],
     ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))]); auto.
      + apply eval_var.
      + intros. inversion H; inversion H1. apply eval_lit.
      + simpl. eapply eval_case with (i := 2) (v := VLit (Integer 2)); auto.
        ** apply eval_var.
        ** simpl. reflexivity.
        ** intros. inversion H.
          -- subst. inversion H0.
          -- inversion H2.
            ++ subst. inversion H0.
            ++ inversion H4.
        ** simpl. apply eval_lit.
        ** simpl. eapply eval_apply with (var_list := ["X"%string])
                     (eff := [[]]) (n := 0) (ids := [3])
                     (vals := [VLit (Integer 1)])
                     (body := ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])])
                     (ref := [])
                     (ext := [(0, ("f"%string, 1),
                              (["X"%string],
                              ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))]); auto.
         -- apply eval_funid.
         -- intros. inversion H; inversion H1. simpl. apply eval_lit.
         -- simpl. eapply eval_case with (i := 1) (v := VLit (Integer 1)); auto.
           ++ apply eval_var.
           ++ simpl. auto.
           ++ simpl. reflexivity.
           ++ intros. inversion H.
             *** subst. inversion H0.
             *** inversion H2.
           ++ simpl. apply eval_lit.
           ++ eapply eval_apply with (var_list := ["X"%string])
                     (vals := [VLit (Integer 0)])
                     (eff := [[]]) (n := 0) (ids := [3])
                     (body := ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])])
                     (ref := [])
                     (ext := [(0, ("f"%string, 1),
                              (["X"%string],
                              ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]))]); auto.
             *** simpl. apply eval_funid.
             *** intros. inversion H; inversion H1. apply eval_lit.
             *** reflexivity.
             *** simpl. eapply eval_case with (i := 0) (v := VLit (Integer 0)); auto.
               --- apply eval_var.
               --- simpl. auto.
               --- simpl. reflexivity.
               --- intros. inversion H.
               --- simpl. apply eval_lit.
               --- simpl. apply eval_lit.
  * reflexivity.
Qed.

Example top_overwrite : 
  |[(inr ("fun2"%string, 0), 
       VClos [] [(0, ("fun2"%string, 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))], 1,
  ELetRec [(("fun2"%string, 0), ([], ELit (Integer 40)))] 
     (EApp (EFunId ("fun2"%string, 0)) []), [] | 
-e>
  |2, inl (VLit (Integer 40)), []|.
Proof.
  eapply eval_letrec; auto.
  * unfold append_funs_to_env. simpl. eapply eval_apply with (vals := []) (eff := []) (n := 1) (ids := [])
                                  (ref := [(inr ("fun2"%string, 0), VClos [] 
                                                                    [(0, ("fun2"%string, 0), 
                                                                    ([], ELit (Integer 42)))] 0 []
                                                                    (ELit (Integer 42)))]) 
                                  (ext := [(1, ("fun2"%string, 0), ([],  (ELit (Integer 40)) ))]) 
                                  (body := (ELit (Integer 40))) (var_list := []); auto.
    - unfold append_funs_to_env. simpl. apply eval_funid.
    - intros. inversion H.
    - apply eval_lit.
  * reflexivity.
Qed.

Example top_no_overwrite : 
  |[(inr ("fun2"%string, 0), 
     VClos [] [(0, ("fun2"%string, 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)))], 1,
   ELetRec [(("fun2"%string, 1), (["X"%string], (ELit (Integer 40))))] 
     (EApp (EFunId ("fun2"%string, 0)) []), [] |
-e> 
  | 2, inl (VLit (Integer 42)), []|.
Proof.
  eapply eval_letrec; auto.
  * simpl. eapply eval_apply with (vals := []) (n := 0)
                                  (ref := []) (ids := [])
                                  (ext := [(0, ("fun2"%string, 0), ([], ELit (Integer 42)))]) 
                                  (body := ELit (Integer 42)) 
                                  (var_list := [])
                                  (eff := []); auto.
    - apply eval_funid.
    - intros. inversion H.
    - apply eval_lit.
  * reflexivity.
Qed.

(** This is not accepted by the compiler in Core Erlang *)
Example eval_let_func : 
  |[(inl "X"%string, VLit (Integer 42))], 0,
   ELet [("X"%string, EFun [] (ENil)); ("X"%string, EFun [] (EEmptyMap))] 
     (EEmptyMap), []| 
-e> 
  |2, inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [VClos [(inl "X"%string, VLit (Integer 42))] [] 0 [] (ENil); 
                                 VClos [(inl "X"%string, VLit (Integer 42))] [] 1 [] (EEmptyMap)])
                       (eff := [[]; []]) (ids := [1;2]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
      + apply eval_fun.
      + inversion H3.
  * reflexivity.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

Example eval_let_apply : 
  |[(inl "X"%string, VLit (Integer 42))], 0,
   ELet [("Y"%string, EFun [] (EVar "X"%string))] 
     (EApp (EVar "Y"%string) []), []| 
-e> 
  |1, inl (VLit (Integer 42)), []|.
Proof.
  eapply eval_let with (vals := [VClos [(inl "X"%string, VLit (Integer 42))] [] 0 [] 
                                          (EVar "X"%string)])
                       (eff := [[]]) (ids := [1]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (n := 0) (ids := [])
                                  (ref := [(inl "X"%string, VLit (Integer 42))]) 
                                  (ext := []) 
                                  (body := (EVar "X"%string)) 
                                  (var_list := [])
                                  (eff := []); auto.
    - apply eval_var.
    - simpl. intros. inversion H.
    - reflexivity.
    - apply eval_var.
Qed.

Example eval_muliple_let : 
  |[], 0, ELet [("X"%string, ELit (Integer 1))] 
            (ELet [("X"%string, ELit (Integer 2))] 
               (EVar "X"%string)), []| 
-e> 
  |0, inl (VLit (Integer 2)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 1)]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * simpl. reflexivity.
  * eapply eval_let with (vals := [VLit (Integer 2)]) (eff := [[]]) (ids := [0]); auto.
    - simpl. intros. inversion H.
      + apply eval_lit.
      + inversion H1.
    - reflexivity.
    - apply eval_var.
Qed.

Example let_eval_1 : 
  |[], 0, ELet [("X"%string, EEmptyTuple)] (EEmptyMap), []|
-e>
  | 0, inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [VEmptyTuple]) (eff := [[]]) (ids := [0]); auto.
  * intros. simpl in *. inversion H.
    - eapply eval_tuple with (eff := []) (ids := []); auto. intros. inversion H0.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

Example let_eval_2 : 
  |[(inl "X"%string, VEmptyMap)], 0, ELet [("X"%string, EEmptyTuple)] (EEmptyMap), []| 
-e> 
  | 0, inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [VEmptyTuple]) (eff := [[]]) (ids := [0]); auto.
  * intros. simpl in *. inversion H.
    - eapply eval_tuple with (eff := []) (ids := []); auto. intros. inversion H0.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

(** This shouldn't compile in Core Erlang *)
Example eval_let_3 : 
  |[(inl "X"%string, VEmptyMap)], 0,
   ELet [("X"%string, EEmptyTuple); ("X"%string, ENil); ("Y"%string, EVar "X"%string)]
     (EVar "Y"%string), []|
-e>
  |0, inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [(VEmptyTuple) ; (VNil); (VEmptyMap)]) 
                       (eff := [[];[];[]]) (ids := [0;0;0]); auto.
  * simpl. intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_emptylist.
      + inversion H3.
        ** eapply eval_tuple with (eff := []) (ids := []); auto. intros. inversion H4.
        ** inversion H5.
  * reflexivity.
  * simpl. apply eval_var.
Qed.

Example let_eval_4 : 
  |[], 0, ELet [("X"%string, ELit (Integer 5))] (EVar "X"%string), []| 
-e> 
  | 0, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [0]); auto.
  * intros. simpl in *. inversion H.
    - apply eval_lit.
    - inversion H1.
  * reflexivity.
  * simpl. apply eval_var.
Qed.

Example tuple_eval : 
  |[(inl "X"%string, VLit (Atom "foo"%string)); 
    (inl "Y"%string, VEmptyTuple)], 0,
   ETuple [ELit (Integer 5); EVar "X"%string; EVar "Y"%string], []| 
-e>
  |0, inl (VTuple [VLit (Integer 5); VLit (Atom "foo"%string); VEmptyTuple]), []|.
Proof.
  eapply eval_tuple with (eff := [[];[];[]]) (ids := [0;0;0]); auto.
  * intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_var.
      + inversion H3.
        ** apply eval_lit.
        ** inversion H5.
Qed.

Example apply_top_eval : 
  |[(inr ("Plus"%string, 2), 
       VClos [] [(0, ("Plus"%string, 2),
                     (["X"%string ; "Y"%string], ELit (Integer 3)))] 
                0 ["X"%string ; "Y"%string] 
                (ELit (Integer 3)))], 1,
   EApp (EFunId ("Plus"%string, 2)) [ELit (Integer 2); ELit (Integer 3)], []|
-e>
  |1, inl ((VLit (Integer 3))), []|.
Proof.
  eapply eval_apply with (vals := [VLit (Integer 2) ; VLit (Integer 3)])
                         (var_list := ["X"%string; "Y"%string]) 
                         (body := ELit (Integer 3)) 
                         (ref := []) (n := 0) (ids := [1;1])
                         (ext := [(0, ("Plus"%string, 2),
                                   (["X"%string ; "Y"%string], ELit (Integer 3)))])
                         (eff := [[];[]]); auto.
  * apply eval_funid.
  * simpl. intros. inversion H.
    - apply eval_lit.
    - inversion H1.
      + apply eval_lit.
      + inversion H3.
  * reflexivity.
  * simpl. apply eval_lit.
Qed.

Example apply_eval : 
  |[(inl "Minus"%string,
      VClos [] [] 0 ["X"%string; "Y"%string] (ELit (Integer 42))) ; 
    (inl "X"%string, VEmptyMap)], 1,
   EApp (EVar "Minus"%string) [EVar "X"%string; EVar "X"%string], []|
-e>
  |1, inl (VLit (Integer 42)), []|.
Proof.
  eapply eval_apply with (vals := [VEmptyMap; VEmptyMap]) (ids := [1;1])
                         (var_list := ["X"%string; "Y"%string]) 
                         (body := (ELit (Integer 42))) (n := 0)
                         (ref := []) (ext := []) (eff := [[];[]]); auto.
  * apply eval_var.
  * simpl. intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_var.
      + inversion H3.
  * reflexivity.
  * simpl. apply eval_lit.
Qed.


Example list_eval : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   ECons (EVar "X"%string) (ENil), []| 
-e>
  | 0, inl (VCons (VLit (Integer 5)) (VNil)), []|.
Proof.
  eapply eval_list.
  * instantiate (1 := []). rewrite app_nil_r. reflexivity.
  * apply eval_emptylist.
  * apply eval_var.
Qed.

Example list_eval2 : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   ECons (EVar "X"%string) 
         (ECons (EVar "X"%string) 
                (ENil)), []| 
-e> 
  |0, inl (VCons (VLit (Integer 5)) 
                 (VCons (VLit (Integer 5)) 
                        (VNil))), []|.
Proof.
  eapply eval_list with (eff2 := []).
  * reflexivity.
  * eapply eval_list with (eff2 := []).
    - reflexivity.
    - apply eval_emptylist.
    - apply eval_var.
  * apply eval_var.
Qed.

Example let_eval_overwrite : 
  |[], 0, ELet [("X"%string, EFun [] (EEmptyTuple))] 
           (ELet [("X"%string, ELit (Integer 5))] 
             (EVar "X"%string)), []|
-e>
  | 1, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 [] (EEmptyTuple)]) (eff := [[]])
                       (ids := [1]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [1]); auto.
    - simpl. intros. inversion H.
      + apply eval_lit.
      + inversion H1.
    - reflexivity.
    - simpl. apply eval_var.
Qed.

Example map_eval :
  |[(inl "X"%string, VLit (Integer 42))], 0,
    EMap [(ELit (Integer 5), EVar "X"%string)], []|
-e>
  | 0, inl (VMap [(VLit (Integer 5), VLit (Integer 42))]), []|.
Proof.
  eapply eval_map with (kvals := [VLit (Integer 5)]) (vvals := [VLit (Integer 42)]) 
                       (eff := [[];[]]) (ids := [0;0]); auto.
  * intros. inversion H.
    - subst. apply eval_lit.
    - inversion H1.
  * intros. inversion H.
    - apply eval_var.
    - inversion H1.
Qed.

Example map_eval2 : 
  |[(inl "X"%string, VLit (Integer 42))], 0,
   EMap [(ELit (Integer 54), EVar "X"%string); (EVar "X"%string, EVar "X"%string)] 
  , []|
-e> 
  |0, inl (VMap [(VLit (Integer 42), VLit (Integer 42)); 
                 (VLit (Integer 54), VLit (Integer 42))])
  , []|.
Proof.
  eapply eval_map with (kvals := [VLit (Integer 54); VLit (Integer 42)])
                       (vvals := [VLit (Integer 42); VLit (Integer 42)])
                       (eff := [[];[];[];[]]) (ids := [0;0;0;0]); auto.
  * intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_lit.
      + inversion H3.
  * intros. inversion H. 
    - apply eval_var.
    - inversion H1.
      + apply eval_var.
      + inversion H3.
Qed.

Example map_eval3 : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   EMap [(ELit (Integer 5), EVar "X"%string); 
         (EVar "X"%string, ECall "plus" 
                              [ELit (Integer 1); (EVar "X"%string)])] 
  , []| 
-e> 
  | 0, inl (VMap [(VLit (Integer 5), VLit (Integer 6))]), []|.
Proof.
  apply eval_map with (kvals := [VLit (Integer 5); VLit (Integer 5)])
                      (vvals := [VLit (Integer 5); VLit (Integer 6)])
                      (eff := [[];[];[];[]]) (ids := [0;0;0;0]); auto.
  * simpl. auto.
  * intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_lit.
      + inversion H3.
  * intros. inversion H.
    - eapply eval_call with (vals := [VLit (Integer 1); VLit (Integer 5)])
                            (eff := [[];[]]) (ids := [0;0]); auto.
      + intros. inversion H0.
        ** apply eval_var.
        ** inversion H3.
          -- apply eval_lit.
          -- inversion H5.
    - inversion H1.
      + simpl. apply eval_var.
      + inversion H3.
Qed.

Example map_eval4 : 
  |[], 0,
   ELet [("X"%string, EFun [] (ELit (Integer 1))); 
         ("Y"%string, EFun [] (ELit (Integer 2))); 
         ("Z"%string, EFun [] (ELit (Integer 3)))]
     (EMap [(EVar "Z"%string, ELit (Integer 10)); 
            (EVar "X"%string, ELit (Integer 11));
            (EVar "Y"%string, ELit (Integer 12)); 
            (EVar "X"%string, ELit (Integer 13))])
  , []| 
-e> 
  | 3, inl (VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                  (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                  (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))])
  , []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 [] (ELit (Integer 1));
                                 VClos [] [] 1 [] (ELit (Integer 2));
                                 VClos [] [] 2 [] (ELit (Integer 3))]) (eff := [[];[];[]])
                       (ids := [1;2;3]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5.
    all: apply eval_fun.
  * reflexivity.
  * apply eval_map with (kvals := [VClos [] [] 2 [] (ELit (Integer 3));
                                   VClos [] [] 0 [] (ELit (Integer 1));
                                   VClos [] [] 1 [] (ELit (Integer 2));
                                   VClos [] [] 0 [] (ELit (Integer 1))])
                        (vvals := [VLit (Integer 10);
                                   VLit (Integer 11);
                                   VLit (Integer 12);
                                   VLit (Integer 13)])
                        (eff := [[];[];[];[];[];[];[];[]])
                        (ids := [3;3;3;3;3;3;3;3]); auto.
    - simpl. auto.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      all: apply eval_var.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      all: apply eval_lit.
Qed.

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite :
  |[], 0,
   ELet [("X"%string, ELit (Integer 42))] 
     (ELet [("Y"%string, EFun ["X"%string] (EVar "X"%string))] 
       (ELet [("X"%string, ELit (Integer 5))] 
         (EApp (EVar "Y"%string) [ELit (Integer 7)]))), []|
-e>
  | 1, inl (VLit (Integer 7)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 42)]) (eff := [[]]) (ids := [0]); auto.
  * simpl. intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with 
             (vals := [VClos [(inl "X"%string, VLit (Integer 42))] [] 
                          0 ["X"%string] (EVar "X"%string)])
             (eff := [[]]) (ids := [1]); auto.
    - simpl. intros. inversion H.
      + apply eval_fun.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [1]); auto.
      + simpl. intros. inversion H.
        ** apply eval_lit.
        ** inversion H1.
      + reflexivity.
      + simpl. eapply eval_apply with 
                    (vals := [VLit (Integer 7)]) (n := 0) (ids := [1])
                    (ref := [(inl "X"%string, VLit (Integer 42))]) 
                    (ext := []) (body := (EVar "X"%string)) 
                    (var_list := ["X"%string]) (eff := [[]]); auto.
        ** simpl. intros. apply eval_var.
        ** intros. inversion H.
          -- apply eval_lit.
          -- inversion H1.
        ** reflexivity.
        ** apply eval_var.
Qed.


(** Example to test that value overwriting does not affect the value in the closure *)
Example let_closure_apply_eval_without_overwrite2 :
  |[], 0,
   ELet [("X"%string, ELit (Integer 42))] 
     (ELet [("Y"%string, EFun [] (EVar "X"%string))] 
       (ELet [("X"%string, ELit (Integer 5))] 
         (EApp (EVar "Y"%string) []))), []|
-e> 
  | 1, inl (VLit (Integer 42)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 42)]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H; inversion H1.
    - apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_let with 
               (vals := [VClos [(inl "X"%string, VLit (Integer 42))] []
                            0 [] (EVar "X"%string)]) (eff := [[]]) (ids := [1]); auto.
    - intros. inversion H; inversion H1.
      + apply eval_fun.
    - reflexivity.
    - eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [1]); auto.
      + intros. inversion H; inversion H1.
        ** apply eval_lit.
      + reflexivity.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                      (body := (EVar "X"%string)) (n := 0)
                                      (ref := [(inl "X"%string, VLit (Integer 42))]) 
                                      (ext := []) (eff := []); auto.
        ** apply eval_var.
        ** intros. inversion H.
        ** reflexivity.
        ** apply eval_var.
Qed.

Example call_eval : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   ECall "plus"%string [EVar "X"%string ; ELit (Integer 2)], []|
-e> 
  |0, inl (VLit (Integer 7)), []|.
Proof.
  eapply eval_call with (vals := ([VLit (Integer 5) ; VLit (Integer 2)]))
                        (eff := [[];[]]) (ids := [0; 0]); auto.
  * simpl. intros. inversion H.
    - apply eval_lit.
    - inversion H1.
      + apply eval_var.
      + inversion H3.
Qed.

Example mutliple_function_let : 
  |[], 0,
   ELet [("Z"%string, ECall "plus"%string [ELit (Integer 2) ; ELit (Integer 2)] )] 
     (ELet [("Y"%string, EFun [] (EVar "Z"%string))] 
        (ELet [("X"%string, EFun [] (EApp (EVar "Y"%string) []))] 
          (EApp (EVar "X"%string) []))), []|
-e>
  | 2, inl (VLit (Integer 4)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 4)]) (eff := [[]]) (ids := [0]); auto.
  * simpl. intros. inversion H.
    - eapply eval_call with (vals := [VLit (Integer 2); VLit (Integer 2)])
                            (eff := [[];[]]) (ids := [0;0]); auto.
      + simpl. intros. inversion H0.
        ** apply eval_lit.
        ** inversion H3.
          -- apply eval_lit.
          -- inversion H5.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VClos [(inl "Z"%string, VLit (Integer 4))] [] 
                                             0 [] (EVar "Z"%string)])
                                (eff := [[]]) (ids := [1]); auto.
    - simpl. intros. inversion H.
      + apply eval_fun.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_let with 
              (vals := [VClos [(inl "Z"%string, VLit (Integer 4));
                                    (inl "Y"%string,
                                    VClos [(inl "Z"%string, VLit (Integer 4))] [] 0 []
                                      (EVar "Z"%string))] [] 1 [] (EApp (EVar "Y"%string) [])])
              (eff := [[]]) (ids := [2]); auto.
      + simpl. intros. inversion H.
        ** apply eval_fun.
        ** inversion H1.
      + reflexivity.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                      (body := (EApp (EVar "Y"%string) [])) 
                                      (ref := [(inl "Z"%string, VLit (Integer 4));
                                               (inl "Y"%string,
                                                VClos [(inl "Z"%string, VLit (Integer 4))] 
                                                       [] 0 [] (EVar "Z"%string))])
                                      (ext := []) (n := 1)
                                      (eff := []); auto.
        ** simpl. apply eval_var.
        ** simpl. intros. inversion H.
        ** reflexivity.
        ** simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                         (body := (EVar "Z"%string)) (n := 0)
                                         (ref := [(inl "Z"%string, VLit (Integer 4))]) 
                                         (ext := []) (eff := []); auto.
          -- apply eval_var.
          -- intros. inversion H.
          -- reflexivity.
          -- simpl. apply eval_var.
Qed.

Example case_eval : 
  |[(inl "X"%string, VEmptyTuple)], 0,
   ECase (EVar "X"%string)
         [(PLit (Integer 5), ELit (Atom "true"%string), ELit (Integer 5)); 
          (PLit (Integer 6), ELit (Atom "true"%string), ELit (Integer 6)); 
          (PVar "Z"%string, ELit (Atom "true"%string), EVar "Z"%string) ]
  , [] |
-e> 
  | 0, inl (VEmptyTuple), []|.
Proof.
  eapply eval_case with (i := 2) (v := VEmptyTuple); auto.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. inversion H0.
    - inversion H2.
      + subst. inversion H0.
      + subst. inversion H4.
  * reflexivity.
  * simpl. apply eval_lit.
  * simpl. apply eval_var.
Qed.

Example case_eval2 :
  |[(inl "X"%string, VEmptyTuple)], 0,
   ECase (EVar "X"%string) 
         [(PLit (Integer 5), ELit (Atom "true"%string), ELit (Integer 5)); 
          (PLit (Integer 6), ELit (Atom "true"%string), ELit (Integer 6));
          (PVar "Z"%string, ELit (Atom "false"%string), EVar "Z"%string);
          (PVar "Z"%string, ELit (Atom "true"%string), EEmptyMap)]

  , []|
-e> 
  | 0, inl (VEmptyMap), []|.
Proof.
  eapply eval_case with (i := 3) (v := VEmptyTuple); auto.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. inversion H0. apply eval_lit.
    - inversion H2.
      + subst. inversion H0.
      + inversion H4.
        ** subst. inversion H0.
        ** inversion H6.
  * reflexivity.
  * apply eval_lit.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

Example case_eval_fun : 
  |[(inl "X"%string, VClos [(inl "Y"%string, ttrue)] [] 0 [] (EVar "Y"%string))], 1,
   ECase (EVar "X"%string) 
         [(PLit (Integer 5), ELit (Atom "true"%string), ELit (Integer 5)); 
          (PLit (Integer 6), ELit (Atom "true"%string), ELit (Integer 6)); 
          (PVar "Z"%string, ELit (Atom "true"%string), EApp (EVar "Z"%string) [])] 
  , []| 
-e> | 1, inl (ttrue), []|.
Proof.
  eapply eval_case with (i := 2) (v := VClos [(inl "Y"%string, ttrue)] [] 0 [] (EVar "Y"%string)); auto.
  * apply eval_var.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. inversion H0.
    - inversion H2.
      + subst. inversion H0.
      + inversion H4.
  * reflexivity.
  * apply eval_lit.
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (n := 0)
                                  (ref := [(inl "Y"%string, ttrue)]) 
                                  (ext := []) (body := (EVar "Y"%string))
                                  (eff := []) (ids := []); auto.
   - apply eval_var.
   - intros. inversion H.
   - reflexivity.
   - simpl. apply eval_var.
Qed.


Example letrec_eval : 
  |[(inr ("fun4"%string, 0), VClos [] [(0, ("fun4"%string, 0), ([], EEmptyMap))] 0 [] (EEmptyMap)) ; 
    (inl "X"%string, VLit (Integer 42))], 1,
   ELetRec [(("fun2"%string, 0), ([], EVar "X"%string)); 
            (("fun4"%string, 1), (["Z"%string],EVar "Z"%string))] 
     (EApp (EFunId ("fun4"%string, 0)) []), []|
-e>
  | 3, inl (VEmptyMap), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EEmptyMap)) 
                                  (ref := []) (eff := []) (n := 0) (ids := [])
                                  (ext := [(0, ("fun4"%string, 0), ([], EEmptyMap))]); auto.
    - apply eval_funid.
    - simpl. intros. inversion H.
    - simpl. reflexivity.
    - eapply eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
      + intros. inversion H.
      + intros. inversion H.
Qed.


Example unnamed_eval : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   EApp (EFun ["Y"%string] (EVar "Y"%string)) [EVar "X"%string], []|
-e> 
  | 1, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_apply with (vals := [VLit (Integer 5)]) 
                         (var_list := ["Y"%string]) (ids := [1])
                         (body := (EVar "Y"%string)) 
                         (ref := [(inl "X"%string, VLit (Integer 5))]) 
                         (ext := []) (eff := [[]]); auto.
  * apply eval_fun.
  * intros. inversion H; inversion H1. apply eval_var.
  * reflexivity.
  * simpl. apply eval_var.
Qed.


Section B_Core.

Definition B : ErlModule := ErlMod "b"%string [
  TopLevelFun ("fun1"%string, 0) ([], (ELit (Integer 6))) ;
  TopLevelFun ("fun2"%string, 0) ([], (ELet [("X"%string, (EFun [] (ELit (Integer 5))))] (
                                         ELet [("X"%string, (EFun [] (ELit (Integer 6))))] 
                                           (EApp (EVar "X"%string) []))) )
].


Example fun2 : 
  |[], 0,
   ELet [("X"%string, (EFun [] (ELit (Integer 5))))] 
     (ELet [("X"%string, (EFun [] (ELit (Integer 6))))] 
       (EApp (EVar "X"%string) [])), []|
-e>
  | 2, inl (VLit (Integer 6)), []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 [] (ELit (Integer 5))]) (eff := [[]])
                       (ids := [1]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VClos [(inl "X"%string, 
                                             VClos [] [] 0 [] (ELit (Integer 5)))] 
                                           [] 1 [] (ELit (Integer 6))])
                                (eff := [[]]) (ids := [2]); auto.
    - simpl. intros. inversion H.
      + apply eval_fun.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                    (body := (ELit (Integer 6))) 
                                    (ref := [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 5)))]) (n := 1)
                                    (ext := []) (eff := []); auto.
      + apply eval_var.
      + intros. inversion H.
      + reflexivity.
      + apply eval_lit.
Qed.

(* Compute initialize_proving B.

Compute initialize_proving_closures B. *)

End B_Core.

Section Documentation_Examples.

Example ex1 : 
  |[], 0, ELet [("X"%string, ELit (Integer 5))] (EVar "X"%string), []|
-e>
  | 0, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H.
    - subst. apply eval_lit.
    - inversion H1.
  * reflexivity.
  * simpl. apply eval_var.
Qed.

Example ex2 : 
  |[], 0,
   ELet [("X"%string, EFun [] (EApp (EVar "X"%string) []))] 
     (EApp (EVar "X"%string) []), []|
-e>
  | 1, inr novar, []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 [] (EApp ( EVar "X"%string) [])])
                       (eff := [[]]) (ids := [1]); auto.
  * intros. inversion H.
    - subst. apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                  (body := (EApp (EVar "X"%string) [])) 
                                  (ref := []) (ext := []) (n := 0) (eff := []); auto.
    - apply eval_var.
    - intros. inversion H.
    - reflexivity.
    - simpl. eapply eval_apply_ex_closure_ex; auto.
      + reflexivity.
      + apply eval_var.
Qed.

Example ex3 :
  |[], 0, ELetRec [(("X"%string, 0), ([], EApp (EFunId ("X"%string, 0)) []))] 
            (EApp (EFunId ("X"%string, 0)) []), []|
-e>
  |1, inl (VEmptyTuple), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (ref := []) (n := 0) (eff := [])
                                  (body := (EApp (EFunId ("X"%string, 0)) [])) (ids := [])
                                  (ext := [(0, ("X"%string, 0), ([], EApp (EFunId ("X"%string, 0)) []))]); 
        try (reflexivity).
    - apply eval_funid.
    - intros. inversion H.
    - reflexivity.
    - simpl. eapply eval_apply with (vals := []) (n := 0) (var_list := []) (ref := []) (eff := [])
                                    (body := (EApp (EFunId ("X"%string, 0)) [])) (ids := [])
                                    (ext := [(0, ("X"%string, 0), ([], EApp (EFunId ("X"%string, 0)) []))]); 
         try (reflexivity).
      + apply eval_funid.
      + intros. inversion H.
      + reflexivity.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (n := 0) (ref := []) (eff := [])
                                      (body := (EApp (EFunId ("X"%string, 0)) [])) (ids := [])
                                      (ext := [(0, ("X"%string, 0), 
                                               ([], EApp (EFunId ("X"%string, 0)) []))]); 
             try (reflexivity).
        ** apply eval_funid.
        ** intros. inversion H.
        ** simpl.
Admitted.

Example ex4 : 
|[], 0, ELet [("X"%string, ELit (Integer 4))] 
          (ELet [("X"%string, EFun [] (EVar "X"%string))] 
             (ELet [("X"%string, EFun [] (EApp (EVar "X"%string) []))] 
                (EApp (EVar "X"%string) []))), []|
-e>
  |2, inl (VLit (Integer 4)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 4)]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H; inversion H1. apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VClos [(inl "X"%string, VLit (Integer 4))] [] 0 [] 
                                            (EVar "X"%string)])
                                (eff := [[]]) (ids := [1]); auto.
    - intros. inversion H; inversion H1. apply eval_fun.
    - reflexivity.
    - simpl. eapply eval_let with (vals := [VClos [(inl "X"%string,
                                              VClos [(inl "X"%string, VLit (Integer 4))] [] 0 []
                                                (EVar "X"%string))] [] 1 [] (EApp (EVar "X"%string) []) ])
                                  (eff := [[]]) (ids := [2]); auto.
       + intros. inversion H; inversion H1. apply eval_fun.
       + reflexivity.
       + simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                       (body := EApp (EVar "X"%string) []) 
                                       (ref := [(inl "X"%string,
                                                 VClos [(inl "X"%string, VLit (Integer 4))] [] 0 []
                                                   (EVar "X"%string))]) (n := 1)
                                       (ext := []) (eff := []); auto.
         ** apply eval_var.
         ** intros. inversion H.
         ** reflexivity.
         ** simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                          (body := EVar "X"%string) 
                                          (ref := [(inl "X"%string, VLit (Integer 4))]) (n := 0)
                                          (ext := []) (eff := []); auto.
           -- apply eval_var.
           -- intros. inversion H.
           -- reflexivity.
           -- apply eval_var.
Qed.

End Documentation_Examples.

Example returned_function :
  |[], 0,
   ELet [("X"%string, EFun [] (EFun [] (ELit (Integer 5))))] 
     (EApp (EApp (EVar "X"%string) []) []), []|
-e>
  | 2, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 [] (EFun [] (ELit (Integer 5)))])
                       (eff := [[]]) (ids := [1]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (ref := []) (ext := []) (eff := [])
                                  (body := ELit (Integer 5)) (var_list := []) (ids := []); auto.
    - eapply eval_apply with (vals := []) (var_list := []) (n := 0) (ids := [])
                             (body := EFun [] (ELit (Integer 5))) 
                             (ref := []) (ext := []) (eff := []); auto.
      + apply eval_var.
      + intros. inversion H.
      + reflexivity.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - reflexivity.
    - apply eval_lit.
Qed.

Example returned_recursive_function : 
  |[], 0,
   ELetRec [(("fun1"%string, 0), ([], (EFun [] (ELit (Integer 5)))))] 
     (EApp (EApp (EFunId ("fun1"%string, 0)) []) []), []|
-e>
  | 2, inl (VLit (Integer 5)), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (ref := [(inr ("fun1"%string, 0),
                                                         VClos [] [(0, ("fun1"%string, 0), ([], 
                                                            EFun [] (ELit (Integer 5))))] 0 []
                                                            (EFun [] (ELit (Integer 5))))]) 
                                  (ext := []) (body := ELit (Integer 5)) (ids := [])
                                  (var_list := []) (eff := []); try (reflexivity).
    - eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                             (body := EFun [] (ELit (Integer 5))) 
                             (ref := []) (eff := []) (n := 0)
                             (ext := [(0, ("fun1"%string, 0), ([], EFun [] (ELit (Integer 5))))]);
          try (reflexivity).
      + apply eval_funid.
      + intros. inversion H.
      + simpl. apply eval_fun with (id := 1).
    - intros. inversion H.
    - reflexivity.
    - apply eval_lit.
Qed.

Example returned_function2 :
  |[(inl "X"%string, VLit (Integer 7))], 0,
   ELet [("X"%string, EFun [] (EFun [] (EVar "X"%string)))] 
     (EApp (EApp (EVar "X"%string) []) []), []|
-e>
  | 2, inl (VLit (Integer 7)), []|.
Proof.
  eapply eval_let with (vals := [VClos [(inl "X"%string, VLit (Integer 7))] [] 
                                  0 [] (EFun [] (EVar "X"%string))])
                       (eff := [[]]) (ids := [1]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (ids := []) (ref := [(inl "X"%string, VLit (Integer 7))]) 
                                 (ext := []) (body := EVar "X"%string) (var_list := []) (eff := []) (n := 1); auto.
    - eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                             (body := EFun [] (EVar "X"%string)) 
                             (ref := [(inl "X"%string, VLit (Integer 7))]) 
                             (ext := []) (n := 0) (eff := []); auto.
      + apply eval_var.
      + intros. inversion H.
      + reflexivity.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - reflexivity.
    - simpl. apply eval_var.
Qed.

Example returned_recursive_function2 :
  |[(inl "X"%string, VLit (Integer 7))], 0,
   ELetRec [(("fun1"%string, 0), ([], EFun [] (EVar "X"%string)))] 
     (EApp (EApp (EFunId ("fun1"%string, 0)) []) []), []|
-e>
  | 2, inl (VLit (Integer 7)), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (eff := []) (ids := [])
                                 (ref := [(inl "X"%string, VLit (Integer 7)) ; 
                                          (inr ("fun1"%string, 0),
                                             VClos [(inl "X"%string, VLit (Integer 7))] 
                                                      [(0, ("fun1"%string, 0), 
                                                          ([], EFun [] (EVar "X"%string)))] 
                                                      0 [] 
                                                      (EFun [] (EVar "X"%string)))]) 
                                 (body := EVar "X"%string) (n := 1)
                                 (var_list := []) (ext := []); try (reflexivity).
    - eapply eval_apply with (vals := []) (var_list := []) (eff := []) (ids := [])
                             (body := EFun [] (EVar "X"%string)) (n := 0)
                             (ref := [(inl "X"%string, VLit (Integer 7))]) 
                             (ext := [(0, ("fun1"%string, 0), ([], EFun [] (EVar "X"%string)))]); 
          try (reflexivity).
      + apply eval_funid.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - reflexivity.
    - simpl. apply eval_var.
Qed.

Example returned_function3 : 
  |[], 0,
   ELet [("F"%string, 
     EFun ["X"%string] 
        (ELet [("Y"%string, ECall "plus"%string [EVar "X"%string; ELit (Integer 3)] )] 
              (EFun ["Z"%string] 
                    (ECall "plus"%string 
                          [ECall "plus"%string [EVar "X"%string; EVar "Y"%string]
                     ; EVar "Z"%string]))))]
  (EApp (EApp (EVar "F"%string) [ELit (Integer 1)]) [ELit (Integer 1)]), []|
-e>
  |2, inl (VLit (Integer 6)), []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 ["X"%string] (ELet [("Y"%string,
                                        ECall "plus"
                                           [EVar "X"%string; ELit (Integer 3)] )]
                                        (EFun ["Z"%string]
                                           (ECall "plus"
                                              [ECall "plus"
                                                 [EVar "X"%string; EVar "Y"%string];
                                              EVar "Z"%string])))])
                        (eff := [[]]) (ids := [1]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_apply with (var_list := ["Z"%string]) (eff := [[]]) (ids := [2])
                                  (body := (ECall "plus"
                                              [ECall "plus"
                                                 [EVar "X"%string; EVar "Y"%string];
                                              EVar "Z"%string]))
                                  (ref := [(inl "X"%string, VLit (Integer 1)); 
                                           (inl "Y"%string, VLit (Integer 4))])
                                  (ext := []) (vals := [VLit (Integer 1)]) (n := 1); auto.
    - eapply eval_apply with (vals := [VLit (Integer 1)]) (var_list := ["X"%string]) (ids := [1])
                             (body := ELet [("Y"%string,
                                        ECall "plus"
                                           [EVar "X"%string; ELit (Integer 3)] )]
                                        (EFun ["Z"%string]
                                           (ECall "plus"
                                              [ECall "plus"
                                                 [EVar "X"%string; EVar "Y"%string];
                                              EVar "Z"%string]))) 
                             (ref := []) (ext := []) (eff := [[]]) (n := 0); auto.
      + apply eval_var.
      + intros. inversion H; inversion H1. apply eval_lit.
      + reflexivity.
      + eapply eval_let with (vals := [VLit (Integer 4)]) (eff := [[]]) (ids := [1]); auto.
        ** intros. inversion H; inversion H1. 
           apply eval_call with (vals := [VLit (Integer 1); VLit (Integer 3)])
                                (eff := [[];[]]) (ids := [1;1]); auto.
          -- intros. inversion H2.
            ++ apply eval_lit.
            ++ inversion H4; inversion H6. apply eval_var.
        ** simpl. apply eval_fun.
    - intros. inversion H; inversion H1. simpl. apply eval_lit.
    - reflexivity.
    - eapply eval_call with (vals := [VLit (Integer 5) ; VLit (Integer 1)])
                            (eff := [[];[]]) (ids := [2;2]); auto.
      + intros. inversion H.
        ** inversion H1. apply eval_var.
        ** inversion H1.
          -- eapply eval_call with (vals := [VLit (Integer 1) ; VLit (Integer 4)])
                                               (eff := [[];[]]) (ids := [2;2]); auto.
            ++ intros. inversion H2.
              *** apply eval_var.
              *** inversion H5; inversion H7. apply eval_var.
          -- simpl. inversion H3.
Qed.

Example sum :
  | [], 0,
    ELetRec [(("f"%string, 1), (["X"%string], 
      
      ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]
      ))] (EApp (EFunId ("f"%string, 1)) [ELit (Integer 2)]), []| -e> |1, inl (VLit (Integer 3)), []|.
Proof.
  eapply eval_letrec; auto.
  2: reflexivity.
  * simpl. eapply eval_apply with (vals := [VLit (Integer 2)]) (eff := [[]]) (eff2 := []) (n := 0)
                                  (var_list := ["X"%string]) (ref := []) (ids := [1])
                                  (body := 
      (ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]))
                                  (ext := [(0, ("f"%string, 1),
                                      (["X"%string],
                                      ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]))]); simpl; auto.
    - apply eval_funid.
    - intros. inversion H; inversion H1. apply eval_lit.
    - unfold concatn. simpl. eapply eval_case with (i := 1) (v := VLit (Integer 2)); auto.
      + apply eval_var.
      + simpl. reflexivity.
      + intros. inversion H; inversion H2. subst. inversion H0.
      + reflexivity.
      + simpl. apply eval_lit.
      + eapply eval_call with (vals := [VLit (Integer 2); VLit (Integer 1)]) 
                              (eff := [[]; []]) (ids := [1;1]); auto.
        ** intros. inversion H; inversion H1. 3: inversion H3.
          -- simpl. eapply eval_apply with (vals := [VLit (Integer 1)]) (eff := [[]]) (eff2 := [])
                                  (var_list := ["X"%string]) (ref := []) (ids := [1])
                                  (body := 
      (ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]))
                                  (ext := [(0, ("f"%string, 1),
                                      (["X"%string],
                                      ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]))]) (n := 0); simpl; auto.
            ++ apply eval_funid.
            ++ intros. inversion H2; inversion H4.
               eapply eval_call with (vals := [VLit (Integer 2); VLit (Integer (-1))])
                                     (eff := [[];[]]) (ids := [1;1]); auto.
              *** simpl. intros. inversion H5; inversion H7. 3: inversion H9.
                --- apply eval_lit.
                --- apply eval_var.
            ++ {
            eapply eval_case with (i := 1) (v := VLit (Integer 1)); auto.
              + apply eval_var.
              + simpl. reflexivity.
              + intros. inversion H2; inversion H5. subst. inversion H3.
              + reflexivity.
              + simpl. apply eval_lit.
              + subst. simpl. eapply eval_call with (vals := [VLit (Integer 1); VLit (Integer (0))])
                                                    (eff := [[];[]]) (ids := [1;1]); auto.
                * simpl. intros. inversion H1; inversion H3. 3: inversion H5. 
                  - eapply eval_apply with (vals := [VLit (Integer 0)]) (eff := [[]]) (eff2 := [])
                                  (var_list := ["X"%string]) (ref := []) (n := 0) (ids := [1])
                                  (body := 
      (ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]))
                                  (ext := [(0, ("f"%string, 1),
                                      (["X"%string],
                                      ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]))]); simpl; auto.
                  ** apply eval_funid.
                  ** intros. inversion H4. 2: inversion H6.
                     eapply eval_call with (vals := [VLit (Integer 1); VLit (Integer (-1))])
                                           (eff := [[];[]]) (ids := [1;1]); auto.
                    -- intros. inversion H5; inversion H8.
                      ++ simpl. apply eval_lit.
                      ++ simpl. apply eval_var.
                      ++ inversion H10.
                  ** eapply eval_case with (i := 0) (v := VLit (Integer 0)); auto.
                    -- apply eval_var.
                    -- simpl. omega.
                    -- reflexivity.
                    -- intros. inversion H4.
                    -- reflexivity.
                    -- simpl. apply eval_lit.
                    -- subst. apply eval_lit.
              - apply eval_var. 
            }
          -- simpl. apply eval_var.
Qed.

Example letrec_no_replace :
  |[], 0,
   ELet [("X"%string, ELit (Integer 42))] 
     (ELetRec [(("f"%string, 0), ([], EVar "X"%string))]
       (ELet [("X"%string, ELit (Integer 5))]
         (EApp (EFunId ("f"%string, 0)) []))), []|
-e>
  | 1, inl (VLit (Integer 42)), []|.
Proof.
  eapply eval_let with (vals := [VLit (Integer 42)]) (eff := [[]]) (ids := [0]); auto.
  * intros. inversion H; inversion H1.
    - apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_letrec; auto.
    2: reflexivity.
    - eapply eval_let with (vals := [VLit (Integer 5)]) (eff := [[]]) (ids := [1]); auto.
      + intros. inversion H; inversion H1.
        ** apply eval_lit.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (ids := [])
                                      (body := (EVar "X"%string)) 
                                      (ref := [(inl "X"%string, VLit (Integer 42))]) 
                                      (ext := [(0, ("f"%string, 0), ([], EVar "X"%string))])
                                      (eff := []) (n := 0); auto.
        ** apply eval_funid.
        ** intros. inversion H.
        ** simpl. reflexivity.
        ** simpl. apply eval_var.
Qed.


End Tests.