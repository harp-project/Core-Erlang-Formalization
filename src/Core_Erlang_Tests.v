Require Core_Erlang_Semantics.

Module Tests.

Import Core_Erlang_Semantics.Semantics.

Import ListNotations.

Open Scope string_scope.

(** This is an endless recursion *)
Example eval_letrec1 : 
  |[], 0, ELetRec [(("x", 1), (["X"], ^EApp (EFunId ("x", 1)) [^EVar "X"])) ]
            (EApp (EFunId ("x", 1)) [^EEmptyTuple]), []|
-e> 
  |1, inl [ErrorValue], []|.
Proof.
  eapply eval_single, eval_letrec; try (reflexivity).
  * simpl. eapply eval_single, eval_app with (vals := [VEmptyTuple]) 
                                  (body := (EApp (EFunId ("x", 1)) [^EVar "X"])) (n := 0)
                                  (ids := [1])
                                  (var_list := ["X"]) 
                                  (ref := [])
                                  (ext := [(0, ("x", 1), 
                                        (["X"], ^EApp (EFunId ("x", 1)) [^EVar "X"]))]) 
                                  (eff := [[]]); try (reflexivity).
    - unfold append_funs_to_env. simpl. eapply eval_single, eval_funid. reflexivity.
    - intros. inversion H.
      + unfold append_funs_to_env, EEmptyTuple. simpl. eapply eval_single, eval_tuple with (eff := []) (vals := [])
                      (ids := []); try(reflexivity). 
        ** intros. inversion H0.
      + inversion H1.
    - eapply eval_single, eval_app with (vals := [VEmptyTuple]) 
                             (body := (EApp (EFunId ("x", 1)) [^EVar "X"])) 
                             (var_list := ["X"]) 
                             (ref := []) (ids := [1])
                             (ext := [(0, ("x", 1),
                                     (["X"], ^EApp (EFunId ("x", 1)) [^EVar "X"]))]) (n := 0)
                             (eff := [[]]); try (reflexivity).
    + apply eval_single, eval_funid. reflexivity.
    + intros. inversion H.
      ** apply eval_single, eval_var. reflexivity.
      ** inversion H1.
    + eapply eval_single, eval_app with (vals := [VEmptyTuple]) 
                             (body := (EApp (EFunId ("x", 1)) [^EVar "X"])) (n := 0)
                             (var_list := ["X"]) 
                             (ref := []) (ids := [1])
                             (ext := [(1, ("x", 1), 
                                     (["X"], ^EApp (EFunId ("x", 1)) [^EVar "X"]))]) 
                             (eff := [[]]); try (reflexivity).
Admitted.

(* (* This is not accepted by the compiler in Core Erlang *)
Example eval_letrec2 : 
  |[], 0, ELet [("F", EFun ["X"] 
         (EApp (EVar "F") [EVar "X"]))] 
            (EApp (EVar "F") [EEmptyTuple]), []| 
-e>
|1, inr novar, []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 ["X"] (EApp (EVar "F") [EVar "X"])]) 
                       (ids := [1])
                       (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * simpl. eapply eval_app with (vals := [VEmptyTuple]) (n := 0)
                                  (var_list := ["X"]) (ids := [1])
                                  (body := (EApp (EVar "F") [EVar "X"])) 
                                  (ref := []) (ext := []) (eff := [[]]); try(reflexivity).
    - apply eval_var. reflexivity.
    - intros. inversion H.
      + eapply eval_tuple with (eff := []) (ids := []); try(reflexivity).
        ** intros. inversion H0.
      + inversion H1.
    - simpl. eapply eval_apply_ex_closure_ex.
      + reflexivity.
      + apply eval_var. reflexivity.
Qed. *)

(* Top level functions, and their closures must be added initially *)
Example multiple_top_level_funs : |[(inr ("fun1", 0), VClos [] [
    (0, ("fun1", 0), ([], (^EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (^ELit (Integer 42))));
    (2, ("fun3", 0), ([], (^EApp (EFunId ("fun2", 0)) [])))
  ] 0 [] (EApp (EFunId ("fun3", 0)) [])) ; 
                                      (inr ("fun2", 0), VClos [] [
    (0, ("fun1", 0), ([], (^EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (^ELit (Integer 42))));
    (2, ("fun3", 0), ([], (^EApp (EFunId ("fun2", 0)) [])))
  ] 1 [] (ELit (Integer 42))) ;
                                      (inr ("fun3", 0), VClos [] [
    (0, ("fun1", 0), ([], (^EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (^ELit (Integer 42))));
    (2, ("fun3", 0), ([], (^EApp (EFunId ("fun2", 0)) [])))
  ] 2 [] (EApp (EFunId ("fun2", 0)) []))], 3
                                      , EApp (EFunId ("fun1",0)) [], []| 
-e> 
  |3, inl [VLit (Integer 42)], []|.
Proof.
  remember [
  (0, ("fun1", 0), ([], (^EApp (EFunId ("fun3", 0)) [])));
  (1, ("fun2", 0), ([], (^ELit (Integer 42))));
  (2, ("fun3", 0), ([], (^EApp (EFunId ("fun2", 0)) [])))
] as ext.
  eapply eval_single, eval_app with (vals := []) (ref := []) (ext := ext) (eff := [])
                         (body := (EApp (EFunId ("fun3", 0)) [])) 
                         (var_list := []) (n := 0) (ids := []); auto.
  * apply eval_single, eval_funid. reflexivity.
  * simpl. intros. inversion H.
  * simpl. eapply eval_single, eval_app with (vals := []) (n := 2) (ref := []) (ext := ext) (eff := [])
                                 (body := (EApp (EFunId ("fun2", 0)) [])) 
                                 (var_list := []) (ids := []); auto.
    - rewrite Heqext. simpl. apply eval_single, eval_funid. reflexivity.
    - intros. inversion H.
    - simpl. eapply eval_single, eval_app with (vals := []) (n := 1) (ref := []) (ext := ext) (eff := [])
                                    (body := (ELit (Integer 42))) (var_list := []) (ids := []); auto.
      + rewrite Heqext. apply eval_single, eval_funid. reflexivity.
      + intros. inversion H.
      + apply eval_single, eval_lit.
Qed.

Example multiple_top_level_funs2 :
  | [], 0, ELetRec [(("fun1",0), ([], ^EApp (EFunId ("fun3", 0)) [])); 
                    (("fun2",0), ([], ^ELit (Integer 42))); 
                    (("fun3",0), ([], ^EApp (EFunId ("fun2", 0)) []))]
     (EApp (EFunId ("fun1",0)) []), [] |
-e>
  |3, inl [VLit (Integer 42)], []|.
Proof.
  eapply eval_single, eval_letrec; try(reflexivity).
  unfold append_funs_to_env. simpl.
  (*remember [
     (2, ("fun3", 0), ([], EApp (EFunId ("fun2", 0)) []));
     (1, ("fun2", 0), ([], ELit (Integer 42)));
     (0, ("fun1", 0), ([], EApp (EFunId ("fun3", 0)) []))
  ] as ext.*)
  eapply eval_single, eval_app with (vals := []) (ref := []) 
                         (ext := [
     (2, ("fun3", 0), ([], ^EApp (EFunId ("fun2", 0)) []));
     (1, ("fun2", 0), ([], ^ELit (Integer 42)));
     (0, ("fun1", 0), ([], ^EApp (EFunId ("fun3", 0)) []))
  ])
                         (eff := [])
                         (body := (EApp (EFunId ("fun3", 0)) [])) 
                         (var_list := []) (n := 0) (ids := []); auto.
  * apply eval_single, eval_funid. reflexivity.
  * simpl. intros. inversion H.
  * simpl. eapply eval_single, eval_app with (vals := []) (n := 2) (ref := []) 
                                  (ext := [
     (2, ("fun3", 0), ([], ^EApp (EFunId ("fun2", 0)) []));
     (1, ("fun2", 0), ([], ^ELit (Integer 42)));
     (0, ("fun1", 0), ([], ^EApp (EFunId ("fun3", 0)) []))
  ]) 
                                 (eff := [])
                                 (body := (EApp (EFunId ("fun2", 0)) [])) 
                                 (var_list := []) (ids := []); auto.
    - simpl. apply eval_single, eval_funid. reflexivity.
    - intros. inversion H.
    - simpl. eapply eval_single, eval_app with (vals := []) (n := 1) (ref := [])
                                    (ext := [
     (2, ("fun3", 0), ([], ^EApp (EFunId ("fun2", 0)) []));
     (1, ("fun2", 0), ([], ^ELit (Integer 42)));
     (0, ("fun1", 0), ([], ^EApp (EFunId ("fun3", 0)) []))
  ]) 
                                    (eff := [])
                                    (body := (ELit (Integer 42))) (var_list := []) (ids := []); auto.
      + apply eval_single, eval_funid. reflexivity.
      + intros. inversion H.
      + apply eval_single, eval_lit.
Qed.

Theorem length_succ {B : Type} (a2 : B) (n : nat) (l2 : list B):
n = length l2
->
S n = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Example weird_apply : |[], 0, ELetRec [(("f", 1), (["X"],
   ^ECase (EVar "X")
          [([PLit (Integer 0)], ^ELit (Atom "true"), ^ELit (Integer 5));
           ([PLit (Integer 1)], ^ELit (Atom "true"), ^EApp (EFunId ("f", 1)) [^ELit (Integer 0)]);
           ([PVar "A"], ^ELit (Atom "true"), ^EApp (EFunId ("f", 1)) [^ELit (Integer 1)])]
   ))]
   (ELet ["X"] (^EFun ["F"]
       (ELetRec [(("f", 1), (["X"], ^ELit (Integer 0)))] 
          (EApp (EVar "F") [^ELit (Integer 2)])
       ))
    (EApp (EVar "X") [^EFunId ("f", 1)])
   ), []|
-e> 
  |3, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_letrec; auto.
  simpl. eapply eval_single, eval_let; auto.
  * apply eval_single, eval_fun.
  * auto.
  * simpl. eapply eval_single, eval_app with (var_list := ["F"]) (n := 1) (eff := [[]]) (ids := [2])
  (body := (ELetRec [(("f", 1), (["X"], ^ELit (Integer 0)))]
       (EApp (EVar "F") [^ELit (Integer 2)])))
  (ext := []); auto.
    - apply length_succ. apply eq_sym, length_zero_iff_nil. reflexivity.
    - apply eval_single, eval_var. reflexivity.
    - reflexivity.
    - intros. inversion H; inversion H1. simpl. apply eval_single, eval_funid. reflexivity.
    - simpl. eapply eval_single, eval_letrec; auto. simpl.
      eapply eval_single, eval_app with (var_list := ["X"]) (eff := [[]])
        (vals := [VLit (Integer 2)])
        (ref := []) (n := 0) (ids := [3]); auto.
      + apply eval_single, eval_var. reflexivity.
      + intros. inversion H; inversion H1. apply eval_single, eval_lit.
      + simpl. eapply eval_single, eval_case with (i := 2); auto.
        ** subst. simpl. eapply eval_single, eval_var. reflexivity.
        ** simpl. reflexivity.
        ** intros. inversion H. 
          -- subst. simpl in H0. inversion H0.
          -- simpl in H0. inversion H2.
            ++ subst. inversion H0.
            ++ inversion H4.
        ** simpl. eapply eval_single, eval_lit.
        ** simpl. eapply eval_single, eval_app with (var_list := ["X"])
                     (eff := [[]]) (n := 0) (ids := [3])
                     (vals := [VLit (Integer 1)]); auto.  
         -- apply eval_single, eval_funid. reflexivity.
         -- intros. inversion H; inversion H1. simpl. apply eval_single, eval_lit.
         -- simpl. eapply eval_single, eval_case with (i := 1); auto.
           ++ eapply eval_single, eval_var. reflexivity.
           ++ simpl. lia. 
           ++ simpl. reflexivity.
           ++ intros. inversion H.
             *** subst. inversion H0.
             *** inversion H2.
           ++ simpl. eapply eval_single, eval_lit.
           ++ simpl. eapply eval_single, eval_app with (var_list := ["X"])
                     (vals := [VLit (Integer 0)])
                     (eff := [[]]) (n := 0) (ids := [3]); auto.
             *** simpl. apply eval_single, eval_funid. reflexivity.
             *** intros. inversion H; inversion H1. apply eval_single, eval_lit.
             *** simpl. eapply eval_single, eval_case with (i := 0); auto.
               --- eapply eval_single, eval_var. reflexivity.
               --- simpl. lia.
               --- simpl. reflexivity.
               --- intros. inversion H.
               --- simpl. eapply eval_single, eval_lit.
               --- simpl. eapply eval_single, eval_lit.
Qed.

Example top_overwrite : 
  |[(inr ("fun2", 0), 
       VClos [] [(0, ("fun2", 0),([],  (^ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))], 1,
  ELetRec [(("fun2", 0), ([], ^ELit (Integer 40)))] 
     (EApp (EFunId ("fun2", 0)) []), [] | 
-e>
  |2, inl [VLit (Integer 40)], []|.
Proof.
  eapply eval_single, eval_letrec; auto.
  * unfold append_funs_to_env. simpl. eapply eval_single, eval_app with (vals := []) (eff := []) (n := 1) (ids := [])
                                  (ref := [(inr ("fun2", 0), VClos [] 
                                                                    [(0, ("fun2", 0), 
                                                                    ([], ^ELit (Integer 42)))] 0 []
                                                                    (^ELit (Integer 42)))]) 
                                  (ext := [(1, ("fun2", 0), ([],  (^ELit (Integer 40)) ))]) 
                                  (body := (ELit (Integer 40))) (var_list := []); auto.
    - unfold append_funs_to_env. simpl. apply eval_single, eval_funid. reflexivity.
    - intros. inversion H.
    - apply eval_single, eval_lit.
Qed.

Example top_no_overwrite : 
  |[(inr ("fun2", 0), 
     VClos [] [(0, ("fun2", 0), ([], ^ELit (Integer 42)))] 0 [] (ELit (Integer 42)))], 1,
   ELetRec [(("fun2", 1), (["X"], (^ELit (Integer 40))))] 
     (EApp (EFunId ("fun2", 0)) []), [] |
-e> 
  | 2, inl [VLit (Integer 42)], []|.
Proof.
  eapply eval_single, eval_letrec; auto.
  * simpl. eapply eval_single, eval_app with (vals := []) (n := 0)
                                  (ref := []) (ids := [])
                                  (ext := [(0, ("fun2", 0), ([], ^ELit (Integer 42)))]) 
                                  (body := ELit (Integer 42)) 
                                  (var_list := [])
                                  (eff := []); auto.
    - apply eval_single, eval_funid. reflexivity.
    - intros. inversion H.
    - apply eval_single, eval_lit.
Qed.

(** This is not accepted by the compiler in Core Erlang *)
Example eval_let_func : 
  |[(inl "X", VLit (Integer 42))], 0,
   ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] EEmptyMap]) 
     (EEmptyMap), []| 
-e> 
  |2, inl [VEmptyMap], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * simpl. eapply eval_values with (vals := [VClos [(inl "X", VLit (Integer 42))] [] 0 [] ENil; VClos [(inl "X", VLit (Integer 42))] [] 1 [] EEmptyMap]) (eff := [[];[]]) 
                                   (ids := [1;2]); auto.
    intros. inversion H. 2: inversion H1. 3: inversion H3.
    - simpl. apply eval_fun.
    - apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_single, eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
    - reflexivity.
    - reflexivity.
Qed.

Example eval_let_apply : 
  |[(inl "X", VLit (Integer 42))], 0,
   ELet ["Y"] (EValues [EFun [] (EVar "X")])
     (EApp (EVar "Y") []), []| 
-e> 
  |1, inl [VLit (Integer 42)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_values with (vals := [VClos [(inl "X", VLit (Integer 42))] [] 0 [] 
                                          (EVar "X")])
                       (eff := [[]]) (ids := [1]); auto.
      simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_single, eval_app with (vals := []) (n := 0) (ids := [])
                                  (ref := [(inl "X", VLit (Integer 42))]) 
                                  (ext := []) 
                                  (body := (EVar "X")) 
                                  (var_list := [])
                                  (eff := []); auto.
    - apply eval_single, eval_var. reflexivity.
    - simpl. intros. inversion H.
    - apply eval_single, eval_var. reflexivity.
Qed.

Example eval_muliple_let : 
  |[], 0, ELet ["X"] (ELit (Integer 1)) 
            (ELet ["X"] (ELit (Integer 2)) 
               (EVar "X")), []| 
-e> 
  |0, inl [VLit (Integer 2)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * eapply eval_single, eval_let; auto.
    - apply eval_single, eval_lit.
    - reflexivity.
    - apply eval_single, eval_var. reflexivity.
Qed.

Example let_eval_1 : 
  |[], 0, ELet ["X"] EEmptyTuple (EEmptyMap), []|
-e>
  | 0, inl [VEmptyMap], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * eapply eval_single, eval_tuple with (eff := []) (ids := []) (vals := []); auto. intros. inversion H.
  * reflexivity.
  * simpl. eapply eval_single, eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
    - reflexivity.
    - reflexivity.
Qed.

Example let_eval_2 : 
  |[(inl "X", VEmptyMap)], 0, ELet ["X"] EEmptyTuple (EEmptyMap), []| 
-e> 
  | 0, inl [VEmptyMap], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * eapply eval_single, eval_tuple with (eff := []) (ids := []) (vals := []); auto. intros. inversion H.
  * reflexivity.
  * simpl. eapply eval_single, eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
    - reflexivity.
    - reflexivity.
Qed.

(** This shouldn't compile in Core Erlang *)
Example eval_let_3 : 
  |[(inl "X", VEmptyMap)], 0,
   ELet ["X"; "X"; "Y"] (EValues [EEmptyTuple; ENil; EVar "X"])
     (EVar "Y"), []|
-e>
  |0, inl [VEmptyMap], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * eapply eval_values with (vals := [VEmptyTuple; VNil; VEmptyMap]) (eff := [[];[];[]]) (ids := [0;0;0]); auto. 
    intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5.
    - apply eval_var. reflexivity.
    - apply eval_nil.
    - eapply eval_tuple with (eff := []) (ids := []); auto. intros. inversion H4.
  * reflexivity.
  * simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example let_eval_4 : 
  |[], 0, ELet ["X"] (ELit (Integer 5)) (EVar "X"), []| 
-e> 
  | 0, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example tuple_eval : 
  |[(inl "X", VLit (Atom "foo")); 
    (inl "Y", VEmptyTuple)], 0,
   ETuple [^ELit (Integer 5); ^EVar "X"; ^EVar "Y"], []| 
-e>
  |0, inl [VTuple [VLit (Integer 5); VLit (Atom "foo"); VEmptyTuple]], []|.
Proof.
  eapply eval_single, eval_tuple with (eff := [[];[];[]]) (ids := [0;0;0]); auto.
  * intros. inversion H.
    - apply eval_single, eval_var. reflexivity.
    - inversion H1.
      + apply eval_single, eval_var. reflexivity.
      + inversion H3.
        ** apply eval_single, eval_lit.
        ** inversion H5.
Qed.

Example apply_top_eval : 
  |[(inr ("Plus", 2), 
       VClos [] [(0, ("Plus", 2),
                     (["X" ; "Y"], ^ELit (Integer 3)))] 
                0 ["X" ; "Y"] 
                (ELit (Integer 3)))], 1,
   EApp (EFunId ("Plus", 2)) [^ELit (Integer 2); ^ELit (Integer 3)], []|
-e>
  |1, inl [VLit (Integer 3)], []|.
Proof.
  eapply eval_single, eval_app with (vals := [VLit (Integer 2) ; VLit (Integer 3)])
                         (var_list := ["X"; "Y"]) 
                         (body := ELit (Integer 3)) 
                         (ref := []) (n := 0) (ids := [1;1])
                         (ext := [(0, ("Plus", 2),
                                   (["X" ; "Y"], ^ELit (Integer 3)))])
                         (eff := [[];[]]); auto.
  * apply eval_single, eval_funid. reflexivity.
  * simpl. intros. inversion H.
    - apply eval_single, eval_lit.
    - inversion H1.
      + apply eval_single, eval_lit.
      + inversion H3.
  * simpl. apply eval_single, eval_lit.
Qed.

Example apply_eval : 
  |[(inl "Minus",
      VClos [] [] 0 ["X"; "Y"] (ELit (Integer 42))) ; 
    (inl "X", VEmptyMap)], 1,
   EApp (EVar "Minus") [^EVar "X"; ^EVar "X"], []|
-e>
  |1, inl [VLit (Integer 42)], []|.
Proof.
  eapply eval_single, eval_app with (vals := [VEmptyMap; VEmptyMap]) (ids := [1;1])
                         (var_list := ["X"; "Y"]) 
                         (body := (ELit (Integer 42))) (n := 0)
                         (ref := []) (ext := []) (eff := [[];[]]); auto.
  * apply eval_single, eval_var. reflexivity.
  * simpl. intros. inversion H.
    - apply eval_single, eval_var. reflexivity.
    - inversion H1.
      + apply eval_single, eval_var. reflexivity.
      + inversion H3.
  * simpl. apply eval_single, eval_lit.
Qed.


Example list_eval : 
  |[(inl "X", VLit (Integer 5))], 0,
   ECons (EVar "X") (ENil), []| 
-e>
  | 0, inl [VCons (VLit (Integer 5)) (VNil)], []|.
Proof.
  eapply eval_single, eval_cons.
  * apply eval_single, eval_nil.
  * apply eval_single, eval_var. reflexivity.
Qed.

Example list_eval2 : 
  |[(inl "X", VLit (Integer 5))], 0,
   ECons (EVar "X") 
         (ECons (EVar "X") 
                (ENil)), []| 
-e> 
  |0, inl [VCons (VLit (Integer 5)) 
                 (VCons (VLit (Integer 5)) 
                        (VNil))], []|.
Proof.
  eapply eval_single, eval_cons with (eff2 := []).
  * eapply eval_single, eval_cons with (eff2 := []).
    - apply eval_single, eval_nil.
    - apply eval_single, eval_var. reflexivity.
  * apply eval_single, eval_var. reflexivity.
Qed.

Example let_eval_overwrite : 
  |[], 0, ELet ["X"] (EFun [] EEmptyTuple) 
           (ELet ["X"] (ELit (Integer 5)) 
             (EVar "X")), []|
-e>
  | 1, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_fun.
  * reflexivity.
  * simpl. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_lit.
    - reflexivity.
    - simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example map_eval :
  |[(inl "X", VLit (Integer 42))], 0,
    EMap [(^ELit (Integer 5), ^EVar "X")], []|
-e>
  | 0, inl [VMap [(VLit (Integer 5), VLit (Integer 42))]], []|.
Proof.
  eapply eval_single, eval_map with (kvals := [VLit (Integer 5)]) (vvals := [VLit (Integer 42)]) 
                       (eff := [[];[]]) (ids := [0;0]); auto.
  * intros. inversion H.
    - subst. apply eval_single, eval_lit.
    - inversion H1.
  * intros. inversion H.
    - apply eval_single, eval_var. reflexivity.
    - inversion H1.
  * reflexivity.
  * reflexivity.
Qed.

Example map_eval2 : 
  |[(inl "X", VLit (Integer 42))], 0,
   EMap [(^ELit (Integer 54), ^EVar "X"); (^EVar "X", ^EVar "X")] 
  , []|
-e> 
  |0, inl [VMap [(VLit (Integer 42), VLit (Integer 42)); 
                 (VLit (Integer 54), VLit (Integer 42))]]
  , []|.
Proof.
  eapply eval_single, eval_map with (kvals := [VLit (Integer 54); VLit (Integer 42)])
                       (vvals := [VLit (Integer 42); VLit (Integer 42)])
                       (eff := [[];[];[];[]]) (ids := [0;0;0;0]); auto.
  * intros. inversion H.
    - apply eval_single, eval_var. reflexivity.
    - inversion H1.
      + apply eval_single, eval_lit.
      + inversion H3.
  * intros. inversion H. 
    - apply eval_single, eval_var. reflexivity.
    - inversion H1.
      + apply eval_single, eval_var. reflexivity.
      + inversion H3.
  * reflexivity.
  * reflexivity.
Qed.

Example map_eval3 : 
  |[(inl "X", VLit (Integer 5))], 0,
   EMap [(^ELit (Integer 5), ^EVar "X"); 
         (^EVar "X", ^ECall "+" 
                              [^ELit (Integer 1); (^EVar "X")])] 
  , []| 
-e> 
  | 0, inl [VMap [(VLit (Integer 5), VLit (Integer 6))]], []|.
Proof.
  eapply eval_single, eval_map with (kvals := [VLit (Integer 5); VLit (Integer 5)])
                      (vvals := [VLit (Integer 5); VLit (Integer 6)])
                      (eff := [[];[];[];[]]) (ids := [0;0;0;0]); auto.
  * intros. inversion H.
    - apply eval_single, eval_var. reflexivity.
    - inversion H1.
      + apply eval_single, eval_lit.
      + inversion H3.
  * intros. inversion H.
    - eapply eval_single, eval_call with (vals := [VLit (Integer 1); VLit (Integer 5)])
                            (eff := [[];[]]) (ids := [0;0]); auto.
      + intros. inversion H0.
        ** apply eval_single, eval_var. reflexivity.
        ** inversion H3.
          -- apply eval_single, eval_lit.
          -- inversion H5.
    - inversion H1.
      + simpl. apply eval_single, eval_var. reflexivity.
      + inversion H3.
  * reflexivity.
  * reflexivity.
  * simpl. auto.
Qed.

Example map_eval4 : 
  |[], 0,
   ELet ["X"; "Y"; "Z"] 
        (EValues [EFun [] (ELit (Integer 1)); 
                  EFun [] (ELit (Integer 2)); 
                  EFun [] (ELit (Integer 3))])
     (EMap [(^EVar "Z", ^ELit (Integer 10)); 
            (^EVar "X", ^ELit (Integer 11));
            (^EVar "Y", ^ELit (Integer 12)); 
            (^EVar "X", ^ELit (Integer 13))])
  , []| 
-e> 
  | 3, inl [VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                  (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                  (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))]]
  , []|.
Proof.
  eapply eval_single, eval_let; auto.
  eapply eval_values with (vals := [VClos [] [] 0 [] (ELit (Integer 1));
                                 VClos [] [] 1 [] (ELit (Integer 2));
                                 VClos [] [] 2 [] (ELit (Integer 3))]) (eff := [[];[];[]])
                       (ids := [1;2;3]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5.
    all: apply eval_fun.
  * reflexivity.
  * eapply eval_single, eval_map with (kvals := [VClos [] [] 2 [] (ELit (Integer 3));
                                   VClos [] [] 0 [] (ELit (Integer 1));
                                   VClos [] [] 1 [] (ELit (Integer 2));
                                   VClos [] [] 0 [] (ELit (Integer 1))])
                        (vvals := [VLit (Integer 10);
                                   VLit (Integer 11);
                                   VLit (Integer 12);
                                   VLit (Integer 13)])
                        (eff := [[];[];[];[];[];[];[];[]])
                        (ids := [3;3;3;3;3;3;3;3]); auto.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      all: apply eval_single, eval_var; reflexivity.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      all: apply eval_single, eval_lit.
    - reflexivity.
    - reflexivity.
    - simpl. auto.
Qed.

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite :
  |[], 0,
   ELet ["X"] (ELit (Integer 42))
     (ELet ["Y"] (EFun ["X"] (EVar "X")) 
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EVar "Y") [^ELit (Integer 7)]))), []|
-e>
  | 1, inl [VLit (Integer 7)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * simpl. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - simpl. eapply eval_single, eval_let; auto.
      + apply eval_single, eval_lit.
      + reflexivity.
      + simpl. eapply eval_single, eval_app with 
                    (vals := [VLit (Integer 7)]) (n := 0) (ids := [1])
                    (ref := [(inl "X", VLit (Integer 42))]) 
                    (ext := []) (body := (EVar "X")) 
                    (var_list := ["X"]) (eff := [[]]); auto.
        ** simpl. intros. apply eval_single, eval_var. reflexivity.
        ** intros. inversion H.
          -- apply eval_single, eval_lit.
          -- inversion H1.
        ** apply eval_single, eval_var. reflexivity.
Qed.


(** Example to test that value overwriting does not affect the value in the closure *)
Example let_closure_apply_eval_without_overwrite2 :
  |[], 0,
   ELet ["X"] (ELit (Integer 42)) 
     (ELet ["Y"] (EFun [] (EVar "X"))
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EVar "Y") []))), []|
-e> 
  | 1, inl [VLit (Integer 42)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * simpl. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - eapply eval_single, eval_let; auto.
      + apply eval_single, eval_lit.
      + reflexivity.
      + simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                      (body := (EVar "X")) (n := 0)
                                      (ref := [(inl "X", VLit (Integer 42))]) 
                                      (ext := []) (eff := []); auto.
        ** apply eval_single, eval_var. reflexivity.
        ** intros. inversion H.
        ** apply eval_single, eval_var. reflexivity.
Qed.

Example call_eval : 
  |[(inl "X", VLit (Integer 5))], 0,
   ECall "+" [^EVar "X" ; ^ELit (Integer 2)], []|
-e> 
  |0, inl [VLit (Integer 7)], []|.
Proof.
  eapply eval_single, eval_call with (vals := ([VLit (Integer 5) ; VLit (Integer 2)]))
                        (eff := [[];[]]) (ids := [0; 0]); auto.
  * simpl. intros. inversion H.
    - apply eval_single, eval_lit.
    - inversion H1.
      + apply eval_single, eval_var. reflexivity.
      + inversion H3.
Qed.

Example mutliple_function_let : 
  |[], 0,
   ELet ["Z"] (ECall "+" [^ELit (Integer 2) ; ^ELit (Integer 2)] ) 
     (ELet ["Y"] (EFun [] (EVar "Z"))
        (ELet ["X"] (EFun [] (EApp (EVar "Y") [])) 
          (EApp (EVar "X") []))), []|
-e>
  | 2, inl [VLit (Integer 4)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * simpl. eapply eval_single, eval_call with (vals := [VLit (Integer 2); VLit (Integer 2)])
                            (eff := [[];[]]) (ids := [0;0]); auto.
    - simpl. intros. inversion H.
      + apply eval_single, eval_lit.
      + inversion H1.
        ** apply eval_single, eval_lit.
        ** inversion H3.
    - reflexivity.
  * reflexivity.
  * simpl. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - simpl. eapply eval_single, eval_let; auto.
      + simpl. apply eval_single, eval_fun.
      + reflexivity.
      + simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                      (body := (EApp (EVar "Y") [])) 
                                      (ref := [(inl "Z", VLit (Integer 4));
                                               (inl "Y",
                                                VClos [(inl "Z", VLit (Integer 4))] 
                                                       [] 0 [] (EVar "Z"))])
                                      (ext := []) (n := 1)
                                      (eff := []); auto.
        ** simpl. apply eval_single, eval_var. reflexivity.
        ** simpl. intros. inversion H.
        ** simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                         (body := (EVar "Z")) (n := 0)
                                         (ref := [(inl "Z", VLit (Integer 4))]) 
                                         (ext := []) (eff := []); auto.
          -- apply eval_single, eval_var. reflexivity.
          -- intros. inversion H.
          -- simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example case_eval : 
  |[(inl "X", VEmptyTuple)], 0,
   ECase (EVar "X")
         [([PLit (Integer 5)], ^ELit (Atom "true"), ^ELit (Integer 5)); 
          ([PLit (Integer 6)], ^ELit (Atom "true"), ^ELit (Integer 6)); 
          ([PVar "Z"], ^ELit (Atom "true"), ^EVar "Z") ]
  , [] |
-e> 
  | 0, inl [VEmptyTuple], []|.
Proof.
  eapply eval_single, eval_case with (i := 2); auto.
  * eapply eval_single, eval_var. reflexivity.
  * reflexivity.
  * intros. simpl in H0. inversion H.
    - subst. simpl in H0. inversion H0.
    - inversion H2.
      + subst. simpl in H0. inversion H0.
      + inversion H4.
  * simpl. eapply eval_single, eval_lit.
  * simpl. eapply eval_single, eval_var. reflexivity.
Qed.

Example case_eval2 :
  |[(inl "X", VEmptyTuple)], 0,
   ECase (EVar "X") 
         [([PLit (Integer 5)], ^ELit (Atom "true"), ^ELit (Integer 5)); 
          ([PLit (Integer 6)], ^ELit (Atom "true"), ^ELit (Integer 6));
          ([PVar "Z"], ^ELit (Atom "false"), ^EVar "Z");
          ([PVar "Z"], ^ELit (Atom "true"), ^EEmptyMap)]

  , []|
-e> 
  | 0, inl [VEmptyMap], []|.
Proof.
  eapply eval_single, eval_case with (i := 3); auto.
  * apply eval_single, eval_var. reflexivity.
  * reflexivity.
  * intros. simpl in *. inversion H.
    - subst. inversion H0. simpl. eapply eval_single, eval_lit.
    - inversion H2.
      + subst. simpl in *. inversion H0.
      + inversion H4.
        ** subst. simpl in H0. inversion H0.
        ** inversion H6.
  * simpl. eapply eval_single, eval_lit.
  * simpl. eapply eval_single, eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
    - intros. inversion H.
    - intros. inversion H.
    - reflexivity.
    - reflexivity.
Qed.

Example case_eval_fun : 
  |[(inl "X", VClos [(inl "Y", ttrue)] [] 0 [] (EVar "Y")); (inl "Y", ttrue)], 1,
   ECase (EValues [EVar "X"; EVar "Y"])
         [([PLit (Integer 5); PLit (Atom "true")], ^ELit (Atom "true"), ^ELit (Integer 5)); 
          ([PLit (Integer 6); PLit (Atom "true")], ^ELit (Atom "true"), ^ELit (Integer 6)); 
          ([PVar "Z"; PLit (Atom "true")], ^ELit (Atom "true"), ^EApp (EVar "Z") [])] 
  , []| 
-e> | 1, inl [ttrue], []|.
Proof.
  eapply eval_single, eval_case with (i := 2); auto.
  eapply eval_values with (vals := [VClos [(inl "Y", ttrue)] [] 0 [] (EVar "Y"); ttrue]) (eff := [[];[]]) (ids := [1;1]); auto.
  * intros. inversion H.
    - subst. simpl. eapply eval_var. reflexivity.
    - inversion H1.
      + eapply eval_var. reflexivity.
      + inversion H3.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. simpl in H0. inversion H0.
    - inversion H2.
      ++ subst. simpl in H0. inversion H0.
      ++ inversion H4.
  * simpl. eapply eval_single, eval_lit.
  * simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (n := 0)
                                  (ref := [(inl "Y", ttrue)]) 
                                  (ext := []) (body := (EVar "Y"))
                                  (eff := []) (ids := []); auto.
   - apply eval_single, eval_var. reflexivity.
   - intros. inversion H.
   - simpl. apply eval_single, eval_var. reflexivity.
Qed.


Example letrec_eval : 
  |[(inr ("fun4", 0), VClos [] [(0, ("fun4", 0), ([], ^EEmptyMap))] 0 [] (EEmptyMap)) ; 
    (inl "X", VLit (Integer 42))], 1,
   ELetRec [(("fun2", 0), ([], ^EVar "X")); 
            (("fun4", 1), (["Z"], ^EVar "Z"))] 
     (EApp (EFunId ("fun4", 0)) []), []|
-e>
  | 3, inl [VEmptyMap], []|.
Proof.
  eapply eval_single, eval_letrec; try (reflexivity).
  * simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (body := (EEmptyMap)) 
                                  (ref := []) (eff := []) (n := 0) (ids := [])
                                  (ext := [(0, ("fun4", 0), ([], ^EEmptyMap))]); auto.
    - apply eval_single,  eval_funid. reflexivity.
    - simpl. intros. inversion H.
    - eapply eval_single, eval_map with (kvals := []) (vvals := []) (eff := []) (ids := []); auto.
      + intros. inversion H.
      + intros. inversion H. 
      + reflexivity.
      + reflexivity.
Qed.


Example unnamed_eval : 
  |[(inl "X", VLit (Integer 5))], 0,
   EApp (EFun ["Y"] (EVar "Y")) [^EVar "X"], []|
-e> 
  | 1, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_app with (vals := [VLit (Integer 5)]) 
                         (var_list := ["Y"]) (ids := [1])
                         (body := (EVar "Y")) 
                         (ref := [(inl "X", VLit (Integer 5))]) 
                         (ext := []) (eff := [[]]); auto.
  * apply eval_single, eval_fun.
  * intros. inversion H; inversion H1. apply eval_single, eval_var. reflexivity.
  * simpl. apply eval_single, eval_var. reflexivity.
Qed.


Section B_Core.

Definition B : ErlModule := ErlMod "b" [
  TopLevelFun ("fun1", 0) [] (ELit (Integer 6)) ;
  TopLevelFun ("fun2", 0) [] (ELet ["X"] (EFun [] (ELit (Integer 5))) (
                                         ELet ["X"] (EFun [] (ELit (Integer 6)))
                                           (EApp (EVar "X") [])) )
].


Example fun2 : 
  |[], 0,
   ELet ["X"] (EFun [] (ELit (Integer 5))) 
     (ELet ["X"] (EFun [] (ELit (Integer 6))) 
       (EApp (EVar "X") [])), []|
-e>
  | 2, inl [VLit (Integer 6)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_fun.
  * reflexivity.
  * simpl. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                    (body := (ELit (Integer 6))) 
                                    (ref := [(inl "X", VClos [] [] 0 [] (ELit (Integer 5)))]) (n := 1)
                                    (ext := []) (eff := []); auto.
      + apply eval_single, eval_var. reflexivity.
      + intros. inversion H.
      + apply eval_single, eval_lit.
Qed.

(* Compute initialize_proving B.

Compute initialize_proving_closures B. *)

End B_Core.

Section Documentation_Examples.

Example ex1 : 
  |[], 0, ELet ["X"] (ELit (Integer 5)) (EVar "X"), []|
-e>
  | 0, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * simpl. apply eval_single, eval_var. reflexivity.
Qed.

(* Example ex2 : 
  |[], 0,
   ELet [("X", EFun [] (EApp (EVar "X") []))] 
     (EApp (EVar "X") []), []|
-e>
  | 1, inr novar, []|.
Proof.
  eapply eval_let with (vals := [VClos [] [] 0 [] (EApp ( EVar "X") [])])
                       (eff := [[]]) (ids := [1]); auto.
  * intros. inversion H.
    - subst. apply eval_fun.
    - inversion H1.
  * simpl. eapply eval_app with (vals := []) (var_list := []) (ids := [])
                                  (body := (EApp (EVar "X") [])) 
                                  (ref := []) (ext := []) (n := 0) (eff := []); auto.
    - apply eval_var. reflexivity.
    - intros. inversion H.
    - simpl. eapply eval_app_ex_closure_ex; auto.
      + reflexivity.
      + apply eval_var. reflexivity.
Qed. *)

Example ex3 :
  |[], 0, ELetRec [(("X", 0), ([], ^EApp (EFunId ("X", 0)) []))] 
            (EApp (EFunId ("X", 0)) []), []|
-e>
  |1, inl [VEmptyTuple], []|.
Proof.
  eapply eval_single, eval_letrec; try (reflexivity).
  * simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ref := []) (n := 0) (eff := [])
                                  (body := (EApp (EFunId ("X", 0)) [])) (ids := [])
                                  (ext := [(0, ("X", 0), ([], ^EApp (EFunId ("X", 0)) []))]); 
        try (reflexivity).
    - apply eval_single, eval_funid. reflexivity.
    - intros. inversion H.
    - simpl. eapply eval_single, eval_app with (vals := []) (n := 0) (var_list := []) (ref := []) (eff := [])
                                    (body := (EApp (EFunId ("X", 0)) [])) (ids := [])
                                    (ext := [(0, ("X", 0), ([], ^EApp (EFunId ("X", 0)) []))]); 
         try (reflexivity).
      + apply eval_single, eval_funid. reflexivity.
      + intros. inversion H.
      + simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (n := 0) (ref := []) (eff := [])
                                      (body := (EApp (EFunId ("X", 0)) [])) (ids := [])
                                      (ext := [(0, ("X", 0), 
                                               ([], ^EApp (EFunId ("X", 0)) []))]); 
             try (reflexivity).
        ** apply eval_single, eval_funid. reflexivity.
        ** intros. inversion H.
        ** simpl. eapply eval_single, eval_app.
Admitted.

Example ex4 : 
|[], 0, ELet ["X"] (ELit (Integer 4)) 
          (ELet ["X"] (EFun [] (EVar "X")) 
             (ELet ["X"] (EFun [] (EApp (EVar "X") []))
                (EApp (EVar "X") []))), []|
-e>
  |2, inl [VLit (Integer 4)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * simpl. eapply eval_single, eval_let; auto.
    - apply eval_single, eval_fun.
    - reflexivity.
    - simpl. eapply eval_single, eval_let; auto.
       + apply eval_single, eval_fun.
       + reflexivity.
       + simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                       (body := EApp (EVar "X") []) 
                                       (ref := [(inl "X",
                                                 VClos [(inl "X", VLit (Integer 4))] [] 0 []
                                                   (EVar "X"))]) (n := 1)
                                       (ext := []) (eff := []); auto.
         ** apply eval_single, eval_var. reflexivity.
         ** intros. inversion H.
         ** simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                          (body := EVar "X") 
                                          (ref := [(inl "X", VLit (Integer 4))]) (n := 0)
                                          (ext := []) (eff := []); auto.
           -- apply eval_single, eval_var. reflexivity.
           -- intros. inversion H.
           -- apply eval_single, eval_var. reflexivity.
Qed.

End Documentation_Examples.

Example returned_function :
  |[], 0,
   ELet ["X"] (EFun [] (EFun [] (ELit (Integer 5))))
     (EApp (EApp (EVar "X") []) []), []|
-e>
  | 2, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_fun.
  * reflexivity.
  * simpl. eapply eval_single, eval_app with (vals := []) (ref := []) (ext := []) (eff := [])
                                  (body := ELit (Integer 5)) (var_list := []) (ids := []); auto.
    - eapply eval_single, eval_app with (vals := []) (var_list := []) (n := 0) (ids := [])
                             (body := EFun [] (ELit (Integer 5))) 
                             (ref := []) (ext := []) (eff := []); auto.
      + apply eval_single, eval_var. reflexivity.
      + intros. inversion H.
      + simpl. apply eval_single, eval_fun.
    - intros. inversion H.
    - apply eval_single, eval_lit.
Qed.

Example returned_recursive_function : 
  |[], 0,
   ELetRec [(("fun1", 0), ([], (^EFun [] (ELit (Integer 5)))))] 
     (EApp (EApp (EFunId ("fun1", 0)) []) []), []|
-e>
  | 2, inl [VLit (Integer 5)], []|.
Proof.
  eapply eval_single, eval_letrec; try (reflexivity).
  * simpl. eapply eval_single, eval_app with (vals := []) (ref := [(inr ("fun1", 0),
                                                         VClos [] [(0, ("fun1", 0), ([], 
                                                            ^EFun [] (ELit (Integer 5))))] 0 []
                                                            (EFun [] (ELit (Integer 5))))]) 
                                  (ext := []) (body := ELit (Integer 5)) (ids := [])
                                  (var_list := []) (eff := []); try (reflexivity).
    - eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                             (body := EFun [] (ELit (Integer 5))) 
                             (ref := []) (eff := []) (n := 0)
                             (ext := [(0, ("fun1", 0), ([], ^EFun [] (ELit (Integer 5))))]);
          try (reflexivity).
      + apply eval_single, eval_funid. reflexivity.
      + intros. inversion H.
      + simpl. apply eval_single, eval_fun with (id := 1).
    - intros. inversion H.
    - apply eval_single, eval_lit.
Qed.

Example returned_function2 :
  |[(inl "X", VLit (Integer 7))], 0,
   ELet ["X"] (EFun [] (EFun [] (EVar "X")))
     (EApp (EApp (EVar "X") []) []), []|
-e>
  | 2, inl [VLit (Integer 7)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_fun.
  * reflexivity.
  * simpl. eapply eval_single, eval_app with (vals := []) (ids := []) (ref := [(inl "X", VLit (Integer 7))]) 
                                 (ext := []) (body := EVar "X") (var_list := []) (eff := []) (n := 1); auto.
    - eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                             (body := EFun [] (EVar "X")) 
                             (ref := [(inl "X", VLit (Integer 7))]) 
                             (ext := []) (n := 0) (eff := []); auto.
      + apply eval_single, eval_var. reflexivity.
      + intros. inversion H.
      + simpl. apply eval_single, eval_fun.
    - intros. inversion H.
    - simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example returned_recursive_function2 :
  |[(inl "X", VLit (Integer 7))], 0,
   ELetRec [(("fun1", 0), ([], ^EFun [] (EVar "X")))] 
     (EApp (EApp (EFunId ("fun1", 0)) []) []), []|
-e>
  | 2, inl [VLit (Integer 7)], []|.
Proof.
  eapply eval_single, eval_letrec; try (reflexivity).
  * simpl. eapply eval_single, eval_app with (vals := []) (eff := []) (ids := [])
                                 (ref := [(inl "X", VLit (Integer 7)) ; 
                                          (inr ("fun1", 0),
                                             VClos [(inl "X", VLit (Integer 7))] 
                                                      [(0, ("fun1", 0), 
                                                          ([], ^EFun [] (EVar "X")))] 
                                                      0 [] 
                                                      (EFun [] (EVar "X")))]) 
                                 (body := EVar "X") (n := 1)
                                 (var_list := []) (ext := []); try (reflexivity).
    - eapply eval_single, eval_app with (vals := []) (var_list := []) (eff := []) (ids := [])
                             (body := EFun [] (EVar "X")) (n := 0)
                             (ref := [(inl "X", VLit (Integer 7))]) 
                             (ext := [(0, ("fun1", 0), ([], ^EFun [] (EVar "X")))]); 
          try (reflexivity).
      + apply eval_single, eval_funid. reflexivity.
      + intros. inversion H.
      + simpl. apply eval_single, eval_fun.
    - intros. inversion H.
    - simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example returned_function3 : 
  |[], 0,
   ELet ["F"] 
     (EFun ["X"] 
        (ELet ["Y"] (ECall "+" [^EVar "X"; ^ELit (Integer 3)] ) 
              (EFun ["Z"] 
                    (ECall "+" 
                          [^ECall "+" [^EVar "X"; ^EVar "Y"]
                     ; ^EVar "Z"]))))
  (EApp (EApp (EVar "F") [^ELit (Integer 1)]) [^ELit (Integer 1)]), []|
-e>
  |2, inl [VLit (Integer 6)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_fun.
  * reflexivity.
  * eapply eval_single, eval_app with (var_list := ["Z"]) (eff := [[]]) (ids := [2])
                                  (body := (ECall "+"
                                              [^ECall "+"
                                                 [^EVar "X"; ^EVar "Y"];
                                              ^EVar "Z"]))
                                  (ref := [(inl "X", VLit (Integer 1)); 
                                           (inl "Y", VLit (Integer 4))])
                                  (ext := []) (vals := [VLit (Integer 1)]) (n := 1); auto.
    - eapply eval_single, eval_app with (vals := [VLit (Integer 1)]) (var_list := ["X"]) (ids := [1])
                             (body := ELet ["Y"]
                                        (ECall "+"
                                           [^EVar "X"; ^ELit (Integer 3)] )
                                        (EFun ["Z"]
                                           (ECall "+"
                                              [^ECall "+"
                                                 [^EVar "X"; ^EVar "Y"];
                                              ^EVar "Z"]))) 
                             (ref := []) (ext := []) (eff := [[]]) (n := 0); auto.
      + apply eval_single, eval_var. reflexivity.
      + intros. inversion H; inversion H1. apply eval_single, eval_lit.
      + eapply eval_single, eval_let; auto.
        ** apply eval_single, eval_call with (vals := [VLit (Integer 1); VLit (Integer 3)])
                                (eff := [[];[]]) (ids := [1;1]); auto.
          -- intros. inversion H.
            ++ apply eval_single, eval_lit.
            ++ inversion H1; inversion H3. apply eval_single, eval_var. reflexivity.
          -- reflexivity.
        ** reflexivity.
        ** simpl. apply eval_single, eval_fun.
    - intros. inversion H; inversion H1. simpl. apply eval_single, eval_lit.
    - eapply eval_single, eval_call with (vals := [VLit (Integer 5) ; VLit (Integer 1)])
                            (eff := [[];[]]) (ids := [2;2]); auto.
      + intros. inversion H.
        ** inversion H1. apply eval_single, eval_var. reflexivity.
        ** inversion H1.
          -- eapply eval_single, eval_call with (vals := [VLit (Integer 1) ; VLit (Integer 4)])
                                               (eff := [[];[]]) (ids := [2;2]); auto.
            ++ intros. inversion H2.
              *** apply eval_single, eval_var. reflexivity.
              *** inversion H5; inversion H7. apply eval_single, eval_var. reflexivity.
          -- simpl. inversion H3.
Qed.

Example sum :
  | [], 0,
    ELetRec [(("f", 1), (["X"], 
      
      ^ECase (EVar "X") [([PLit (Integer 0)], ^ELit (Atom "true"), ^ELit (Integer 0)); 
                               ([PVar "Y"], ^ELit (Atom "true"), 
                               ^ECall "+" [
                                     ^EVar "Y"; 
                                     ^EApp (EFunId ("f", 1)) [ ^ECall "+" [^EVar "Y"; ^ELit (Integer (Z.pred 0))] ]
                              ])]
      ))] (EApp (EFunId ("f", 1)) [^ELit (Integer 2)]), []| -e> |1, inl [VLit (Integer 3)], []|.
Proof.
  eapply eval_single, eval_letrec; auto.
  * simpl. eapply eval_single, eval_app with (vals := [VLit (Integer 2)]) (eff := [[]]) (eff2 := []) (n := 0)
                                  (var_list := ["X"]) (ref := []) (ids := [1]); simpl; auto.
    - apply eval_single, eval_funid. reflexivity.
    - intros. inversion H. 
      + apply eval_single, eval_lit.
      + inversion H1.
    - simpl. eapply eval_single, eval_case with (i := 1); auto.
      + eapply eval_single, eval_var. reflexivity.
      + simpl. reflexivity.
      + intros. inversion H. 
        ** subst. simpl in H0. inversion H0.
        ** inversion H2. 
      + simpl. apply eval_single, eval_lit.
      + simpl. eapply eval_single, eval_call with (vals := [VLit (Integer 2); VLit (Integer 1)]) 
                              (eff := [[]; []]) (ids := [1;1]); auto.
        ** intros. inversion H. 
          -- simpl. eapply eval_single, eval_app with (vals := [VLit (Integer 1)]) (eff := [[]]) (eff2 := [])
                                  (var_list := ["X"]) (ref := []) (ids := [1]); simpl; auto.
            ++ apply eval_single, eval_funid. reflexivity.
            ++ intros. inversion H0. subst.
               eapply eval_single, eval_call with (vals := [VLit (Integer 2); VLit (Integer (-1))])
                                     (eff := [[];[]]) (ids := [1;1]); auto.
              *** simpl. intros. inversion H1. 
                --- apply eval_single, eval_lit.
                --- inversion H3.
                  +++ apply eval_single, eval_var. reflexivity.
                  +++ inversion H5.
              *** inversion H3.
            ++ {
            eapply eval_single, eval_case with (i := 1); auto.
              + eapply eval_single, eval_var. reflexivity. 
              + simpl. reflexivity.
              + simpl. intros. inversion H0.
                * subst. simpl in H2. inversion H2.
                * inversion H4.
              + simpl. apply eval_single, eval_lit.
              + subst. simpl. eapply eval_single, eval_call with (vals := [VLit (Integer 1); VLit (Integer (0))])
                                                    (eff := [[];[]]) (ids := [1;1]); auto.
                * simpl. intros. inversion H0. 
                  - subst. simpl. eapply eval_single, eval_app with (vals := [VLit (Integer 0)]) (eff := [[]]) (eff2 := [])
                                  (var_list := ["X"]) (ref := []) (n := 0) (ids := [1]); simpl; auto.
                  ** apply eval_single, eval_funid. reflexivity.
                  ** intros. inversion H1.
                    -- subst. simpl.
                     eapply eval_single, eval_call with (vals := [VLit (Integer 1); VLit (Integer (-1))])
                                           (eff := [[];[]]) (ids := [1;1]); auto.
                      intros. inversion H2.
                      ++ subst. simpl. eapply eval_single, eval_lit.
                      ++ inversion H4.
                        *** subst. simpl. eapply eval_single, eval_var. reflexivity.
                        *** inversion H6.
                    -- inversion H3.
                  ** simpl. eapply eval_single, eval_case with (i := 0); auto.
                    -- eapply eval_single, eval_var. reflexivity.
                    -- simpl. lia.
                    -- simpl. reflexivity.
                    -- intros. inversion H1.
                    -- simpl. eapply eval_single, eval_lit.
                    -- simpl. eapply eval_single, eval_lit.
              - inversion H2.
               ** subst. simpl. apply eval_single, eval_var. reflexivity.
               ** inversion H4.
            }
          -- simpl. inversion H1.
           ++ apply eval_single, eval_var. reflexivity.
           ++ inversion H3.
Qed.

Example letrec_no_replace :
  |[], 0,
   ELet ["X"] (ELit (Integer 42)) 
     (ELetRec [(("f", 0), ([], ^EVar "X"))]
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EFunId ("f", 0)) []))), []|
-e>
  | 1, inl [VLit (Integer 42)], []|.
Proof.
  eapply eval_single, eval_let; auto.
  * apply eval_single, eval_lit.
  * reflexivity.
  * simpl. eapply eval_single, eval_letrec; auto.
    - eapply eval_single, eval_let; auto.
      + apply eval_single, eval_lit.
      + reflexivity.
      + simpl. eapply eval_single, eval_app with (vals := []) (var_list := []) (ids := [])
                                      (body := (EVar "X")) 
                                      (ref := [(inl "X", VLit (Integer 42))]) 
                                      (ext := [(0, ("f", 0), ([], ^EVar "X"))])
                                      (eff := []) (n := 0); auto.
        ** apply eval_single, eval_funid. reflexivity.
        ** intros. inversion H.
        ** simpl. apply eval_single, eval_var. reflexivity.
Qed.

Example seq_eval1 :
  | [], 0, ESeq (ELet ["X"] (ELit (Integer 42)) (EVar "X"))
                (ELet ["Y"] (ELit (Integer 20)) (EVar "Y"))
   , [] |
-e>
  | 0, inl [VLit (Integer 20)], [] |.
Proof.
  eapply eval_single, eval_seq; auto.
  * eapply eval_single, eval_let; auto.
    - apply eval_single, eval_lit.
    - reflexivity.
    - apply eval_single, eval_var. reflexivity.
  * eapply eval_single, eval_let; auto.
    - apply eval_single, eval_lit.
    - reflexivity.
    - apply eval_single, eval_var. reflexivity.
Qed.

End Tests.