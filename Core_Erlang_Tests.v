Load Core_Erlang_Semantics.

Module Core_Erlang_Tests.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Helpers.
Import Core_Erlang_Side_Effects.

(** This is an edless recursion *)
Example eval_letrec1 : 
  |[], ELetrec [("x"%string, 1)] [["X"%string]] 
         [EApply (EFunId ("x"%string, 1)) [EVar "X"%string]] 
            (EApply (EFunId ("x"%string, 1)) [EEmptyTuple]), []|
-e> 
  |inl ErrorValue, []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := [VEmptyTuple]) 
                                  (body := (EApply (EFunId ("x"%string, 1)) [EVar "X"%string])) (n := 0)
                                  (var_list := ["X"%string]) 
                                  (ref := []) 
                                  (ext := [("x"%string, 1, 
                                        (["X"%string], EApply (EFunId ("x"%string, 1)) [EVar "X"%string]))]) 
                                  (eff := [[]]); try (reflexivity).
    - apply eval_funid.
    - intros. inversion H.
      + simpl. apply eval_tuple with (eff := []); try(reflexivity). 
        ** intros. inversion H0.
      + inversion H1.
    - simpl. reflexivity.
    - eapply eval_apply with (vals := [VEmptyTuple]) 
                             (body := (EApply (EFunId ("x"%string, 1)) [EVar "X"%string])) 
                             (var_list := ["X"%string]) 
                             (ref := []) 
                             (ext := [("x"%string, 1,
                                     (["X"%string], EApply (EFunId ("x"%string, 1)) [EVar "X"%string]))]) (n := 0)
                             (eff := [[]]); try (reflexivity).
    + apply eval_funid.
    + intros. inversion H.
      ** apply eval_var.
      ** inversion H1.
    + simpl. reflexivity.
    + eapply eval_apply with (vals := [VEmptyTuple]) 
                             (body := (EApply (EFunId ("x"%string, 1)) [EVar "X"%string])) (n := 0)
                             (var_list := ["X"%string]) 
                             (ref := []) 
                             (ext := [("x"%string, 1, 
                                     (["X"%string], EApply (EFunId ("x"%string, 1)) [EVar "X"%string]))]) 
                             (eff := [[]]); try (reflexivity).
Admitted.

(* This is not accepted by the compiler in Core Erlang *)
Example eval_letrec2 : 
  |[], ELet ["F"%string] [EFun ["X"%string] 
         (EApply (EVar "F"%string) [EVar "X"%string])] 
            (EApply (EVar "F"%string) [EEmptyTuple]), []| 
-e>
|inr novar, []|.
Proof.
  eapply eval_let with (vals := [VClosure [] [] 0 ["X"%string] (EApply (EVar "F"%string) [EVar "X"%string])]) 
                       (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := [VEmptyTuple]) (n := 0)
                                  (var_list := ["X"%string]) 
                                  (body := (EApply (EVar "F"%string) [EVar "X"%string])) 
                                  (ref := []) (ext := []) (eff := [[]]); auto.
    - apply eval_var.
    - intros. inversion H.
      + eapply eval_tuple with (eff := []); auto.
        ** intros. inversion H0.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_apply_ex_closure_ex.
      + reflexivity.
      + apply eval_var.
Qed.

(* Top level functions, and their closures must be added initially *)
Example multiple_top_level_funs : |[(inr ("fun1"%string, 0), VClosure [] [
    (("fun1"%string, 0), ([], (EApply (EFunId ("fun3"%string, 0)) [])));
    (("fun2"%string, 0), ([], (ELiteral (Integer 42))));
    (("fun3"%string, 0), ([], (EApply (EFunId ("fun2"%string, 0)) [])))
  ] 0 [] (EApply (EFunId ("fun3"%string, 0)) [])) ; 
                                      (inr ("fun2"%string, 0), VClosure [] [
    (("fun1"%string, 0), ([], (EApply (EFunId ("fun3"%string, 0)) [])));
    (("fun2"%string, 0), ([], (ELiteral (Integer 42))));
    (("fun3"%string, 0), ([], (EApply (EFunId ("fun2"%string, 0)) [])))
  ] 1 [] (ELiteral (Integer 42))) ;
                                      (inr ("fun3"%string, 0), VClosure [] [
    (("fun1"%string, 0), ([], (EApply (EFunId ("fun3"%string, 0)) [])));
    (("fun2"%string, 0), ([], (ELiteral (Integer 42))));
    (("fun3"%string, 0), ([], (EApply (EFunId ("fun2"%string, 0)) [])))
  ] 2 [] (EApply (EFunId ("fun2"%string, 0)) []))]
                                      , EApply (EFunId ("fun1"%string,0)) [], []| 
-e> 
  |inl (VLiteral (Integer 42)), []|.
Proof.
  remember [
  (("fun1"%string, 0), ([], (EApply (EFunId ("fun3"%string, 0)) [])));
  (("fun2"%string, 0), ([], (ELiteral (Integer 42))));
  (("fun3"%string, 0), ([], (EApply (EFunId ("fun2"%string, 0)) [])))
] as ext.
  eapply eval_apply with (vals := []) (ref := []) (ext := ext) (eff := [])
                         (body := (EApply (EFunId ("fun3"%string, 0)) [])) 
                         (var_list := []) (n := 0); auto.
  * apply eval_funid.
  * simpl. intros. inversion H.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (n := 2) (ref := []) (ext := ext) (eff := [])
                                 (body := (EApply (EFunId ("fun2"%string, 0)) [])) 
                                 (var_list := []); auto.
    - rewrite Heqext. simpl. apply eval_funid.
    - intros. inversion H.
    - simpl. reflexivity.
    - simpl. eapply eval_apply with (vals := []) (n := 1) (ref := []) (ext := ext) (eff := [])
                                    (body := (ELiteral (Integer 42))) (var_list := []); auto.
      + rewrite Heqext. apply eval_funid.
      + intros. inversion H.
      + reflexivity.
      + apply eval_lit.
Qed.

Example weird_apply : |[], ELetrec [("f"%string, 1)] [["X"%string]]
   [ECase (EVar "X"%string)
          [PLiteral (Integer 0) ; PLiteral (Integer 1); PVar "X"%string]
          [ELiteral (Atom "true"%string); ELiteral (Atom "true"%string); ELiteral (Atom "true"%string)]
          [ELiteral (Integer 5);
           EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
           EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]
          ]
   ]
   (ELet ["X"%string] [EFun ["F"%string]
       (ELetrec [("f"%string, 1)] [["X"%string]] [ELiteral (Integer 0)] 
          (EApply (EVar "F"%string) [ELiteral (Integer 2)])
       )
     ]
    (EApply (EVar "X"%string) [EFunId ("f"%string, 1)])
   ), []|
-e> 
  |inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_letrec; auto.
  simpl. eapply eval_let with (vals := [
 VClosure 
  [(inr ("f"%string, 1),
   VClosure []
     [("f"%string, 1,
      (["X"%string],
      ECase (EVar "X"%string)
        [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
        EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))] 0 ["X"%string]
     (ECase (EVar "X"%string)
        [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
        EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))
  ]
  [] 1
  ["F"%string]
  (ELetrec [("f"%string, 1)] [["X"%string]] [ELiteral (Integer 0)]
        (EApply (EVar "F"%string) [ELiteral (Integer 2)]))
 ]
  ) (eff := [[]]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * simpl. eapply eval_apply with (var_list := ["F"%string]) (n := 1) (eff := [[]])
  (vals := [VClosure []
     [("f"%string, 1,
      (["X"%string],
      ECase (EVar "X"%string)
        [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
        EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))] 0 ["X"%string]
     (ECase (EVar "X"%string)
        [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
        EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]])])
  (body := (ELetrec [("f"%string, 1)] [["X"%string]] [ELiteral (Integer 0)]
       (EApply (EVar "F"%string) [ELiteral (Integer 2)])))
  (ref := [(inr ("f"%string, 1),
     VClosure []
       [("f"%string, 1,
        (["X"%string],
        ECase (EVar "X"%string)
          [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
          [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
          [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
          EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))] 0 ["X"%string]
       (ECase (EVar "X"%string)
          [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
          [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
          [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
          EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))])
  (ext := []); auto.
    - apply eval_var.
    - intros. inversion H; inversion H1. apply eval_funid.
    - simpl. eapply eval_letrec; auto. simpl.
      eapply eval_apply with (var_list := ["X"%string]) (eff := [[]])
        (vals := [VLiteral (Integer 2)])
        (ref := []) (n := 0)
        (body := (ECase (EVar "X"%string)
       [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
       [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
       [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
       EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))
        (ext := [("f"%string, 1,
     (["X"%string],
     ECase (EVar "X"%string)
       [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
       [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
       [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
       EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))]); auto.
      + apply eval_var.
      + intros. inversion H; inversion H1. apply eval_lit.
      + simpl. eapply eval_case with (i := 2) (v := VLiteral (Integer 2)); auto.
        ** apply eval_var.
        ** simpl. reflexivity.
        ** intros. inversion H.
          -- subst. inversion H0.
          -- inversion H2.
            ++ subst. inversion H0.
            ++ inversion H4.
        ** simpl. apply eval_lit.
        ** simpl. eapply eval_apply with (var_list := ["X"%string])
                     (eff := [[]]) (n := 0)
                     (vals := [VLiteral (Integer 1)])
                     (body := (ECase (EVar "X"%string)
                                [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
                                [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
                                [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
                                EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))
                     (ref := [])
                     (ext := [("f"%string, 1,
                              (["X"%string],
                              ECase (EVar "X"%string)
                                [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
                                [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
                                [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
                                EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))]); auto.
         -- apply eval_funid.
         -- intros. inversion H; inversion H1. apply eval_lit.
         -- simpl. eapply eval_case with (i := 1) (v := VLiteral (Integer 1)); auto.
           ++ apply eval_var.
           ++ simpl. auto.
           ++ simpl. reflexivity.
           ++ intros. inversion H.
             *** subst. inversion H0.
             *** inversion H2.
           ++ simpl. apply eval_lit.
           ++ eapply eval_apply with (var_list := ["X"%string])
                     (vals := [VLiteral (Integer 0)])
                     (eff := [[]]) (n := 0)
                     (body := (ECase (EVar "X"%string)
                                [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
                                [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
                                [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
                                EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))
                     (ref := [])
                     (ext := [("f"%string, 1,
                              (["X"%string],
                              ECase (EVar "X"%string)
                                [PLiteral (Integer 0); PLiteral (Integer 1); PVar "X"%string]
                                [ELiteral (Atom "true"); ELiteral (Atom "true"); ELiteral (Atom "true")]
                                [ELiteral (Integer 5); EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 0)];
                                EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 1)]]))]); auto.
             *** simpl. apply eval_funid.
             *** intros. inversion H; inversion H1. apply eval_lit.
             *** reflexivity.
             *** simpl. eapply eval_case with (i := 0) (v := VLiteral (Integer 0)); auto.
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
       VClosure [] [(("fun2"%string, 0),([],  (ELiteral (Integer 42)) ))] 0 [] (ELiteral (Integer 42)))],
  ELetrec [("fun2"%string, 0)] [[]] [ELiteral (Integer 40)] 
     (EApply (EFunId ("fun2"%string, 0)) []), [] | 
-e>
  |inl (VLiteral (Integer 40)), []|.
Proof.
  eapply eval_letrec; auto.
  * simpl. eapply eval_apply with (vals := []) (eff := []) (n := 0)
                                  (ref := [(inr ("fun2"%string, 0), VClosure [] 
                                                                    [("fun2"%string, 0, 
                                                                    ([], ELiteral (Integer 42)))] 0 []
                                                                    (ELiteral (Integer 42)))]) 
                                  (ext := [(("fun2"%string, 0), ([],  (ELiteral (Integer 40)) ))]) 
                                  (body := (ELiteral (Integer 40))) (var_list := []); auto.
    - apply eval_funid.
    - intros. inversion H.
    - apply eval_lit.
  * reflexivity.
Qed.

Example top_no_overwrite : 
  |[(inr ("fun2"%string, 0), 
     VClosure [] [(("fun2"%string, 0), ([], ELiteral (Integer 42)))] 0 [] (ELiteral (Integer 42)))],
   ELetrec [("fun2"%string, 1)] [["X"%string]] [(ELiteral (Integer 40))] 
     (EApply (EFunId ("fun2"%string, 0)) []), [] |
-e> 
  |inl (VLiteral (Integer 42)), []|.
Proof.
  eapply eval_letrec; auto.
  * simpl. eapply eval_apply with (vals := []) (n := 0)
                                  (ref := [])
                                  (ext := [("fun2"%string, 0, ([], ELiteral (Integer 42)))]) 
                                  (body := ELiteral (Integer 42)) 
                                  (var_list := [])
                                  (eff := []); auto.
    - apply eval_funid.
    - intros. inversion H.
    - apply eval_lit.
  * reflexivity.
Qed.

(** This is not accepted by the compiler in Core Erlang *)
Example eval_let_func : 
  |[(inl "X"%string, VLiteral (Integer 42))], 
   ELet ["X"%string; "X"%string] [EFun [] (EEmptyList); EFun [] (EEmptyMap)] 
     (EEmptyMap), []| 
-e> 
  |inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [VClosure [(inl "X"%string, VLiteral (Integer 42))] [] 0 [] (EEmptyList); 
                                 VClosure [(inl "X"%string, VLiteral (Integer 42))] [] 0 [] (EEmptyMap)])
                       (eff := [[]; []]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
      + apply eval_fun.
      + inversion H3.
  * reflexivity.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

Example eval_let_apply : 
  |[(inl "X"%string, VLiteral (Integer 42))], 
   ELet ["Y"%string] [EFun [] (EVar "X"%string)] 
     (EApply (EVar "Y"%string) []), []| 
-e> 
  |inl (VLiteral (Integer 42)), []|.
Proof.
  eapply eval_let with (vals := [VClosure [(inl "X"%string, VLiteral (Integer 42))] [] 0 [] 
                                          (EVar "X"%string)])
                       (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (n := 0)
                                  (ref := [(inl "X"%string, VLiteral (Integer 42))]) 
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
  |[], ELet ["X"%string] [ELiteral (Integer 1)] 
         (ELet ["X"%string] [ELiteral (Integer 2)] 
            (EVar "X"%string)), []| 
-e> 
  |inl (VLiteral (Integer 2)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 1)]) (eff := [[]]); auto.
  * intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * simpl. reflexivity.
  * eapply eval_let with (vals := [VLiteral (Integer 2)]) (eff := [[]]); auto.
    - simpl. intros. inversion H.
      + apply eval_lit.
      + inversion H1.
    - reflexivity.
    - apply eval_var.
Qed.

Example let_eval_1 : 
  |[], ELet ["X"%string] [EEmptyTuple] (EEmptyMap), []|
-e>
  |inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [VEmptyTuple]) (eff := [[]]); auto.
  * intros. simpl in *. inversion H.
    - eapply eval_tuple with (eff := []); auto. intros. inversion H0.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

Example let_eval_2 : 
  |[(inl "X"%string, VEmptyMap)], ELet ["X"%string] [EEmptyTuple] (EEmptyMap), []| 
-e> 
  |inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [VEmptyTuple]) (eff := [[]]); auto.
  * intros. simpl in *. inversion H.
    - eapply eval_tuple with (eff := []); auto. intros. inversion H0.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

(** This shouldn't compile in Core Erlang *)
Example eval_let_3 : 
  |[(inl "X"%string, VEmptyMap)],
   ELet ["X"%string; "X"%string; "Y"%string] [EEmptyTuple; EEmptyList; EVar "X"%string] 
     (EVar "Y"%string), []|
-e>
  |inl (VEmptyMap), []|.
Proof.
  eapply eval_let with (vals := [(VEmptyTuple) ; (VEmptyList); (VEmptyMap)]) 
                       (eff := [[];[];[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_emptylist.
      + inversion H3.
        ** eapply eval_tuple with (eff := []); auto. intros. inversion H4.
        ** inversion H5.
  * reflexivity.
  * simpl. apply eval_var.
Qed.

Example let_eval_4 : 
  |[], ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string), []| 
-e> 
  | inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
  * intros. simpl in *. inversion H.
    - apply eval_lit.
    - inversion H1.
  * reflexivity.
  * simpl. apply eval_var.
Qed.

Example tuple_eval : 
  |[(inl "X"%string, VLiteral (Atom "asd"%string)); 
    (inl "Y"%string, VEmptyTuple)], 
   ETuple [ELiteral (Integer 5); EVar "X"%string; EVar "Y"%string], []| 
-e>
  |inl (VTuple [VLiteral (Integer 5); VLiteral (Atom "asd"%string); VEmptyTuple]), []|.
Proof.
  eapply eval_tuple with (eff := [[];[];[]]); auto.
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
       VClosure [] [(("Plus"%string, 2),
                     (["X"%string ; "Y"%string], ELiteral (Integer 3)))] 
                0 ["X"%string ; "Y"%string] 
                (ELiteral (Integer 3)))], 
   EApply (EFunId ("Plus"%string, 2)) [ELiteral (Integer 2); ELiteral (Integer 3)], []|
-e>
  |inl ((VLiteral (Integer 3))), []|.
Proof.
  eapply eval_apply with (vals := [VLiteral (Integer 2) ; VLiteral (Integer 3)])
                         (var_list := ["X"%string; "Y"%string]) 
                         (body := ELiteral (Integer 3)) 
                         (ref := []) (n := 0)
                         (ext := [(("Plus"%string, 2),
                                   (["X"%string ; "Y"%string], ELiteral (Integer 3)))])
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
      VClosure [] [] 0 ["X"%string; "Y"%string] (ELiteral (Integer 42))) ; 
    (inl "X"%string, VEmptyMap)], 
   EApply (EVar "Minus"%string) [EVar "X"%string; EVar "X"%string], []|
-e>
  |inl (VLiteral (Integer 42)), []|.
Proof.
  eapply eval_apply with (vals := [VEmptyMap; VEmptyMap]) 
                         (var_list := ["X"%string; "Y"%string]) 
                         (body := (ELiteral (Integer 42))) (n := 0)
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
  |[(inl "X"%string, VLiteral (Integer 5))],
   EList (EVar "X"%string) (EEmptyList), []| 
-e>
  | inl (VList (VLiteral (Integer 5)) (VEmptyList)), []|.
Proof.
  eapply eval_list.
  * instantiate (1 := []). rewrite app_nil_r. reflexivity.
  * apply eval_emptylist.
  * apply eval_var.
Qed.

Example list_eval2 : 
  |[(inl "X"%string, VLiteral (Integer 5))], 
   EList (EVar "X"%string) 
         (EList (EVar "X"%string) 
                (EEmptyList)), []| 
-e> 
  |inl (VList (VLiteral (Integer 5)) 
              (VList (VLiteral (Integer 5)) 
                     (VEmptyList))), []|.
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
  |[], ELet ["X"%string] [EFun [] (EEmptyTuple)] 
         (ELet ["X"%string] [ELiteral (Integer 5)] 
            (EVar "X"%string)), []|
-e>
  |inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VClosure [] [] 0 [] (EEmptyTuple)]) (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
    - simpl. intros. inversion H.
      + apply eval_lit.
      + inversion H1.
    - reflexivity.
    - simpl. apply eval_var.
Qed.

Example map_eval :
  |[(inl "X"%string, VLiteral (Integer 42))], 
    EMap [ELiteral (Integer 5)] [EVar "X"%string], []|
-e>
  |inl (VMap [VLiteral (Integer 5)] [VLiteral (Integer 42)]), []|.
Proof.
  eapply eval_map with (kvals := [VLiteral (Integer 5)]) (vvals := [VLiteral (Integer 42)]) 
                       (eff := [[];[]]); auto.
  * intros. inversion H.
    - subst. apply eval_lit.
    - inversion H1.
  * intros. inversion H.
    - apply eval_var.
    - inversion H1.
Qed.

Example map_eval2 : 
  |[(inl "X"%string, VLiteral (Integer 42))], 
   EMap [ELiteral (Integer 54); EVar "X"%string] 
        [EVar "X"%string; EVar "X"%string], []|
-e> 
  |inl (VMap [VLiteral (Integer 42); VLiteral (Integer 54)] 
             [VLiteral (Integer 42); VLiteral (Integer 42)]), []|.
Proof.
  eapply eval_map with (kvals := [VLiteral (Integer 54); VLiteral (Integer 42)])
                       (vvals := [VLiteral (Integer 42); VLiteral (Integer 42)])
                       (eff := [[];[];[];[]]); auto.
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
  |[(inl "X"%string, VLiteral (Integer 5))], 
   EMap [ELiteral (Integer 5); EVar "X"%string] 
        [EVar "X"%string; ECall "plus" 
                              [ELiteral (Integer 1); (EVar "X"%string)]], []| 
-e> 
  |inl (VMap [VLiteral (Integer 5)] [VLiteral (Integer 6)]), []|.
Proof.
  apply eval_map with (kvals := [VLiteral (Integer 5); VLiteral (Integer 5)])
                      (vvals := [VLiteral (Integer 5); VLiteral (Integer 6)])
                      (eff := [[];[];[];[]]); auto.
  * intros. inversion H.
    - apply eval_var.
    - inversion H1.
      + apply eval_lit.
      + inversion H3.
  * intros. inversion H.
    - eapply eval_call with (vals := [VLiteral (Integer 1); VLiteral (Integer 5)])
                            (eff := [[];[]]); auto.
      + intros. inversion H0.
        ** apply eval_var.
        ** inversion H3.
          -- apply eval_lit.
          -- inversion H5.
    - inversion H1.
      + simpl. apply eval_var.
      + inversion H3.
Qed.

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite :
  |[], 
   ELet ["X"%string] [ELiteral (Integer 42)] 
     (ELet ["Y"%string] [EFun ["X"%string] (EVar "X"%string)] 
       (ELet ["X"%string] [ELiteral (Integer 5)] 
         (EApply (EVar "Y"%string) [ELiteral (Integer 7)]))), []|
-e>
  |inl (VLiteral (Integer 7)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 42)]) (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_lit.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with 
             (vals := [VClosure [(inl "X"%string, VLiteral (Integer 42))] [] 
                          0 ["X"%string] (EVar "X"%string)])
             (eff := [[]]); auto.
    - simpl. intros. inversion H.
      + apply eval_fun.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      + simpl. intros. inversion H.
        ** apply eval_lit.
        ** inversion H1.
      + reflexivity.
      + simpl. eapply eval_apply with 
                    (vals := [VLiteral (Integer 7)]) (n := 0)
                    (ref := [(inl "X"%string, VLiteral (Integer 42))]) 
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
  |[],
   ELet ["X"%string] [ELiteral (Integer 42)] 
     (ELet ["Y"%string] [EFun [] (EVar "X"%string)] 
       (ELet ["X"%string] [ELiteral (Integer 5)] 
         (EApply (EVar "Y"%string) []))), []|
-e> 
  |inl (VLiteral (Integer 42)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 42)]) (eff := [[]]); auto.
  * intros. inversion H; inversion H1.
    - apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_let with 
               (vals := [VClosure [(inl "X"%string, VLiteral (Integer 42))] []
                            0 [] (EVar "X"%string)]) (eff := [[]]); auto.
    - intros. inversion H; inversion H1.
      + apply eval_fun.
    - reflexivity.
    - eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      + intros. inversion H; inversion H1.
        ** apply eval_lit.
      + reflexivity.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                      (body := (EVar "X"%string)) (n := 0)
                                      (ref := [(inl "X"%string, VLiteral (Integer 42))]) 
                                      (ext := []) (eff := []); auto.
        ** apply eval_var.
        ** intros. inversion H.
        ** reflexivity.
        ** apply eval_var.
Qed.

Example call_eval : 
  |[(inl "X"%string, VLiteral (Integer 5))], 
   ECall "plus"%string [EVar "X"%string ; ELiteral (Integer 2)], []|
-e> 
  |inl (VLiteral (Integer 7)), []|.
Proof.
  eapply eval_call with (vals := ([VLiteral (Integer 5) ; VLiteral (Integer 2)]))
                        (eff := [[];[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_lit.
    - inversion H1.
      + apply eval_var.
      + inversion H3.
Qed.

Example mutliple_function_let : 
  |[], 
   ELet ["Z"%string] [ECall "plus"%string [ELiteral (Integer 2) ; ELiteral (Integer 2)] ] 
     (ELet ["Y"%string] [EFun [] (EVar "Z"%string)] 
        (ELet ["X"%string] [EFun [] (EApply (EVar "Y"%string) [])] 
          (EApply (EVar "X"%string) []))), []|
-e>
  | inl (VLiteral (Integer 4)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 4)]) (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - eapply eval_call with (vals := [VLiteral (Integer 2); VLiteral (Integer 2)])
                            (eff := [[];[]]); auto.
      + simpl. intros. inversion H0.
        ** apply eval_lit.
        ** inversion H3.
          -- apply eval_lit.
          -- inversion H5.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VClosure [(inl "Z"%string, VLiteral (Integer 4))] [] 
                                             0 [] (EVar "Z"%string)])
                                (eff := [[]]); auto.
    - simpl. intros. inversion H.
      + apply eval_fun.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_let with 
              (vals := [VClosure [(inl "Z"%string, VLiteral (Integer 4));
                                    (inl "Y"%string,
                                    VClosure [(inl "Z"%string, VLiteral (Integer 4))] [] 0 []
                                      (EVar "Z"%string))] [] 1 [] (EApply (EVar "Y"%string) [])])
              (eff := [[]]); auto.
      + simpl. intros. inversion H.
        ** apply eval_fun.
        ** inversion H1.
      + reflexivity.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                      (body := (EApply (EVar "Y"%string) [])) 
                                      (ref := [(inl "Z"%string, VLiteral (Integer 4));
                                               (inl "Y"%string,
                                                VClosure [(inl "Z"%string, VLiteral (Integer 4))] 
                                                       [] 0 [] (EVar "Z"%string))])
                                      (ext := []) (n := 1)
                                      (eff := []); auto.
        ** simpl. apply eval_var.
        ** simpl. intros. inversion H.
        ** reflexivity.
        ** simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                         (body := (EVar "Z"%string)) (n := 0)
                                         (ref := [(inl "Z"%string, VLiteral (Integer 4))]) 
                                         (ext := []) (eff := []); auto.
          -- apply eval_var.
          -- intros. inversion H.
          -- reflexivity.
          -- simpl. apply eval_var.
Qed.

Example case_eval : 
  |[(inl "X"%string, VEmptyTuple)],
   ECase (EVar "X"%string)
         [(PLiteral (Integer 5)); (PLiteral (Integer 6)); (PVar "Z"%string) ]
         [(ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string))]
         [(ELiteral (Integer 5)); (ELiteral (Integer 6)); (EVar "Z"%string)], []| 
-e> 
  |inl (VEmptyTuple), []|.
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
  |[(inl "X"%string, VEmptyTuple)],
   ECase (EVar "X"%string) 
         [(PLiteral (Integer 5)); (PLiteral (Integer 6)); (PVar "Z"%string); (PVar "Z"%string)]
         [(ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string)); 
          (ELiteral (Atom "false"%string)); (ELiteral (Atom "true"%string))]
         [(ELiteral (Integer 5)); (ELiteral (Integer 6)); (EVar "Z"%string); (EEmptyMap)], []|
-e> 
  |inl (VEmptyMap), []|.
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
  * simpl. eapply eval_map with (kvals := []) (vvals := []) (eff := []); auto.
    - intros. inversion H.
    - intros. inversion H.
Qed.

Example case_eval_fun : 
  |[(inl "X"%string, VClosure [(inl "Y"%string, ttrue)] [] 0 [] (EVar "Y"%string))], 
   ECase (EVar "X"%string) 
         [(PLiteral (Integer 5)); (PLiteral (Integer 6)); (PVar "Z"%string)] 
         [(ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string)); (ELiteral (Atom "true"%string))] 
         [(ELiteral (Integer 5)); (ELiteral (Integer 6)); (EApply (EVar "Z"%string) [])], []| 
-e> |inl (ttrue), []|.
Proof.
  eapply eval_case with (i := 2) (v := VClosure [(inl "Y"%string, ttrue)] [] 0 [] (EVar "Y"%string)); auto.
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
                                  (eff := []); auto.
   - apply eval_var.
   - intros. inversion H.
   - reflexivity.
   - simpl. apply eval_var.
Qed.


Example letrec_eval : 
  |[(inr ("fun4"%string, 0), VClosure [] [(("fun4"%string, 0), ([], EEmptyMap))] 0 [] (EEmptyMap)) ; 
    (inl "X"%string, VLiteral (Integer 42))],
   ELetrec [("fun2"%string, 0); ("fun4"%string, 1)] [[]; ["Z"%string]] [(EVar "X"%string) ; (EVar "Z"%string)] 
     (EApply (EFunId ("fun4"%string, 0)) []), []|
-e>
  |inl (VEmptyMap), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (body := (EEmptyMap)) 
                                  (ref := []) (eff := []) (n := 0)
                                  (ext := [("fun4"%string, 0, ([], EEmptyMap))]); auto.
    - apply eval_funid.
    - simpl. intros. inversion H.
    - simpl. reflexivity.
    - eapply eval_map with (kvals := []) (vvals := []) (eff := []); auto.
      + intros. inversion H.
      + intros. inversion H.
Qed.


Example unnamed_eval : 
  |[(inl "X"%string, VLiteral (Integer 5))], 
   EApply (EFun ["Y"%string] (EVar "Y"%string)) [EVar "X"%string], []|
-e> 
  |inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_apply with (vals := [VLiteral (Integer 5)]) 
                         (var_list := ["Y"%string]) 
                         (body := (EVar "Y"%string)) 
                         (ref := [(inl "X"%string, VLiteral (Integer 5))]) 
                         (ext := []) (eff := [[]]); auto.
  * apply eval_fun.
  * intros. inversion H; inversion H1. apply eval_var.
  * reflexivity.
  * simpl. apply eval_var.
Qed.


Section B_Core.

Definition B : ErlModule := ErlMod "b"%string [
  TopLevelFun ("fun1"%string, 0) ([], (ELiteral (Integer 6))) ;
  TopLevelFun ("fun2"%string, 0) ([], (ELet ["X"%string] [(EFun [] (ELiteral (Integer 5)))] (
                                         ELet ["X"%string] [(EFun [] (ELiteral (Integer 6)))] 
                                           (EApply (EVar "X"%string) []))) )
].


Example fun2 : 
  |[], 
   ELet ["X"%string] [(EFun [] (ELiteral (Integer 5)))] 
     (ELet ["X"%string] [(EFun [] (ELiteral (Integer 6)))] 
       (EApply (EVar "X"%string) [])), []|
-e>
  | inl (VLiteral (Integer 6)), []|.
Proof.
  eapply eval_let with (vals := [VClosure [] [] 0 [] (ELiteral (Integer 5))]) (eff := [[]]); auto.
  * simpl. intros. inversion H.
    - apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VClosure [(inl "X"%string, 
                                             VClosure [] [] 0 [] (ELiteral (Integer 5)))] 
                                           [] 1 [] (ELiteral (Integer 6))])
                                (eff := [[]]); auto.
    - simpl. intros. inversion H.
      + apply eval_fun.
      + inversion H1.
    - reflexivity.
    - simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                    (body := (ELiteral (Integer 6))) 
                                    (ref := [(inl "X"%string, VClosure [] [] 0 [] (ELiteral (Integer 5)))]) (n := 1)
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
  |[], ELet ["X"%string] [ELiteral (Integer 5)] (EVar "X"%string), []|
-e>
  |inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]).
  * reflexivity.
  * reflexivity.
  * intros. inversion H.
    - subst. apply eval_lit.
    - inversion H1.
  * reflexivity.
  * simpl. apply eval_var.
Qed.

Example ex2 : 
  |[],
   ELet ["X"%string] [EFun [] (EApply (EVar "X"%string) [])] 
     (EApply (EVar "X"%string) []), []|
-e>
  |inr novar, []|.
Proof.
  eapply eval_let with (vals := [VClosure [] [] 0 [] (EApply ( EVar "X"%string) [])])
                       (eff := [[]]); auto.
  * intros. inversion H.
    - subst. apply eval_fun.
    - inversion H1.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                  (body := (EApply (EVar "X"%string) [])) 
                                  (ref := []) (ext := []) (n := 0) (eff := []); auto.
    - apply eval_var.
    - intros. inversion H.
    - reflexivity.
    - simpl. eapply eval_apply_ex_closure_ex; auto.
      + reflexivity.
      + apply eval_var.
Qed.

Example ex3 :
  |[], ELetrec [("X"%string, 0)] [[]] [(EApply (EFunId ("X"%string, 0)) [])] 
         (EApply (EFunId ("X"%string, 0)) []), []|
-e>
  |inl (VEmptyTuple), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (var_list := []) (ref := []) (n := 0) (eff := [])
                                  (body := (EApply (EFunId ("X"%string, 0)) []))
                                  (ext := [("X"%string, 0, ([], EApply (EFunId ("X"%string, 0)) []))]); 
        try (reflexivity).
    - apply eval_funid.
    - intros. inversion H.
    - reflexivity.
    - simpl. eapply eval_apply with (vals := []) (n := 0) (var_list := []) (ref := []) (eff := [])
                                    (body := (EApply (EFunId ("X"%string, 0)) []))
                                    (ext := [("X"%string, 0, ([], EApply (EFunId ("X"%string, 0)) []))]); 
         try (reflexivity).
      + apply eval_funid.
      + intros. inversion H.
      + reflexivity.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) (n := 0) (ref := []) (eff := [])
                                      (body := (EApply (EFunId ("X"%string, 0)) [])) 
                                      (ext := [("X"%string, 0, 
                                               ([], EApply (EFunId ("X"%string, 0)) []))]); 
             try (reflexivity).
        ** apply eval_funid.
        ** intros. inversion H.
        ** simpl.
Admitted.

Example ex4 : 
|[], ELet ["X"%string] [ELiteral (Integer 4)] 
       (ELet ["X"%string] [EFun [] (EVar "X"%string)] 
          (ELet ["X"%string] [EFun [] (EApply (EVar "X"%string) [])] 
             (EApply (EVar "X"%string) []))), []|
-e>
  |inl (VLiteral (Integer 4)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 4)]) (eff := [[]]); auto.
  * intros. inversion H; inversion H1. apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_let with (vals := [VClosure [(inl "X"%string, VLiteral (Integer 4))] [] 0 [] 
                                            (EVar "X"%string)])
                                (eff := [[]]); auto.
    - intros. inversion H; inversion H1. apply eval_fun.
    - reflexivity.
    - simpl. eapply eval_let with (vals := [VClosure [(inl "X"%string,
                                              VClosure [(inl "X"%string, VLiteral (Integer 4))] [] 0 []
                                                (EVar "X"%string))] [] 1 [] (EApply (EVar "X"%string) []) ])
                                  (eff := [[]]); auto.
       + intros. inversion H; inversion H1. apply eval_fun.
       + reflexivity.
       + simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                       (body := EApply (EVar "X"%string) []) 
                                       (ref := [(inl "X"%string,
                                                 VClosure [(inl "X"%string, VLiteral (Integer 4))] [] 0 []
                                                   (EVar "X"%string))]) (n := 1)
                                       (ext := []) (eff := []); auto.
         ** apply eval_var.
         ** intros. inversion H.
         ** reflexivity.
         ** simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                          (body := EVar "X"%string) 
                                          (ref := [(inl "X"%string, VLiteral (Integer 4))]) (n := 0)
                                          (ext := []) (eff := []); auto.
           -- apply eval_var.
           -- intros. inversion H.
           -- reflexivity.
           -- apply eval_var.
Qed.

End Documentation_Examples.

Example returned_function :
  |[], 
   ELet ["X"%string] [EFun [] (EFun [] (ELiteral (Integer 5)))] 
     (EApply (EApply (EVar "X"%string) []) []), []|
-e>
  |inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_let with (vals := [VClosure [] [] 0 [] (EFun [] (ELiteral (Integer 5)))])
                       (eff := [[]]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (ref := []) (ext := []) (eff := [])
                                  (body := ELiteral (Integer 5)) (var_list := []); auto.
    - eapply eval_apply with (vals := []) (var_list := []) (n := 0)
                             (body := EFun [] (ELiteral (Integer 5))) 
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
  |[], 
   ELetrec [("fun1"%string, 0)] [[]] [(EFun [] (ELiteral (Integer 5)))] 
     (EApply (EApply (EFunId ("fun1"%string, 0)) []) []), []|
-e>
  |inl (VLiteral (Integer 5)), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (ref := [(inr ("fun1"%string, 0),
                                                         VClosure [] [("fun1"%string, 0, ([], 
                                                            EFun [] (ELiteral (Integer 5))))] 0 []
                                                            (EFun [] (ELiteral (Integer 5))))]) 
                                  (ext := []) (body := ELiteral (Integer 5)) 
                                  (var_list := []) (eff := []); try (reflexivity).
    - eapply eval_apply with (vals := []) (var_list := []) 
                             (body := EFun [] (ELiteral (Integer 5))) 
                             (ref := []) (eff := []) (n := 0)
                             (ext := [("fun1"%string, 0, ([], EFun [] (ELiteral (Integer 5))))]);
          try (reflexivity).
      + apply eval_funid.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - reflexivity.
    - apply eval_lit.
Qed.

Example returned_function2 :
  |[(inl "X"%string, VLiteral (Integer 7))],
   ELet ["X"%string] [EFun [] (EFun [] (EVar "X"%string))] 
     (EApply (EApply (EVar "X"%string) []) []), []|
-e>
  |inl (VLiteral (Integer 7)), []|.
Proof.
  eapply eval_let with (vals := [VClosure [(inl "X"%string, VLiteral (Integer 7))] [] 
                                  0 [] (EFun [] (EVar "X"%string))])
                       (eff := [[]]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_apply with (vals := []) (ref := [(inl "X"%string, VLiteral (Integer 7))]) 
                                 (ext := []) (body := EVar "X"%string) (var_list := []) (eff := []) (n := 0); auto.
    - eapply eval_apply with (vals := []) (var_list := []) 
                             (body := EFun [] (EVar "X"%string)) 
                             (ref := [(inl "X"%string, VLiteral (Integer 7))]) 
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
  |[(inl "X"%string, VLiteral (Integer 7))], 
   ELetrec [("fun1"%string, 0)] [[]] [(EFun [] (EVar "X"%string))] 
     (EApply (EApply (EFunId ("fun1"%string, 0)) []) []), []|
-e>
  |inl (VLiteral (Integer 7)), []|.
Proof.
  eapply eval_letrec; try (reflexivity).
  * simpl. eapply eval_apply with (vals := []) (eff := [])
                                 (ref := [(inl "X"%string, VLiteral (Integer 7)) ; 
                                          (inr ("fun1"%string, 0),
                                             VClosure [(inl "X"%string, VLiteral (Integer 7))] 
                                                      [("fun1"%string, 0, 
                                                          ([], EFun [] (EVar "X"%string)))] 
                                                      0 [] 
                                                      (EFun [] (EVar "X"%string)))]) 
                                 (body := EVar "X"%string) 
                                 (var_list := []) (ext := []); try (reflexivity).
    - eapply eval_apply with (vals := []) (var_list := []) (eff := [])
                             (body := EFun [] (EVar "X"%string)) (n := 0)
                             (ref := [(inl "X"%string, VLiteral (Integer 7))]) 
                             (ext := [("fun1"%string, 0, ([], EFun [] (EVar "X"%string)))]); 
          try (reflexivity).
      + apply eval_funid.
      + intros. inversion H.
      + simpl. apply eval_fun.
    - intros. inversion H.
    - reflexivity.
    - simpl. apply eval_var.
Qed.

Example returned_function3 : 
  |[], 
   ELet ["F"%string] [
     EFun ["X"%string] 
        (ELet ["Y"%string] 
              [ECall "plus"%string [EVar "X"%string; ELiteral (Integer 3)] ] 
              (EFun ["Z"%string] 
                    (ECall "plus"%string 
                          [ECall "plus"%string [EVar "X"%string; EVar "Y"%string]
                     ; EVar "Z"%string])))]
  (EApply (EApply (EVar "F"%string) [ELiteral (Integer 1)]) [ELiteral (Integer 1)]), []|
-e>
  |inl (VLiteral (Integer 6)), []|.
Proof.
  eapply eval_let with (vals := [VClosure [] [] 0 ["X"%string] (ELet ["Y"%string]
                                        [ECall "plus"
                                           [EVar "X"%string; ELiteral (Integer 3)] ]
                                        (EFun ["Z"%string]
                                           (ECall "plus"
                                              [ECall "plus"
                                                 [EVar "X"%string; EVar "Y"%string];
                                              EVar "Z"%string])))])
                        (eff := [[]]); auto.
  * intros. inversion H; inversion H1. apply eval_fun.
  * reflexivity.
  * simpl. eapply eval_apply with (var_list := ["Z"%string]) (eff := [[]])
                                  (body := (ECall "plus"
                                              [ECall "plus"
                                                 [EVar "X"%string; EVar "Y"%string];
                                              EVar "Z"%string]))
                                  (ref := [(inl "X"%string, VLiteral (Integer 1)); 
                                           (inl "Y"%string, VLiteral (Integer 4))])
                                  (ext := []) (vals := [VLiteral (Integer 1)]); auto.
    - eapply eval_apply with (vals := [VLiteral (Integer 1)]) (var_list := ["X"%string]) 
                             (body := ELet ["Y"%string]
                                        [ECall "plus"
                                           [EVar "X"%string; ELiteral (Integer 3)] ]
                                        (EFun ["Z"%string]
                                           (ECall "plus"
                                              [ECall "plus"
                                                 [EVar "X"%string; EVar "Y"%string];
                                              EVar "Z"%string]))) 
                             (ref := []) (ext := []) (eff := [[]]) (n := 0); auto.
      + apply eval_var.
      + intros. inversion H; inversion H1. apply eval_lit.
      + reflexivity.
      + eapply eval_let with (vals := [VLiteral (Integer 4)]) (eff := [[]]); auto.
        ** intros. inversion H; inversion H1. 
           apply eval_call with (vals := [VLiteral (Integer 1); VLiteral (Integer 3)])
                                (eff := [[];[]]); auto.
          -- intros. inversion H2.
            ++ apply eval_lit.
            ++ inversion H4; inversion H6. apply eval_var.
        ** simpl. apply eval_fun.
    - intros. inversion H; inversion H1. apply eval_lit.
    - reflexivity.
    - eapply eval_call with (vals := [VLiteral (Integer 5) ; VLiteral (Integer 1)])
                            (eff := [[];[]]); auto.
      + intros. inversion H.
        ** inversion H1. apply eval_var.
        ** inversion H1.
          -- eapply eval_call with (vals := [VLiteral (Integer 1) ; VLiteral (Integer 4)])
                                               (eff := [[];[]]); auto.
            ++ intros. inversion H2.
              *** apply eval_var.
              *** inversion H5; inversion H7. apply eval_var.
          -- simpl. inversion H3.
Qed.

Example sum :
  | [],
    ELetrec [("f"%string, 1)] [["X"%string]] 
      [
      ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
                              [ELiteral (Atom "true"%string); ELiteral (Atom "true"%string)]
                              [
                              ELiteral (Integer 0)
                              ;
                              ECall "plus"%string [
                                     EVar "Y"%string; 
                                     EApply (EFunId ("f"%string, 1)) [ECall "plus"%string [EVar "Y"%string; ELiteral (Integer (Z.pred 0))] ]
                              ]
     ] ] (EApply (EFunId ("f"%string, 1)) [ELiteral (Integer 2)]), []| -e> |inl (VLiteral (Integer 3)), []|.
Proof.
  eapply eval_letrec; auto.
  2: reflexivity.
  * simpl. eapply eval_apply with (vals := [VLiteral (Integer 2)]) (eff := [[]]) (eff2 := []) (n := 0)
                                  (var_list := ["X"%string]) (ref := []) 
                                  (body := 
      (ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 0);
        ECall "plus"
          [EVar "Y"%string;
          EApply (EFunId ("f"%string, 1))
            [ECall "plus" [EVar "Y"%string; ELiteral (Integer (-1))]]]]))
                                  (ext := [("f"%string, 1,
                                      (["X"%string],
                                      ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
                                        [ELiteral (Atom "true"); ELiteral (Atom "true")]
                                        [ELiteral (Integer 0);
                                        ECall "plus"
                                          [EVar "Y"%string;
                                          EApply (EFunId ("f"%string, 1))
                                            [ECall "plus" [EVar "Y"%string; 
                                                ELiteral (Integer (-1))]]]]))]); simpl; auto.
    - apply eval_funid.
    - intros. inversion H; inversion H1. apply eval_lit.
    - unfold concatn. simpl. eapply eval_case with (i := 1) (v := VLiteral (Integer 2)); auto.
      + apply eval_var.
      + simpl. reflexivity.
      + intros. inversion H; inversion H2. subst. inversion H0.
      + reflexivity.
      + simpl. apply eval_lit.
      + eapply eval_call with (vals := [VLiteral (Integer 2); VLiteral (Integer 1)]) (eff := [[]; []]); auto.
        ** intros. inversion H; inversion H1. 3: inversion H3.
          -- simpl. eapply eval_apply with (vals := [VLiteral (Integer 1)]) (eff := [[]]) (eff2 := [])
                                  (var_list := ["X"%string]) (ref := []) 
                                  (body := 
      (ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 0);
        ECall "plus"
          [EVar "Y"%string;
          EApply (EFunId ("f"%string, 1))
            [ECall "plus" [EVar "Y"%string; ELiteral (Integer (-1))]]]]))
                                  (ext := [("f"%string, 1,
                                      (["X"%string],
                                      ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
                                        [ELiteral (Atom "true"); ELiteral (Atom "true")]
                                        [ELiteral (Integer 0);
                                        ECall "plus"
                                          [EVar "Y"%string;
                                          EApply (EFunId ("f"%string, 1))
                                            [ECall "plus" [EVar "Y"%string; 
                                                ELiteral (Integer (-1))]]]]))]) (n := 0); simpl; auto.
            ++ apply eval_funid.
            ++ intros. inversion H2; inversion H4. eapply eval_call with (vals := [VLiteral (Integer 2); VLiteral (Integer (-1))]) (eff := [[];[]]); auto.
              *** simpl. intros. inversion H5; inversion H7. 3: inversion H9.
                --- apply eval_lit.
                --- apply eval_var.
            ++ {
            eapply eval_case with (i := 1) (v := VLiteral (Integer 1)); auto.
              + apply eval_var.
              + simpl. reflexivity.
              + intros. inversion H2; inversion H5. subst. inversion H3.
              + reflexivity.
              + simpl. apply eval_lit.
              + subst. simpl. eapply eval_call with (vals := [VLiteral (Integer 1); VLiteral (Integer (0))]) (eff := [[];[]]); auto.
                * simpl. intros. inversion H1; inversion H3. 3: inversion H5. 
                  - eapply eval_apply with (vals := [VLiteral (Integer 0)]) (eff := [[]]) (eff2 := [])
                                  (var_list := ["X"%string]) (ref := []) (n := 0)
                                  (body := 
      (ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
        [ELiteral (Atom "true"); ELiteral (Atom "true")]
        [ELiteral (Integer 0);
        ECall "plus"
          [EVar "Y"%string;
          EApply (EFunId ("f"%string, 1))
            [ECall "plus" [EVar "Y"%string; ELiteral (Integer (-1))]]]]))
                                  (ext := [("f"%string, 1,
                                      (["X"%string],
                                      ECase (EVar "X"%string) [PLiteral (Integer 0); PVar "Y"%string]
                                        [ELiteral (Atom "true"); ELiteral (Atom "true")]
                                        [ELiteral (Integer 0);
                                        ECall "plus"
                                          [EVar "Y"%string;
                                          EApply (EFunId ("f"%string, 1))
                                            [ECall "plus" [EVar "Y"%string; 
                                                ELiteral (Integer (-1))]]]]))]); simpl; auto.
                  ** apply eval_funid.
                  ** intros. inversion H4. 2: inversion H6. eapply eval_call with (vals := [VLiteral (Integer 1); VLiteral (Integer (-1))]) (eff := [[];[]]); auto.
                    -- intros. inversion H5; inversion H8.
                      ++ simpl. apply eval_lit.
                      ++ simpl. apply eval_var.
                      ++ inversion H10.
                  ** eapply eval_case with (i := 0) (v := VLiteral (Integer 0)); auto.
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
  |[], 
   ELet ["X"%string] [ELiteral (Integer 42)] 
     (ELetrec [("f"%string, 0)] [[]] [EVar "X"%string]
       (ELet ["X"%string] [ELiteral (Integer 5)] 
         (EApply (EFunId ("f"%string, 0)) []))), []|
-e>
  |inl (VLiteral (Integer 42)), []|.
Proof.
  eapply eval_let with (vals := [VLiteral (Integer 42)]) (eff := [[]]); auto.
  * intros. inversion H; inversion H1.
    - apply eval_lit.
  * reflexivity.
  * simpl. eapply eval_letrec; auto.
    2: reflexivity.
    - eapply eval_let with (vals := [VLiteral (Integer 5)]) (eff := [[]]); auto.
      + intros. inversion H; inversion H1.
        ** apply eval_lit.
      + simpl. eapply eval_apply with (vals := []) (var_list := []) 
                                      (body := (EVar "X"%string)) 
                                      (ref := [(inl "X"%string, VLiteral (Integer 42))]) 
                                      (ext := [("f"%string, 0, ([], EVar "X"%string))]) (eff := []) (n := 0); auto.
        ** apply eval_funid.
        ** intros. inversion H.
        ** simpl. reflexivity.
        ** simpl. apply eval_var.
Qed.


End Core_Erlang_Tests.