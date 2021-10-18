Require Core_Erlang_Tactics.
Require Core_Erlang_Functional_Big_Step.

(**
  IMPORTANT NOTICE:
  To use the `solve` tactic, the abbreviations (e.g. `ETuple []`)
  should not be used (use `ETuple []` instead).
*)

Module Automated_Tests.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.
Import Core_Erlang_Functional_Big_Step.Functional_Big_Step.

Import ListNotations.

Open Scope string_scope.

(** 
  Every first example: functional big-step semantics
  Every second example: big-step semantics
*)

(** This is an endless recursion *)

Example eval_letrec1_fbs : 
  fbs_expr 1000 [] 0 (ELetRec [(("x", 1), (["X"], EApp (EFunId ("x", 1)) [EVar "X"])) ]
            (EApp (EFunId ("x", 1)) [ETuple []])) []
=
  Timeout.
Proof.
  auto.
Qed.

Example eval_letrec1 : 
  |[], 0, ELetRec [(("x", 1), (["X"], EApp (EFunId ("x", 1)) [EVar "X"])) ]
            (EApp (EFunId ("x", 1)) [ETuple []]), []|
-e> 
  |1, inl [ErrorValue], []|.
Proof.
  try (timeout 4 solve).
Abort.

(* (* This is not accepted by the compiler in Core Erlang *)
Example eval_letrec2 : 
  |[], 0, ELet [("F", EFun ["X"] 
         (EApp (EVar "F") [EVar "X"]))] 
            (EApp (EVar "F") [ETuple []]), []| 
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
Example multiple_top_level_funs_fbs : 
 fbs_expr 1000 [(inr ("fun1", 0), VClos [] [
    (0, ("fun1", 0), ([], (EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (ELit (Integer 42))));
    (2, ("fun3", 0), ([], (EApp (EFunId ("fun2", 0)) [])))
  ] 0 [] (EApp (EFunId ("fun3", 0)) [])) ; 
                                      (inr ("fun2", 0), VClos [] [
    (0, ("fun1", 0), ([], (EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (ELit (Integer 42))));
    (2, ("fun3", 0), ([], (EApp (EFunId ("fun2", 0)) [])))
  ] 1 [] (ELit (Integer 42))) ;
                                      (inr ("fun3", 0), VClos [] [
    (0, ("fun1", 0), ([], (EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (ELit (Integer 42))));
    (2, ("fun3", 0), ([], (EApp (EFunId ("fun2", 0)) [])))
  ] 2 [] (EApp (EFunId ("fun2", 0)) []))] 3
                                       (EApp (EFunId ("fun1",0)) []) []
=
  Result 3 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example multiple_top_level_funs : |[(inr ("fun1", 0), VClos [] [
    (0, ("fun1", 0), ([], (EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (ELit (Integer 42))));
    (2, ("fun3", 0), ([], (EApp (EFunId ("fun2", 0)) [])))
  ] 0 [] (EApp (EFunId ("fun3", 0)) [])) ; 
                                      (inr ("fun2", 0), VClos [] [
    (0, ("fun1", 0), ([], (EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (ELit (Integer 42))));
    (2, ("fun3", 0), ([], (EApp (EFunId ("fun2", 0)) [])))
  ] 1 [] (ELit (Integer 42))) ;
                                      (inr ("fun3", 0), VClos [] [
    (0, ("fun1", 0), ([], (EApp (EFunId ("fun3", 0)) [])));
    (1, ("fun2", 0), ([], (ELit (Integer 42))));
    (2, ("fun3", 0), ([], (EApp (EFunId ("fun2", 0)) [])))
  ] 2 [] (EApp (EFunId ("fun2", 0)) []))], 3
                                      , EApp (EFunId ("fun1",0)) [], []| 
-e> 
  |3, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

Example multiple_top_level_funs2_fbs :
  fbs_expr 1000 [] 0 (ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) [])); 
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
     (EApp (EFunId ("fun1",0)) [])) []
=
  Result 3 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example multiple_top_level_funs2 :
  | [], 0, ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) [])); 
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
     (EApp (EFunId ("fun1",0)) []), [] |
-e>
  |3, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

Example weird_apply_fbs : 
  fbs_expr 1000 [] 0 (ELetRec [(("f", 1), (["X"],
   ECase (EVar "X")
          [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 5));
           ([PLit (Integer 1)], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 0)]);
           ([PVar "A"], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 1)])]
   ))]
   (ELet ["X"] (EFun ["F"]
       (ELetRec [(("f", 1), (["X"], ELit (Integer 0)))] 
          (EApp (EVar "F") [ELit (Integer 2)])
       ))
    (EApp (EVar "X") [EFunId ("f", 1)])
   )) []
=
  Result 3 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example weird_apply : |[], 0, ELetRec [(("f", 1), (["X"],
   ECase (EVar "X")
          [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 5));
           ([PLit (Integer 1)], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 0)]);
           ([PVar "A"], ELit (Atom "true"), EApp (EFunId ("f", 1)) [ELit (Integer 1)])]
   ))]
   (ELet ["X"] (EFun ["F"]
       (ELetRec [(("f", 1), (["X"], ELit (Integer 0)))] 
          (EApp (EVar "F") [ELit (Integer 2)])
       ))
    (EApp (EVar "X") [EFunId ("f", 1)])
   ), []|
-e> 
  |3, inl [VLit (Integer 5)], []|.
Proof.
  solve.
Qed.

Example top_overwrite_fbs : 
  fbs_expr 1000 [(inr ("fun2", 0), 
       VClos [] [(0, ("fun2", 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))] 1
  (ELetRec [(("fun2", 0), ([], ELit (Integer 40)))] 
     (EApp (EFunId ("fun2", 0)) [])) []
=
  Result 2 (inl [VLit (Integer 40)]) [].
Proof.
  auto.
Qed.

Example top_overwrite : 
  |[(inr ("fun2", 0), 
       VClos [] [(0, ("fun2", 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))], 1,
  ELetRec [(("fun2", 0), ([], ELit (Integer 40)))] 
     (EApp (EFunId ("fun2", 0)) []), [] | 
-e>
  |2, inl [VLit (Integer 40)], []|.
Proof.
  solve.
Qed.

Example top_no_overwrite_fbs : 
  fbs_expr 1000 [(inr ("fun2", 0), 
     VClos [] [(0, ("fun2", 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)))] 1
   (ELetRec [(("fun2", 1), (["X"], (ELit (Integer 40))))] 
     (EApp (EFunId ("fun2", 0)) [])) []
=
  Result 2 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example top_no_overwrite : 
  |[(inr ("fun2", 0), 
     VClos [] [(0, ("fun2", 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)))], 1,
   ELetRec [(("fun2", 1), (["X"], (ELit (Integer 40))))] 
     (EApp (EFunId ("fun2", 0)) []), [] |
-e> 
  | 2, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

(** This is not accepted by the compiler in Core Erlang *)
Example eval_let_func_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 42))] 0
   (ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] (EMap [])])
     (EMap [])) [] 
=
  Result 2 (inl [VEmptyMap]) [].
Proof.
  auto.
Qed.

Example eval_let_func : 
  |[(inl "X", VLit (Integer 42))], 0,
   ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] (EMap [])]) 
     (EMap []), []| 
-e> 
  |2, inl [VEmptyMap], []|.
Proof.
  solve.
Qed.

Example eval_let_apply_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 42))] 0
   (ELet ["Y"] (EValues [EFun [] (EVar "X")])
     (EApp (EVar "Y") [])) []
=
  Result 1 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example eval_let_apply : 
  |[(inl "X", VLit (Integer 42))], 0,
   ELet ["Y"] (EValues [EFun [] (EVar "X")])
     (EApp (EVar "Y") []), []| 
-e> 
  |1, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

Example eval_muliple_let_fbs : 
  fbs_expr 1000 [] 0 (ELet ["X"] (ELit (Integer 1)) 
            (ELet ["X"] (ELit (Integer 2)) 
               (EVar "X"))) [] 
=
  Result 0 (inl [VLit (Integer 2)]) [].
Proof.
  auto.
Qed.

Example eval_muliple_let : 
  |[], 0, ELet ["X"] (ELit (Integer 1)) 
            (ELet ["X"] (ELit (Integer 2)) 
               (EVar "X")), []| 
-e> 
  |0, inl [VLit (Integer 2)], []|.
Proof.
  solve.
Qed.

Example let_eval_1_fbs : 
  fbs_expr 1000 [] 0 (ELet ["X"] (ETuple []) (EMap [])) []
=
  Result 0 (inl [VEmptyMap]) [].
Proof.
  auto.
Qed.

Example let_eval_1 : 
  |[], 0, ELet ["X"] (ETuple []) (EMap []), []|
-e>
  | 0, inl [VEmptyMap], []|.
Proof.
  solve.
Qed.

Example let_eval_2_fbs : 
  fbs_expr 1000 [(inl "X", VEmptyMap)] 0 (ELet ["X"] (ETuple []) (EMap [])) [] 
=
  Result 0 (inl [VEmptyMap]) [].
Proof.
  auto.
Qed.

Example let_eval_2 : 
  |[(inl "X", VEmptyMap)], 0, ELet ["X"] (ETuple []) (EMap []), []| 
-e> 
  | 0, inl [VEmptyMap], []|.
Proof.
  solve.
Qed.

(** This shouldn't compile in Core Erlang *)
Example eval_let_3_fbs : 
  fbs_expr 1000 [(inl "X", VEmptyMap)] 0
   (ELet ["X"; "X"; "Y"] (EValues [ETuple []; ENil; EVar "X"])
     (EVar "Y")) []
=
  Result 0 (inl [VEmptyMap]) [].
Proof.
  auto.
Qed.

Example eval_let_3 : 
  |[(inl "X", VEmptyMap)], 0,
   ELet ["X"; "X"; "Y"] (EValues [ETuple []; ENil; EVar "X"])
     (EVar "Y"), []|
-e>
  |0, inl [VEmptyMap], []|.
Proof.
  solve.
Qed.

Example let_eval_4_fbs : 
  fbs_expr 1000 [] 0 (ELet ["X"] (ELit (Integer 5)) (EVar "X")) []
=
  Result 0 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example let_eval_4 : 
  |[], 0, ELet ["X"] (ELit (Integer 5)) (EVar "X"), []| 
-e> 
  | 0, inl [VLit (Integer 5)], []|.
Proof.
  solve.
Qed.

Example tuple_eval_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Atom "foo")); 
    (inl "Y", VEmptyTuple)] 0
   (ETuple [ELit (Integer 5); EVar "X"; EVar "Y"]) [] 
=
  Result 0 (inl [VTuple [VLit (Integer 5); VLit (Atom "foo"); VEmptyTuple]]) [].
Proof.
  auto.
Qed.

Example tuple_eval : 
  |[(inl "X", VLit (Atom "foo")); 
    (inl "Y", VEmptyTuple)], 0,
   ETuple [ELit (Integer 5); EVar "X"; EVar "Y"], []| 
-e>
  |0, inl [VTuple [VLit (Integer 5); VLit (Atom "foo"); VEmptyTuple]], []|.
Proof.
  solve.
Qed.

Example apply_top_eval_fbs : 
  fbs_expr 1000 [(inr ("Plus", 2), 
       VClos [] [(0, ("Plus", 2),
                     (["X" ; "Y"], ELit (Integer 3)))] 
                0 ["X" ; "Y"] 
                (ELit (Integer 3)))] 1
   (EApp (EFunId ("Plus", 2)) [ELit (Integer 2); ELit (Integer 3)]) []
=
  Result 1 (inl [VLit (Integer 3)]) [].
Proof.
  auto.
Qed.

Example apply_top_eval : 
  |[(inr ("Plus", 2), 
       VClos [] [(0, ("Plus", 2),
                     (["X" ; "Y"], ELit (Integer 3)))] 
                0 ["X" ; "Y"] 
                (ELit (Integer 3)))], 1,
   EApp (EFunId ("Plus", 2)) [ELit (Integer 2); ELit (Integer 3)], []|
-e>
  |1, inl [VLit (Integer 3)], []|.
Proof.
  solve.
Qed.

Example apply_eval_fbs : 
  fbs_expr 1000 [(inl "Minus",
      VClos [] [] 0 ["X"; "Y"] (ELit (Integer 42))) ; 
    (inl "X", VEmptyMap)] 1
   (EApp (EVar "Minus") [EVar "X"; EVar "X"]) []
=
  Result 1 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example apply_eval : 
  |[(inl "Minus",
      VClos [] [] 0 ["X"; "Y"] (ELit (Integer 42))) ; 
    (inl "X", VEmptyMap)], 1,
   EApp (EVar "Minus") [EVar "X"; EVar "X"], []|
-e>
  |1, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

Example list_eval_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 5))] 0
   (ECons (EVar "X") (ENil)) [] 
=
  Result 0 (inl [VCons (VLit (Integer 5)) (VNil)]) [].
Proof.
  auto.
Qed.

Example list_eval : 
  |[(inl "X", VLit (Integer 5))], 0,
   ECons (EVar "X") (ENil), []| 
-e>
  | 0, inl [VCons (VLit (Integer 5)) (VNil)], []|.
Proof.
  solve.
Qed.

Example list_eval2_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 5))] 0
   (ECons (EVar "X") 
         (ECons (EVar "X") 
                (ENil))) [] 
=
  Result 0 (inl [VCons (VLit (Integer 5))
                 (VCons (VLit (Integer 5)) 
                        (VNil))]) [].
Proof.
  auto.
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
  solve.
Qed.

Example let_eval_overwrite_fbs : 
  fbs_expr 1000 [] 0 (ELet ["X"] (EFun [] (ETuple [])) 
           (ELet ["X"] (ELit (Integer 5)) 
             (EVar "X"))) []
=
  Result 1 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example let_eval_overwrite : 
  |[], 0, ELet ["X"] (EFun [] (ETuple [])) 
           (ELet ["X"] (ELit (Integer 5)) 
             (EVar "X")), []|
-e>
  | 1, inl [VLit (Integer 5)], []|.
Proof.
  solve.
Qed.

Example map_eval_fbs :
  fbs_expr 1000 [(inl "X", VLit (Integer 42))] 0
    (EMap [(ELit (Integer 5), EVar "X")]) []
=
  Result 0 (inl [VMap [(VLit (Integer 5), VLit (Integer 42))]]) [].
Proof.
  auto.
Qed.

Example map_eval :
  |[(inl "X", VLit (Integer 42))], 0,
    EMap [(ELit (Integer 5), EVar "X")], []|
-e>
  | 0, inl [VMap [(VLit (Integer 5), VLit (Integer 42))]], []|.
Proof.
  solve.
Qed.

Example map_eval2_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 42))] 0
   (EMap [(ELit (Integer 54), EVar "X"); (EVar "X", EVar "X")] )
   []
=
  Result 0 (inl [VMap [(VLit (Integer 42), VLit (Integer 42)); 
                 (VLit (Integer 54), VLit (Integer 42))]])
  [].
Proof.
  auto.
Qed.

Example map_eval2 : 
  |[(inl "X", VLit (Integer 42))], 0,
   EMap [(ELit (Integer 54), EVar "X"); (EVar "X", EVar "X")] 
  , []|
-e> 
  |0, inl [VMap [(VLit (Integer 42), VLit (Integer 42)); 
                 (VLit (Integer 54), VLit (Integer 42))]]
  , []|.
Proof.
  solve.
Qed.

Example map_eval3_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 5))] 0
   (EMap [(ELit (Integer 5), EVar "X"); 
         (EVar "X", ECall "erlang" "+" 
                              [ELit (Integer 1); (EVar "X")])])
   []
=
  Result 0 (inl [VMap [(VLit (Integer 5), VLit (Integer 6))]]) [].
Proof.
  auto.
Qed.

Example map_eval3 : 
  |[(inl "X", VLit (Integer 5))], 0,
   EMap [(ELit (Integer 5), EVar "X"); 
         (EVar "X", ECall "erlang" "+" 
                              [ELit (Integer 1); (EVar "X")])] 
  , []| 
-e> 
  | 0, inl [VMap [(VLit (Integer 5), VLit (Integer 6))]], []|.
Proof.
  solve.
Qed.

Example map_eval4_fbs : 
  fbs_expr 1000 [] 0
   (ELet ["X"; "Y"; "Z"] 
        (EValues [EFun [] (ELit (Integer 1)); 
                  EFun [] (ELit (Integer 2)); 
                  EFun [] (ELit (Integer 3))])
     (EMap [(EVar "Z", ELit (Integer 10)); 
            (EVar "X", ELit (Integer 11));
            (EVar "Y", ELit (Integer 12)); 
            (EVar "X", ELit (Integer 13))]))
   []
= 
  Result 3 (inl [VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                      (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                      (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))]])
   [].
Proof.
  auto.
Qed.

Example map_eval4 : 
  |[], 0,
   ELet ["X"; "Y"; "Z"] 
        (EValues [EFun [] (ELit (Integer 1)); 
                  EFun [] (ELit (Integer 2)); 
                  EFun [] (ELit (Integer 3))])
     (EMap [(EVar "Z", ELit (Integer 10)); 
            (EVar "X", ELit (Integer 11));
            (EVar "Y", ELit (Integer 12)); 
            (EVar "X", ELit (Integer 13))])
  , []| 
-e> 
  | 3, inl [VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                  (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                  (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))]]
  , []|.
Proof.
  solve.
Qed.

(** Function parameter always overwrites everything *)
Example let_closure_apply_eval_without_overwrite_fbs :
  fbs_expr 1000 [] 0
   (ELet ["X"] (ELit (Integer 42))
     (ELet ["Y"] (EFun ["X"] (EVar "X")) 
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EVar "Y") [ELit (Integer 7)])))) []
=
  Result 1 (inl [VLit (Integer 7)]) [].
Proof.
  auto.
Qed.

Example let_closure_apply_eval_without_overwrite :
  |[], 0,
   ELet ["X"] (ELit (Integer 42))
     (ELet ["Y"] (EFun ["X"] (EVar "X")) 
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EVar "Y") [ELit (Integer 7)]))), []|
-e>
  | 1, inl [VLit (Integer 7)], []|.
Proof.
  solve.
Qed.


(** Example to test that value overwriting does not affect the value in the closure *)
Example let_closure_apply_eval_without_overwrite2_fbs :
  fbs_expr 1000 [] 0
   (ELet ["X"] (ELit (Integer 42)) 
     (ELet ["Y"] (EFun [] (EVar "X"))
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EVar "Y") [])))) []
=
  Result 1 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example let_closure_apply_eval_without_overwrite2 :
  |[], 0,
   ELet ["X"] (ELit (Integer 42)) 
     (ELet ["Y"] (EFun [] (EVar "X"))
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EVar "Y") []))), []|
-e> 
  | 1, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

Example call_eval_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 5))] 0
   (ECall "erlang" "+" [EVar "X" ; ELit (Integer 2)]) []
=
  Result 0 (inl [VLit (Integer 7)]) [].
Proof.
  auto.
Qed.

Example call_eval : 
  |[(inl "X", VLit (Integer 5))], 0,
   ECall "erlang" "+" [EVar "X" ; ELit (Integer 2)], []|
-e> 
  |0, inl [VLit (Integer 7)], []|.
Proof.
  solve.
Qed.

Example mutliple_function_let_fbs : 
  fbs_expr 1000 [] 0
   (ELet ["Z"] (ECall "erlang" "+" [ELit (Integer 2) ; ELit (Integer 2)] ) 
     (ELet ["Y"] (EFun [] (EVar "Z"))
        (ELet ["X"] (EFun [] (EApp (EVar "Y") [])) 
          (EApp (EVar "X") [])))) []
=
  Result 2 (inl [VLit (Integer 4)]) [].
Proof.
  auto.
Qed.

Example mutliple_function_let : 
  |[], 0,
   ELet ["Z"] (ECall "erlang" "+" [ELit (Integer 2) ; ELit (Integer 2)] ) 
     (ELet ["Y"] (EFun [] (EVar "Z"))
        (ELet ["X"] (EFun [] (EApp (EVar "Y") [])) 
          (EApp (EVar "X") []))), []|
-e>
  | 2, inl [VLit (Integer 4)], []|.
Proof.
  solve.
Qed.

Example case_eval_fbs : 
  fbs_expr 1000 [(inl "X", VEmptyTuple)] 0
   (ECase (EVar "X")
         [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6)); 
          ([PVar "Z"], ELit (Atom "true"), EVar "Z") ])
   []
= 
  Result 0 (inl [VEmptyTuple]) [].
Proof.
  auto.
Qed.

Example case_eval : 
  |[(inl "X", VEmptyTuple)], 0,
   ECase (EVar "X")
         [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6)); 
          ([PVar "Z"], ELit (Atom "true"), EVar "Z") ]
  , [] |
-e> 
  | 0, inl [VEmptyTuple], []|.
Proof.
  solve.
Qed.

Example case_eval2_fbs :
  fbs_expr 1000 [(inl "X", VEmptyTuple)] 0
   (ECase (EVar "X") 
         [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6));
          ([PVar "Z"], ELit (Atom "false"), EVar "Z");
          ([PVar "Z"], ELit (Atom "true"), EMap [])])

   []
=
  Result 0 (inl [VEmptyMap]) [].
Proof.
  auto.
Qed.

Example case_eval2 :
  |[(inl "X", VEmptyTuple)], 0,
   ECase (EVar "X") 
         [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6));
          ([PVar "Z"], ELit (Atom "false"), EVar "Z");
          ([PVar "Z"], ELit (Atom "true"), EMap [])]

  , []|
-e> 
  | 0, inl [VEmptyMap], []|.
Proof.
  solve.
Qed.

Example case_eval_fun_fbs : 
  fbs_expr 1000 [(inl "X", VClos [(inl "Y", ttrue)] [] 0 [] (EVar "Y")); (inl "Y", ttrue)] 1
   (ECase (EValues [EVar "X"; EVar "Y"])
         [([PLit (Integer 5); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 6)); 
          ([PVar "Z"; PLit (Atom "true")], ELit (Atom "true"), EApp (EVar "Z") [])])
   []
= Result 1 (inl [ttrue]) [].
Proof.
  auto.
Qed.

Example case_eval_fun : 
  |[(inl "X", VClos [(inl "Y", ttrue)] [] 0 [] (EVar "Y")); (inl "Y", ttrue)], 1,
   ECase (EValues [EVar "X"; EVar "Y"])
         [([PLit (Integer 5); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 5)); 
          ([PLit (Integer 6); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 6)); 
          ([PVar "Z"; PLit (Atom "true")], ELit (Atom "true"), EApp (EVar "Z") [])] 
  , []| 
-e> | 1, inl [ttrue], []|.
Proof.
  solve.
Qed.

Example letrec_eval_fbs : 
  fbs_expr 1000 [(inr ("fun4", 0), VClos [] [(0, ("fun4", 0), ([], EMap []))] 0 [] (EMap [])) ; 
    (inl "X", VLit (Integer 42))] 1
   (ELetRec [(("fun2", 0), ([], EVar "X")); 
            (("fun4", 1), (["Z"], EVar "Z"))] 
     (EApp (EFunId ("fun4", 0)) [])) []
=
  Result 3 (inl [VEmptyMap]) [].
Proof.
  auto.
Qed.

Example letrec_eval : 
  |[(inr ("fun4", 0), VClos [] [(0, ("fun4", 0), ([], EMap []))] 0 [] (EMap [])) ; 
    (inl "X", VLit (Integer 42))], 1,
   ELetRec [(("fun2", 0), ([], EVar "X")); 
            (("fun4", 1), (["Z"], EVar "Z"))] 
     (EApp (EFunId ("fun4", 0)) []), []|
-e>
  | 3, inl [VEmptyMap], []|.
Proof.
  solve.
Qed.

Example unnamed_eval_fbs : 
  fbs_expr 1000 [(inl "X", VLit (Integer 5))] 0
   (EApp (EFun ["Y"] (EVar "Y")) [EVar "X"]) []
=
  Result 1 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example unnamed_eval : 
  |[(inl "X", VLit (Integer 5))], 0,
   EApp (EFun ["Y"] (EVar "Y")) [EVar "X"], []|
-e> 
  | 1, inl [VLit (Integer 5)], []|.
Proof.
  solve.
Qed.


Section B_Core.
(*
Definition B : ErlModule := ErlMod "b" [
  TopLevelFun ("fun1", 0) [] (ELit (Integer 6)) ;
  TopLevelFun ("fun2", 0) [] (ELet ["X"] (EFun [] (ELit (Integer 5))) (
                                         ELet ["X"] (EFun [] (ELit (Integer 6)))
                                           (EApp (EVar "X") [])) )
].
*)

Example fun2_fbs : 
  fbs_expr 1000 [] 0
   (ELet ["X"] (EFun [] (ELit (Integer 5))) 
     (ELet ["X"] (EFun [] (ELit (Integer 6))) 
       (EApp (EVar "X") []))) []
=
  Result 2 (inl [VLit (Integer 6)]) [].
Proof.
  auto.
Qed.

Example fun2 : 
  |[], 0,
   ELet ["X"] (EFun [] (ELit (Integer 5))) 
     (ELet ["X"] (EFun [] (ELit (Integer 6))) 
       (EApp (EVar "X") [])), []|
-e>
  | 2, inl [VLit (Integer 6)], []|.
Proof.
  solve.
Qed.

(* Compute initialize_proving B.

Compute initialize_proving_closures B. *)

End B_Core.

Section Documentation_Examples.

Example ex1_fbs : 
  fbs_expr 1000 [] 0 (ELet ["X"] (ELit (Integer 5)) (EVar "X")) []
=
  Result 0 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example ex1 : 
  |[], 0, ELet ["X"] (ELit (Integer 5)) (EVar "X"), []|
-e>
  | 0, inl [VLit (Integer 5)], []|.
Proof.
  solve.
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

Example ex3_fbs :
  fbs_expr 1000 [] 0 (ELetRec [(("X", 0), ([], EApp (EFunId ("X", 0)) []))]
            (EApp (EFunId ("X", 0)) [])) []
=
  Timeout.
Proof.
  auto.
Qed.

Example ex3 :
  |[], 0, ELetRec [(("X", 0), ([], EApp (EFunId ("X", 0)) []))] 
            (EApp (EFunId ("X", 0)) []), []|
-e>
  |1, inl [VEmptyTuple], []|.
Proof.
  try (timeout 4 solve).
Abort.

Example ex4_fbs : 
  fbs_expr 1000 [] 0 (ELet ["X"] (ELit (Integer 4)) 
          (ELet ["X"] (EFun [] (EVar "X")) 
             (ELet ["X"] (EFun [] (EApp (EVar "X") []))
                (EApp (EVar "X") [])))) []
=
  Result 2 (inl [VLit (Integer 4)]) [].
Proof.
  auto.
Qed.

Example ex4 : 
|[], 0, ELet ["X"] (ELit (Integer 4)) 
          (ELet ["X"] (EFun [] (EVar "X")) 
             (ELet ["X"] (EFun [] (EApp (EVar "X") []))
                (EApp (EVar "X") []))), []|
-e>
  |2, inl [VLit (Integer 4)], []|.
Proof.
  solve.
Qed.

End Documentation_Examples.

Example returned_function_fbs :
  fbs_expr 1000 [] 0
   (ELet ["X"] (EFun [] (EFun [] (ELit (Integer 5))))
     (EApp (EApp (EVar "X") []) [])) []
=
  Result 2 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example returned_function :
  |[], 0,
   ELet ["X"] (EFun [] (EFun [] (ELit (Integer 5))))
     (EApp (EApp (EVar "X") []) []), []|
-e>
  | 2, inl [VLit (Integer 5)], []|.
Proof.
  solve.
Qed.

Example returned_recursive_function_fbs : 
  fbs_expr 1000 [] 0
   (ELetRec [(("fun1", 0), ([], (EFun [] (ELit (Integer 5)))))] 
     (EApp (EApp (EFunId ("fun1", 0)) []) [])) []
=
  Result 2 (inl [VLit (Integer 5)]) [].
Proof.
  auto.
Qed.

Example returned_recursive_function : 
  |[], 0,
   ELetRec [(("fun1", 0), ([], (EFun [] (ELit (Integer 5)))))] 
     (EApp (EApp (EFunId ("fun1", 0)) []) []), []|
-e>
  | 2, inl [VLit (Integer 5)], []|.
Proof.
  solve.
Qed.

Example returned_function2_fbs :
  fbs_expr 1000 [(inl "X", VLit (Integer 7))] 0
   (ELet ["X"] (EFun [] (EFun [] (EVar "X")))
     (EApp (EApp (EVar "X") []) [])) []
=
  Result 2 (inl [VLit (Integer 7)]) [].
Proof.
  auto.
Qed.

Example returned_function2 :
  |[(inl "X", VLit (Integer 7))], 0,
   ELet ["X"] (EFun [] (EFun [] (EVar "X")))
     (EApp (EApp (EVar "X") []) []), []|
-e>
  | 2, inl [VLit (Integer 7)], []|.
Proof.
  solve.
Qed.

Example returned_recursive_function2_fbs :
  fbs_expr 1000 [(inl "X", VLit (Integer 7))] 0
   (ELetRec [(("fun1", 0), ([], EFun [] (EVar "X")))] 
     (EApp (EApp (EFunId ("fun1", 0)) []) [])) []
=
  Result 2 (inl [VLit (Integer 7)]) [].
Proof.
  auto.
Qed.

Example returned_recursive_function2 :
  |[(inl "X", VLit (Integer 7))], 0,
   ELetRec [(("fun1", 0), ([], EFun [] (EVar "X")))] 
     (EApp (EApp (EFunId ("fun1", 0)) []) []), []|
-e>
  | 2, inl [VLit (Integer 7)], []|.
Proof.
  solve.
Qed.

Example returned_function3_fbs : 
  fbs_expr 1000 [] 0
   (ELet ["F"] 
     (EFun ["X"] 
        (ELet ["Y"] (ECall "erlang" "+" [EVar "X"; ELit (Integer 3)] ) 
              (EFun ["Z"] 
                    (ECall "erlang" "+" 
                          [ECall "erlang" "+" [EVar "X"; EVar "Y"]
                     ; EVar "Z"]))))
  (EApp (EApp (EVar "F") [ELit (Integer 1)]) [ELit (Integer 1)])) []
=
  Result 2 (inl [VLit (Integer 6)]) [].
Proof.
  auto.
Qed.

Example returned_function3 : 
  |[], 0,
   ELet ["F"] 
     (EFun ["X"] 
        (ELet ["Y"] (ECall "erlang" "+" [EVar "X"; ELit (Integer 3)] ) 
              (EFun ["Z"] 
                    (ECall "erlang" "+" 
                          [ECall "erlang" "+" [EVar "X"; EVar "Y"]
                     ; EVar "Z"]))))
  (EApp (EApp (EVar "F") [ELit (Integer 1)]) [ELit (Integer 1)]), []|
-e>
  |2, inl [VLit (Integer 6)], []|.
Proof.
  solve.
Qed.

Example sum_fbs :
  fbs_expr 1000 [] 0
    (ELetRec [(("f", 1), (["X"], 
      
      ECase (EVar "X") [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 0)); 
                               ([PVar "Y"], ELit (Atom "true"), 
                               ECall "erlang" "+" [
                                     EVar "Y"; 
                                     EApp (EFunId ("f", 1)) [ ECall "erlang" "+" [EVar "Y"; ELit (Integer (Z.pred 0))] ]
                              ])]
      ))] (EApp (EFunId ("f", 1)) [ELit (Integer 2)])) [] 
= Result 1 (inl [VLit (Integer 3)]) [].
Proof.
  auto.
Qed.

Example sum :
  | [], 0,
    ELetRec [(("f", 1), (["X"], 
      
      ECase (EVar "X") [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 0)); 
                               ([PVar "Y"], ELit (Atom "true"), 
                               ECall "erlang" "+" [
                                     EVar "Y"; 
                                     EApp (EFunId ("f", 1)) [ ECall "erlang" "+" [EVar "Y"; ELit (Integer (Z.pred 0))] ]
                              ])]
      ))] (EApp (EFunId ("f", 1)) [ELit (Integer 2)]), []| -e> |1, inl [VLit (Integer 3)], []|.
Proof.
  solve.
Qed.

Example letrec_no_replace_fbs :
  fbs_expr 1000 [] 0
   (ELet ["X"] (ELit (Integer 42)) 
     (ELetRec [(("f", 0), ([], EVar "X"))]
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EFunId ("f", 0)) [])))) []
=
  Result 1 (inl [VLit (Integer 42)]) [].
Proof.
  auto.
Qed.

Example letrec_no_replace :
  |[], 0,
   ELet ["X"] (ELit (Integer 42)) 
     (ELetRec [(("f", 0), ([], EVar "X"))]
       (ELet ["X"] (ELit (Integer 5))
         (EApp (EFunId ("f", 0)) []))), []|
-e>
  | 1, inl [VLit (Integer 42)], []|.
Proof.
  solve.
Qed.

Example seq_eval1_fbs :
  fbs_expr 1000 [] 0 (ESeq (ELet ["X"] (ELit (Integer 42)) (EVar "X"))
                (ELet ["Y"] (ELit (Integer 20)) (EVar "Y")))
   []
=
  Result 0 (inl [VLit (Integer 20)]) [].
Proof.
  auto.
Qed.

Example seq_eval1 :
  | [], 0, ESeq (ELet ["X"] (ELit (Integer 42)) (EVar "X"))
                (ELet ["Y"] (ELit (Integer 20)) (EVar "Y"))
   , [] |
-e>
  | 0, inl [VLit (Integer 20)], [] |.
Proof.
  solve.
Qed.

End Automated_Tests.