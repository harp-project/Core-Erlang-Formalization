From CoreErlang.Eqvivalence.BsFs Require Import Helpers.

Import BigStep.

Open Scope string_scope.

(** CONTENT:
* ERASE_NAMES_TEST_SUCCESS (LEMMAS)
  - EraseNames_Test_Compute
  - EraseNames_Test_Success
* ERASE_NAMES_TEST_EXCEPTION (LEMMAS)
  - EraseNames_Test_Exception
*)












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_NAMES_TEST_SUCCESS /////////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EraseNames_Test_Compute.



Compute erase_names
  []
  (ECons ENil (ELit (Integer 1))).
(*
  ° Syntax.ECons (˝ Syntax.VNil) (˝ Syntax.VLit 1%Z)
*)



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (EVar "X").



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (ECons ENil (EVar "X")).
(*
  ° Syntax.ECons (˝ Syntax.VNil) (˝ Syntax.VLit 2%Z)
*)



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (EFun ["X"] (EVar "X")).
(*
  ° Syntax.EFun 1 (˝ VVar 0)
*)



Compute erase_names
  [(inl "X", (VLit (Integer 2)))]
  (ECons (EVar "X") (EFun ["X"] (EVar "X"))).
(*
  ° Syntax.ECons (˝ Syntax.VLit 2%Z) (° Syntax.EFun 1 (˝ VVar 0))
*)



Compute erase_names
  []
  (ELetRec [(("x", 1), (["X"], EApp (EFunId ("x", 1)) [EVar "X"])) ]
           (EApp (EFunId ("x", 1)) [ETuple []])).
(*
° Syntax.ELetRec [(1, ° Syntax.EApp (˝ VFunId (1, 1)) [˝ VVar 0])]
           (° Syntax.EApp (˝ VFunId (0, 1)) [° Syntax.ETuple []])
*)



Compute erase_names
  [(inl "X", (VLit (Integer 1))); (inl "Z", (VLit (Integer 4)))]
  (ELet
    ["X"; "Y"]
    (EValues [EVar "Z"; ELit (Integer 3)]) (EFun ["X"]
    (ETuple [EVar "X"; EVar "Y"; EVar "Z"]))).



Compute erase_names
  [(inl "X",
    (VClos
      [(inl "Z", (VLit (Integer 1))); (inl "X", (VLit (Integer 1))); (inl "Y", (VLit (Integer 4)))]
      []
      0
      ["Y";"X"]
      (ETuple [EVar "X"; EVar "Y"])))]
  (EVar "X").



End EraseNames_Test_Compute.









Section EraseNames_Test_Success.



  Lemma erase_names_test_X1 :
    step_any
      []
      (erase_names
        []
        ((ELetRec [(("fun1",0), ([], EApp (EFunId ("fun3", 0)) []));
                    (("fun2",0), ([], ELit (Integer 42))); 
                    (("fun3",0), ([], EApp (EFunId ("fun2", 0)) []))]
                  (EApp (EFunId ("fun1",0)) []))))
      (erase_result
        ((inl [VLit (Integer 42)]))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X2 :
    step_any
      []
      (erase_names
        []
        (ELetRec
          [(("f", 1), (["X"],
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
           )))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 50 do_step.
  Qed.



  Lemma erase_names_test_X3 :
    step_any
      []
      (erase_names
        [(inr ("fun2", 0), 
         VClos [] [(0, ("fun2", 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))]
        (ELetRec [(("fun2", 0), ([], ELit (Integer 40)))] 
           (EApp (EFunId ("fun2", 0)) [])))
      (erase_result
        (inl [VLit (Integer 40)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X4 :
    step_any
      []
      (erase_names
        [(inr ("fun2", 0), 
           VClos [] [(0, ("fun2", 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)))]
        (ELetRec [(("fun2", 1), (["X"], (ELit (Integer 40))))] 
           (EApp (EFunId ("fun2", 0)) [])))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X5 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["X"; "X"] (EValues [EFun [] ENil; EFun [] (EMap [])])
           (EMap [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X6 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (ELet ["Y"] (EValues [EFun [] (EVar "X")])
          (EApp (EVar "Y") [])))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X7 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 1)) 
              (ELet ["X"] (ELit (Integer 2)) 
                 (EVar "X"))))
      (erase_result
        (inl [VLit (Integer 2)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X8 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ETuple []) (EMap [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X9 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyMap)]
        (ELet ["X"] (ETuple []) (EMap [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X10 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyMap)]
        (ELet ["X"; "X"; "Y"] (EValues [ETuple []; ENil; EVar "X"])
          (EVar "Y")))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X11 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 5)) (EVar "X")))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 5 do_step.
  Qed.



  Lemma erase_names_test_X12 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Atom "foo")); 
          (inl "Y", VEmptyTuple)]
        (ETuple [ELit (Integer 5); EVar "X"; EVar "Y"]))
      (erase_result
        (inl [VTuple [VLit (Integer 5); VLit (Atom "foo"); VEmptyTuple]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 9 do_step.
  Qed.



  Lemma erase_names_test_X13 :
    step_any
      []
      (erase_names
        [(inr ("Plus", 2), 
         VClos [] [(0, ("Plus", 2),
                       (["X" ; "Y"], ELit (Integer 3)))] 
                  0 ["X" ; "Y"] 
                  (ELit (Integer 3)))]
        (EApp (EFunId ("Plus", 2)) [ELit (Integer 2); ELit (Integer 3)]))
      (erase_result
        (inl [VLit (Integer 3)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X14 :
    step_any
      []
      (erase_names
        [(inl "Minus",
            VClos [] [] 0 ["X"; "Y"] (ELit (Integer 42))) ; 
          (inl "X", VEmptyMap)]
        (EApp (EVar "Minus") [EVar "X"; EVar "X"]))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X15 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (ECons (EVar "X") (ENil)))
      (erase_result
        (inl [VCons (VLit (Integer 5)) (VNil)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X16 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (ECons (EVar "X") 
           (ECons (EVar "X") 
                  (ENil))))
      (erase_result
        (inl [VCons (VLit (Integer 5))
                   (VCons (VLit (Integer 5)) 
                          (VNil))])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X17 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (EFun [] (ETuple [])) 
             (ELet ["X"] (ELit (Integer 5)) 
               (EVar "X"))))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X18 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (EMap [(ELit (Integer 5), EVar "X")]))
      (erase_result
        (inl [VMap [(VLit (Integer 5), VLit (Integer 42))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X19 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 42))]
        (EMap [(ELit (Integer 54), EVar "X"); (EVar "X", EVar "X")] ))
      (erase_result
        (inl [VMap [(VLit (Integer 42), VLit (Integer 42)); 
                   (VLit (Integer 54), VLit (Integer 42))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X20 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (EMap [(ELit (Integer 5), EVar "X"); 
           (EVar "X", ECall (ELit (Atom "erlang")) (ELit (Atom "+")) 
                                [ELit (Integer 1); (EVar "X")])]))
      (erase_result
        (inl [VMap [(VLit (Integer 5), VLit (Integer 6))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X21 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"; "Y"; "Z"] 
              (EValues [EFun [] (ELit (Integer 1)); 
                        EFun [] (ELit (Integer 2)); 
                        EFun [] (ELit (Integer 3))])
           (EMap [(EVar "Z", ELit (Integer 10)); 
                  (EVar "X", ELit (Integer 11));
                  (EVar "Y", ELit (Integer 12)); 
                  (EVar "X", ELit (Integer 13))])))
      (erase_result
        (inl [VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                    (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                    (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))]])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
      do 16 do_step.
      do 1 do_step.
      (* make_val_map different ?*)
      (* maybe the id?*)
  Admitted.



  Lemma erase_names_test_X22 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 42))
         (ELet ["Y"] (EFun ["X"] (EVar "X")) 
           (ELet ["X"] (ELit (Integer 5))
             (EApp (EVar "Y") [ELit (Integer 7)])))))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 17 do_step.
  Qed.



  Lemma erase_names_test_X23 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 42)) 
         (ELet ["Y"] (EFun [] (EVar "X"))
           (ELet ["X"] (ELit (Integer 5))
             (EApp (EVar "Y") [])))))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X24 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X" ; ELit (Integer 2)]))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



  Lemma erase_names_test_X25 :
    step_any
      []
      (erase_names
        []
        (ELet ["Z"] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 2) ; ELit (Integer 2)] ) 
         (ELet ["Y"] (EFun [] (EVar "Z"))
            (ELet ["X"] (EFun [] (EApp (EVar "Y") [])) 
              (EApp (EVar "X") [])))))
      (erase_result
        (inl [VLit (Integer 4)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 28 do_step.
  Qed.



  Lemma erase_names_test_X26 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyTuple)]
        (ECase (EVar "X")
           [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
            ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6)); 
            ([PVar "Z"], ELit (Atom "true"), EVar "Z") ]))
      (erase_result
        (inl [VEmptyTuple])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 10 do_step.
  Qed.



  Lemma erase_names_test_X27 :
    step_any
      []
      (erase_names
        [(inl "X", VEmptyTuple)]
        (ECase (EVar "X") 
           [([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 5)); 
            ([PLit (Integer 6)], ELit (Atom "true"), ELit (Integer 6));
            ([PVar "Z"], ELit (Atom "false"), EVar "Z");
            ([PVar "Z"], ELit (Atom "true"), EMap [])]))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X28 :
    step_any
      []
      (erase_names
        [(inl "X", VClos [(inl "Y", VLit (Atom "true"))] [] 0 [] (EVar "Y")); (inl "Y", VLit (Atom "true"))]
        (ECase (EValues [EVar "X"; EVar "Y"])
           [([PLit (Integer 5); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 5)); 
            ([PLit (Integer 6); PLit (Atom "true")], ELit (Atom "true"), ELit (Integer 6)); 
            ([PVar "Z"; PLit (Atom "true")], ELit (Atom "true"), EApp (EVar "Z") [])]))
      (erase_result
        (inl [VLit (Atom "true")])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 18 do_step.
  Qed.



  Lemma erase_names_test_X29 :
    step_any
      []
      (erase_names
        [(inr ("fun4", 0), VClos [] [(0, ("fun4", 0), ([], EMap []))] 0 [] (EMap [])) ; 
          (inl "X", VLit (Integer 42))]
        (ELetRec [(("fun2", 0), ([], EVar "X")); 
              (("fun4", 1), (["Z"], EVar "Z"))] 
          (EApp (EFunId ("fun4", 0)) [])))
      (erase_result
        (inl [VEmptyMap])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X30 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 5))]
        (EApp (EFun ["Y"] (EVar "Y")) [EVar "X"]))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X31 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (EFun [] (ELit (Integer 5))) 
         (ELet ["X"] (EFun [] (ELit (Integer 6))) 
           (EApp (EVar "X") []))))
      (erase_result
        (inl [VLit (Integer 6)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X32 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 5)) (EVar "X")))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 5 do_step.
  Qed.



  Lemma erase_names_test_X33 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 4)) 
            (ELet ["X"] (EFun [] (EVar "X")) 
               (ELet ["X"] (EFun [] (EApp (EVar "X") []))
                  (EApp (EVar "X") [])))))
      (erase_result
        (inl [VLit (Integer 4)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X34 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (EFun [] (EFun [] (ELit (Integer 5))))
        (EApp (EApp (EVar "X") []) [])))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X35 :
    step_any
      []
      (erase_names
        []
        (ELetRec [(("fun1", 0), ([], (EFun [] (ELit (Integer 5)))))] 
        (EApp (EApp (EFunId ("fun1", 0)) []) [])))
      (erase_result
        (inl [VLit (Integer 5)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



  Lemma erase_names_test_X36 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 7))]
        (ELet ["X"] (EFun [] (EFun [] (EVar "X")))
       (EApp (EApp (EVar "X") []) [])))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X37 :
    step_any
      []
      (erase_names
        [(inl "X", VLit (Integer 7))]
        (ELetRec [(("fun1", 0), ([], EFun [] (EVar "X")))] 
        (EApp (EApp (EFunId ("fun1", 0)) []) [])))
      (erase_result
        (inl [VLit (Integer 7)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



  Lemma erase_names_test_X38 :
    step_any
      []
      (erase_names
        []
        (ELet ["F"] 
       (EFun ["X"] 
          (ELet ["Y"] (ECall (ELit (Atom "erlang" ))  (ELit (Atom "+" )) [EVar "X"; ELit (Integer 3)] ) 
                (EFun ["Z"] 
                      (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))
                            [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "X"; EVar "Y"]
                       ; EVar "Z"]))))
    (EApp (EApp (EVar "F") [ELit (Integer 1)]) [ELit (Integer 1)])))
      (erase_result
        (inl [VLit (Integer 6)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 47 do_step.
  Qed.



  Lemma erase_names_test_X39 :
    step_any
      []
      (erase_names
        []
        (ELetRec [(("f", 1), (["X"], 
          ECase (EVar "X") [([PLit (Integer 0)], ELit (Atom "true"), ELit (Integer 0)); 
                                 ([PVar "Y"], ELit (Atom "true"), 
                                 ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [
                                       EVar "Y"; 
                                       EApp (EFunId ("f", 1)) [ ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [EVar "Y"; ELit (Integer (Z.pred 0))] ]
                                ])]
        ))] (EApp (EFunId ("f", 1)) [ELit (Integer 2)])))
      (erase_result
        (inl [VLit (Integer 3)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 74 do_step.
  Qed.



  Lemma erase_names_test_X40 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"] (ELit (Integer 42)) 
         (ELetRec [(("f", 0), ([], EVar "X"))]
           (ELet ["X"] (ELit (Integer 5))
             (EApp (EFunId ("f", 0)) [])))))
      (erase_result
        (inl [VLit (Integer 42)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X41 :
    step_any
      []
      (erase_names
        []
        (ESeq (ELet ["X"] (ELit (Integer 42)) (EVar "X"))
                  (ELet ["Y"] (ELit (Integer 20)) (EVar "Y"))))
      (erase_result
        (inl [VLit (Integer 20)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 11 do_step.
  Qed.



End EraseNames_Test_Success.












(*
////////////////////////////////////////////////////////////////////////////////
//// CHAPTER: ERASE_NAMES_TEST_EXCEPTION ///////////////////////////////////////
////////////////////////////////////////////////////////////////////////////////
*)






Section EraseNames_Test_Exception.



  Lemma erase_names_test_X42 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X43 :
    step_any
      []
      (erase_names
        []
        (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])   (ELit (Atom "error"%string))) )
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 16 do_step.
  Qed.



  Lemma erase_names_test_X44 :
    step_any
      []
      (erase_names
        []
        (ECons (ELit (Atom "error"%string)) (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ENil))))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 18 do_step.
  Qed.



  Lemma erase_names_test_X45 :
    step_any
      []
      (erase_names
        []
        (ETuple [ELit (Atom "error"%string) ; ELit (Atom "error"%string); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X46 :
    step_any
      []
      (erase_names
        []
        (ETry (ETuple []) ["X"%string]
                 (ELit (Atom "ok"%string)) 
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ELit (Atom "error"%string))))
      (erase_result
        (inl [VLit (Atom "ok")])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 6 do_step.
  Qed.



  Lemma erase_names_test_X47 :
    step_any
      []
      (erase_names
        []
        (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
                 (ELit (Atom "ok"%string))
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ELit (Atom "error"%string))))
      (erase_result
        (inl [VLit (Atom "error"%string)])).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X48 :
    step_any
      []
      (erase_names
        []
        (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
                 (ELit (Atom "ok"%string))
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 25 do_step.
  Qed.



  Lemma erase_names_test_X49 :
    step_any
      []
      (erase_names
        []
        (ETry (ETuple []) ["X"%string]
                 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                 ["Ex1"%string; "Ex2"%string; "Ex3"%string]
                 (ELit (Atom "error"%string))))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 16 do_step.
  Qed.



  Lemma erase_names_test_X50 :
    step_any
      []
      (erase_names
        []
        (ECase (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                   [([PVar "X"%string], ELit (Atom "true"), ELit (Integer 1))]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X51 :
    step_any
      []
      (erase_names
        [(inl "Y"%string, VLit (Integer 2))]
        (ECase (EVar "Y"%string)
            [([PLit (Integer 1)], ELit (Atom "true"), ELit (Integer 1)); 
             ([PVar "Z"%string], ELit (Atom "false"), ELit (Integer 2))]))
      (erase_result
        (inr (if_clause))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 8 do_step.
  Qed.



  Lemma erase_names_test_X52 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string []))
      (erase_result
        (inr (undef (VLit (Atom "+"))))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X53 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ETuple []]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 12 do_step.
  Qed.



  Lemma erase_names_test_X54 :
    step_any
      []
      (erase_names
        []
        (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 21 do_step.
  Qed.



  Lemma erase_names_test_X55 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"%string; "Y"%string] 
                 (EValues [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) (ETuple [])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 19 do_step.
  Qed.



  Lemma erase_names_test_X56 :
    step_any
      []
      (erase_names
        []
        (ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
                 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 20 do_step.
  Qed.



  Lemma erase_names_test_X57 :
    step_any
      []
      (erase_names
        []
        (EApp (ELit (Integer 4)) [ELit (Integer 5); ELit (Integer 5)]))
      (erase_result
        (inr (badfun (VLit (Integer 4))))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 9 do_step.
  Qed.



  Lemma erase_names_test_X58 :
    step_any
      []
      (erase_names
        []
        (EApp (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) [ELit (Integer 5); ELit (Integer 5)]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X59 :
    step_any
      []
      (erase_names
        [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))]
        (EApp (EVar "X"%string) [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 17 do_step.
  Qed.



  Lemma erase_names_test_X60 :
    step_any
      []
      (erase_names
        [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))]
        (EApp (EVar "X"%string) [ELit (Integer 2)]))
      (erase_result
        (inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)))))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 7 do_step.
  Qed.



  Lemma erase_names_test_X61 :
    step_any
      []
      (erase_names
        [(inl "X"%string, VClos [] [] 0 [] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))]
        (EApp (EVar "X"%string) []))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 16 do_step.
  Qed.



  Lemma erase_names_test_X62 :
    step_any
      []
      (erase_names
        []
        (ELetRec [(("fun1"%string, 0), ([], ELit (Atom "error"%string)))] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 13 do_step.
  Qed.



  Lemma erase_names_test_X63 :
    step_any
      []
      (erase_names
        []
        (EMap [(ELit (Atom "error"%string),  ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []], ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string))]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 22 do_step.
  Qed.



  Lemma erase_names_test_X64 :
    step_any
      []
      (erase_names
        []
        (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string))]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 20 do_step.
  Qed.



  Lemma erase_names_test_X65 :
    step_any
      []
      (erase_names
        []
        (ESeq (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                  (ELit (Integer 42))))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 14 do_step.
  Qed.



  Lemma erase_names_test_X66 :
    step_any
      []
      (erase_names
        []
        (ESeq (ELit (Integer 42))
                  (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 15 do_step.
  Qed.



  Lemma erase_names_test_X67 :
    step_any
      []
      (erase_names
        []
        (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                  (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                  (ELit (Atom "error"%string), ELit (Atom "error"%string));
                  (ELit (Atom "error"%string), ELit (Atom "error"%string))], ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])])])])])])]))
      (erase_result
        (inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])))).
  Proof.
    cbn.
    eei; spl.
    * cns; scope_solver.
    * do 114 do_step.
  Qed.



End EraseNames_Test_Exception.