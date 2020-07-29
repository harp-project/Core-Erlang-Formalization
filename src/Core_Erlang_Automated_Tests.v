Require Core_Erlang_Tactics.

(**
  IMPORTANT NOTICE:
  To use the `solve` tactic, the abbreviations (e.g. `EEmptyTuple`)
  should not be used (use `ETuple []` instead).
*)

Module Automated_Tests.

Import Core_Erlang_Tactics.Tactics.
Import Core_Erlang_Semantics.Semantics.
Import ListNotations.

(** This is an edless recursion *)
Example eval_letrec1 : 
  |[], 0, ELetRec [(("x"%string, 1), (["X"%string], EApp (EFunId ("x"%string, 1)) [EVar "X"%string])) ]
            (EApp (EFunId ("x"%string, 1)) [ETuple []]), []|
-e> 
  |1, inl ErrorValue, []|.
Proof.
  try(timeout 5 solve).
Abort.

(* This is not accepted by the compiler in Core Erlang 
  TODO: contains application exception: solve hasn't been working yet!
*)
(* Example eval_letrec2 : 
  |[], 0, ELet [("F"%string, EFun ["X"%string] 
         (EApp (EVar "F"%string) [EVar "X"%string]))] 
            (EApp (EVar "F"%string) [ETuple []]), []| 
-e>
|1, inr novar, []|.
Proof.
  try(timeout 10 solve).
Qed. *)

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
  try(timeout 5 solve).
Qed.

Example multiple_top_level_funs2 :
  | [], 0, ELetRec [(("fun1"%string,0), ([], EApp (EFunId ("fun3"%string, 0)) [])); 
                    (("fun2"%string,0), ([], ELit (Integer 42))); 
                    (("fun3"%string,0), ([], EApp (EFunId ("fun2"%string, 0)) []))]
     (EApp (EFunId ("fun1"%string,0)) []), [] |
-e>
  |3, inl (VLit (Integer 42)), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example top_overwrite : 
  |[(inr ("fun2"%string, 0), 
       VClos [] [(0, ("fun2"%string, 0),([],  (ELit (Integer 42)) ))] 0 [] (ELit (Integer 42)))], 1,
  ELetRec [(("fun2"%string, 0), ([], ELit (Integer 40)))] 
     (EApp (EFunId ("fun2"%string, 0)) []), [] | 
-e>
  |2, inl (VLit (Integer 40)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example top_no_overwrite : 
  |[(inr ("fun2"%string, 0), 
     VClos [] [(0, ("fun2"%string, 0), ([], ELit (Integer 42)))] 0 [] (ELit (Integer 42)))], 1,
   ELetRec [(("fun2"%string, 1), (["X"%string], (ELit (Integer 40))))] 
     (EApp (EFunId ("fun2"%string, 0)) []), [] |
-e> 
  | 2, inl (VLit (Integer 42)), []|.
Proof.
  try(timeout 5 solve).
Qed.

(** This is not accepted by the compiler in Core Erlang *)
Example eval_let_func : 
  |[(inl "X"%string, VLit (Integer 42))], 0,
   ELet [("X"%string, EFun [] (ENil)); ("X"%string, EFun [] (EMap []))] 
     (EMap []), []| 
-e> 
  |2, inl (VMap []), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example eval_let_apply : 
  |[(inl "X"%string, VLit (Integer 42))], 0,
   ELet [("Y"%string, EFun [] (EVar "X"%string))] 
     (EApp (EVar "Y"%string) []), []| 
-e> 
  |1, inl (VLit (Integer 42)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example eval_muliple_let : 
  |[], 0, ELet [("X"%string, ELit (Integer 1))] 
            (ELet [("X"%string, ELit (Integer 2))] 
               (EVar "X"%string)), []| 
-e> 
  |0, inl (VLit (Integer 2)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example let_eval_1 : 
  |[], 0, ELet [("X"%string, ETuple [])] (EMap []), []|
-e>
  | 0, inl (VMap []), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example let_eval_2 : 
  |[(inl "X"%string, VMap [])], 0, ELet [("X"%string, ETuple [])] (EMap []), []| 
-e> 
  | 0, inl (VMap []), []|.
Proof.
  try(timeout 5 solve).
Qed.

(** This shouldn't compile in Core Erlang *)
Example eval_let_3 : 
  |[(inl "X"%string, VMap [])], 0,
   ELet [("X"%string, ETuple []); ("X"%string, ENil); ("Y"%string, EVar "X"%string)]
     (EVar "Y"%string), []|
-e>
  |0, inl (VMap []), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example let_eval_4 : 
  |[], 0, ELet [("X"%string, ELit (Integer 5))] (EVar "X"%string), []| 
-e> 
  | 0, inl (VLit (Integer 5)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example tuple_eval : 
  |[(inl "X"%string, VLit (Atom "foo"%string)); 
    (inl "Y"%string, VEmptyTuple)], 0,
   ETuple [ELit (Integer 5); EVar "X"%string; EVar "Y"%string], []| 
-e>
  |0, inl (VTuple [VLit (Integer 5); VLit (Atom "foo"%string); VEmptyTuple]), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example apply_eval : 
  |[(inl "Minus"%string,
      VClos [] [] 0 ["X"%string; "Y"%string] (ELit (Integer 42))) ; 
    (inl "X"%string, VMap [])], 1,
   EApp (EVar "Minus"%string) [EVar "X"%string; EVar "X"%string], []|
-e>
  |1, inl (VLit (Integer 42)), []|.
Proof.
  try(timeout 5 solve).
Qed.


Example list_eval : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   ECons (EVar "X"%string) (ENil), []| 
-e>
  | 0, inl (VCons (VLit (Integer 5)) (VNil)), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example let_eval_overwrite : 
  |[], 0, ELet [("X"%string, EFun [] (ETuple []))] 
           (ELet [("X"%string, ELit (Integer 5))] 
             (EVar "X"%string)), []|
-e>
  | 1, inl (VLit (Integer 5)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example map_eval :
  |[(inl "X"%string, VLit (Integer 42))], 0,
    EMap [(ELit (Integer 5), EVar "X"%string)], []|
-e>
  | 0, inl (VMap [(VLit (Integer 5), VLit (Integer 42))]), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example map_eval3 : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   EMap [(ELit (Integer 5), EVar "X"%string); 
         (EVar "X"%string, ECall "+" 
                              [ELit (Integer 1); (EVar "X"%string)])] 
  , []| 
-e> 
  | 0, inl (VMap [(VLit (Integer 5), VLit (Integer 6))]), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
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
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example call_eval : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   ECall "+"%string [EVar "X"%string ; ELit (Integer 2)], []|
-e> 
  |0, inl (VLit (Integer 7)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example mutliple_function_let : 
  |[], 0,
   ELet [("Z"%string, ECall "+"%string [ELit (Integer 2) ; ELit (Integer 2)] )] 
     (ELet [("Y"%string, EFun [] (EVar "Z"%string))] 
        (ELet [("X"%string, EFun [] (EApp (EVar "Y"%string) []))] 
          (EApp (EVar "X"%string) []))), []|
-e>
  | 2, inl (VLit (Integer 4)), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example case_eval2 :
  |[(inl "X"%string, VEmptyTuple)], 0,
   ECase (EVar "X"%string) 
         [(PLit (Integer 5), ELit (Atom "true"%string), ELit (Integer 5)); 
          (PLit (Integer 6), ELit (Atom "true"%string), ELit (Integer 6));
          (PVar "Z"%string, ELit (Atom "false"%string), EVar "Z"%string);
          (PVar "Z"%string, ELit (Atom "true"%string), EMap [])]

  , []|
-e> 
  | 0, inl (VMap []), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.


Example letrec_eval : 
  |[(inr ("fun4"%string, 0), VClos [] [(0, ("fun4"%string, 0), ([], EMap []))] 0 [] (EMap [])) ; 
    (inl "X"%string, VLit (Integer 42))], 1,
   ELetRec [(("fun2"%string, 0), ([], EVar "X"%string)); 
            (("fun4"%string, 1), (["Z"%string],EVar "Z"%string))] 
     (EApp (EFunId ("fun4"%string, 0)) []), []|
-e>
  | 3, inl (VMap []), []|.
Proof.
  try(timeout 5 solve).
Qed.


Example unnamed_eval : 
  |[(inl "X"%string, VLit (Integer 5))], 0,
   EApp (EFun ["Y"%string] (EVar "Y"%string)) [EVar "X"%string], []|
-e> 
  | 1, inl (VLit (Integer 5)), []|.
Proof.
  try(timeout 5 solve).
Qed.


Section B_Core.

Definition B : ErlModule := ErlMod "b"%string [
  TopLevelFun ("fun1"%string, 0) [] (ELit (Integer 6)) ;
  TopLevelFun ("fun2"%string, 0) [] (ELet [("X"%string, (EFun [] (ELit (Integer 5))))] (
                                         ELet [("X"%string, (EFun [] (ELit (Integer 6))))] 
                                           (EApp (EVar "X"%string) [])) )
].


Example fun2 : 
  |[], 0,
   ELet [("X"%string, (EFun [] (ELit (Integer 5))))] 
     (ELet [("X"%string, (EFun [] (ELit (Integer 6))))] 
       (EApp (EVar "X"%string) [])), []|
-e>
  | 2, inl (VLit (Integer 6)), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

(* 
  TODO: solve can't be used yet for exceptions
Example ex2 : 
  |[], 0,
   ELet [("X"%string, EFun [] (EApp (EVar "X"%string) []))] 
     (EApp (EVar "X"%string) []), []|
-e>
  | 1, inr novar, []|.
Proof.
  try(timeout 5 solve).
Qed. *)

Example ex3 :
  |[], 0, ELetRec [(("X"%string, 0), ([], EApp (EFunId ("X"%string, 0)) []))] 
            (EApp (EFunId ("X"%string, 0)) []), []|
-e>
  |1, inl (VEmptyTuple), []|.
Proof.
  try(timeout 5 solve).
Abort.

Example ex4 : 
|[], 0, ELet [("X"%string, ELit (Integer 4))] 
          (ELet [("X"%string, EFun [] (EVar "X"%string))] 
             (ELet [("X"%string, EFun [] (EApp (EVar "X"%string) []))] 
                (EApp (EVar "X"%string) []))), []|
-e>
  |2, inl (VLit (Integer 4)), []|.
Proof.
  try(timeout 5 solve).
Qed.

End Documentation_Examples.

Example returned_function :
  |[], 0,
   ELet [("X"%string, EFun [] (EFun [] (ELit (Integer 5))))] 
     (EApp (EApp (EVar "X"%string) []) []), []|
-e>
  | 2, inl (VLit (Integer 5)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example returned_recursive_function : 
  |[], 0,
   ELetRec [(("fun1"%string, 0), ([], (EFun [] (ELit (Integer 5)))))] 
     (EApp (EApp (EFunId ("fun1"%string, 0)) []) []), []|
-e>
  | 2, inl (VLit (Integer 5)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example returned_function2 :
  |[(inl "X"%string, VLit (Integer 7))], 0,
   ELet [("X"%string, EFun [] (EFun [] (EVar "X"%string)))] 
     (EApp (EApp (EVar "X"%string) []) []), []|
-e>
  | 2, inl (VLit (Integer 7)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example returned_recursive_function2 :
  |[(inl "X"%string, VLit (Integer 7))], 0,
   ELetRec [(("fun1"%string, 0), ([], EFun [] (EVar "X"%string)))] 
     (EApp (EApp (EFunId ("fun1"%string, 0)) []) []), []|
-e>
  | 2, inl (VLit (Integer 7)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example returned_function3 : 
  |[], 0,
   ELet [("F"%string, 
     EFun ["X"%string] 
        (ELet [("Y"%string, ECall "+"%string [EVar "X"%string; ELit (Integer 3)] )] 
              (EFun ["Z"%string] 
                    (ECall "+"%string 
                          [ECall "+"%string [EVar "X"%string; EVar "Y"%string]
                     ; EVar "Z"%string]))))]
  (EApp (EApp (EVar "F"%string) [ELit (Integer 1)]) [ELit (Integer 1)]), []|
-e>
  |2, inl (VLit (Integer 6)), []|.
Proof.
  try(timeout 5 solve).
Qed.

Example sum :
  | [], 0,
    ELetRec [(("f"%string, 1), (["X"%string], 
      
      ECase (EVar "X"%string) [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 0)); 
                               (PVar "Y"%string, ELit (Atom "true"%string), 
                               ECall "+"%string [
                                     EVar "Y"%string; 
                                     EApp (EFunId ("f"%string, 1)) [ECall "+"%string [EVar "Y"%string; ELit (Integer (Z.pred 0))] ]
                              ])]
      ))] (EApp (EFunId ("f"%string, 1)) [ELit (Integer 2)]), []| -e> |1, inl (VLit (Integer 3)), []|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example seq_eval1 :
  | [], 0, ESeq (ELet [("X"%string, ELit (Integer 42))] (EVar "X"%string))
                (ELet [("Y"%string, ELit (Integer 20))] (EVar "Y"%string))
   , [] |
-e>
  | 0, inl (VLit (Integer 20)), [] |.
Proof.
  try(timeout 5 solve).
Qed.

End Automated_Tests.