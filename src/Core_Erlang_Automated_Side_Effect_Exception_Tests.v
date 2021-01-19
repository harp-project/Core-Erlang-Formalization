Require Core_Erlang_Tactics.
Require Core_Erlang_Functional_Big_Step.

Module Side_Effect_Exception_Tests.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.
Import Core_Erlang_Functional_Big_Step.Functional_Big_Step.

Import ListNotations.


(** 
  Every first example: functional big-step semantics
  Every second example: big-step semantics
*)
Definition side_exception_exp (a : Z) (s : string) : Expression := ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom s)])
      (EApp (ELit (Integer a)) []).

Example side_exception_fbs (env : Environment) (eff : SideEffectList) (a : Z)
                       (s : string) (id : nat) :
  fbs_expr 1000 env id (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom s)])
      (EApp (ELit (Integer a)) [])) eff
=
  Result id (inr (badfun (VLit (Integer a)))) (app eff [(Output, [VLit (Atom s)])]).
Proof.
  auto.
Qed.

Example side_exception (env : Environment) (eff : SideEffectList) (a : Z)
                       (s : string) (id : nat) :
  | env, id, ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom s)])
      (EApp (ELit (Integer a)) []) , eff| 
-e>
  |id, inr (badfun (VLit (Integer a))), app eff [(Output, [VLit (Atom s)])]|.
Proof.
  solve.
Qed.

Example eval_list_tail_fbs :
  fbs_expr 1000 [] 0 (ECons (ECall "fwrite" [ELit (Atom "a")]) (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) []))) []
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example eval_list_tail :
  | [], 0, ECons (ECall "fwrite" [ELit (Atom "a")]) (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) [])), []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "b")])]|.
Proof.
  solve.
Qed.

Example eval_list_head_fbs :
  fbs_expr 1000 [] 0 (ECons (EApp (ELit (Integer 0)) []) (ECall "fwrite" [ELit (Atom "a")])) [] 
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example eval_list_head :
  | [], 0, ECons (EApp (ELit (Integer 0)) []) (ECall "fwrite" [ELit (Atom "a")]), []| 
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_tuple_s_e_fbs :
  fbs_expr 1000 [] 0 (ETuple [ECall "fwrite" [ELit (Atom "a")]; ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) [])]) []
=
  Result 0 (inr (badfun (VLit (Integer 0))))
          [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example eval_tuple_s_e :
  | [], 0, ETuple [ECall "fwrite" [ELit (Atom "a")]; ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) [])], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
          [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  solve.
Qed.

Example eval_try_s_e_fbs :
  fbs_expr 1000 [] 0 (ETry (ECall "fwrite" [ELit (Atom "a")]) ["X"%string] 
  (ELet
     ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
       (EApp (ELit (Integer 0)) [])) 
  ["Ex1"%string; "Ex2"%string; "Ex3"%string]
  (ELit (Atom "error"%string))) []
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example eval_try_s_e :
  | [], 0, ETry (ECall "fwrite" [ELit (Atom "a")]) ["X"%string] 
  (ELet
     ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
       (EApp (ELit (Integer 0)) [])) 
  ["Ex1"%string; "Ex2"%string; "Ex3"%string]
  (ELit (Atom "error"%string))
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  solve.
Qed.

Example eval_catch_fbs :
  fbs_expr 1000 [] 0 (ETry (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) [])) ["X"%string]
   (ECall "fwrite" [ELit (Atom "a")]) 
   ["Ex1"%string; "Ex2"%string; "Ex3"%string]
   (ECall "fwrite" [ELit (Atom "c")])) []
=
  Result 0 (inl [ok]) [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])].
Proof.
  auto.
Qed.

Example eval_catch :
  | [], 0, ETry (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) [])) ["X"%string]
   (ECall "fwrite" [ELit (Atom "a")]) 
   ["Ex1"%string; "Ex2"%string; "Ex3"%string]
   (ECall "fwrite" [ELit (Atom "c")])
  , []|
-e>
  | 0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  solve.
Qed.

Example eval_case_pat_fbs :
  fbs_expr 1000 [] 0 (ECase (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) []))
                 [([PVar "X"%string], ELit (Atom "true"), ECall "fwrite" [ELit (Atom "b")])])
  []
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example eval_case_pat :
  | [],0,  ECase (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) []))
                 [([PVar "X"%string], ELit (Atom "true"), ECall "fwrite" [ELit (Atom "b")])]
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_case_clause_fbs :
  fbs_expr 1000 [(inl "Y"%string, VLit (Integer 2))] 0
     (ECase (ELet ["X"%string] (ECall "fwrite" [ELit (Atom "a")]) (EVar "Y"%string))
          [([PLit (Integer 1)], ELit (Atom "true"), ECall "fwrite" [ELit (Atom "b")]); 
           ([PVar "Z"%string], ELit (Atom "false"), ECall "fwrite" [ELit (Atom "c")])])
  []
=
  Result 0 (inr (if_clause)) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.


Example eval_case_clause :
  | [(inl "Y"%string, VLit (Integer 2))], 0,
     ECase (ELet ["X"%string] (ECall "fwrite" [ELit (Atom "a")]) (EVar "Y"%string))
          [([PLit (Integer 1)], ELit (Atom "true"), ECall "fwrite" [ELit (Atom "b")]); 
           ([PVar "Z"%string], ELit (Atom "false"), ECall "fwrite" [ELit (Atom "c")])]
  , []|
-e>
  | 0, inr (if_clause), [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_call_s_e_fbs :
  fbs_expr 1000 [] 0 (ECall "fwrite" [ECall "fwrite" [ELit (Atom "a")]; EApp (ELit (Integer 0)) []]) []
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example eval_call_s_e :
  | [], 0, ECall "fwrite" [ECall "fwrite" [ELit (Atom "a")]; EApp (ELit (Integer 0)) []], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_apply_closure_ex_fbs :
  fbs_expr 1000 [] 0 (EApp (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) [])) []) []
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example eval_apply_closure_ex :
  | [], 0, EApp (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) [])) [], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_apply_param_fbs :
  fbs_expr 1000 [] 0 (EApp (ECall "fwrite" [ELit (Atom "a")]) [ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) [])]) []
=
  Result 0 (inr (badfun (VLit (Integer 0))))
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example eval_apply_param :
  | [], 0, EApp (ECall "fwrite" [ELit (Atom "a")]) [ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) [])], []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  solve.
Qed.

Example eval_apply_closure_fbs :
  fbs_expr 1000 [] 0 (EApp (ECall "fwrite" [ELit (Atom "a")]) [ECall "fwrite" [ELit (Atom "b")]]) []
=
  Result 0 (inr (badfun (VLit (Atom "ok"))))
      [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example eval_apply_closure :
  | [], 0, EApp (ECall "fwrite" [ELit (Atom "a")]) [ECall "fwrite" [ELit (Atom "b")]], []|
-e>
  | 0, inr (badfun (VLit (Atom "ok"))), 
      [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  solve.
Qed.

Example eval_apply_param_len_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 5)))] 1
    (EApp (EVar "X"%string) [ECall "fwrite" [ELit (Atom "a")]]) []
=
  Result 1 (inr (badarity (VClos [] [] 0 [] (ELit (Integer 5)))))
       [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example eval_apply_param_len :
  | [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 5)))], 1,
    EApp (EVar "X"%string) [ECall "fwrite" [ELit (Atom "a")]], []|
-e>
  | 1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 5)))), 
       [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_let_fbs:
  fbs_expr 1000 [] 0 (ELet ["X"%string] (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 2)) [])) (EApp (ELit (Integer 0)) [])) []
=
  Result 0 (inr (badfun (VLit (Integer 2)))) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example eval_let:
  | [], 0, ELet ["X"%string] (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 2)) [])) (EApp (ELit (Integer 0)) []), []|
-e>
  | 0, inr (badfun (VLit (Integer 2))), [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example eval_map_key_fbs:
  fbs_expr 1000 [] 0 
      (EMap [(ECall "fwrite" [ELit (Atom "a")], ECall "fwrite" [ELit (Atom "b")]);
                 (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "c")])
      (EApp (ELit (Integer 0)) []), ECall "fwrite" [ELit (Atom "d")])])
  []
=
  Result 0 (inr (badfun (VLit (Integer 0))))
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
        (Output, [VLit (Atom "c")])].
Proof.
  auto.
Qed.

Example eval_map_key:
  | [], 0, EMap [(ECall "fwrite" [ELit (Atom "a")], ECall "fwrite" [ELit (Atom "b")]);
                 (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "c")])
      (EApp (ELit (Integer 0)) []), ECall "fwrite" [ELit (Atom "d")])]
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
       [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
        (Output, [VLit (Atom "c")])]|.
Proof.
  solve.
Qed.

Example eval_map_value_fbs:
  fbs_expr 1000 [] 0 
          (EMap [(ECall "fwrite" [ELit (Atom "a")], ECall "fwrite" [ELit (Atom "b")]);
                 (ECall "fwrite" [ELit (Atom "c")], ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "d")])
      (EApp (ELit (Integer 0)) []))])
  []
=
  Result 0 (inr (badfun (VLit (Integer 0))))
        [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
         (Output, [VLit (Atom "c")]); (Output, [VLit (Atom "d")])].
Proof.
  auto.
Qed.

Example eval_map_value:
  | [], 0, EMap [(ECall "fwrite" [ELit (Atom "a")], ECall "fwrite" [ELit (Atom "b")]);
                 (ECall "fwrite" [ELit (Atom "c")], ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "d")])
      (EApp (ELit (Integer 0)) []))]
  , []|
-e>
  | 0, inr (badfun (VLit (Integer 0))), 
        [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); 
         (Output, [VLit (Atom "c")]); (Output, [VLit (Atom "d")])]|.
Proof.
  solve.
Qed.

Example seq_eval_ex_1_fbs :
  fbs_expr 1000 [] 0 (ESeq (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) []))
                (ECall "fwrite" [ELit (Atom "b")]))
   []
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example seq_eval_ex_1 :
  | [], 0, ESeq (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "a")])
      (EApp (ELit (Integer 0)) []))
                (ECall "fwrite" [ELit (Atom "b")])
   , [] |
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")])] |.
Proof.
  solve.
Qed.

Example seq_eval_ex_2_fbs :
  fbs_expr 1000 [] 0 (ESeq (ECall "fwrite" [ELit (Atom "a")])
                (ESeq (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) []))
                      (ECall "fwrite" [ELit (Atom "c")])))
    [] 
=
  Result 0 (inr (badfun (VLit (Integer 0)))) [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example seq_eval_ex_2 :
  | [], 0, ESeq (ECall "fwrite" [ELit (Atom "a")])
                (ESeq (ELet
   ["X"%string] (ECall "fwrite" [ELit (Atom "b")])
      (EApp (ELit (Integer 0)) []))
                      (ECall "fwrite" [ELit (Atom "c")]))
   , [] |
-e>
  | 0, inr (badfun (VLit (Integer 0))), [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] |.
Proof.
  solve.
Qed.

End Side_Effect_Exception_Tests.