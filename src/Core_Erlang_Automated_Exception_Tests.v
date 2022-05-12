Require Core_Erlang_Tactics.
Require Core_Erlang_Functional_Big_Step.

Module Exception_Tests.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.
Import Core_Erlang_Functional_Big_Step.Functional_Big_Step.

Import ListNotations.

Definition exception : ValueSequence + Exception := inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])).

(** 
  Every first example: functional big-step semantics
  Every second example: big-step semantics
*)
Example eval_exception_call_fbs :
  (forall (env : Environment) (eff : SideEffectList) (id : nat), 
  fbs_expr 1000 env [] "" id (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) eff = Result id exception eff).
Proof.
  intros.  reflexivity. 
Qed.

Example eval_exception_call :
  forall {env : Environment}  {eff : SideEffectList} {id : nat}, 
  |env, [], "", id, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []], eff|
-e> 
  |id, exception, eff|.
Proof.
  intros.
  solve.
  
Qed.


Example exception_var_fbs :
  fbs_expr 1000 [] [] "" 0 (EVar "X"%string) [] = Failure.
Proof.
  simpl. reflexivity.
Qed.

(** DOES NOT COMPPILE IN CORE ERLANG *)
Example exception_var :
forall res,
  ~|[], [], "", 0, EVar "X"%string, []|
-e>
  |0, res, []|.
Proof.
  unfold not. intros. inversion H. subst. inversion H5.
Qed.

Example exception_list_hd_fbs :
  fbs_expr 1000 [] [] "" 0 
  (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ELit (Atom "error"%string))) 
  [] = Result 0 exception [].
Proof.
  simpl. reflexivity.
Qed.

Example exception_list_hd :
  |[], [], "", 0, ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ELit (Atom "error"%string)), []|
-e>
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example exception_list_tl_fbs : 
  fbs_expr 1000 [] [] "" 0 (ECons (ELit (Atom "error"%string)) (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ENil))) []
=
  Result 0 exception [].
Proof.
  simpl. reflexivity.
Qed.

Example exception_list_tl : 
  |[], [], "", 0, ECons (ELit (Atom "error"%string)) (ECons (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) (ENil)), []|
-e> 
  | 0, exception, []|.
Proof.
  solve.   

Qed.

Example exception_tuple_fbs : 
  fbs_expr 1000 [] [] "" 0 (ETuple [ELit (Atom "error"%string) ; ELit (Atom "error"%string); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) []
=
  Result 0 exception [].
Proof.
  reflexivity.
Qed.

Example exception_tuple : 
  |[], [], "", 0, ETuple [ELit (Atom "error"%string) ; ELit (Atom "error"%string); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]], []|
-e>
  | 0, exception, []|.
Proof.
  solve. 

Qed.

Example try_eval_fbs : 
  fbs_expr 1000 [] [] "" 0 
               (ETry (ETuple []) ["X"%string]
               (ELit (Atom "ok"%string)) 
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string)))
  []
=
  Result 0 (inl [ok]) []
.
Proof.
  reflexivity.
Qed.

Example try_eval : 
  |[], [], "", 0, ETry (ETuple []) ["X"%string]
               (ELit (Atom "ok"%string)) 
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string)) 
  , []|
-e>
  |0, inl [ok], []|
.
Proof.
  solve.
Qed.

Example try_eval_catch_fbs : 
  fbs_expr 1000 [] [] "" 0 
               (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string)))
  []
=
  Result 0 (inl [VLit (Atom "error"%string)]) []
.
Proof.
  auto.
Qed.

Example try_eval_catch : 
  |[], [], "", 0, ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string)) 
   , []|
-e> 
  |0, inl [VLit (Atom "error"%string)], []|
.
Proof.
  solve.
Qed.

Example try_eval_exception_fbs : 
  fbs_expr 1000 [] [] "" 0 
               (ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))
  []
=
  Result 0 exception []
.
Proof.
  auto.
Qed.

Example try_eval_exception : 
  |[], [], "", 0, ETry (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) 
  , []|
-e>
  |0, exception, []|
.
Proof.
  solve. 
Qed.

Example try_eval_exception2_fbs : 
  fbs_expr 1000 [] [] "" 0 
               (ETry (ETuple []) ["X"%string]
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string)))
  []
=
  Result 0 exception []
.
Proof.
  auto.
Qed.

Example try_eval_exception2 : 
  |[], [], "", 0, ETry (ETuple []) ["X"%string]
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string))
  , []|
-e>
  | 0, exception, []|
.
Proof.
solve.

Qed.

Example eval_case_pat_ex_fbs :
  fbs_expr 1000 [] [] "" 0 (ECase (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                 [([PVar "X"%string], ELit (Atom "true"), ELit (Integer 1))]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example eval_case_pat_ex :
  |[], [], "", 0, ECase (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                 [([PVar "X"%string], ELit (Atom "true"), ELit (Integer 1))], []|
-e>
  | 0, exception, []|.
Proof.
  solve. 
Qed.

Example eval_case_clause_ex_fbs :
  fbs_expr 1000 [(inl "Y"%string, VLit (Integer 2))] [] "" 0
     (ECase (EVar "Y"%string)
          [([PLit (Integer 1)], ELit (Atom "true"), ELit (Integer 1)); 
           ([PVar "Z"%string], ELit (Atom "false"), ELit (Integer 2))]) []
=
  Result 0 (inr (if_clause)) [].
Proof.
  auto.
Qed.

Example eval_case_clause_ex :
  | [(inl "Y"%string, VLit (Integer 2))], [], "", 0,
     ECase (EVar "Y"%string)
          [([PLit (Integer 1)], ELit (Atom "true"), ELit (Integer 1)); 
           ([PVar "Z"%string], ELit (Atom "false"), ELit (Integer 2))], []|
-e>
  | 0, inr (if_clause), []|.
Proof.
  solve.
Qed.

Example call_eval_body_ex_fbs : 
  fbs_expr 1000 [] [] "" 0 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string []) []
=
  Result 0 (inr (undef (VLit (Atom "+")))) [].
Proof.
  auto.
Qed.

Example call_eval_body_ex : 
  |[], [], "", 0, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [], []|
-e>
  | 0, inr (undef (VLit (Atom "+"))), []|.
Proof.
  solve. 
Qed.

Example call_eval_body_ex2_fbs :
  fbs_expr 1000 [] [] "" 0 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ETuple []]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example call_eval_body_ex2 :
  |[], [], "", 0, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ETuple []], []|
-e>
  | 0, exception, []|.
Proof.
  solve. 
Qed.

Example call_eval_param_ex_fbs :
  fbs_expr 1000 [] [] "" 0 (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example call_eval_param_ex :
  |[], [], "", 0, ECall (ELit (Atom "erlang" )) (ELit (Atom "+" ))%string [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]], []|
-e>
  |0, exception, []|.
Proof.
  solve. 
Qed.

Example let_eval_exception_params_fbs :
  fbs_expr 1000 [] [] "" 0 (ELet ["X"%string; "Y"%string] 
               (EValues [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) (ETuple [])) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example let_eval_exception_params :
  |[], [], "", 0, ELet ["X"%string; "Y"%string] 
               (EValues [ELit (Integer 5); ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) (ETuple []), []|
-e>
  | 0, exception, []|.
Proof.
  solve. 
Qed.

Example let_eval_exception_body_fbs :
  fbs_expr 1000 [] [] "" 0 (ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example let_eval_exception_body :
  |[], [], "", 0, ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
               (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]), []|
-e>
  |0, exception, []|.
Proof.
  solve. 
Qed.

Example apply_eval_exception_closure_fbs :
  fbs_expr 1000 [] [] "" 0 (EApp (ELit (Integer 4)) [ELit (Integer 5); ELit (Integer 5)]) []
=
  Result 0 (inr (badfun (VLit (Integer 4)))) [].
Proof.
  auto.
Qed.

Example apply_eval_exception_closure :
  |[], [], "", 0, EApp (ELit (Integer 4)) [ELit (Integer 5); ELit (Integer 5)], []|
-e>
  | 0, inr (badfun (VLit (Integer 4))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_closure2_fbs :
  fbs_expr 1000 [] [] "" 0 (EApp (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) [ELit (Integer 5); ELit (Integer 5)]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example apply_eval_exception_closure2 :
  |[], [], "", 0, EApp (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]) [ELit (Integer 5); ELit (Integer 5)], []|
-e>
  | 0, exception, []|.
Proof.
  solve. 
Qed.

Example apply_eval_exception_param_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))] [] "" 1
    (EApp (EVar "X"%string) [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]]) []
=
  Result 1 exception [].
Proof.
  auto.
Qed.

Example apply_eval_exception_param :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], [], "", 1,
    EApp (EVar "X"%string) [ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]], []|
-e>
  |1, exception, []|.
Proof.
  solve. 
Qed.

Example apply_eval_exception_param_count_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))] [] "" 1
   (EApp (EVar "X"%string) [ELit (Integer 2)]) []
=
  Result 1 (inr (badarity (VClos [] [] 0 [] (ELit (Integer 4))))) [].
Proof.
  auto.
Qed.

Example apply_eval_exception_param_count :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], [], "", 1,
   EApp (EVar "X"%string) [ELit (Integer 2)], []|
-e>
  |1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_body_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))] [] "" 1
   (EApp (EVar "X"%string) []) []
=
  Result 1 exception [].
Proof.
  auto.
Qed.

Example apply_eval_exception_body :
  |[(inl "X"%string, VClos [] [] 0 [] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]))], [], "", 1,
   EApp (EVar "X"%string) [], []|
-e> 
  | 1, exception, []|.
Proof.
  solve. 
Qed.

Example letrec_exception_fbs : 
  fbs_expr 1000 [] [] "" 0 (ELetRec [(("fun1"%string, 0), ([], ELit (Atom "error"%string)))] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])) []
=
  Result 1 exception [].
Proof.
  auto.
Qed.

Example letrec_exception : 
  |[], [], "", 0, ELetRec [(("fun1"%string, 0), ([], ELit (Atom "error"%string)))] (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]), []|
-e>
  |1, exception, []|.
Proof.
  solve. 
Qed.

Example map_eval_ex_key_fbs :
  fbs_expr 1000 [] [] "" 0 (EMap [(ELit (Atom "error"%string),  ELit (Atom "error"%string)); 
                (ELit (Atom "error"%string), ELit (Atom "error"%string));
                (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []], ELit (Atom "error"%string));
                (ELit (Atom "error"%string), ELit (Atom "error"%string))]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example map_eval_ex_key :
  |[], [], "", 0, EMap [(ELit (Atom "error"%string),  ELit (Atom "error"%string)); 
                (ELit (Atom "error"%string), ELit (Atom "error"%string));
                (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []], ELit (Atom "error"%string));
                (ELit (Atom "error"%string), ELit (Atom "error"%string))], []|
-e>
  |0, exception, []|.
Proof.
  solve. 
Qed.

Example map_eval_ex_val_fbs :
  fbs_expr 1000 [] [] "" 0 
                (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                (ELit (Atom "error"%string), ELit (Atom "error"%string));
                (ELit (Atom "error"%string), ELit (Atom "error"%string))]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example map_eval_ex_val :
  |[], [], "", 0, EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
                (ELit (Atom "error"%string), ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []]);
                (ELit (Atom "error"%string), ELit (Atom "error"%string));
                (ELit (Atom "error"%string), ELit (Atom "error"%string))], []|
-e>
  |0, exception, []|.
Proof.
  solve. 
Qed.

Example seq_eval_ex_1_fbs :
  fbs_expr 1000 [] [] "" 0 (ESeq (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                (ELit (Integer 42))) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example seq_eval_ex_1 :
  |[], [], "", 0, ESeq (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
                (ELit (Integer 42))
   , [] |
-e>
  | 0, exception, [] |.
Proof.
  solve. 
Qed.

Example seq_eval_ex_2_fbs :
  fbs_expr 1000 [] [] "" 0 (ESeq (ELit (Integer 42))
                (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])) []
=
  Result 0 exception [] .
Proof.
  auto.
Qed.

Example seq_eval_ex_2 :
  |[], [], "", 0, ESeq (ELit (Integer 42))
                (ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])
   , [] |
-e>
  | 0, exception, [] |.
Proof.
  solve. 
Qed.

Example map_eval_ex_val2_fbs :
  fbs_expr 1000 [] [] "" 0 (EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
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
                (ELit (Atom "error"%string), ELit (Atom "error"%string))], ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])])])])])])]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.


Example map_eval_ex_val2 :
  |[], [], "", 0, EMap [(ELit (Atom "error"%string), ELit (Atom "error"%string)); 
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
                (ELit (Atom "error"%string), ELit (Atom "error"%string))], ECall (ELit (Atom "erlang" )) (ELit (Atom "+" )) [ELit (Integer 5); ETuple []])])])])])])], []|
-e>
  |0, exception, []|.
Proof.
  solve. 
Qed.

End Exception_Tests.