Require Core_Erlang_Tactics.

Module Exception_Tests.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.

Import ListNotations.

Example eval_exception_call :
  forall {env : Environment} {eff : SideEffectList} {id : nat}, 
  |env, id, ECall "+" [^ELit (Integer 5); ^ETuple []], eff|
-e> 
  |id, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), eff|.
Proof.
  intros.
  solve.
Qed.

(** DOES NOT COMPPILE IN CORE ERLANG *)
Example exception_var :
  |[], 0, EVar "X"%string, []|
-e>
  |0, inr novar, []|.
Proof.
  solve.
Qed.

Example exception_list_hd :
  |[], 0, ECons (ECall "+" [^ELit (Integer 5); ^ETuple []]) (ELit (Atom "error"%string)), []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example exception_list_tl : 
  |[], 0, ECons (ELit (Atom "error"%string)) (ECons (ECall "+" [^ELit (Integer 5); ^ETuple []]) (ENil)), []|
-e> 
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example exception_tuple : 
  |[], 0, ETuple [^ELit (Atom "error"%string) ; ^ELit (Atom "error"%string); ^ECall "+" [^ELit (Integer 5); ^ETuple []]], []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example try_eval : 
  |[], 0, ETry (ETuple []) ["X"%string]
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

Example try_eval_catch : 
  |[], 0, ETry (ECall "+" [^ELit (Integer 5); ^ETuple []]) ["X"%string]
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

Example try_eval_exception : 
  |[], 0, ETry (ECall "+" [^ELit (Integer 5); ^ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ECall "+" [^ELit (Integer 5); ^ETuple []]) 
  , []|
-e>
  |0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|
.
Proof.
  solve.
Qed.

Example try_eval_exception2 : 
  |[], 0, ETry (ETuple []) ["X"%string]
               (ECall "+" [^ELit (Integer 5); ^ETuple []])
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ELit (Atom "error"%string))
  , []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|
.
Proof.
  solve.
Qed.

Example eval_case_pat_ex :
  | [], 0, ECase (ECall "+" [^ELit (Integer 5); ^ETuple []])
                 [([PVar "X"%string], ^ELit (Atom "true"), ^ELit (Integer 1))], []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example eval_case_clause_ex :
  | [(inl "Y"%string, VLit (Integer 2))], 0,
     ECase (EVar "Y"%string)
          [([PLit (Integer 1)], ^ELit (Atom "true"), ^ELit (Integer 1)); 
           ([PVar "Z"%string], ^ELit (Atom "false"), ^ELit (Integer 2))], []|
-e>
  | 0, inr (if_clause), []|.
Proof.
  solve.
Qed.

Example call_eval_body_ex : 
  |[], 0, ECall "+"%string [], []|
-e>
  | 0, inr (undef (VLit (Atom "+"))), []|.
Proof.
  solve.
Qed.

Example call_eval_body_ex2 :
  |[], 0, ECall "+"%string [^ELit (Integer 5); ^ETuple []], []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example call_eval_param_ex :
  |[], 0, ECall "+"%string [^ELit (Integer 5); ^ECall "+" [^ELit (Integer 5); ^ETuple []]], []|
-e>
  |0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example let_eval_exception_params :
  |[], 0, ELet ["X"%string; "Y"%string] 
               (EValues [ELit (Integer 5); ECall "+" [^ELit (Integer 5); ^ETuple []]]) (ETuple []), []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example let_eval_exception_body :
  |[], 0, ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
               (ECall "+" [^ELit (Integer 5); ^ETuple []]), []|
-e>
  |0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_closure :
  |[], 0, EApp (ELit (Integer 4)) [^ELit (Integer 5); ^ELit (Integer 5)], []|
-e>
  | 0, inr (badfun (VLit (Integer 4))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_closure2 :
  |[], 0, EApp (ECall "+" [^ELit (Integer 5); ^ETuple []]) [^ELit (Integer 5); ^ELit (Integer 5)], []|
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_param :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], 1,
    EApp (EVar "X"%string) [^ECall "+" [^ELit (Integer 5); ^ETuple []]], []|
-e>
  |1, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_param_count :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], 1,
   EApp (EVar "X"%string) [^ELit (Integer 2)], []|
-e>
  |1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_body :
  |[(inl "X"%string, VClos [] [] 0 [] (ECall "+" [^ELit (Integer 5); ^ETuple []]))], 1,
   EApp (EVar "X"%string) [], []|
-e> 
  | 1, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example letrec_exception : 
  |[], 0, ELetRec [(("fun1"%string, 0), ([], ^ELit (Atom "error"%string)))] (ECall "+" [^ELit (Integer 5); ^ETuple []]), []|
-e>
  |1, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example map_eval_ex_key :
  |[], 0, EMap [(^ELit (Atom "error"%string), ^ ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ECall "+" [^ELit (Integer 5); ^ETuple []], ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))], []|
-e>
  |0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example map_eval_ex_val :
  |[], 0, EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ECall "+" [^ELit (Integer 5); ^ETuple []]);
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))], []|
-e>
  |0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

Example seq_eval_ex_1 :
  | [], 0, ESeq (ECall "+" [^ELit (Integer 5); ^ETuple []])
                (ELit (Integer 42))
   , [] |
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), [] |.
Proof.
  solve.
Qed.

Example seq_eval_ex_2 :
  | [], 0, ESeq (ELit (Integer 42))
                (ECall "+" [^ELit (Integer 5); ^ETuple []])
   , [] |
-e>
  | 0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), [] |.
Proof.
  solve.
Qed.

Example map_eval_ex_val2 :
  |[], 0, EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ECall "+" [^ELit (Integer 5); ^ETuple []]);
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))], ^ECall "+" [^ELit (Integer 5); ^ETuple []])])])])])])], []|
-e>
  |0, inr (badarith (VCons (VLit (Integer 5)) (VTuple []))), []|.
Proof.
  solve.
Qed.

End Exception_Tests.