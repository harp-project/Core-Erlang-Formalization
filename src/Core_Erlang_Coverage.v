Require Core_Erlang_Auxiliaries.

Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.

Import ListNotations.

(**
 ** NOTE: This module should only be used for coverage measurment!
 ** The very same definitions are available in Core_Erlang_Functional_Big_Step.
 **)
Inductive Semantic_rule : Set :=
| _EVAL_SINGLE
| _EVAL_VALUES
| _EVAL_LIST_CONS
| _EVAL_LIST_EMPTY
| _EVAL_LIST_EX_PROP
| _EVAL_LIST_EX_CREATE
| _EVAL_LIT
| _EVAL_VAR
| _EVAL_FUNID
| _EVAL_FUN
| _EVAL_CONS
| _EVAL_NIL
| _EVAL_CONS_HD_EX
| _EVAL_CONS_TL_EX
| _EVAL_TUPLE
| _EVAL_TUPLE_EX
| _EVAL_CALL (f : string) (* the name of the built-in operation *)
| _EVAL_CALL_EX
| _EVAL_PRIMOP (f : string) (* the name of the built-in operation *)
| _EVAL_PRIMOP_EX
| _EVAL_APP
| _EVAL_APP_EX
| _EVAL_APP_EX_PARAM
| _EVAL_APP_EX_BADFUN
| _EVAL_APP_EX_BADARITY
| _EVAL_CASE
| _EVAL_CASE_EX
| _EVAL_CASE_TRUE
| _EVAL_CASE_FALSE
| _EVAL_CASE_IFCLAUSE
| _EVAL_CASE_NOMATCH
| _EVAL_LET
| _EVAL_LET_EX
| _EVAL_LETREC
| _EVAL_SEQ
| _EVAL_SEQ_EX
| _EVAL_MAP
| _EVAL_MAP_EX
| _EVAL_TRY
| _EVAL_CATCH
| _FAIL
| _TIMEOUT
.

Definition Log := list Semantic_rule.

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Fixpoint fbs_values {A : Type} (f : Log -> Environment -> nat -> A -> SideEffectList -> ResultType * Log) (log : Log) (env : Environment) (id : nat) (exps : list A) (eff : SideEffectList) : ResultType * Log :=
match exps with
| []    => (Result id (inl []) eff, _EVAL_LIST_EMPTY::log)
| x::xs => match f log env id x eff with
          | (Result id' (inl [v]) eff', log') => 
            let res := fbs_values f log' env id' xs eff' in
              match res with
              | (Result id'' (inl xs') eff'', log'') => 
                  (Result id'' (inl (v::xs')) eff'', _EVAL_LIST_CONS::log'')
              | (r, log'') => (r, _EVAL_LIST_EX_PROP::log'')
              end
          | (Result id' (inl val) eff', log') => (Failure, _FAIL::log') (* undefined behaviour *)
          | (r, log') => (r, _EVAL_LIST_EX_CREATE::log')
          end
end.

Fixpoint fbs_case (log : Log) (l : list (list Pattern * Expression * Expression)) (env : Environment) (id' : nat) (eff' : SideEffectList) (vals : ValueSequence) (f : Log -> Environment -> nat -> Expression -> SideEffectList -> ResultType * Log) : ResultType * Log :=
match l with
| [] => (Result id' (inr if_clause) eff', _EVAL_CASE_IFCLAUSE::log)
| (pl, gg, bb)::xs =>
(* TODO: side effects cannot be produced here *)
 if match_valuelist_to_patternlist vals pl
 then
   match f log (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' gg eff' with
   | (Result id'' (inl [v]) eff'', log'') =>  
     if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
     then
       match v with
       | VLit (Atom s) =>
         if String.eqb s "true"%string then
           f (_EVAL_CASE_TRUE::log'') (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' bb eff'
         else if String.eqb s "false"%string 
              then fbs_case (_EVAL_CASE_FALSE::log'') xs env id' eff' vals f
              else (Failure, _FAIL::log'')
       | _ => (Failure, _FAIL::log'')
       end
     else (Failure, _FAIL::log'')
   | (_, log'') => (Failure, _FAIL::log'')
   end
 else fbs_case (_EVAL_CASE_NOMATCH::log) xs env id' eff' vals f
end.

Fixpoint fbs_expr (clock : nat) (log : Log) (env : Environment) (id : nat) (expr : Expression) (eff : SideEffectList) {struct clock} : ResultType * Log :=
match clock with
| 0 => (Timeout, _TIMEOUT::log)
| S clock' =>
  match expr with
   | EValues el => fbs_values (fbs_single clock') (_EVAL_VALUES::log) env id el eff
   | ESingle e => fbs_single clock' (_EVAL_SINGLE::log) env id e eff
  end
end
with fbs_single (clock : nat) (log : Log) (env : Environment) (id : nat) (expr : SingleExpression) (eff : SideEffectList) {struct clock} : ResultType * Log :=
match clock with
| 0 => (Timeout, _TIMEOUT::log)
| S clock' =>
  match expr with
   | ENil => (Result id (inl [VNil]) eff, _EVAL_NIL::log)
   | ELit l => (Result id (inl [VLit l]) eff, _EVAL_LIT::log)
   | EVar v => match get_value env (inl v) with
               | Some res => (Result id (inl res) eff, _EVAL_VAR::log)
               | None => (Failure, _FAIL::log)
               end
   | EFunId f => match get_value env (inr f) with
                 | Some res => (Result id (inl res) eff, _EVAL_FUNID::log)
                 | None => (Failure, _FAIL::log)
                 end
   | EFun vl e => (Result (S id) (inl [VClos env [] id vl e]) eff, _EVAL_FUN::log)
   | ECons hd tl => 
     match fbs_expr clock' log env id tl eff with
       | (Result id' (inl [tlv]) eff', log') =>
         match fbs_expr clock' log' env id' hd eff' with
         | (Result id'' (inl [hdv]) eff'', log'') => (Result id'' (inl [VCons hdv tlv]) eff'', _EVAL_CONS::log'')
         | (Result id'' (inl vals) eff'', log'') => (Failure, _FAIL::log'') (* undefined behaviour *)
         | (r, log'') => (r, _EVAL_CONS_HD_EX::log'')
         end
       | (Result id' (inl vals) eff', log'') => (Failure, _FAIL::log'') (* undefined behaviour *)
       | (r, log'') => (r, _EVAL_CONS_TL_EX::log'')
     end
   | ETuple l =>
     let res := fbs_values (fbs_expr clock') log env id l eff in
       match res with
       | (Result id' (inl vl) eff', log') => 
             (Result id' (inl [VTuple vl]) eff', _EVAL_TUPLE::log')
       | (r, log') => (r, _EVAL_TUPLE_EX::log')
       end
   | ECall f l => 
     let res := fbs_values (fbs_expr clock') log env id l eff in
       match res with
       | (Result id' (inl vl) eff', log') => 
            (Result id' (fst (eval f vl eff')) (snd (eval f vl eff')) ,(_EVAL_CALL f)::log')
       | (r, log') => (r, _EVAL_CALL_EX::log')
       end
   | EPrimOp f l =>
     let res := fbs_values (fbs_expr clock') log env id l eff in
       match res with
       | (Result id' (inl vl) eff', log') => 
            (Result id' (fst (eval f vl eff')) (snd (eval f vl eff')) ,(_EVAL_PRIMOP f)::log')
       | (r, log') => (r, _EVAL_PRIMOP_EX::log')
       end
   | EApp exp l =>
     match fbs_expr clock' log env id exp eff with
     | (Result id' (inl [v]) eff', log') =>
       let res := fbs_values (fbs_expr clock') log' env id' l eff' in
         match res with
         | (Result id'' (inl vl) eff'', log'') => 
           match v with
           | VClos ref ext closid varl body =>
              if Nat.eqb (length varl) (length vl)
              then fbs_expr clock' (_EVAL_APP::log'') (append_vars_to_env varl vl (get_env ref ext)) id'' body eff''
              else (Result id'' (inr (badarity v)) eff'', _EVAL_APP_EX_BADARITY::log'')
           | _ => (Result id'' (inr (badfun v)) eff'', _EVAL_APP_EX_BADFUN::log'')
           end
         | (r, log'') => (r, _EVAL_APP_EX_PARAM::log'')
         end
     | (Result id' (inl val) eff', log') => (Failure, _FAIL::log')
     | (r, log') => (r, _EVAL_APP_EX::log')
     end
   | ECase e l =>
     match fbs_expr clock' log env id e eff with
     | (Result id' (inl vals) eff', log') =>
        fbs_case (_EVAL_CASE::log') l env id' eff' vals (fbs_expr clock')
     | (r, log') => (r, _EVAL_CASE_EX::log')
     end
   | ELet l e1 e2 =>
      match fbs_expr clock' log env id e1 eff with
      | (Result id' (inl vals) eff', log') =>
        if Nat.eqb (length vals) (length l)
        then fbs_expr clock' (_EVAL_LET::log') (append_vars_to_env l vals env) id' e2 eff'
        else (Failure, _FAIL::log')
      | (r, log') => (r, _EVAL_LET_EX::log')
      end
   | ESeq e1 e2 =>
      match fbs_expr clock' log env id e1 eff with
      | (Result id' (inl [v]) eff', log') => fbs_expr clock' (_EVAL_SEQ::log') env id' e2 eff'
      | (Result id' (inl vals) eff', log') => (Failure, _FAIL::log')
      | (r, log') => (r, _EVAL_SEQ_EX::log')
      end
   | ELetRec l e => fbs_expr clock' (_EVAL_LETREC::log) (append_funs_to_env l env id) (id + length l) e eff
   | EMap l =>
     let res := fbs_values (fbs_expr clock') log env id (make_map_exps l) eff in
       match res with
       | (Result id' (inl vals) eff', log') => 
         match make_map_vals_inverse vals with
         | None => (Failure, _FAIL::log')
         | Some (kvals, vvals) =>
             (Result id' (inl [VMap (combine (fst (make_value_map kvals vvals)) (snd (make_value_map kvals vvals)))]) eff', _EVAL_MAP::log')
         end
       | (r, log') => (r, _EVAL_MAP_EX::log')
       end
   | ETry e1 vl1 e2 vl2 e3 =>
     match fbs_expr clock' log env id e1 eff with
     | (Result id' (inl vals) eff', log') =>
       if Nat.eqb (length vals) (length vl1)
       then fbs_expr clock' (_EVAL_TRY::log') (append_vars_to_env vl1 vals env) id' e2 eff'
       else (Failure, _FAIL::log')
     | (Result id' (inr ex) eff', log') =>
       fbs_expr clock' (_EVAL_CATCH::log') (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) id' e3 eff'
     | r => r
     end
  end
end
.

Definition pretty_print_semantic_rule (r : Semantic_rule) : string :=
match r with
 | _EVAL_SINGLE => "'_EVAL_SINGLE'"
 | _EVAL_VALUES => "'_EVAL_VALUES'"
 | _EVAL_LIST_CONS => "'_EVAL_LIST_CONS'"
 | _EVAL_LIST_EMPTY => "'_EVAL_LIST_EMPTY'"
 | _EVAL_LIST_EX_PROP => "'_EVAL_LIST_EX_PROP'"
 | _EVAL_LIST_EX_CREATE => "'_EVAL_LIST_EX_CREATE'"
 | _EVAL_LIT => "'_EVAL_LIT'"
 | _EVAL_VAR => "'_EVAL_VAR'"
 | _EVAL_FUNID => "'_EVAL_FUNID'"
 | _EVAL_FUN => "'_EVAL_FUN'"
 | _EVAL_CONS => "'_EVAL_CONS'"
 | _EVAL_NIL => "'_EVAL_NIL'"
 | _EVAL_CONS_HD_EX => "'_EVAL_CONS_HD_EX'"
 | _EVAL_CONS_TL_EX => "'_EVAL_CONS_TL_EX'"
 | _EVAL_TUPLE => "'_EVAL_TUPLE'"
 | _EVAL_TUPLE_EX => "'_EVAL_TUPLE_EX'"
 | _EVAL_CALL f => "'_EVAL_CALL'"
 | _EVAL_CALL_EX => "'_EVAL_CALL_EX'"
 | _EVAL_PRIMOP f => "'_EVAL_PRIMOP'"
 | _EVAL_PRIMOP_EX => "'_EVAL_PRIMOP_EX'"
 | _EVAL_APP => "'_EVAL_APP'"
 | _EVAL_APP_EX => "'_EVAL_APP_EX'"
 | _EVAL_APP_EX_PARAM => "'_EVAL_APP_EX_PARAM'"
 | _EVAL_APP_EX_BADFUN => "'_EVAL_APP_EX_BADFUN'"
 | _EVAL_APP_EX_BADARITY => "'_EVAL_APP_EX_BADARITY'"
 | _EVAL_CASE => "'_EVAL_CASE'"
 | _EVAL_CASE_EX => "'_EVAL_CASE_EX'"
 | _EVAL_CASE_TRUE => "'_EVAL_CASE_TRUE'"
 | _EVAL_CASE_FALSE => "'_EVAL_CASE_FALSE'"
 | _EVAL_CASE_IFCLAUSE => "'_EVAL_CASE_IFCLAUSE'"
 | _EVAL_CASE_NOMATCH => "'_EVAL_CASE_NOMATCH'"
 | _EVAL_LET => "'_EVAL_LET'"
 | _EVAL_LET_EX => "'_EVAL_LET_EX'"
 | _EVAL_LETREC => "'_EVAL_LETREC'"
 | _EVAL_SEQ => "'_EVAL_SEQ'"
 | _EVAL_SEQ_EX => "'_EVAL_SEQ_EX'"
 | _EVAL_MAP => "'_EVAL_MAP'"
 | _EVAL_MAP_EX => "'_EVAL_MAP_EX'"
 | _EVAL_TRY => "'_EVAL_TRY'"
 | _EVAL_CATCH => "'_EVAL_CATCH'"
 | _FAIL => "'_FAIL'"
 | _TIMEOUT => "'_TIMEOUT'"
end.


Fixpoint pretty_print_log (log : Log) : string :=
match log with
| [] => ""
| [x] => pretty_print_semantic_rule x
| x::xs => pretty_print_semantic_rule x ++ "," ++ pretty_print_log xs
end.

Definition result_value (res : ResultType * Log) : option string :=
match res with
| (Result _ (inl [val]) _, log) =>
    Some ("{" ++ pretty_print_value val ++ ", [" ++ pretty_print_log log ++ "] }")%string
| _ => None
end.




(*
(** TESTS *)

Compute result_value (fbs_expr 1000 [] [] 0 (EVar "X"%string) []).

Definition exception : ValueSequence + Exception := inr (badarith (VTuple [VLit (Atom "+"); VLit (Integer 5); VTuple []])).


Compute
  result_value (
  fbs_expr 1000 [] [] 0 
  (ECons (ECall "+" [^ELit (Integer 5); ^ELit (Integer 5)]) (ELit (Atom "error"%string))) 
  []).

Compute
  fbs_expr 1000 [] [] 0 (ECons (ELit (Atom "error"%string)) (ECons (ECall "+" [^ELit (Integer 5); ^ETuple []]) (ENil))) [].

Example exception_list_tl : 
  |[], 0, ECons (ELit (Atom "error"%string)) (ECons (ECall "+" [^ELit (Integer 5); ^ETuple []]) (ENil)), []|
-e> 
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example exception_tuple_fbs : 
  fbs_expr 1000 [] 0 (ETuple [^ELit (Atom "error"%string) ; ^ELit (Atom "error"%string); ^ECall "+" [^ELit (Integer 5); ^ETuple []]]) []
=
  Result 0 exception [].
Proof.
  reflexivity.
Qed.

Example exception_tuple : 
  |[], 0, ETuple [^ELit (Atom "error"%string) ; ^ELit (Atom "error"%string); ^ECall "+" [^ELit (Integer 5); ^ETuple []]], []|
-e>
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example try_eval_fbs : 
  fbs_expr 1000 [] 0 
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

Example try_eval_catch_fbs : 
  fbs_expr 1000 [] 0 
               (ETry (ECall "+" [^ELit (Integer 5); ^ETuple []]) ["X"%string]
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

Example try_eval_exception_fbs : 
  fbs_expr 1000 [] 0 
               (ETry (ECall "+" [^ELit (Integer 5); ^ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ECall "+" [^ELit (Integer 5); ^ETuple []]))
  []
=
  Result 0 exception []
.
Proof.
  auto.
Qed.

Example try_eval_exception : 
  |[], 0, ETry (ECall "+" [^ELit (Integer 5); ^ETuple []]) ["X"%string]
               (ELit (Atom "ok"%string))
               ["Ex1"%string; "Ex2"%string; "Ex3"%string]
               (ECall "+" [^ELit (Integer 5); ^ETuple []]) 
  , []|
-e>
  |0, exception, []|
.
Proof.
  solve.
Qed.

Example try_eval_exception2_fbs : 
  fbs_expr 1000 [] 0 
               (ETry (ETuple []) ["X"%string]
               (ECall "+" [^ELit (Integer 5); ^ETuple []])
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
  |[], 0, ETry (ETuple []) ["X"%string]
               (ECall "+" [^ELit (Integer 5); ^ETuple []])
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
  fbs_expr 1000 [] 0 (ECase (ECall "+" [^ELit (Integer 5); ^ETuple []])
                 [([PVar "X"%string], ^ELit (Atom "true"), ^ELit (Integer 1))]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example eval_case_pat_ex :
  | [], 0, ECase (ECall "+" [^ELit (Integer 5); ^ETuple []])
                 [([PVar "X"%string], ^ELit (Atom "true"), ^ELit (Integer 1))], []|
-e>
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example eval_case_clause_ex_fbs :
  fbs_expr 1000 [(inl "Y"%string, VLit (Integer 2))] 0
     (ECase (EVar "Y"%string)
          [([PLit (Integer 1)], ^ELit (Atom "true"), ^ELit (Integer 1)); 
           ([PVar "Z"%string], ^ELit (Atom "false"), ^ELit (Integer 2))]) []
=
  Result 0 (inr (if_clause)) [].
Proof.
  auto.
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

Example call_eval_body_ex_fbs : 
  fbs_expr 1000 [] 0 (ECall "+"%string []) []
=
  Result 0 (inr (undef (VLit (Atom "+")))) [].
Proof.
  auto.
Qed.

Example call_eval_body_ex : 
  |[], 0, ECall "+"%string [], []|
-e>
  | 0, inr (undef (VLit (Atom "+"))), []|.
Proof.
  solve.
Qed.

Example call_eval_body_ex2_fbs :
  fbs_expr 1000 [] 0 (ECall "+"%string [^ELit (Integer 5); ^ETuple []]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example call_eval_body_ex2 :
  |[], 0, ECall "+"%string [^ELit (Integer 5); ^ETuple []], []|
-e>
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example call_eval_param_ex_fbs :
  fbs_expr 1000 [] 0 (ECall "+"%string [^ELit (Integer 5); ^ECall "+" [^ELit (Integer 5); ^ETuple []]]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example call_eval_param_ex :
  |[], 0, ECall "+"%string [^ELit (Integer 5); ^ECall "+" [^ELit (Integer 5); ^ETuple []]], []|
-e>
  |0, exception, []|.
Proof.
  solve.
Qed.

Example let_eval_exception_params_fbs :
  fbs_expr 1000 [] 0 (ELet ["X"%string; "Y"%string] 
               (EValues [ELit (Integer 5); ECall "+" [^ELit (Integer 5); ^ETuple []]]) (ETuple [])) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example let_eval_exception_params :
  |[], 0, ELet ["X"%string; "Y"%string] 
               (EValues [ELit (Integer 5); ECall "+" [^ELit (Integer 5); ^ETuple []]]) (ETuple []), []|
-e>
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example let_eval_exception_body_fbs :
  fbs_expr 1000 [] 0 (ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
               (ECall "+" [^ELit (Integer 5); ^ETuple []])) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example let_eval_exception_body :
  |[], 0, ELet ["X"%string; "Y"%string] (EValues [ELit (Integer 5); ELit (Integer 5)])
               (ECall "+" [^ELit (Integer 5); ^ETuple []]), []|
-e>
  |0, exception, []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_closure_fbs :
  fbs_expr 1000 [] 0 (EApp (ELit (Integer 4)) [^ELit (Integer 5); ^ELit (Integer 5)]) []
=
  Result 0 (inr (badfun (VLit (Integer 4)))) [].
Proof.
  auto.
Qed.

Example apply_eval_exception_closure :
  |[], 0, EApp (ELit (Integer 4)) [^ELit (Integer 5); ^ELit (Integer 5)], []|
-e>
  | 0, inr (badfun (VLit (Integer 4))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_closure2_fbs :
  fbs_expr 1000 [] 0 (EApp (ECall "+" [^ELit (Integer 5); ^ETuple []]) [^ELit (Integer 5); ^ELit (Integer 5)]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example apply_eval_exception_closure2 :
  |[], 0, EApp (ECall "+" [^ELit (Integer 5); ^ETuple []]) [^ELit (Integer 5); ^ELit (Integer 5)], []|
-e>
  | 0, exception, []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_param_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))] 1
    (EApp (EVar "X"%string) [^ECall "+" [^ELit (Integer 5); ^ETuple []]]) []
=
  Result 1 exception [].
Proof.
  auto.
Qed.

Example apply_eval_exception_param :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], 1,
    EApp (EVar "X"%string) [^ECall "+" [^ELit (Integer 5); ^ETuple []]], []|
-e>
  |1, exception, []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_param_count_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))] 1
   (EApp (EVar "X"%string) [^ELit (Integer 2)]) []
=
  Result 1 (inr (badarity (VClos [] [] 0 [] (ELit (Integer 4))))) [].
Proof.
  auto.
Qed.

Example apply_eval_exception_param_count :
  |[(inl "X"%string, VClos [] [] 0 [] (ELit (Integer 4)))], 1,
   EApp (EVar "X"%string) [^ELit (Integer 2)], []|
-e>
  |1, inr (badarity (VClos [] [] 0 [] (ELit (Integer 4)))), []|.
Proof.
  solve.
Qed.

Example apply_eval_exception_body_fbs :
  fbs_expr 1000 [(inl "X"%string, VClos [] [] 0 [] (ECall "+" [^ELit (Integer 5); ^ETuple []]))] 1
   (EApp (EVar "X"%string) []) []
=
  Result 1 exception [].
Proof.
  auto.
Qed.

Example apply_eval_exception_body :
  |[(inl "X"%string, VClos [] [] 0 [] (ECall "+" [^ELit (Integer 5); ^ETuple []]))], 1,
   EApp (EVar "X"%string) [], []|
-e> 
  | 1, exception, []|.
Proof.
  solve.
Qed.

Example letrec_exception_fbs : 
  fbs_expr 1000 [] 0 (ELetRec [(("fun1"%string, 0), ([], ^ELit (Atom "error"%string)))] (ECall "+" [^ELit (Integer 5); ^ETuple []])) []
=
  Result 1 exception [].
Proof.
  auto.
Qed.

Example letrec_exception : 
  |[], 0, ELetRec [(("fun1"%string, 0), ([], ^ELit (Atom "error"%string)))] (ECall "+" [^ELit (Integer 5); ^ETuple []]), []|
-e>
  |1, exception, []|.
Proof.
  solve.
Qed.

Example map_eval_ex_key_fbs :
  fbs_expr 1000 [] 0 (EMap [(^ELit (Atom "error"%string), ^ ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ECall "+" [^ELit (Integer 5); ^ETuple []], ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example map_eval_ex_key :
  |[], 0, EMap [(^ELit (Atom "error"%string), ^ ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ECall "+" [^ELit (Integer 5); ^ETuple []], ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))], []|
-e>
  |0, exception, []|.
Proof.
  solve.
Qed.

Example map_eval_ex_val_fbs :
  fbs_expr 1000 [] 0 
                (EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ECall "+" [^ELit (Integer 5); ^ETuple []]);
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))]) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example map_eval_ex_val :
  |[], 0, EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
                (^ELit (Atom "error"%string), ^ECall "+" [^ELit (Integer 5); ^ETuple []]);
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string));
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))], []|
-e>
  |0, exception, []|.
Proof.
  solve.
Qed.

Example seq_eval_ex_1_fbs :
  fbs_expr 1000 [] 0 (ESeq (ECall "+" [^ELit (Integer 5); ^ETuple []])
                (ELit (Integer 42))) []
=
  Result 0 exception [].
Proof.
  auto.
Qed.

Example seq_eval_ex_1 :
  | [], 0, ESeq (ECall "+" [^ELit (Integer 5); ^ETuple []])
                (ELit (Integer 42))
   , [] |
-e>
  | 0, exception, [] |.
Proof.
  solve.
Qed.

Example seq_eval_ex_2_fbs :
  fbs_expr 1000 [] 0 (ESeq (ELit (Integer 42))
                (ECall "+" [^ELit (Integer 5); ^ETuple []])) []
=
  Result 0 exception [] .
Proof.
  auto.
Qed.

Example seq_eval_ex_2 :
  | [], 0, ESeq (ELit (Integer 42))
                (ECall "+" [^ELit (Integer 5); ^ETuple []])
   , [] |
-e>
  | 0, exception, [] |.
Proof.
  solve.
Qed.

Example map_eval_ex_val2_fbs :
  fbs_expr 1000 [] 0 (EMap [(^ELit (Atom "error"%string), ^ELit (Atom "error"%string)); 
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
                (^ELit (Atom "error"%string), ^ELit (Atom "error"%string))], ^ECall "+" [^ELit (Integer 5); ^ETuple []])])])])])])]) []
=
  Result 0 exception [].
Proof.
  auto.
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
  |0, exception, []|.
Proof.
  solve.
Qed.

End Exception_Tests.*)