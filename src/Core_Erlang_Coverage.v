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

Definition pp_semantic_rule (r : Semantic_rule) : string :=
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


Fixpoint pp_list {A : Type} (pp : A -> string) (l : list A) : string :=
match l with
| [] => ""%string
| [x] => pp x
| x::xs => (pp x ++ "," ++ pp_list pp xs)%string
end.

Definition pp_exception_class (cl : ExceptionClass) : string :=
match cl with
| Error => "error"
| Throw => "throw"
| Exit  => "exit"
end.

Definition pp_exception (e : Exception) : string :=
match e with
| (class, reason, info) => "{" ++ pp_exception_class class  ++ "," ++
                                  pretty_print_value reason ++ "," ++
                                  pretty_print_value info   ++ "}"
end.

Definition result_value (res : ResultType * Log) : string :=
match res with
| (Result _ (inl [val]) _, log) =>
    "__coqresult: {" ++ pretty_print_value val ++ ", [" ++ pp_list pp_semantic_rule log ++ "] }"
| (Result _ (inl vals) _, log)  =>
    "__invalidcoqresult: {[" ++ pp_list pretty_print_value vals ++ "], [" ++ pp_list pp_semantic_rule log ++ "] }"
| (Result _ (inr ex) _, log) =>
    "__exceptioncoqresult: {" ++ pp_exception ex ++ ", [" ++ pp_list pp_semantic_rule log ++ "] }"
| (Timeout, log) =>
    "__invalidcoqresult: {Timeout, [" ++ pp_list pp_semantic_rule log ++ "] }"
| (Failure, log) =>
    "__invalidcoqresult: {Failure, [" ++ pp_list pp_semantic_rule log ++ "] }"
end.

