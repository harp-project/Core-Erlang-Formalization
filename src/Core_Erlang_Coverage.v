Require Core_Erlang_Auxiliaries.
Require Core_Erlang_Module_Helper.
(* From Coq Require FSets.FMapWeakList. *)

Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.
Export Core_Erlang_Module_Helper.Module_Helper.

Import ListNotations.
Import Numbers.DecimalString.
(* Import FMapWeakList DecidableType. *)

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
| _EVAL_FUNID_MODULE
| _EVAL_FUN
| _EVAL_CONS
| _EVAL_NIL
| _EVAL_CONS_HD_EX
| _EVAL_CONS_TL_EX
| _EVAL_TUPLE
| _EVAL_TUPLE_EX
| _EVAL_CALL
| _EVAL_CALL_MODULE
| _EVAL_CALL_EX
| _EVAL_CALL_MEXP_EX
| _EVAL_CALL_FEXP_EX
| _EVAL_CALL_MEXP_BADARG_EX
| _EVAL_CALL_FEXP_FUN_CLAUSE_EX
| _EVAL_PRIMOP
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
(* | _FAIL
| _TIMEOUT *)
.

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Definition rule_list : list Semantic_rule :=
[ _EVAL_SINGLE; _EVAL_VALUES; _EVAL_LIST_CONS; _EVAL_LIST_EMPTY; _EVAL_LIST_EX_PROP; _EVAL_LIST_EX_CREATE;
  _EVAL_LIT; _EVAL_VAR; _EVAL_FUNID; _EVAL_FUNID_MODULE; _EVAL_FUN; _EVAL_CONS; _EVAL_NIL; _EVAL_CONS_HD_EX; _EVAL_CONS_TL_EX;
  _EVAL_TUPLE; _EVAL_TUPLE_EX; _EVAL_CALL; _EVAL_CALL_MODULE; _EVAL_CALL_EX; _EVAL_CALL_MEXP_EX ; _EVAL_CALL_FEXP_EX; _EVAL_CALL_MEXP_BADARG_EX;
  _EVAL_CALL_FEXP_FUN_CLAUSE_EX; _EVAL_PRIMOP; _EVAL_PRIMOP_EX; _EVAL_APP;
  _EVAL_APP_EX; _EVAL_APP_EX_PARAM; _EVAL_APP_EX_BADFUN; _EVAL_APP_EX_BADARITY; _EVAL_CASE; _EVAL_CASE_EX;
  _EVAL_CASE_TRUE; _EVAL_CASE_FALSE; _EVAL_CASE_IFCLAUSE; _EVAL_CASE_NOMATCH; _EVAL_LET; _EVAL_LET_EX;
  _EVAL_LETREC; _EVAL_SEQ; _EVAL_SEQ_EX; _EVAL_MAP; _EVAL_MAP_EX; _EVAL_TRY; _EVAL_CATCH (*; _FAIL; _TIMEOUT*) ].

(** Check whether there was a rule missing *)
Goal length rule_list = 46. Proof. simpl. auto. Qed.

Definition BIF_list : list BIFCode :=
[ BPlus ; BMinus ; BMult ; BDivide ; BRem ; BDiv ; BAbs
; BFwrite ; BFread 
; BAnd ; BOr ; BNot ; BIsNumber ; BIsInteger ; BIsBoolean ; BIsAtom
; BEq ; BTypeEq ; BNeq ; BTypeNeq
; BApp ; BMinusMinus
; BTupleToList ; BListToTuple
; BLt ; BLe ; BGt ; BGe
; BLength ; BTupleSize
; BTl ; BHd ; BSl ; BSr
; BElement ; BSetElement
; BNothing].

(** Check whether there was a rule missing *)
Goal length BIF_list = 37. Proof. simpl. auto. Qed.

Scheme Equality for BIFCode.
Scheme Equality for Semantic_rule.

(*
TODO FAIL:
Module BIFCode_as_DT <: DecidableType.

  Definition t := BIFCode.

  Definition eq (x y : t) := x = y \/ x <> y.

  Lemma eq_refl : forall x : t, eq x x. Proof. firstorder. Qed.
  Lemma eq_sym : forall x y : t, eq x y -> eq y x. Proof. firstorder. Qed.
  Lemma eq_trans : forall x y z : t, eq x y -> eq y z -> eq x z.
  Proof.
    intros.
  Admitted.

  Definition eq_dec := forall (x y : t), {eq x y} + {~ eq x y}.
End BIFCode_as_DT.

Module Import BIFMap := FMapWeakList.Make(BIFCode).*)

Definition LogMap (A : Type) : Type := list (A * Z).

Fixpoint put {A : Type} (k : A) (v : Z) (m : LogMap A) (eqb : A -> A -> bool) : LogMap A :=
match m with
| []           => [(k, v)]
| (k', v')::xs => if eqb k' k then (k, v)::xs else (k', v')::(put k v xs eqb)
end.

Fixpoint increase {A : Type} (k : A) (m : LogMap A) (eqb : A -> A -> bool)  : LogMap A :=
match m with
| []           => []
| (k', v')::xs => if eqb k' k then (k, Z.add 1 v')::xs else (k', v')::(increase k xs eqb)
end.

Definition Log : Type := LogMap Semantic_rule * LogMap (BIFCode).

Definition log_increase (k : Semantic_rule + BIFCode) (m : Log) : Log :=
match k, m with
| inl rule, (rule_map, bif_map) => (increase rule rule_map Semantic_rule_beq, bif_map)
| inr code, (rule_map, bif_map) => (rule_map, increase code bif_map BIFCode_beq)
end.

Fixpoint fbs_values {A : Type} (f : Log -> Environment -> (list ErlModule) -> string -> nat -> A -> SideEffectList -> ResultType * Log) (log : Log) (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat) (exps : list A) (eff : SideEffectList) : ResultType * Log :=
match exps with
| []    => (Result id (inl []) eff, log_increase (inl _EVAL_LIST_EMPTY) log)
| x::xs => match f log env modules own_module id x eff with
          | (Result id' (inl [v]) eff', log') => 
            let res := fbs_values f log' env modules own_module id' xs eff' in
              match res with
              | (Result id'' (inl xs') eff'', log'') => 
                  (Result id'' (inl (v::xs')) eff'', log_increase (inl _EVAL_LIST_CONS) log'')
              | (r, log'') => (r, log_increase (inl _EVAL_LIST_EX_PROP) log'')
              end
          | (Result _ (inl _) _, log') => (Failure, log') (* undefined behaviour *)
          | (r, log') => (r, log_increase (inl _EVAL_LIST_EX_CREATE) log')
          end
end.

Fixpoint fbs_case (log : Log) (l : list (list Pattern * Expression * Expression)) (env : Environment) (modules : list ErlModule) (own_module : string) (id' : nat) (eff' : SideEffectList) (vals : ValueSequence) (f : Log -> Environment -> list ErlModule -> string -> nat -> Expression -> SideEffectList -> ResultType * Log) : ResultType * Log :=
match l with
| [] => (Result id' (inr if_clause) eff', log_increase (inl _EVAL_CASE_IFCLAUSE) log)
| (pl, gg, bb)::xs =>
(* TODO: side effects cannot be produced here *)
 if match_valuelist_to_patternlist vals pl
 then
   match f log (add_bindings (match_valuelist_bind_patternlist vals pl) env) modules own_module  id' gg eff' with
   | (Result id'' (inl [v]) eff'', log'') =>  
     if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
     then
       match v with
       | VLit (Atom s) =>
         if String.eqb s "true"%string then
           f (log_increase (inl _EVAL_CASE_TRUE) log'') (add_bindings (match_valuelist_bind_patternlist vals pl) env) modules own_module id' bb eff'
         else if String.eqb s "false"%string 
              then fbs_case (log_increase (inl _EVAL_CASE_FALSE) log'') xs env modules own_module id' eff' vals f
              else (Failure, log'')
       | _ => (Failure, log'')
       end
     else (Failure, log'')
   | (_, log'') => (Failure, log'')
   end
 else fbs_case (log_increase (inl _EVAL_CASE_NOMATCH) log) xs env modules own_module id' eff' vals f
end.

Fixpoint fbs_expr (clock : nat) (log : Log) (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat) (expr : Expression) (eff : SideEffectList) {struct clock} : ResultType * Log :=
match clock with
| 0 => (Timeout, log)
| S clock' =>
  match expr with
   | EValues el => fbs_values (fbs_expr clock') (log_increase (inl _EVAL_VALUES) log) env modules own_module id el eff
(*    | ESingle e => fbs_single clock' (log_increase (inl _EVAL_SINGLE) log) env id e eff
  end
end
with fbs_single (clock : nat) (log : Log) (env : Environment) (id : nat) (expr : SingleExpression) (eff : SideEffectList) {struct clock} : ResultType * Log :=
match clock with
| 0 => (Timeout, log)
| S clock' =>
  match expr with *)
   | ENil => (Result id (inl [VNil]) eff, log_increase (inl _EVAL_NIL) log)
   | ELit l => (Result id (inl [VLit l]) eff, log_increase (inl _EVAL_LIT) log)
   | EVar v => match get_value env (inl v) with
               | Some res => (Result id (inl res) eff, log_increase (inl _EVAL_VAR) log)
               | None => (Failure, log)
               end
   | EFunId f => match get_value env (inr f) with
                 | Some res => (Result id (inl res) eff, log_increase (inl _EVAL_FUNID) log)
                 | None => 
                 let tlf := get_own_modfunc own_module (fst f) (snd f) ( modules ++ stdlib) in
                 match tlf with
                   | Some func  => (Result id (inl [VClos env [] id (varl func) (body func)]) eff, log_increase (inl _EVAL_FUNID_MODULE) log)
                   | None => (Failure, log)
                 end
              end

   | EFun vl e => (Result (S id) (inl [VClos env [] id vl e]) eff, log_increase (inl _EVAL_FUN) log)
   | ECons hd tl => 
     match fbs_expr clock' log env modules own_module id tl eff with
       | (Result id' (inl [tlv]) eff', log') =>
         match fbs_expr clock' log' env modules own_module id' hd eff' with
         | (Result id'' (inl [hdv]) eff'', log'') => (Result id'' (inl [VCons hdv tlv]) eff'', log_increase (inl _EVAL_CONS) log'')
         | (Result _ (inl _) _, log'') => (Failure, log'') (* undefined behaviour *)
         | (r, log'') => (r, log_increase (inl _EVAL_CONS_HD_EX) log'')
         end
       | (Result _ (inl _) _, log'') => (Failure, log'') (* undefined behaviour *)
       | (r, log'') => (r, log_increase (inl _EVAL_CONS_TL_EX) log'')
     end
   | ETuple l =>
     let res := fbs_values (fbs_expr clock') log env modules own_module id l eff in
       match res with
       | (Result id' (inl vl) eff', log') => 
             (Result id' (inl [VTuple vl]) eff', log_increase (inl _EVAL_TUPLE) log')
       | (r, log') => (r, log_increase (inl _EVAL_TUPLE_EX) log')
       end
   | ECall m f l =>
    match fbs_expr clock' log env modules own_module id m eff with
      | (Result id' (inl [v]) eff',  log') =>
        match fbs_expr clock' log' env modules own_module id' f eff with
          | (Result id'' (inl [v']) eff'', log'') =>
            let res := fbs_values (fbs_expr clock') log'' env modules own_module id'' l eff'' in
            match res with
                | (Result id''' (inl vl) eff''', log''') =>
                  match v with  
                    | VLit (Atom mname) =>
                      match v' with
                        | VLit (Atom fname) => 
                          let tlf := get_modfunc mname fname (length vl) (modules ++ stdlib) in
                          match tlf with
                            | Some func  =>
                              fbs_expr clock' (log_increase (inl _EVAL_CALL_MODULE) log''') (append_vars_to_env (varl func) vl [])  (modules) mname id''' (body func) eff''' 
                            | None => (Result id''' (fst (eval mname fname vl eff''')) (snd (eval mname fname vl eff''')) ,log_increase (inr (convert_string_to_code (mname,fname))) (log_increase (inl _EVAL_CALL) log'''))
                          end
                        | _ =>  (Result id''' (inr (fun_clause v')) eff''' , log_increase(inl _EVAL_CALL_FEXP_FUN_CLAUSE_EX) log''' )
                      end
                    | _ => (Result id''' (inr (badarg v)) eff''', log_increase(inl _EVAL_CALL_MEXP_BADARG_EX) log''')
                  end
                | (r, log') => (r, log_increase (inl _EVAL_CALL_EX) log')
            end
          | (Result _ (inl _) _, log'') => (Failure, log'') (* undefined behaviour *)
          | (r, log'') => (r, log_increase (inl _EVAL_CALL_FEXP_EX) log'')
        end
      | (Result _ (inl _) _, log'') => (Failure, log'') (* undefined behaviour *)
      | (r, log'') => (r, log_increase (inl _EVAL_CALL_MEXP_EX) log'')
    end
   | EPrimOp f l =>
     let res := fbs_values (fbs_expr clock') log env modules own_module id l eff in
       match res with
       | (Result id' (inl vl) eff', log') => 
            (Result id' (fst (primop_eval f vl eff')) (snd (primop_eval f vl eff')) ,log_increase (inr (convert_primop_to_code (f))) (log_increase (inl _EVAL_PRIMOP) log'))
       | (r, log') => (r, log_increase (inl _EVAL_PRIMOP_EX) log')
       end
   | EApp exp l =>
     match fbs_expr clock' log env modules own_module id exp eff with
     | (Result id' (inl [v]) eff', log') =>
       let res := fbs_values (fbs_expr clock') log' env modules own_module id' l eff' in
         match res with
         | (Result id'' (inl vl) eff'', log'') => 
           match v with
           | VClos ref ext closid varl body =>
              if Nat.eqb (length varl) (length vl)
              then fbs_expr clock' (log_increase (inl _EVAL_APP) log'') (append_vars_to_env varl vl (get_env ref ext)) modules own_module id'' body eff''
              else (Result id'' (inr (badarity v)) eff'', log_increase (inl _EVAL_APP_EX_BADARITY) log'')
           | _ => (Result id'' (inr (badfun v)) eff'', log_increase (inl _EVAL_APP_EX_BADFUN) log'')
           end
         | (r, log'') => (r, log_increase (inl _EVAL_APP_EX_PARAM) log'')
         end
     | (Result _ (inl _) _, log') => (Failure, log')
     | (r, log') => (r, log_increase (inl _EVAL_APP_EX) log')
     end
   | ECase e l =>
     match fbs_expr clock' log env modules own_module id e eff with
     | (Result id' (inl vals) eff', log') =>
        fbs_case (log_increase (inl _EVAL_CASE) log') l env modules own_module id' eff' vals (fbs_expr clock')
     | (r, log') => (r, log_increase (inl _EVAL_CASE_EX) log')
     end
   | ELet l e1 e2 =>
      match fbs_expr clock' log env modules own_module id e1 eff with
      | (Result id' (inl vals) eff', log') =>
        if Nat.eqb (length vals) (length l)
        then fbs_expr clock' (log_increase (inl _EVAL_LET) log') (append_vars_to_env l vals env) modules own_module id' e2 eff'
        else (Failure, log')
      | (r, log') => (r, log_increase (inl _EVAL_LET_EX) log')
      end
   | ESeq e1 e2 =>
      match fbs_expr clock' log env modules own_module id e1 eff with
      | (Result id' (inl [v]) eff', log') => fbs_expr clock' (log_increase (inl _EVAL_SEQ) log') env modules own_module id' e2 eff'
      | (Result _ (inl _) _, log') => (Failure, log')
      | (r, log') => (r, log_increase (inl _EVAL_SEQ_EX) log')
      end
   | ELetRec l e => fbs_expr clock' (log_increase (inl _EVAL_LETREC) log) (append_funs_to_env l env id) modules own_module (id + length l) e eff
   | EMap l =>
     let res := fbs_values (fbs_expr clock') log env modules own_module id (make_map_exps l) eff in
       match res with
       | (Result id' (inl vals) eff', log') => 
         match make_map_vals_inverse vals with
         | None => (Failure, log')
         | Some (kvals, vvals) =>
             (Result id' (inl [VMap (combine (fst (make_value_map kvals vvals)) (snd (make_value_map kvals vvals)))]) eff', log_increase (inl _EVAL_MAP) log')
         end
       | (r, log') => (r, log_increase (inl _EVAL_MAP_EX) log')
       end
   | ETry e1 vl1 e2 vl2 e3 =>
     match fbs_expr clock' log env modules own_module id e1 eff with
     | (Result id' (inl vals) eff', log') =>
       if Nat.eqb (length vals) (length vl1)
       then fbs_expr clock' (log_increase (inl _EVAL_TRY) log') (append_vars_to_env vl1 vals env) modules own_module id' e2 eff'
       else (Failure, log')
     | (Result id' (inr ex) eff', log') =>
       fbs_expr clock' (log_increase (inl _EVAL_CATCH) log') (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) modules own_module id' e3 eff'
     | r => r
     end
  end
end
.

Definition pp_semantic_rule (r : Semantic_rule) : string :=
match r with
 | _EVAL_SINGLE => "'_SINGLE'"
 | _EVAL_VALUES => "'_VALUES'"
 | _EVAL_LIST_CONS => "'_LIST_CONS'"
 | _EVAL_LIST_EMPTY => "'_LIST_EMPTY'"
 | _EVAL_LIST_EX_PROP => "'_LIST_EX_PROP'"
 | _EVAL_LIST_EX_CREATE => "'_LIST_EX_CREATE'"
 | _EVAL_LIT => "'_LIT'"
 | _EVAL_VAR => "'_VAR'"
 | _EVAL_FUNID => "'_FUNID'"
 | _EVAL_FUNID_MODULE => "'_FUNID_MODULE'" 
 | _EVAL_FUN => "'_FUN'"
 | _EVAL_CONS => "'_CONS'"
 | _EVAL_NIL => "'_NIL'"
 | _EVAL_CONS_HD_EX => "'_CONS_HD_EX'"
 | _EVAL_CONS_TL_EX => "'_CONS_TL_EX'"
 | _EVAL_TUPLE => "'_TUPLE'"
 | _EVAL_TUPLE_EX => "'_TUPLE_EX'"
 | _EVAL_CALL => "'_CALL'"
 | _EVAL_CALL_MODULE => "'_CALL_MODULE'"
 | _EVAL_CALL_FEXP_EX => "'_CALL_FEXP_EX'"
 | _EVAL_CALL_FEXP_FUN_CLAUSE_EX => "'_CALL_FEXP_FUN_CLAUSE_EX'"
 | _EVAL_CALL_MEXP_BADARG_EX => "'_CALL_MEXP_BADARG_EX'"
 | _EVAL_CALL_MEXP_EX => "'_CALL_MEXP_EX'"
 | _EVAL_CALL_EX => "'_CALL_EX'"
 | _EVAL_PRIMOP => "'_PRIMOP'"
 | _EVAL_PRIMOP_EX => "'_PRIMOP_EX'"
 | _EVAL_APP => "'_APP'"
 | _EVAL_APP_EX => "'_APP_EX'"
 | _EVAL_APP_EX_PARAM => "'_APP_EX_PARAM'"
 | _EVAL_APP_EX_BADFUN => "'_APP_EX_BADFUN'"
 | _EVAL_APP_EX_BADARITY => "'_APP_EX_BADARITY'"
 | _EVAL_CASE => "'_CASE'"
 | _EVAL_CASE_EX => "'_CASE_EX'"
 | _EVAL_CASE_TRUE => "'_CASE_TRUE'"
 | _EVAL_CASE_FALSE => "'_CASE_FALSE'"
 | _EVAL_CASE_IFCLAUSE => "'_CASE_IFCLAUSE'"
 | _EVAL_CASE_NOMATCH => "'_CASE_NOMATCH'"
 | _EVAL_LET => "'_LET'"
 | _EVAL_LET_EX => "'_LET_EX'"
 | _EVAL_LETREC => "'_LETREC'"
 | _EVAL_SEQ => "'_SEQ'"
 | _EVAL_SEQ_EX => "'_SEQ_EX'"
 | _EVAL_MAP => "'_MAP'"
 | _EVAL_MAP_EX => "'_MAP_EX'"
 | _EVAL_TRY => "'_TRY'"
 | _EVAL_CATCH => "'_CATCH'"
 (* | _FAIL => "'_FAIL'"
 | _TIMEOUT => "'_TIMEOUT'" *)
end.

Definition pp_BIF (c : BIFCode) : string :=
match c with
| BPlus => "'+'"
| BMinus => "'-'"
| BMult => "'*'"
| BDivide => "'/'"
| BSl => "'bsl'"
| BSr => "'bsr'"
| BRem => "'rem'"
| BDiv => "'div'"
| BAbs => "'abs'"
| BFwrite => "'fwrite'"
| BFread => "'fread'"
| BAnd => "'and'"
| BOr => "'or'"
| BNot => "'not'"
| BEq => "'=='"
| BTypeEq => "'=:='"
| BNeq => "'/='"
| BTypeNeq => "'=/='"
| BApp => "'++'"
| BMinusMinus => "'--'"
| BTupleToList => "'tuple_to_list'"
| BListToTuple => "'list_to_tuple'"
| BLt => "'<'"
| BGt => "'>'"
| BLe => "'=<'"
| BGe => "'>='"
| BLength => "'length'"
| BTupleSize => "'tuple_size'"
| BHd => "'hd'"
| BTl => "'tl'"
| BElement => "'element'"
| BSetElement => "'setelement'"
| BIsNumber => "is_number"%string
| BIsInteger => "is_integer"%string
| BIsAtom => "is_atom"%string
| BIsBoolean => "is_boolean"%string
| BError => "error"%string
| PMatchFail => "error"%string
(** anything else *)
| BNothing => "'undef'"
end.

Open Scope string_scope.

Fixpoint pp_list {A : Type} (pp : A -> string) (l : list A) : string :=
match l with
| [] => ""
| [x] => pp x
| x::xs => (pp x ++ "," ++ pp_list pp xs)
end.

Fixpoint pp_map {A : Type} (pp : A -> string) (l : LogMap A) : string :=
match l with
| [] => ""
| [(k, v)] => pp k ++ " => " ++ NilZero.string_of_int (Z.to_int v)
| (k, v)::xs => (pp k ++ " => " ++ NilZero.string_of_int (Z.to_int v) ++ "," ++ pp_map pp xs)
end.

Definition result_value (res : ResultType * Log) : string :=
match res with
| (Result _ (inl [val]) _, log) =>
    "__coqresult: " ++ pretty_print_value val ++ " % #{" ++ pp_map pp_semantic_rule (fst log) ++ "} % #{" ++ pp_map pp_BIF (snd log) ++ "}"
| (Result _ (inl vals) _, log)  =>
    "__invalidcoqresult: [" ++ pp_list pretty_print_value vals ++ "] % #{" ++ pp_map pp_semantic_rule (fst log) ++ "} % #{" ++ pp_map pp_BIF (snd log) ++ "}"
| (Result _ (inr ex) _, log) =>
    "__exceptioncoqresult: " ++ pp_exception ex ++ " % #{" ++ pp_map pp_semantic_rule (fst log) ++ "} % #{" ++ pp_map pp_BIF (snd log) ++ "}"
| (Timeout, log) =>
    "__invalidcoqresult: Timeout % #{" ++ pp_map pp_semantic_rule (fst log) ++ "} % #{" ++ pp_map pp_BIF (snd log) ++ "}"
| (Failure, log) =>
    "__invalidcoqresult: Failure % #{" ++ pp_map pp_semantic_rule (fst log) ++ "} % #{" ++ pp_map pp_BIF (snd log) ++ "}"
end.

Fixpoint init_map {A : Type} (l : list A) (eqb : A -> A -> bool) : LogMap A :=
match l with
| [] => []
| x::xs => put x 0%Z (init_map xs eqb) eqb
end.

Definition init_logs : Log :=
  (init_map rule_list Semantic_rule_beq, init_map BIF_list BIFCode_beq).
  
  




