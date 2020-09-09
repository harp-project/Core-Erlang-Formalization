Require Core_Erlang_Auxiliaries.

Module Functional_Big_Step.


Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.

Import ListNotations.


Fixpoint list_eqb {A : Type} (eq : A -> A -> bool) (l1 l2 : list A) : bool :=
match l1, l2 with
| [], [] => true
| x::xs, y::ys => eq x y && list_eqb eq xs ys
| _, _ => false
end.

Definition effect_id_eqb (id1 id2 : SideEffectId) : bool :=
match id1, id2 with
 | Input, Input => true
 | Output, Output => true
 | _, _ => false
end.


Definition effect_eqb (e1 e2 : SideEffectId * list Value) : bool :=
match e1, e2 with
| (id1, vals1), (id2, vals2) => effect_id_eqb id1 id2 && list_eqb Value_eqb vals1 vals2
end.

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Inductive MapResultType : Type :=
| MapResult (id : nat) (res : (ValueSequence * ValueSequence) + Exception) (eff : SideEffectList)
| MapTimeout
| MapFailure.

Fixpoint fbs_expr (env : Environment) (id : nat) (expr : Expression) (eff : SideEffectList) (clock : nat) {struct clock} : ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
  match expr with
   | EValues el => 
       (fix eval_list env id exps eff : ResultType := 
                   match exps with
                   | []    => Result id (inl []) eff
                   | x::xs => match fbs_single env id x eff clock' with
                              | Result id' (inl [v]) eff' => 
                                let res := eval_list env id' xs eff' in
                                  match res with
                                  | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
                                  | r => r
                                  end
                              | Result id' (inl val) eff' => Failure (* undefined behaviour *)
                              | r => r
                              end
                   end
                   ) env id el eff
   | ESingle e => fbs_single env id e eff clock'
  end
end
with fbs_single (env : Environment) (id : nat) (expr : SingleExpression) (eff : SideEffectList) (clock : nat) {struct clock} : ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
  match expr with
   | ENil => Result id (inl [VNil]) eff
   | ELit l => Result id (inl [VLit l]) eff
   | EVar v => Result id (get_value env (inl v)) eff
   | EFunId f => Result id (get_value env (inr f)) eff
   | EFun vl e => Result (S id) (inl [VClos env [] id vl e]) eff
   | ECons hd tl => 
     match fbs_expr env id hd eff clock' with
       | Result id' (inl [hdv]) eff' =>
         match fbs_expr env id' tl eff' clock' with
         | Result id'' (inl [tlv]) eff'' => Result id'' (inl [VCons hdv tlv]) eff''
         | Result id'' (inl val) eff'' => Failure (* undefined behaviour *)
         | r => r
         end
       | Result id' (inl val) eff' => Failure (* undefined behaviour *)
       | r => r
     end
   | ETuple l =>
     let res := 
     (fix eval_list env id exps eff : ResultType := 
         match exps with
         | []    => Result id (inl []) eff
         | x::xs => match fbs_expr env id x eff clock' with
                    | Result id' (inl [v]) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inl val) eff' => Failure (* undefined behaviour *)
                    | r => r
                    end
         end
         ) env id l eff
       in
       match res with
       | Result id' (inl vl) eff' => Result id' (inl [VTuple vl]) eff'
       | r => r
       end
   | ECall f l => 
     let res := 
     (fix eval_list env id exps eff : ResultType := 
         match exps with
         | []    => Result id (inl []) eff
         | x::xs => match fbs_expr env id x eff clock' with
                    | Result id' (inl [v]) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inl val) eff' => Failure (* undefined behaviour *)
                    | r => r
                    end
         end
         ) env id l eff
       in
       match res with
       | Result id' (inl vl) eff' => let (x, y) := eval f vl eff' in Result id' x y
       | r => r
       end
   | EPrimOp f l =>
     let res := 
     (fix eval_list env id exps eff : ResultType := 
         match exps with
         | []    => Result id (inl []) eff
         | x::xs => match fbs_expr env id x eff clock' with
                    | Result id' (inl [v]) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inl val) eff' => Failure (* undefined behaviour *)
                    | r => r
                    end
         end
         ) env id l eff
       in
       match res with
       | Result id' (inl vl) eff' => let (x, y) := eval f vl eff' in Result id' x y
       | r => r
       end
   | EApp exp l =>
     match fbs_expr env id exp eff clock' with
     | Result id' (inl [v]) eff' =>
       let res := 
       (fix eval_list env id exps eff : ResultType := 
         match exps with
         | []    => Result id (inl []) eff
         | x::xs => match fbs_expr env id x eff clock' with
                    | Result id' (inl [v]) eff' => 
                      let res := eval_list env id' xs eff' in
                        match res with
                        | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
                        | r => r
                        end
                    | Result id' (inl val) eff' => Failure (* undefined behaviour *)
                    | r => r
                    end
         end
         ) env id' l eff'
         in
         match res with
         | Result id'' (inl vl) eff'' => 
           match v with
           | VClos ref ext closid varl body =>
              if Nat.eqb (length varl) (length vl)
              then fbs_expr (append_vars_to_env varl vl (get_env ref ext)) id'' body eff'' clock'
              else Result id'' (inr (badarity v)) eff''
           | _ => Result id'' (inr (badfun v)) eff''
           end
         | r => r
         end
     | Result id' (inl val) eff' => Failure
     | r => r
     end
   | ECase e l =>
     match fbs_expr env id e eff clock' with
     | Result id' (inl vals) eff' =>
       (fix clause_eval l i' :=
         let i := (length l) - i' in
           match i' with
           | 0 => Result id' (inr if_clause) eff'
           | S i'' =>
           (* TODO: side effects cannot be produced here *)
             match match_clause vals l i with
             | Some (gg, bb, bindings) =>
               match fbs_expr (add_bindings bindings env) id' gg eff' clock' with
               | Result id'' (inl [v]) eff'' =>  
                   match v with
                   | VLit (Atom "true"%string)  => 
                      if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
                      then fbs_expr (add_bindings bindings env) id' bb eff' clock'
                      else (* undef *) Failure
                   | VLit (Atom "false"%string) => clause_eval l i''
                   | _ => Failure
                   end
               | _ => Failure
               end
             | None => clause_eval l i''
             end
           end
       ) l (length l)
     | r => r
     end
   | ELet l e1 e2 =>
      match fbs_expr env id e1 eff clock' with
      | Result id' (inl vals) eff' =>
        if Nat.eqb (length vals) (length l)
        then fbs_expr (append_vars_to_env l vals env) id' e2 eff' clock'
        else Failure
      | r => r
      end
   | ESeq e1 e2 =>
      match fbs_expr env id e1 eff clock' with
      | Result id' (inl [v]) eff' => fbs_expr env id' e2 eff' clock'
      | Result id' (inl vals) eff' => Failure
      | r => r
      end
   | ELetRec l e => fbs_expr (append_funs_to_env l env id) (id + length l) e eff clock'
   | EMap l =>
     let res :=
     (fix eval_list_map env id exps eff : MapResultType :=
       match exps with
       | [] => MapResult id (inl ([], [])) eff
       | (key, val)::xs =>
         match fbs_expr env id key eff clock' with
         | Result id' (inl [kval]) eff' =>
            match fbs_expr env id' val eff' clock' with
            | Result id'' (inl [vval]) eff'' => 
               let res := eval_list_map env id'' xs eff''
               in match res with
               | MapResult id''' (inl (kvals, vvals)) eff''' =>
                  MapResult id''' (inl (kval::kvals, vval::vvals)) eff'''
               | r => r
               end
            | Result id'' (inl vals) eff'' => MapFailure
            | Result id'' (inr ex) eff'' => MapResult id'' (inr ex) eff''
            | Failure => MapFailure
            | Timeout => MapTimeout
            end
         | Result id' (inl vals) eff' => MapFailure
         | Result id'' (inr ex) eff'' => MapResult id'' (inr ex) eff''
         | Failure => MapFailure
         | Timeout => MapTimeout
         end
       end
     ) env id l eff in
     match res with
     | MapResult id' (inl (kvals, vvals)) eff' =>
       let (x, y) := make_value_map kvals vvals
       in Result id' (inl [VMap (combine x y)]) eff'
     | MapResult id' (inr ex) eff' => Result id' (inr ex) eff'
     | MapFailure => Failure
     | MapTimeout => Timeout
     end
   | ETry e1 vl1 e2 vl2 e3 =>
     match fbs_expr env id e1 eff clock' with
     | Result id' (inl vals) eff' =>
       if Nat.eqb (length vals) (length vl1)
       then fbs_expr (append_vars_to_env vl1 vals env) id' e2 eff' clock'
       else Failure
     | Result id' (inr ex) eff' =>
       fbs_expr (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) id' e3 eff' clock'
     | r => r
     end
  end
end
.

End Functional_Big_Step.