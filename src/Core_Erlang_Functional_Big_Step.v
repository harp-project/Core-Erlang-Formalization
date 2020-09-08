Require Core_Erlang_Auxiliaries.

(** The Semantics of Core Erlang *)
Module Semantics.

Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.

Module Functional_Big_Step.

Import ListNotations.

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Fixpoint fbs_expr (env : Environment) (id : nat) (expr : Expression) (eff : SideEffectList) (clock : nat) : ResultType :=
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
                              | r => r
                              end
                   end
                   ) env id el eff
   | ESingle e => fbs_single env id e eff clock
  end
end
with fbs_single (env : Environment) (id : nat) (expr : SingleExpression) (eff : SideEffectList) (clock : nat) : ResultType :=
match expr with
 | ENil => Result id (inl [VNil]) eff
 | ELit l => Result id (inl [VLit l]) eff
 | EVar v => Result id (get_value env (inl v)) eff
 | EFunId f => Result id (get_value env (inr f)) eff
 | EFun vl e => Result id (inl [VClos env [] id vl e]) eff
 | ECons hd tl => Result id (inr novar) eff
 | ETuple l => Result id (inr novar) eff
 | ECall f l => Result id (inr novar) eff
 | EPrimOp f l => Result id (inr novar) eff
 | EApp exp l => Result id (inr novar) eff
 | ECase e l => Result id (inr novar) eff
 | ELet l e1 e2 => Result id (inr novar) eff
 | ESeq e1 e2 => Result id (inr novar) eff
 | ELetRec l e => Result id (inr novar) eff
 | EMap l => Result id (inr novar) eff
 | ETry e1 vl1 e2 vl2 e0 => Result id (inr novar) eff
end
.

End Functional_Big_Step.