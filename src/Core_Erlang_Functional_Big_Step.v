Require Core_Erlang_Module_Helper.

Module Functional_Big_Step.


Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Module_Helper.Module_Helper.

Export Core_Erlang_Environment.Environment.

Import ListNotations.

(* Module Helpers *)

(*
(* Returns a module by name from a module list *)
Fixpoint get_module (name : string) (ml : list ErlModule) : option ErlModule := 
    match ml with
    | m :: ms => if (eqb  (fst (fst (fst m)))  name)  then Some m else get_module name ms
    | [] => None
end
.

(* Checks if a function is in the list of function identifiers*)
Fixpoint check_in_functions (name : string) (arity : nat) (fl: list FunctionIdentifier) : bool :=
    match fl with
    | f :: fs => if andb (eqb (fst f) name)  (Nat.eqb (snd f) arity) then true else check_in_functions name arity fs 
    | [] => false
end.

(* Returns a function from a list of top-level function by name *)
Fixpoint get_function (name : string) (arity : nat) (fl: list TopLevelFunction) : option TopLevelFunction :=
    match fl with
    | f :: fs => if andb (eqb (fst (fst f)) (name)) (Nat.eqb (snd (fst f)) (arity)) then Some f else get_function name arity fs
    | [] => None

end.


Definition get_modfunc (mname : string) (fname : string) (arity : nat) (ml : list ErlModule) : option TopLevelFunction  :=
    match get_module mname ml with
    | Some (name, fns, atrs, funcs) => 
        if check_in_functions fname arity fns then
                get_function fname arity funcs
            else
                None
    | None => None
end.

*)


(* A notation would be helpful for records (or not??)
  Name conflict is wierd :D

*)

(* Module Helpers end *)

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Fixpoint fbs_values {A : Type} (f : Environment -> (list ErlModule) -> string -> nat -> A -> SideEffectList -> ResultType) (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat) (exps : list A) (eff : SideEffectList) : ResultType :=
match exps with
| []    => Result id (inl []) eff
| x::xs => match f env modules own_module id x eff with
          | Result id' (inl [v]) eff' => 
            let res := fbs_values f env modules own_module id' xs eff' in
              match res with
              | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
              | r => r
              end
          | Result _ (inl _) _ => Failure (* undefined behaviour *)
          | r => r
          end
end.

Fixpoint fbs_case (l : list (list Pattern * Expression * Expression)) (env : Environment) (modules : list ErlModule) (own_module : string) (id' : nat) (eff' : SideEffectList) (vals : ValueSequence) (f : Environment -> (list ErlModule) -> string -> nat -> Expression -> SideEffectList -> ResultType) : ResultType :=
match l with
| [] => Result id' (inr if_clause) eff'
| (pl, gg, bb)::xs =>
(* TODO: side effects cannot be produced here *)
 if match_valuelist_to_patternlist vals pl
 then
   match f (add_bindings (match_valuelist_bind_patternlist vals pl) env) modules own_module id' gg eff' with
   | Result id'' (inl [v]) eff'' =>  
     if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
     then
       match v with
       | VLit (Atom s) =>
         if String.eqb s "true"%string then
           f (add_bindings (match_valuelist_bind_patternlist vals pl) env) modules own_module id' bb eff'
         else if String.eqb s "false"%string 
              then fbs_case xs env modules own_module id' eff' vals f
              else Failure
       | _ => Failure
       end
     else Failure
   | _ => Failure
   end
 else fbs_case xs env modules own_module id' eff' vals f
end.

Fixpoint fbs_expr (clock : nat) (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat) (expr : Expression) (eff : SideEffectList) {struct clock} : ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
  match expr with
   | EValues el => fbs_values (fbs_expr clock') env modules own_module id el eff
(*    | ESingle e => fbs_single clock' env id e eff
  end
end
with fbs_single (clock : nat) (env : Environment) (id : nat) (expr : SingleExpression) (eff : SideEffectList) {struct clock} : ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
  match expr with *)
   | ENil => Result id (inl [VNil]) eff
   | ELit l => Result id (inl [VLit l]) eff
   | EVar v => match get_value env (inl v) with
               | Some res => Result id (inl res) eff
               | None => Failure
               end
   | EFunId f => match get_value env (inr f) with
                 | Some res => Result id (inl res) eff
                 | None => 
                    let tlf := get_own_modfunc own_module (fst f) (snd f) ( modules ++ stdlib) in
                    match tlf with
                      | Some func  => Result id (inl [VClos env [] id (varl func) (body func)]) eff 
                      | None => Failure
                    end
                 end
   | EFun vl e => Result (S id) (inl [VClos env [] id vl e]) eff
   | ECons hd tl => 
     match fbs_expr clock' env modules own_module id tl eff with
       | Result id' (inl [tlv]) eff' =>
         match fbs_expr clock' env modules own_module id' hd eff' with
         | Result id'' (inl [hdv]) eff'' => Result id'' (inl [VCons hdv tlv]) eff''
         | Result _ (inl _) _ => Failure (* undefined behaviour *)
         | r => r
         end
       | Result _ (inl _) _ => Failure (* undefined behaviour *)
       | r => r
     end
   | ETuple l =>
     let res := fbs_values (fbs_expr clock') env modules own_module id l eff in
       match res with
       | Result id' (inl vl) eff' => Result id' (inl [VTuple vl]) eff'
       | r => r
       end
   | ECall m f l =>
    match fbs_expr clock' env modules own_module id m eff with
      | Result id' (inl [v]) eff' =>
        match fbs_expr clock' env modules own_module id' f eff' with
          | Result id'' (inl [v']) eff'' =>
            (* Both module and func expression is correct (ASK: split by types needed?) *)
            let res := fbs_values (fbs_expr clock') env modules own_module id'' l eff'' in
            match res with
              | Result id''' (inl vl) eff''' =>
                match v with
                  | VLit (Atom mname) =>
                    match v' with
                    | VLit (Atom fname) => 
                      let tlf := get_modfunc mname fname (length vl) (modules ++ stdlib) in
                      match tlf with
                        | Some func  =>
                          fbs_expr clock' (append_vars_to_env (varl func) vl []) (modules) mname id''' (body func) eff''' 
                        | None => 
                          match res with
                              | Result id''' (inl vl) eff''' => Result id''' (fst (eval mname fname vl eff''')) (snd (eval mname fname vl eff'''))
                              | r => r
                          end
                      end
                    | _ => Result id''' (inr (fun_clause v')) eff'''
                    end
                  | _ => Result id''' (inr (badarg v)) eff'''
                end          
              | r => r
            end
          | Result _ (inl _) _ => Failure
          | r => r
        end
      | Result _ (inl _) _ => Failure
      | r => r
    end
   | EPrimOp f l =>
     let res := fbs_values (fbs_expr clock') env modules own_module id l eff in
       match res with
       | Result id' (inl vl) eff' => Result id' (fst (primop_eval f vl eff')) (snd (primop_eval f vl eff'))
       | r => r
       end
   | EApp exp l =>
     match fbs_expr clock' env modules own_module id exp eff with
     | Result id' (inl [v]) eff' =>
       let res := fbs_values (fbs_expr clock') env modules own_module id' l eff' in
         match res with
         | Result id'' (inl vl) eff'' => 
           match v with
           | VClos ref ext closid varl body =>
              if Nat.eqb (length varl) (length vl)
              then fbs_expr clock' (append_vars_to_env varl vl (get_env ref ext)) modules own_module id'' body eff''
              else Result id'' (inr (badarity v)) eff''
           | _ => Result id'' (inr (badfun v)) eff''
           end
         | r => r
         end
     | Result _ (inl _) _ => Failure
     | r => r
     end
   | ECase e l =>
     match fbs_expr clock' env modules own_module id e eff with
     | Result id' (inl vals) eff' =>
        fbs_case l env modules own_module id' eff' vals (fbs_expr clock')
     | r => r
     end
   | ELet l e1 e2 =>
      match fbs_expr clock' env modules own_module id e1 eff with
      | Result id' (inl vals) eff' =>
        if Nat.eqb (length vals) (length l)
        then fbs_expr clock' (append_vars_to_env l vals env) modules own_module id' e2 eff'
        else Failure
      | r => r
      end
   | ESeq e1 e2 =>
      match fbs_expr clock' env modules own_module id e1 eff with
      | Result id' (inl [v]) eff' => fbs_expr clock' env modules own_module id' e2 eff'
      | Result _ (inl _) _ => Failure
      | r => r
      end
   | ELetRec l e => fbs_expr clock' (append_funs_to_env l env id) modules own_module (id + length l) e eff
   | EMap l =>
     let res := fbs_values (fbs_expr clock') env modules own_module id (make_map_exps l) eff in
       match res with
       | Result id' (inl vals) eff' => 
         match make_map_vals_inverse vals with
         | None => Failure
         | Some (kvals, vvals) =>
             Result id' (inl [VMap (combine (fst (make_value_map kvals vvals)) (snd (make_value_map kvals vvals)))]) eff'
         end
       | r => r
       end
   | ETry e1 vl1 e2 vl2 e3 =>
     match fbs_expr clock' env modules own_module id e1 eff with
     | Result id' (inl vals) eff' =>
       if Nat.eqb (length vals) (length vl1)
       then fbs_expr clock' (append_vars_to_env vl1 vals env) modules own_module id' e2 eff'
       else Failure
     | Result id' (inr ex) eff' =>
       fbs_expr clock' (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) modules own_module id' e3 eff'
     | r => r
     end
  end
end
.

(**
  https://arxiv.org/pdf/2003.06458.pdf 145. site
**)
Ltac break_match_hyp :=
match goal with
| [ H : context [ match ?X with _=>_ end ] |- _] =>
     match type of X with
     | sumbool _ _=>destruct X
     | _=>destruct X eqn:? 
     end 
end.

Ltac break_match_goal :=
match goal with
| [ |- context [ match ?X with _=>_ end ] ] => 
    match type of X with
    | sumbool _ _ => destruct X
    | _ => destruct X eqn:?
    end
end.

Ltac break_match_singleton :=
break_match_hyp; [ break_match_hyp;
                       [ break_match_hyp;
                         [ congruence | break_match_hyp; [ idtac | congruence] ]
                       | idtac ]
 | congruence | congruence ].

Ltac break_match_list :=
break_match_hyp; [ break_match_hyp
 | congruence | congruence ].

Fixpoint pp_list {A : Type} (pp : A -> string) (l : list A) : string :=
match l with
| [] => ""
| [x] => pp x
| x::xs => (pp x ++ "," ++ pp_list pp xs)
end.

Definition result_value (res : ResultType) : string :=
match res with
| Result _ (inl [val]) _ =>
    "__coqresult: " ++ pretty_print_value val
| Result _ (inl vals) _ =>
    "__invalidcoqresult: [" ++ pp_list pretty_print_value vals ++ "]"
| Result _ (inr ex) _ =>
    "__exceptioncoqresult: " ++ pp_exception ex
| Timeout =>
    "__invalidcoqresult: Timeout"
| Failure =>
    "__invalidcoqresult: Failure"
end.

Section clock_increasing.

Theorem clock_list_increase :
forall {A:Type} {l env modules own_module id eff id' res eff' clock} {f : nat -> Environment -> (list ErlModule) -> string -> nat -> A -> SideEffectList -> ResultType},
(forall (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat) (exp : A) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          f clock env modules own_module id exp eff = Result id' res eff' ->
          f (S clock) env modules own_module id exp eff = Result id' res eff') ->
  fbs_values (f clock) env modules own_module id l eff = Result id' res eff'
->
  fbs_values (f (S clock)) env modules own_module id l eff = Result id' res eff'.
Proof.
  induction l; intros.
  * simpl. inversion H0. subst. auto.
  * simpl in H0. break_match_singleton.
    - apply H in Heqr.
      remember (S clock) as cl. simpl. rewrite Heqr.
      rewrite Heqcl in *.
      break_match_list.
      + pose (IHl _ _ _ _ _ _ _ _ _ _ H Heqr0). rewrite e. auto.
      + apply IHl in Heqr0. rewrite Heqr0. auto. intros. apply H. auto.
    - apply H in Heqr. inversion H0. subst.
      remember (S clock) as cl. simpl. rewrite Heqr. auto.
Qed.

Theorem bigger_clock_list :
  forall {A : Type} {clock env modules own_module id exps eff id' res eff'} {f : nat -> Environment -> (list ErlModule) -> string -> nat -> A -> SideEffectList -> ResultType} clock',
  clock <= clock' ->
  (forall (clock : nat) (env : Environment) (modules : list ErlModule) (own_module : string) (id : nat) (exp : A) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          f clock env modules own_module id exp eff = Result id' res eff' ->
          f (S clock) env modules own_module id exp eff = Result id' res eff') ->
  fbs_values (f clock) env modules own_module id exps eff = Result id' res eff'
->
  fbs_values (f clock') env modules own_module id exps eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption.
  * apply clock_list_increase. 2: auto. intros. auto.
Qed.

Lemma case_clock_increase :
forall {clock env modules own_module l id' res eff' id0 eff0 vals},
fbs_case l env modules own_module id0 eff0 vals (fbs_expr clock) = Result id' res eff' ->
(forall (env : Environment) (id : nat) (exp : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          fbs_expr clock env modules own_module id exp eff = Result id' res eff' ->
          fbs_expr (S clock) env modules own_module id exp eff = Result id' res eff')
->
fbs_case l env modules own_module id0 eff0 vals (fbs_expr (S clock)) = Result id' res eff'.
Proof.
  induction l; intros.
  * simpl in *. auto.
  * destruct a. destruct p. remember (S clock) as cl.
    simpl. simpl in H.
    break_match_hyp.
    - break_match_singleton. 2: congruence.
      apply H0 in Heqr; rewrite Heqr.
      break_match_hyp. 2: congruence.
      break_match_hyp; try congruence. break_match_hyp; try congruence.
      break_match_hyp.
      + apply H0 in H. exact H.
      + break_match_hyp. 2: congruence. apply IHl; auto.
    - apply IHl; auto.
Qed.

(* Ltac solve_call_expr := (
   apply IHclock in Heqr;
   apply IHclock in Heqr0;
   apply clock_list_increase in Heqr1;
   remember (S clock) as cl; simpl;
   rewrite Heqr; rewrite Heqr0;
   rewrite Heqr1; auto; auto). *)


(* Theorem clock_increase_single :
forall {clock env id exp eff id' res eff'},
  fbs_single clock env id exp eff = Result id' res eff'
->
  fbs_single (S clock) env id exp eff = Result id' res eff' *)
Theorem clock_increase_expr :
forall {clock env modules own_module id exp eff id' res eff'},
  fbs_expr clock env modules own_module id exp eff = Result id' res eff'
->
  fbs_expr (S clock) env modules own_module id exp eff = Result id' res eff'.
Proof.
  induction clock; intros.
  * simpl in H. inversion H.
  * simpl in H. destruct exp; intros.
    2-6: simpl; inversion H; reflexivity.
    - apply clock_list_increase in H. remember (S clock) as cl. simpl. auto. auto.
    - remember (S clock) as cl. simpl.
      rewrite Heqcl in *.
      break_match_singleton.
      + apply IHclock in Heqr. rewrite Heqr.
        break_match_singleton; apply IHclock in Heqr0; rewrite Heqr0; auto.
      + apply IHclock in Heqr. rewrite Heqr. auto.
    - break_match_list; apply clock_list_increase in Heqr;
        [ remember (S clock) as cl; simpl; rewrite Heqr; auto | auto |
          remember (S clock) as cl; simpl; rewrite Heqr; auto | auto ].
    (* -  break_match_list.
        + destruct get_modfunc eqn: Heqo. (* break_match_hyp. break_match_hyp. break_match_hyp. *)
          ++  apply clock_list_increase in Heqr. remember (S clock) as cl.
            simpl. rewrite Heqr. rewrite Heqo. auto. auto.
          ++ apply clock_list_increase in Heqr. remember (S clock) as cl.
            simpl. rewrite Heqr. rewrite Heqo. auto. auto.
        +  apply clock_list_increase in Heqr. remember (S clock) as cl.
           simpl.  rewrite Heqr. auto. auto. *)
    - break_match_hyp.
      -- break_match_hyp.
        + break_match_hyp.
          ++ apply IHclock in Heqr. remember (S clock) as cl. simpl.
             rewrite Heqr. auto.
          ++ break_match_hyp.
            +++ break_match_hyp. break_match_hyp. break_match_hyp.
              --- apply IHclock in Heqr. apply IHclock in Heqr0. remember (S clock) as cl. simpl.
                  rewrite Heqr. rewrite Heqr0. auto.
              --- break_match_hyp. break_match_hyp. break_match_hyp. break_match_hyp.
                ---- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ---- break_match_hyp. break_match_hyp.
                  ----- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                        rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                  ----- break_match_hyp. break_match_hyp.
                    ------ apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                            rewrite Heqr. rewrite Heqr0. rewrite Heqr1. rewrite Heqo. auto. auto.
                    ------ apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                            rewrite Heqr. rewrite Heqr0. rewrite Heqr1. rewrite Heqo. auto. auto.
                    ------ apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                            rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                  
                            ----- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                        rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                  ----- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                        rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                  ----- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                        rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                  ----- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                        rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                  ----- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                        rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ---- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ---- apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ----  apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ----  apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ----  apply IHclock in Heqr. apply IHclock in Heqr0. apply clock_list_increase in Heqr1. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. rewrite Heqr1. auto. auto.
                ---- congruence.
                ---- congruence.
                ----  apply IHclock in Heqr. apply IHclock in Heqr0. remember (S clock) as cl. simpl.
                      rewrite Heqr. rewrite Heqr0. auto.
              --- apply IHclock in Heqr. apply IHclock in Heqr0. remember (S clock) as cl. simpl.
                  rewrite Heqr. rewrite Heqr0. auto.
              --- congruence.
              --- congruence.
            +++ apply IHclock in Heqr. remember (S clock) as cl. simpl.
                rewrite Heqr. auto.
        + apply IHclock in Heqr. remember (S clock) as cl. simpl.
          rewrite Heqr. auto.
      -- congruence.
      -- congruence.
    - break_match_list.
      + apply clock_list_increase in Heqr. 2: auto. remember (S clock) as cl.
        simpl. rewrite Heqr. auto.
      + apply clock_list_increase in Heqr. 2: auto. remember (S clock) as cl.
        simpl. rewrite Heqr. auto.
    
    - break_match_singleton.
      + apply IHclock in Heqr. remember (S clock) as cl.
        simpl. rewrite Heqr.
        break_match_list.
        ** apply clock_list_increase in Heqr0. rewrite <- Heqcl in Heqr0. rewrite Heqr0.
            break_match_hyp; try congruence.
            break_match_hyp.
            -- apply IHclock in H. rewrite H. auto.
            -- auto.
            -- intros. apply IHclock in H0. rewrite <- Heqcl. auto.
        ** apply clock_list_increase in Heqr0. rewrite <- Heqcl in Heqr0. rewrite Heqr0. auto.
            intros. apply IHclock in H0. rewrite <- Heqcl. auto.
      + apply IHclock in Heqr. remember (S clock) as cl. simpl. rewrite Heqr. auto.
    - break_match_list.
      + apply IHclock in Heqr. remember (S clock) as cl.
        simpl. rewrite Heqr.
        apply case_clock_increase in H. rewrite <- Heqcl in H.
        auto.
        intros. apply IHclock in H0. rewrite <- Heqcl. auto.
      + apply IHclock in Heqr. remember (S clock) as cl.
        simpl. rewrite Heqr. inversion H. auto.
    - break_match_list. break_match_hyp; try congruence.
      + apply IHclock in Heqr. remember (S clock) as cl. simpl.
        rewrite Heqr, Heqb. apply IHclock in H. auto.
      + apply IHclock in Heqr. remember (S clock) as cl. simpl.
        rewrite Heqr. auto.
    - break_match_singleton.
      + apply IHclock in Heqr. remember (S clock) as cl. simpl.
        rewrite Heqr. apply IHclock in H. auto.
      + apply IHclock in Heqr. remember (S clock) as cl. simpl.
        rewrite Heqr. auto.
    - apply IHclock in H. remember (S clock) as cl. simpl. auto.
    - break_match_list.
      + apply clock_list_increase in Heqr. 2: auto. remember (S clock) as cl. simpl.
        rewrite Heqr. auto.
      + apply clock_list_increase in Heqr. 2: auto. remember (S clock) as cl. simpl.
        rewrite Heqr. auto.
    - break_match_list.
      + break_match_hyp. 2: congruence.
        apply IHclock in Heqr. remember (S clock) as cl. simpl.
        rewrite Heqr, Heqb. apply IHclock in H. auto.
      + apply IHclock in Heqr. remember (S clock) as cl. simpl.
        rewrite Heqr. apply IHclock in H. auto.
(*   {
    induction clock.
    * intros. simpl in H. congruence.
    * intros. simpl in H. destruct exp.
      - apply clock_list_increase in H. remember (S clock) as cl. simpl. auto. auto.
      - apply clock_increase_single in H. remember (S clock) as cl. simpl. auto.
  } *)
Qed.

Theorem bigger_clock_expr :
  forall {clock env modules own_module id exp eff id' res eff'} clock',
  clock <= clock' ->
  fbs_expr clock env modules own_module id exp eff = Result id' res eff'
->
  fbs_expr clock' env modules own_module id exp eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption. 
  * apply clock_increase_expr. auto.
Qed.

(* Theorem bigger_clock_single :
  forall {clock env id exp eff id' res eff'} clock',
  clock <= clock' ->
  fbs_single clock env id exp eff = Result id' res eff'
->
  fbs_single clock' env id exp eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption.
  * apply clock_increase_single. auto.
Qed. *)

Lemma bigger_clock_case :
forall {clock env modules own_module l id' res eff' id0 eff0 vals} clock',
fbs_case l env modules own_module id0 eff0 vals (fbs_expr clock) = Result id' res eff' ->
clock <= clock'
->
fbs_case l env modules own_module id0 eff0 vals (fbs_expr clock') = Result id' res eff'.
Proof.
  intros. induction H0.
  * assumption.
  * apply case_clock_increase. auto. intros. apply clock_increase_expr. auto.
Qed.

End clock_increasing.

Section clock_decreasing.

(* Theorem clock_decrease_single :
forall {clock env id exp eff},
  fbs_single (S clock) env id exp eff = Timeout
->
  fbs_single clock env id exp eff = Timeout
with clock_decrease_expr :
forall {clock env id exp eff},
  fbs_expr (S clock) env id exp eff = Timeout
->
  fbs_expr clock env id exp eff = Timeout.
Proof.
{
  intros. induction clock; simpl in H.
  simpl. auto.
  destruct exp; try congruence.
  * destruct (get_value env (inl v)); congruence.
  * destruct (get_value env (inr f)); congruence.
  * admit. Abort. *)

End clock_decreasing.

End Functional_Big_Step.