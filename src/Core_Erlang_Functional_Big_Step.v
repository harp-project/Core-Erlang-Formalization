Require Core_Erlang_Auxiliaries.

Module Functional_Big_Step.


Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.

Import ListNotations.

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

Inductive MapResultType : Type :=
| MapResult (id : nat) (res : (ValueSequence * ValueSequence) + Exception) (eff : SideEffectList)
| MapTimeout
| MapFailure.

Fixpoint fbs_values {A : Type} (f : Environment -> nat -> A -> SideEffectList -> ResultType) (env : Environment) (id : nat) (exps : list A) (eff : SideEffectList) : ResultType :=
match exps with
| []    => Result id (inl []) eff
| x::xs => match f env id x eff with
          | Result id' (inl [v]) eff' => 
            let res := fbs_values f env id' xs eff' in
              match res with
              | Result id'' (inl xs') eff'' => Result id'' (inl (v::xs')) eff''
              | r => r
              end
          | Result id' (inl val) eff' => Failure (* undefined behaviour *)
          | r => r
          end
end.

Fixpoint fbs_expr (clock : nat) (env : Environment) (id : nat) (expr : Expression) (eff : SideEffectList) {struct clock} : ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
  match expr with
   | EValues el => fbs_values (fbs_single clock') env id el eff
   | ESingle e => fbs_single clock' env id e eff
  end
end
with fbs_single (clock : nat) (env : Environment) (id : nat) (expr : SingleExpression) (eff : SideEffectList) {struct clock} : ResultType :=
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
     match fbs_expr clock' env id tl eff with
       | Result id' (inl [tlv]) eff' =>
         match fbs_expr clock' env id' hd eff' with
         | Result id'' (inl [hdv]) eff'' => Result id'' (inl [VCons hdv tlv]) eff''
         | Result id'' (inl vals) eff'' => Failure (* undefined behaviour *)
         | r => r
         end
       | Result id' (inl vals) eff' => Failure (* undefined behaviour *)
       | r => r
     end
   | ETuple l =>
     let res := fbs_values (fbs_expr clock') env id l eff in
       match res with
       | Result id' (inl vl) eff' => Result id' (inl [VTuple vl]) eff'
       | r => r
       end
   | ECall f l => 
     let res := fbs_values (fbs_expr clock') env id l eff in
       match res with
       | Result id' (inl vl) eff' => Result id' (fst (eval f vl eff')) (snd (eval f vl eff'))
       | r => r
       end
   | EPrimOp f l =>
     let res := fbs_values (fbs_expr clock') env id l eff in
       match res with
       | Result id' (inl vl) eff' => Result id' (fst (eval f vl eff')) (snd (eval f vl eff'))
       | r => r
       end
   | EApp exp l =>
     match fbs_expr clock' env id exp eff with
     | Result id' (inl [v]) eff' =>
       let res := fbs_values (fbs_expr clock') env id' l eff' in
         match res with
         | Result id'' (inl vl) eff'' => 
           match v with
           | VClos ref ext closid varl body =>
              if Nat.eqb (length varl) (length vl)
              then fbs_expr clock' (append_vars_to_env varl vl (get_env ref ext)) id'' body eff''
              else Result id'' (inr (badarity v)) eff''
           | _ => Result id'' (inr (badfun v)) eff''
           end
         | r => r
         end
     | Result id' (inl val) eff' => Failure
     | r => r
     end
   | ECase e l =>
     match fbs_expr clock' env id e eff with
     | Result id' (inl vals) eff' =>
       (fix clause_eval l :=
         match l with
         | [] => Result id' (inr if_clause) eff'
         | (pl, gg, bb)::xs =>
         (* TODO: side effects cannot be produced here *)
           if match_valuelist_to_patternlist vals pl
           then
             match fbs_expr clock' (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' gg eff' with
             | Result id'' (inl [v]) eff'' =>  
                 match v with
                 | VLit (Atom s) =>
                   if String.eqb s "true"%string then
                     if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
                     then fbs_expr clock' (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' bb eff'
                     else (* undef *) Failure
                   else if String.eqb s "false"%string 
                   then clause_eval xs
                   else Failure
                 | _ => Failure
                 end
             | _ => Failure
             end
           else clause_eval xs
        end
        ) l
     | r => r
     end
   | ELet l e1 e2 =>
      match fbs_expr clock' env id e1 eff with
      | Result id' (inl vals) eff' =>
        if Nat.eqb (length vals) (length l)
        then fbs_expr clock' (append_vars_to_env l vals env) id' e2 eff'
        else Failure
      | r => r
      end
   | ESeq e1 e2 =>
      match fbs_expr clock' env id e1 eff with
      | Result id' (inl [v]) eff' => fbs_expr clock' env id' e2 eff'
      | Result id' (inl vals) eff' => Failure
      | r => r
      end
   | ELetRec l e => fbs_expr clock' (append_funs_to_env l env id) (id + length l) e eff
   | EMap l =>
     let res := fbs_values (fbs_expr clock') env id (make_map_exps l) eff in
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
     match fbs_expr clock' env id e1 eff with
     | Result id' (inl vals) eff' =>
       if Nat.eqb (length vals) (length vl1)
       then fbs_expr clock' (append_vars_to_env vl1 vals env) id' e2 eff'
       else Failure
     | Result id' (inr ex) eff' =>
       fbs_expr clock' (append_try_vars_to_env vl2 [exclass_to_value (fst (fst ex)); snd (fst ex); snd ex] env) id' e3 eff'
     | r => r
     end
  end
end
.

Definition result_value (res : ResultType) : option Value :=
match res with
| Result _ (inl [val]) _ => Some val
| _ => None
end.

Theorem clock_list_increase :
forall {A:Type} {l env id eff id' res eff' clock} {f : nat -> Environment -> nat -> A -> SideEffectList -> ResultType},
(forall (env : Environment) (id : nat) (exp : A) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          f clock env id exp eff = Result id' res eff' ->
          f (S clock) env id exp eff = Result id' res eff') ->
  fbs_values (f clock) env id l eff = Result id' res eff'
->
  fbs_values (f (S clock)) env id l eff = Result id' res eff'.
Proof.
  induction l; intros.
  * simpl. inversion H0. subst. auto.
  * simpl in H0. case_eq (f clock env id a eff); intros. destruct res0.
    - rewrite H1 in H0. apply H in H1.
      remember (S clock) as cl. simpl. rewrite H1.
      rewrite Heqcl in *.
      case_eq (fbs_values (f clock) env id0 l eff0); intros.
      + pose (IHl _ _ _ _ _ _ _ _ H H2). rewrite e. rewrite H2 in H0. inversion H0. reflexivity.
      + rewrite H2 in H0. destruct v. congruence. destruct v0. congruence. congruence.
      + rewrite H2 in H0. destruct v. congruence. destruct v0. congruence. congruence.
    - rewrite H1 in H0. apply H in H1. inversion H0. subst.
      remember (S clock) as cl. simpl. rewrite H1. auto.
    - rewrite H1 in H0. congruence.
    - rewrite H1 in H0. congruence.
Qed.

Theorem bigger_clock_list :
  forall {A : Type} {clock env id exps eff id' res eff'} {f : nat -> Environment -> nat -> A -> SideEffectList -> ResultType} clock',
  clock <= clock' ->
  (forall (clock : nat) (env : Environment) (id : nat) (exp : A) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          f clock env id exp eff = Result id' res eff' ->
          f (S clock) env id exp eff = Result id' res eff') ->
  fbs_values (f clock) env id exps eff = Result id' res eff'
->
  fbs_values (f clock') env id exps eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption.
  * apply clock_list_increase. 2: auto. intros. auto.
Qed.

Lemma case_clock_increase :
forall {clock env l id' res eff' id0 eff0 vals},
(fix clause_eval l :=
         match l with
         | [] => Result id0 (inr if_clause) eff0
         | (pl, gg, bb)::xs =>
         (* TODO: side effects cannot be produced here *)
           if match_valuelist_to_patternlist vals pl
           then
             match fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 gg eff0 with
             | Result id'' (inl [v]) eff'' =>  
                 match v with
                 | VLit (Atom s) =>
                   if String.eqb s "true"%string then
                     if andb (Nat.eqb id'' id0) (list_eqb effect_eqb eff0 eff'')
                     then fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 bb eff0
                     else (* undef *) Failure
                   else if String.eqb s "false"%string 
                   then clause_eval xs
                   else Failure
                 | _ => Failure
                 end
             | _ => Failure
             end
           else clause_eval xs
        end
        ) l = Result id' res eff' ->
(forall (env : Environment) (id : nat) (exp : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          fbs_expr clock env id exp eff = Result id' res eff' ->
          fbs_expr (S clock) env id exp eff = Result id' res eff')
->
(fix clause_eval l :=
         match l with
         | [] => Result id0 (inr if_clause) eff0
         | (pl, gg, bb)::xs =>
         (* TODO: side effects cannot be produced here *)
           if match_valuelist_to_patternlist vals pl
           then
             match fbs_expr (S clock) (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 gg eff0 with
             | Result id'' (inl [v]) eff'' =>  
                 match v with
                 | VLit (Atom s) =>
                   if String.eqb s "true"%string then
                     if andb (Nat.eqb id'' id0) (list_eqb effect_eqb eff0 eff'')
                     then fbs_expr (S clock) (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 bb eff0
                     else (* undef *) Failure
                   else if String.eqb s "false"%string 
                   then clause_eval xs
                   else Failure
                 | _ => Failure
                 end
             | _ => Failure
             end
           else clause_eval xs
        end
        ) l = Result id' res eff'.
Proof.
  induction l; intros.
  * simpl in *. auto.
  * destruct a. destruct p. remember (S clock) as cl.
    simpl.
    destruct (match_valuelist_to_patternlist vals l0).
    - case_eq (fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals l0) env) id0 e0 eff0);
         intros; rewrite H1 in H.
     + apply H0 in H1; rewrite H1. destruct res0.
       ** destruct v. 2: destruct v0. 1, 3: congruence.
          destruct v; try congruence.
          destruct l1; try congruence.
          destruct (s =? "true")%string.
          -- destruct (((id =? id0) && list_eqb effect_eqb eff0 eff)%bool).
            ++ auto.
            ++ congruence.
          -- destruct (s =? "false")%string.
            ++ apply IHl; auto.
            ++ congruence.
       ** congruence.
     + congruence.
     + congruence.
   - apply IHl; auto.
Qed.

Theorem clock_increase_single :
forall {clock env id exp eff id' res eff'},
  fbs_single clock env id exp eff = Result id' res eff'
->
  fbs_single (S clock) env id exp eff = Result id' res eff'
with clock_increase_expr :
forall {clock env id exp eff id' res eff'},
  fbs_expr clock env id exp eff = Result id' res eff'
->
  fbs_expr (S clock) env id exp eff = Result id' res eff'.
Proof.
  {
  induction clock; intros.
  * simpl in H. inversion H.
  * simpl in H. destruct exp; intros.
    1-5: simpl; inversion H; reflexivity.
    - remember (S clock) as cl. simpl.
      rewrite Heqcl in *.
      case_eq (fbs_expr clock env id tl eff); intros.
      + rewrite H0 in H.
        apply clock_increase_expr in H0. rewrite H0.
        destruct res0.
        ** destruct v. 2: destruct v0. 1, 3: inversion H.
           case_eq (fbs_expr clock env id0 hd eff0); intros; rewrite H1 in H.
           -- apply clock_increase_expr in H1. rewrite H1. destruct res0.
             ++ destruct v0. inversion H. destruct v1. inversion H. auto. inversion H.
             ++ inversion H. auto.
           -- inversion H.
           -- inversion H.
        ** inversion H. auto.
      + rewrite H0 in H. inversion H.
      + rewrite H0 in H. inversion H.
    - case_eq (fbs_values (fbs_expr clock) env id l eff); intros.
      + rewrite H0 in H.
        apply clock_list_increase in H0. 2: auto. remember (S clock) as cl.
        simpl. rewrite H0. auto.
      + rewrite H0 in H. congruence.
      + rewrite H0 in H. congruence.
    - case_eq (fbs_values (fbs_expr clock) env id l eff); intros.
      + rewrite H0 in H.
        apply clock_list_increase in H0. 2: auto. remember (S clock) as cl.
        simpl. rewrite H0. auto.
      + rewrite H0 in H. congruence.
      + rewrite H0 in H. congruence.
    - case_eq (fbs_values (fbs_expr clock) env id l eff); intros.
      + rewrite H0 in H.
        apply clock_list_increase in H0. 2: auto. remember (S clock) as cl.
        simpl. rewrite H0. auto.
      + rewrite H0 in H. congruence.
      + rewrite H0 in H. congruence.
    - case_eq (fbs_expr clock env id exp eff); intros; rewrite H0 in H.
      + apply clock_increase_expr in H0. remember (S clock) as cl.
        simpl. rewrite H0. destruct res0.
        ** destruct v. 2: destruct v0. 1-3: inversion H.
           case_eq (fbs_values (fbs_expr clock) env id0 l eff0); intros; rewrite H1 in H.
           -- apply clock_list_increase in H1. 2: auto. rewrite <- Heqcl in H1. rewrite H1.
              destruct res0.
              ++ destruct v; inversion H; auto.
                 destruct (Datatypes.length vl =? Datatypes.length v0).
                 rewrite H.
                 apply clock_increase_expr in H. rewrite <- Heqcl in H. rewrite H.
                 auto. auto.
              ++ auto.
           -- congruence.
           -- congruence.
        ** inversion H. auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env id e eff); intros; rewrite H0 in H.
      + apply clock_increase_expr in H0. remember (S clock) as cl.
        simpl. rewrite H0. destruct res0.
        ** apply case_clock_increase in H. rewrite <- Heqcl in H.
           auto. auto.
        ** inversion H. auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env id e1 eff); intros; rewrite H0 in H.
      apply clock_increase_expr in H0. remember (S clock) as cl. simpl.
      rewrite H0. destruct res0.
      + destruct (Datatypes.length v =? Datatypes.length l).
        ** apply clock_increase_expr in H. rewrite <- Heqcl in H. auto.
        ** congruence.
      + auto.
      + congruence.
      + congruence.
    - case_eq (fbs_expr clock env id e1 eff); intros; rewrite H0 in H.
      apply clock_increase_expr in H0. remember (S clock) as cl. simpl. rewrite H0.
      destruct res0.
      + destruct v. 2: destruct v0. 1, 3: congruence. apply clock_increase_expr in H.
        rewrite <- Heqcl in H. auto.
      + auto.
      + congruence.
      + congruence.
    - apply clock_increase_expr in H. remember (S clock) as cl. simpl. auto.
    - case_eq (fbs_values (fbs_expr clock) env id (make_map_exps l) eff); intros; rewrite H0 in H.
      apply clock_list_increase in H0. 2: auto. remember (S clock) as cl. simpl.
      rewrite H0. destruct res0.
      ** auto.
      ** auto.
      ** congruence.
      ** congruence.
    - case_eq (fbs_expr clock env id e1 eff); intros; rewrite H0 in H.
      + apply clock_increase_expr in H0. remember (S clock) as cl. simpl. rewrite H0.
        destruct res0.
        ** destruct (Datatypes.length v =? Datatypes.length vl1). 2: congruence.
           apply clock_increase_expr in H. rewrite <- Heqcl in H. auto.
        ** apply clock_increase_expr in H. rewrite <- Heqcl in H. auto.
      + congruence.
      + congruence.
  }
  {
    induction clock.
    * intros. simpl in H. congruence.
    * intros. simpl in H. destruct exp.
      - apply clock_list_increase in H. remember (S clock) as cl. simpl. auto. auto.
      - apply clock_increase_single in H. remember (S clock) as cl. simpl. auto.
  }
Qed.

Theorem bigger_clock_expr :
  forall clock clock' env id exp eff id' res eff',
  clock <= clock' ->
  fbs_expr clock env id exp eff = Result id' res eff'
->
  fbs_expr clock' env id exp eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption. 
  * apply clock_increase_expr. auto.
Qed.

Theorem bigger_clock_single :
  forall clock clock' env id exp eff id' res eff',
  clock <= clock' ->
  fbs_single clock env id exp eff = Result id' res eff'
->
  fbs_single clock' env id exp eff = Result id' res eff'.
Proof.
  intros. induction H.
  * assumption.
  * apply clock_increase_single. auto.
Qed.

Lemma bigger_clock_case :
forall {clock env l id' res eff' id0 eff0 vals} clock',
(fix clause_eval l :=
         match l with
         | [] => Result id0 (inr if_clause) eff0
         | (pl, gg, bb)::xs =>
         (* TODO: side effects cannot be produced here *)
           if match_valuelist_to_patternlist vals pl
           then
             match fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 gg eff0 with
             | Result id'' (inl [v]) eff'' =>  
                 match v with
                 | VLit (Atom s) =>
                   if String.eqb s "true"%string then
                     if andb (Nat.eqb id'' id0) (list_eqb effect_eqb eff0 eff'')
                     then fbs_expr clock (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 bb eff0
                     else (* undef *) Failure
                   else if String.eqb s "false"%string 
                   then clause_eval xs
                   else Failure
                 | _ => Failure
                 end
             | _ => Failure
             end
           else clause_eval xs
        end
        ) l = Result id' res eff' ->
clock <= clock'
->
(fix clause_eval l :=
         match l with
         | [] => Result id0 (inr if_clause) eff0
         | (pl, gg, bb)::xs =>
         (* TODO: side effects cannot be produced here *)
           if match_valuelist_to_patternlist vals pl
           then
             match fbs_expr clock' (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 gg eff0 with
             | Result id'' (inl [v]) eff'' =>  
                 match v with
                 | VLit (Atom s) =>
                   if String.eqb s "true"%string then
                     if andb (Nat.eqb id'' id0) (list_eqb effect_eqb eff0 eff'')
                     then fbs_expr clock' (add_bindings (match_valuelist_bind_patternlist vals pl) env) id0 bb eff0
                     else (* undef *) Failure
                   else if String.eqb s "false"%string 
                   then clause_eval xs
                   else Failure
                 | _ => Failure
                 end
             | _ => Failure
             end
           else clause_eval xs
        end
        ) l = Result id' res eff'.
Proof.
  intros. induction H0.
  * assumption.
  * apply case_clock_increase. auto. intros. apply clock_increase_expr. auto.
Qed.

End Functional_Big_Step.