Require Core_Erlang_Auxiliaries.

Module Functional_Big_Step.


Export Core_Erlang_Auxiliaries.Auxiliaries.
Export Core_Erlang_Environment.Environment.

Import ListNotations.

Inductive ResultType : Type :=
| Result (id : nat) (res : ValueSequence + Exception) (eff : SideEffectList)
| Timeout
| Failure.

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
          | Result _ (inl _) _ => Failure (* undefined behaviour *)
          | r => r
          end
end.

Fixpoint fbs_case (l : list (list Pattern * Expression * Expression)) (env : Environment) (id' : nat) (eff' : SideEffectList) (vals : ValueSequence) (f : Environment -> nat -> Expression -> SideEffectList -> ResultType) : ResultType :=
match l with
| [] => Result id' (inr if_clause) eff'
| (pl, gg, bb)::xs =>
(* TODO: side effects cannot be produced here *)
 if match_valuelist_to_patternlist vals pl
 then
   match f (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' gg eff' with
   | Result id'' (inl [v]) eff'' =>  
     if andb (Nat.eqb id'' id') (list_eqb effect_eqb eff' eff'')
     then
       match v with
       | VLit (Atom s) =>
         if String.eqb s "true"%string then
           f (add_bindings (match_valuelist_bind_patternlist vals pl) env) id' bb eff'
         else if String.eqb s "false"%string 
              then fbs_case xs env id' eff' vals f
              else Failure
       | _ => Failure
       end
     else Failure
   | _ => Failure
   end
 else fbs_case xs env id' eff' vals f
end.

Fixpoint fbs_expr (clock : nat) (env : Environment) (id : nat) (expr : Expression) (eff : SideEffectList) {struct clock} : ResultType :=
match clock with
| 0 => Timeout
| S clock' =>
  match expr with
   | EValues el => fbs_values (fbs_expr clock') env id el eff
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
                 | None => Failure
                 end
   | EFun vl e => Result (S id) (inl [VClos env [] id vl e]) eff
   | ECons hd tl => 
     match fbs_expr clock' env id tl eff with
       | Result id' (inl [tlv]) eff' =>
         match fbs_expr clock' env id' hd eff' with
         | Result id'' (inl [hdv]) eff'' => Result id'' (inl [VCons hdv tlv]) eff''
         | Result _ (inl _) _ => Failure (* undefined behaviour *)
         | r => r
         end
       | Result _ (inl _) _ => Failure (* undefined behaviour *)
       | r => r
     end
   | ETuple l =>
     let res := fbs_values (fbs_expr clock') env id l eff in
       match res with
       | Result id' (inl vl) eff' => Result id' (inl [VTuple vl]) eff'
       | r => r
       end
   | ECall m f l => 
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
     | Result _ (inl _) _ => Failure
     | r => r
     end
   | ECase e l =>
     match fbs_expr clock' env id e eff with
     | Result id' (inl vals) eff' =>
        fbs_case l env id' eff' vals (fbs_expr clock')
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
      | Result _ (inl _) _ => Failure
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
  * simpl in H0. break_match_singleton.
    - apply H in Heqr.
      remember (S clock) as cl. simpl. rewrite Heqr.
      rewrite Heqcl in *.
      break_match_list.
      + pose (IHl _ _ _ _ _ _ _ _ H Heqr0). rewrite e. auto.
      + apply IHl in Heqr0. rewrite Heqr0. auto. intros. apply H. auto.
    - apply H in Heqr. inversion H0. subst.
      remember (S clock) as cl. simpl. rewrite Heqr. auto.
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
fbs_case l env id0 eff0 vals (fbs_expr clock) = Result id' res eff' ->
(forall (env : Environment) (id : nat) (exp : Expression) 
            (eff : SideEffectList) (id' : nat) (res : ValueSequence + Exception)
            (eff' : SideEffectList),
          fbs_expr clock env id exp eff = Result id' res eff' ->
          fbs_expr (S clock) env id exp eff = Result id' res eff')
->
fbs_case l env id0 eff0 vals (fbs_expr (S clock)) = Result id' res eff'.
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

(* Theorem clock_increase_single :
forall {clock env id exp eff id' res eff'},
  fbs_single clock env id exp eff = Result id' res eff'
->
  fbs_single (S clock) env id exp eff = Result id' res eff' *)
Theorem clock_increase_expr :
forall {clock env id exp eff id' res eff'},
  fbs_expr clock env id exp eff = Result id' res eff'
->
  fbs_expr (S clock) env id exp eff = Result id' res eff'.
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
    - break_match_list.
      + apply clock_list_increase in Heqr. 2: auto. remember (S clock) as cl.
        simpl. rewrite Heqr. auto.
      + apply clock_list_increase in Heqr. 2: auto. remember (S clock) as cl.
        simpl. rewrite Heqr. auto.
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
  forall {clock env id exp eff id' res eff'} clock',
  clock <= clock' ->
  fbs_expr clock env id exp eff = Result id' res eff'
->
  fbs_expr clock' env id exp eff = Result id' res eff'.
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
forall {clock env l id' res eff' id0 eff0 vals} clock',
fbs_case l env id0 eff0 vals (fbs_expr clock) = Result id' res eff' ->
clock <= clock'
->
fbs_case l env id0 eff0 vals (fbs_expr clock') = Result id' res eff'.
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