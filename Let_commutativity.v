Load Core_Erlang_Proofs.

Import Core_Erlang_Syntax.
Import Core_Erlang_Semantics.
Import Core_Erlang_Environment.
Import Core_Erlang_Closures.
Import Core_Erlang_Helpers.
Import Core_Erlang_Induction.
Import Core_Erlang_Proofs.
Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.
Import Coq.Init.Logic.
Import Omega.


(* Additional hypotheses needed: see details at the admit statements *)
(* It would be sufficient the X and Y are new (fresh) variables *)
Example let_2_comm (e1 e2 : Expression) (t : Value) :
  ([], [], ELet ["X"%string] [e1] (ELet ["Y"%string] [e2] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))) -e> t
<->
([], [], ELet ["X"%string] [e2] (ELet ["Y"%string] [e1] (ECall "plus"%string [EVar "X"%string ; EVar "Y"%string]))) -e> t
.
Proof.
  split; intros.
  * inversion H. subst. simpl in H6. pose (element_exist Value 0 vals H6). inversion e. inversion H0. subst. inversion H6. apply length_zero_iff_nil in H2. subst. assert (([], [], e1) -e> x).
    {
      apply H7. simpl. auto.
    }
    inversion H8. subst. simpl in H11. pose (element_exist Value 0 vals H11). inversion e0. inversion H2. subst. inversion H11. apply length_zero_iff_nil in H4. subst. assert (
    (match x with
       | VClosure _ varl body =>
           [(inl "X"%string, VClosure (inl "X"%string) varl body)]
       | _ => [(inl "X"%string, x)]
       end, 
    match x with
      | VClosure _ _ _ => [(inl "X"%string, [])]
      | _ => []
      end,
        e2) -e> x0). { apply H12. simpl. auto. }
   
   (*proving starts*)
   apply eval_let with (vals := [x0]).
   - reflexivity.
   - intros. inversion H4. 
     + inversion H5. subst. admit. (*hypo needed: ([],[],e2)-e>x0*) 
     + inversion H5.
   - apply eval_let with (vals := [x]).
     + reflexivity.
     + intros. inversion H4.
       ** inversion H5. subst. admit. (*hypo needed: ((append_vars_to_env ["X"%string] [x0] [],
append_vars_to_closure ["X"%string] [x0] [] [], e1) -e> x)*)
       ** inversion H5.
     + (* call information *)
       inversion H13. subst. simpl in H15. pose (element_exist Value 1 vals (eq_sym H15)). inversion e3. inversion H4. subst. inversion H15. pose (element_exist Value 0 x2 (eq_sym H9)). inversion e4. inversion H5. subst. inversion H9. apply eq_sym, length_zero_iff_nil in H14. subst.
       
       destruct x, x0.
       
       (* BOILER PLATE -> importants are logically enough*)
       (*IMPORTANT*)** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
       
         apply eval_call with (vals := [VLiteral l0; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl get_value. apply plus_comm_basic.
       (*IMPORTANT*)** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [VClosure (inl "X"%string) vl e5; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
         apply eval_call with (vals := [VList x0_1 x0_2; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
         apply eval_call with (vals := [VTuple vl; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
         apply eval_call with (vals := [VMap kl vl; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       (*IMPORTANT*) ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [VLiteral l; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       (*IMPORTANT*) ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e7. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e8. simpl in H21. subst.
         apply eval_call with (vals := [VClosure (inl "X"%string) vl0 e6; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
         
      (*BOILER PLATE FROM NOW ON*)
        ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [ VList x0_1 x0_2; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [ VTuple vl0; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [ VMap kl vl0; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VLiteral l ; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
          apply eval_call with (vals := [ VClosure (inl "X"%string) vl e5; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VList x0_1 x0_2; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VTuple vl ; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VMap kl vl ; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
        ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VLiteral l ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
          apply eval_call with (vals := [ VClosure (inl "X"%string) vl0 e5 ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VList x0_1 x0_2 ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VTuple vl0 ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VMap kl vl0; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VLiteral l; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
          apply eval_call with (vals := [ VClosure (inl "X"%string) vl0 e5; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VList x0_1 x0_2; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VTuple vl0; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VMap kl0 vl0; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.


  * inversion H. subst. simpl in H6. pose (element_exist Value 0 vals H6). inversion e. inversion H0. subst. inversion H6. apply length_zero_iff_nil in H2. subst. assert (([], [], e2) -e> x).
    {
      apply H7. simpl. auto.
    }
    inversion H8. subst. simpl in H11. pose (element_exist Value 0 vals H11). inversion e0. inversion H2. subst. inversion H11. apply length_zero_iff_nil in H4. subst. assert (
    (match x with
       | VClosure _ varl body =>
           [(inl "X"%string, VClosure (inl "X"%string) varl body)]
       | _ => [(inl "X"%string, x)]
       end, 
    match x with
      | VClosure _ _ _ => [(inl "X"%string, [])]
      | _ => []
      end,
        e1) -e> x0). { apply H12. simpl. auto. }
   
   (*proving starts*)
   apply eval_let with (vals := [x0]).
   - reflexivity.
   - intros. inversion H4. 
     + inversion H5. subst. admit. (*hypo needed: ([],[],e2)-e>x0*) 
     + inversion H5.
   - apply eval_let with (vals := [x]).
     + reflexivity.
     + intros. inversion H4.
       ** inversion H5. subst. admit. (*hypo needed: ((append_vars_to_env ["X"%string] [x0] [],
append_vars_to_closure ["X"%string] [x0] [] [], e1) -e> x)*)
       ** inversion H5.
     + (* call information *)
       inversion H13. subst. simpl in H15. pose (element_exist Value 1 vals (eq_sym H15)). inversion e3. inversion H4. subst. inversion H15. pose (element_exist Value 0 x2 (eq_sym H9)). inversion e4. inversion H5. subst. inversion H9. apply eq_sym, length_zero_iff_nil in H14. subst.
       
       destruct x, x0.
       
       (* BOILER PLATE -> importants are logically enough*)
       (*IMPORTANT*)** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
       
         apply eval_call with (vals := [VLiteral l0; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl get_value. apply plus_comm_basic.
       (*IMPORTANT*)** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [VClosure (inl "X"%string) vl e5; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
         apply eval_call with (vals := [VList x0_1 x0_2; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
         apply eval_call with (vals := [VTuple vl; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
         apply eval_call with (vals := [VMap kl vl; VLiteral l]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       (*IMPORTANT*) ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [VLiteral l; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       (*IMPORTANT*) ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e7. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e8. simpl in H21. subst.
         apply eval_call with (vals := [VClosure (inl "X"%string) vl0 e6; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
         
      (*BOILER PLATE FROM NOW ON*)
        ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [ VList x0_1 x0_2; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [ VTuple vl0; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
         apply eval_call with (vals := [ VMap kl vl0; VClosure (inl "Y"%string) vl e5]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VLiteral l ; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
          apply eval_call with (vals := [ VClosure (inl "X"%string) vl e5; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VList x0_1 x0_2; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VTuple vl ; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VMap kl vl ; VList x2 x4]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
        ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VLiteral l ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
          apply eval_call with (vals := [ VClosure (inl "X"%string) vl0 e5 ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VList x0_1 x0_2 ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VTuple vl0 ; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VMap kl vl0; VTuple vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VLiteral l; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. destruct l; reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e6. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e7. simpl in H21. subst.
          apply eval_call with (vals := [ VClosure (inl "X"%string) vl0 e5; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VList x0_1 x0_2; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VTuple vl0; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.
       ** assert (In ((EVar "X"%string), x1) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "X"%string) x1 H10). inversion e5. simpl in H14.
          assert (In ((EVar "Y"%string), x3) (combine [EVar "X"%string; EVar "Y"%string] [x1; x3])). simpl. auto. pose (H16 (EVar "Y"%string) x3 H20). inversion e6. simpl in H21. subst.
          apply eval_call with (vals := [ VMap kl0 vl0; VMap kl vl]).
         -- reflexivity.
         -- intros. inversion H14; inversion H17.
           ++ simpl. apply eval_var.
           ++ inversion H18. apply eval_var.
           ++ inversion H18.
         -- simpl. reflexivity.

Admitted.