
From CoreErlang.FrameStack Require SubstSemantics
CIU SubstSemanticsAutoSolver.
From CoreErlang.FrameStack Require Import Examples.

Open Scope string_scope.

Import FrameStack.SubstSemantics FrameStack.CIU. 
Import FrameStack.SubstSemanticsAutoSolver.

Import ListNotations.

(*Function formalizations*)

(*Identity Function *)
Definition id_fun (e : Exp) : Exp :=
    °ELet
    1
    (°EFun 1 (˝VVar 0))    
    (°EApp (˝VVar 0) [e]).  

(*Constant Function*)
Definition const_fun (e : Exp) : Exp :=
    °ELet
    1
    (°EFun 1 (˝VLit (Atom "ok"%string)))   
    (°EApp (˝VVar 0) [e]).

(*Primitive Addition*)
Definition add_primitive (x y : Exp) : Exp :=
°ECall (˝VLit (Atom "erlang"%string))
      (˝VLit (Atom "+"%string))
      [x; y].

(*Tuple Construction*)
Definition make_tuple (xs : list Exp) : Exp :=
°ETuple xs.

(*List Construction*)
Definition make_list (xs : list Exp) : Exp :=
fold_right (fun x acc => °ECons x acc) (˝VLit (Atom "nil"%string)) xs.

(*Map Construction*)
Definition make_map (pairs : list (Exp * Exp)) : Exp :=
°EMap pairs.

(*Let Binding *)
Definition let_binding (rhs body : Exp) : Exp :=
°ELet 1 rhs body.

(*Case Expression*)
Definition case_expr (scrut : Exp) (branches : list (list Pat * Exp * Exp)) : Exp :=
°ECase scrut branches.

(*Try / Catch*)
Definition try_example (expr handler : Exp) : Exp :=
°ETry expr 0 (˝VLit (Atom "ok"%string)) 3 handler.

(** lists:member/2 - Check if element is in list 
    member(Elem, List) -> 
    case List of
        [H|T] when H =:= Elem -> true;
        [_|T] -> member(Elem, T);
        []    -> false
    end.
*)
Definition member (elem lst : Exp) : Exp :=
   ELetRec [(2, 
     °ECase (˝VVar 2)  (* match on List parameter *)
       [([PCons PVar PVar],  (* [H|T] H = 0, T= 1,fun = 2, elem =3,List =4 *)  
         °ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0; ˝VVar 3],  (* H =:= Elem *)
         ˝VLit "true");
        ([PCons PVar PVar],  (* [_|T] _ = 0, T= 1,fun = 2, elem =3,List =4 *)  
         ˝ttrue,
         °EApp (˝VFunId (2, 2)) [˝VVar 3; ˝VVar 1]);  (* member(Elem, T) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VLit "false")])]
   (EApp (˝VFunId (0, 2)) [elem; lst]).

 (** lists:reverse/2 - Reverse with accumulator 
     reverse(List, Acc) ->
       case List of
         [H|T] -> reverse(T, [H|Acc]);
         []    -> Acc
       end.
 *)
Definition reverse (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar],  (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °EApp (˝VFunId (2, 2)) [˝VVar 1; °ECons (˝VVar 0) (˝VVar 4)]);  (* reverse(T, [H|Acc]) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).

 (** lists:reverse/1 - Reverse a list *)
Definition reverse1 (lst : Exp) : Exp :=
   reverse lst (˝VNil).

 (** lists:sum/2 - Sum with accumulator
     sum(List, Acc) ->
       case List of
         [H|T] -> sum(T, H + Acc);
         []    -> Acc
       end.
 *)
Definition sum (lst acc : Exp) : Exp :=
   ELetRec [(2,
     °ECase (˝VVar 1)  (* match on List parameter *)
       [([PCons PVar PVar], (* [H|T] H = 0, T= 1,fun = 2, List =3, Acc =4 *)  
         ˝ttrue,
         °ELet 1 (ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0; ˝VVar 4])  (* NewAcc = 0 H = 1, T= 2,fun = 3, List =4, Acc =5 *)
           (EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 0]));  (* sum(T, NewAcc) *)
        ([PNil],  (* [] *)
         ˝ttrue,
         ˝VVar 2)])]  (* return Acc *)
   (EApp (˝VFunId (0, 2)) [lst; acc]).

 (** lists:sum/1 - Sum a list *)
Definition sum1 (lst : Exp) : Exp :=
   sum lst (˝VLit 0%Z).

 (** lists:append/2 - Concatenate two lists *)
Definition append (lst1 lst2 : Exp) : Exp :=
   °ECall (˝VLit "erlang") (˝VLit "++") [lst1; lst2].

 (** lists:nth/2 - Get nth element (1-indexed)
     nth(1, [H|_]) -> H;
     nth(N, [_|T]) when N > 1 -> nth(N-1, T).
 *)
Definition nth (n lst : Exp) : Exp :=
   ELetRec [(2,  (* fun = 0 , n = 1, lst = 2 **)
     °ECase (˝VVar 1)  (* match on N parameter *)
       [([PLit (Integer 1)],  (* N = 1 *)
         ˝ttrue,
         °ECase (˝VVar 2) [ (* fun = 0 , n = 1, lst = 2 **)
           ([PCons PVar PVar], ˝ttrue, ˝VVar 0)]);  (* return H,  H=0, T=1 fun = 2 , n = 3, lst = 4 *)
        ([PVar],  (* Var = 0 fun = 1 , n = 2, lst = 3 **)
         °ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit 1%Z],  (* N > 1 *)
         °ECase (˝VVar 3) [  (* match on List *)
           ([PCons PVar PVar],  (* [H|T] H = 0, T=1  Var = 2 fun = 3 , n = 4, lst = 5*)
            ˝ttrue,
            °ELet 1 (ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 4; ˝VLit 1%Z])  (* NewN = N - 1 *)
              (EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2]))])])]  (* nth(NewN, T) *)
   (EApp (˝VFunId (0, 2)) [n; lst]).

   (*Tests**)

(*id test*)
Goal ⟨[], id_fun (˝VLit 42%Z)⟩ -->* RValSeq [VLit 42%Z].
Proof.
 auto_proove_subst_semantics.
Qed.

(*constant function test*)
Goal ⟨[], const_fun (˝VLit 42%Z)⟩ -->* RValSeq [VLit (Atom "ok")].
Proof.
 auto_proove_subst_semantics.
Qed.

(*constant equivalency test*)
Theorem const_equiv :
CIU (const_fun (˝VLit 42%Z)) (const_fun (˝VLit 62%Z)).
Proof.
 pose proof (CIU_eval (const_fun (˝VLit 42%Z)) (RValSeq [VLit (Atom "ok")])).
 pose proof (CIU_eval (const_fun (˝VLit 62%Z)) (RValSeq [VLit (Atom "ok")])).
 destruct H.
 scope_solver.
 auto_proove_subst_semantics.
 destruct H0.
 scope_solver.
 auto_proove_subst_semantics.
 apply (CIU_transitive_closed (const_fun (˝VLit 42%Z)) (RValSeq [VLit (Atom "ok")]) (const_fun (˝VLit 62%Z)));assumption.
Qed. 

(*Addition test*)
Goal ⟨[], add_primitive (˝VLit 1%Z) (˝VLit 2%Z)⟩ -->* RValSeq [VLit 3%Z].
Proof.
 auto_proove_subst_semantics.
Qed.

(*Tuple test*)
Goal ⟨[], make_tuple [˝VLit 1%Z; ˝VLit (Atom "x"%string)]⟩ -->* RValSeq [VTuple [VLit 1%Z; VLit (Atom "x")]].
Proof.
 auto_proove_subst_semantics.
Qed.

(*List test*)
Goal ⟨[], make_list [˝VLit 1%Z; ˝VLit 2%Z]⟩ -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VLit (Atom "nil")))].
Proof.
 auto_proove_subst_semantics.
Qed.

(*Map test*)
Goal ⟨[], make_map [(˝VLit (Atom "a"%string), ˝VLit 1%Z)]⟩ -->* RValSeq [VMap [(VLit (Atom "a"), VLit 1%Z)]].
Proof.
auto_proove_subst_semantics.
Qed.

(*Let test*)
Goal ⟨[], let_binding (add_primitive (˝VLit 5%Z) (˝VLit 7%Z)) (˝VVar 0)⟩ -->* RValSeq [VLit 12%Z].
Proof.
auto_proove_subst_semantics.
Qed.

(*Case test*)
Goal ⟨[], case_expr (˝VLit 1%Z)
    [([PLit (Integer 0)], ˝ttrue, ˝VLit (Atom "zero"%string));
     ([PLit (Integer 1)], ˝ttrue, ˝VLit (Atom "one"%string))]⟩
-->* RValSeq [VLit (Atom "one")].
Proof.
 auto_proove_subst_semantics.
Qed.

(* try/catch tests*)
Goal ⟨[], try_example
(°ECall (˝VLit (Atom "erlang"%string))
     (˝VLit (Atom "error"%string))
     [˝VLit (Atom "oops"%string)])
(°ETuple [˝VLit (Atom "caught"%string); ˝VVar 1])⟩
-->* RValSeq [VTuple [VLit (Atom "caught"%string); VLit (Atom "oops"%string)]].
Proof.
 auto_proove_subst_semantics.
Qed.

Goal ⟨[], °ETry 
(°ECall (˝VLit (Atom "erlang"%string))
       (˝VLit (Atom "+"%string))
       [˝VLit 5%Z; ˝VLit 3%Z])
1       (* bind 1 value on success *)
(˝VVar 0) (* return that value *)
3        (* bind 3 values on exception (class, reason, details) *)
(°ETuple [˝VLit (Atom "error"%string); ˝VVar 1])⟩
-->* RValSeq [VLit 8%Z].
Proof.
 auto_proove_subst_semantics.
Qed.

Goal ⟨[], °ETry
(˝VLit (Atom "success"%string))
1
(˝VVar 0)
3
(°ETuple [˝VLit (Atom "caught"%string); ˝VVar 1])⟩
-->* RValSeq [VLit (Atom "success"%string)].
Proof.
 auto_proove_subst_semantics.
Qed.

(** Test member - element found *)
 Goal ⟨[], member (˝VLit 2%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
   -->* RValSeq [VLit "true"].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test member - element not found *)
 Goal ⟨[], member (˝VLit 5%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))⟩
   -->* RValSeq [VLit "false"].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test reverse/1 wrapper *)
 Goal ⟨[], reverse1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
   -->* RValSeq [VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) VNil))].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test sum/1 wrapper *)
 Goal ⟨[], sum1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
   -->* RValSeq [VLit 6%Z].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test reverse empty list *)
 Goal ⟨[], reverse1 (˝VNil)⟩ -->* RValSeq [VNil].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test sum empty list *)
 Goal ⟨[], sum1 (˝VNil)⟩ -->* RValSeq [VLit 0%Z].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test append *)
 Goal ⟨[], append (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))
                   (˝VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil)))].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test nth - get first element *)
 Goal ⟨[], nth (˝VLit 1%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") VNil)))⟩
   -->* RValSeq [VLit "a"].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (** Test nth - get second element *)
 Goal ⟨[], nth (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") VNil)))⟩
   -->* RValSeq [VLit "b"].
 Proof.
   auto_proove_subst_semantics.
 Qed.


 (** Test member - element not found *)
 Goal ⟨[], member (˝VLit 5%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))⟩
   -->* RValSeq [VLit "false"].
 Proof.
   auto_proove_subst_semantics.
 Qed.

 (*Generated functions and tests*)
 Require Import Coq.Lists.List.
Import ListNotations.

Definition all_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Pred=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ttrue);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        ˝ffalse);
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition any_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Pred=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        ˝ttrue);
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition member_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Elem=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 2; ˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        ˝ttrue);
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]))]));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition search_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Pred=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ETuple [˝VLit "value";˝VVar 0]));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition append_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([(PCons PVar PVar)],  (* H=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 1; ˝VVar 0]))));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition append_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 1; ˝VVar 2])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

   Definition concat_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ELetRec [(1, ((°ECase (˝VLit "_5") 
      [([(PCons PVar PVar)],  (* Sub=0, _2=1 *) 
        ˝ttrue, 
        (°ELetRec [(1, ((°ECase (˝VLit "_7") 
      [([(PCons PVar PVar)],  (* X=0, _4=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _3=0, _4=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 1)) [˝VVar 2]));
      ([PVar],  (* _8=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 1]))));
      ([(PCons PVar PVar)],  (* _1=0, _2=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _6=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 2])))))]
   (°EApp (˝VFunId (0, 1)) [_0]).

   Definition uniq_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* _6=0 *) 
      ˝ttrue, 
      ˝VNil)]));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Seen=0 *) 
      ˝ttrue, 
      (°ECase ((member_2 (˝VVar 1) (˝VVar 0))) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (0, 2)) [˝VVar 2; ˝VVar 0]));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (0, 2)) [˝VVar 2; (°ECons (˝VVar 1) (˝VVar 0))])) ((°ECons (˝VVar 2) (˝VVar 0)))));
      ([PVar],  (* _3=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]). 


   (*TODO This causes problem:
   
   case <> of
		    <>
			when call 'erlang':'=:='
			      (Item,
			       H) ->
			T
		    %% Line 85
		    <> when 'true' ->
			let <_2> =
			    apply 'delete'/2
				(Item, T)
			in  [H|_2]
		  end

   *)
   Definition delete_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Item=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      ˝VVar 1);
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition droplast_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([(PCons PVar PNil)],  (* _3=0 *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* H=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition dropwhile_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Pred=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([PVar], (*  *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 0) [˝VLit "H"])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (1, 2)) [˝VVar 0; ˝VLit "T"]));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        ˝VLit "List");
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition duplicate_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 0%Z))], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* _6=0 *) 
      ˝ttrue, 
      ˝VNil)]));
      ([PVar], (* N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* X=0 *) 
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 1; ˝VLit (Integer 0%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 1; ˝VLit (Integer 1%Z)])) ((°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 0; ˝VVar 1])) ((°ECons (˝VVar 2) (˝VVar 0)))))))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition enumerate_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_I=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2])) ((°ECons ((°ETuple [˝VVar 4;˝VVar 2])) (˝VVar 0)))))));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).


Definition enumerate_1 (_0 : Exp) : Exp := 
  enumerate_2 (˝VLit (Integer 1%Z)) (_0).


Definition filter_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Pred=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],  (* _3=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition filtermap_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PTuple [(PLit (Atom "true"));PVar])],  (* Val=0 *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],  (* _4=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition zf_2 (_0 _1 : Exp) : Exp := 
   filtermap_2 (_0) (_1).


Definition flatlength_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Acc=0 *) 
      (°ECall (˝VLit "erlang") (˝VLit (Atom "is_list")) [˝VVar 1]), 
      (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 1; ˝VVar 0])) ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 0]))))]));
      ([(PCons PVar PVar)], (* _6=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0; ˝VLit (Integer 1%Z)])) ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 0]))))]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition flatlength_1 (_0 : Exp) : Exp := 
   flatlength_2 (_0) (˝VLit (Integer 0%Z)).

   
Definition flatmap_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ELetRec [(1, ((°ECase (˝VLit "_7") 
      [([(PCons PVar PVar)],  (* X=0, _3=1 *) 
        ˝ttrue, 
        (°ELetRec [(1, ((°ECase (˝VLit "_9") 
      [([(PCons PVar PVar)],  (* Y=0, _5=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _4=0, _5=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 1)) [˝VVar 2]));
      ([PVar],  (* _10=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°ELet 1 ((°EApp (˝VVar 5) [˝VVar 1])) ((°EApp (˝VFunId (1, 1)) [˝VVar 0]))))));
      ([(PCons PVar PVar)],  (* _2=0, _3=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _8=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 3])))))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).



Definition flatten_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* Tail=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Tail=0 *) 
      (°ECall (˝VLit "erlang") (˝VLit "is_list") [˝VVar 1]), 
      (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 0])) ((°EApp (˝VFunId (4, 2)) [˝VVar 2; ˝VVar 0]))))]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition flatten_1 (_0 : Exp) : Exp := 
   flatten_2 (_0) (˝VNil).

Definition join_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Sep=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([PCons PVar PNil], (*  *) 
      ˝ttrue, 
      °ECons (˝VVar 0) (˝VNil));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) ((°ECons (˝VVar 3) (˝VVar 0)))))));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition last_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([(PCons PVar PNil)],  (* Last=0 *) 
        ˝ttrue, 
        ˝VVar 0);
      ([(PCons PVar PVar)],  (* _2=0, T=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],  (* _1=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition nth_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 1%Z))], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([(PCons PVar PVar)], (* H=0, _5=1 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)], (* _6=0, T=1 *) 
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 1%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2]))));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition nthtail_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 0%Z))], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* List=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)], (* _5=0, T=1 *) 
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 0%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2]))));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition partition_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_12") 
      [([(PCons PVar PVar)],  (* X=0, _11=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VVar 4) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],  (* _15=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "bad_filter";˝VVar 0])]))]));
      ([(PCons PVar PVar)],  (* _10=0, _11=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _13=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 3])))) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_5") 
      [([(PCons PVar PVar)],  (* Y=0, _3=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VVar 5) [˝VVar 0])) 
      [([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],  (* _cor_variable=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [˝VLit "badarg"]))]));
      ([(PCons PVar PVar)],  (* _2=0, _3=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _6=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))) ((°ETuple [˝VVar 1;˝VVar 0])))))))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition prefix_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* _4=0 *) 
      ˝ttrue, 
      ˝ttrue)]));
      ([(PCons PVar PVar)], (* H=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* _5=0, T2=1 *) 
      (°ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0; ˝VVar 2]), 
      (°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 1]))]));
      ([PVar], (* _6=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _7=0 *) 
      ˝ttrue, 
      ˝ffalse)]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition reverse_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      (°EApp (˝VFunId (3, 2)) [˝VVar 2; (°ECons (˝VVar 1) (˝VVar 0))]))]));
      ([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _2=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition reverse_1 (_0 : Exp) : Exp := 
   reverse_2 (_0) (˝VNil).

Definition split_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 0%Z))], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* List=0 *) 
      ˝ttrue, 
      (°ETuple [˝VNil;˝VVar 0]))]));
      ([PVar], (* N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)], (* H=0, T=1 *) 
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 0%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°ECase ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2])) 
      [([(PTuple [PVar;PVar])],  (* L1=0, L2=1 *) 
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 3) (˝VVar 0));˝VVar 1]));
      ([PVar],  (* _3=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]))));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition sublist_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* _9=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _10=0 *) 
      ˝ttrue, 
      ˝VNil)]))]));
      ([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PLit (Integer 0%Z))], (*  *) 
      ˝ttrue, 
      ˝VNil)]))]));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PLit (Integer 1%Z))], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar], (* Len=0 *) 
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VLit (Integer 1%Z)])) ((°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 3; ˝VLit (Integer 1%Z); ˝VVar 0])) ((°ECons (˝VVar 3) (˝VVar 0)))))))]))]));
      ([(PCons PVar PVar)], (* _13=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Start=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 6) 
      [([PVar], (* Len=0 *) 
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 1; ˝VLit (Integer 1%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 1; ˝VLit (Integer 1%Z)])) ((°EApp (˝VFunId (5, 3)) [˝VVar 4; ˝VVar 0; ˝VVar 1]))))]))]));
      ([PVar], (* _8=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _7=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar], (* _6=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 2;˝VVar 1;˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition sublist_2 (_0 _1 : Exp) : Exp := 
   sublist_3 (_0) (˝VLit (Integer 1%Z)) (_1).

Definition sum_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0; ˝VVar 1])) ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 0]))))]));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition sum_1 (_0 : Exp) : Exp := 
   sum_2 (_0) (˝VLit (Integer 0%Z)).   

Definition takewhile_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Pred=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _3=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition unzip_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        (°ETuple [˝VNil;˝VNil]));
      ([(PCons (PTuple [PVar;PVar]) PVar)],  (* A=0, B=1, T=2 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (3, 1)) [˝VVar 2])) 
      [([(PTuple [PVar;PVar])],  (* La=0, Lb=1 *) 
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 2) (˝VVar 0));(°ECons (˝VVar 3) (˝VVar 1))]));
      ([PVar],  (* _1=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition unzip3_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        (°ETuple [˝VNil;˝VNil;˝VNil]));
      ([(PCons (PTuple [PVar;PVar;PVar]) PVar)],  (* A=0, B=1, C=2, T=3 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (4, 1)) [˝VVar 3])) 
      [([(PTuple [PVar;PVar;PVar])],  (* La=0, Lb=1, Lc=2 *) 
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 3) (˝VVar 0));(°ECons (˝VVar 4) (˝VVar 1));(°ECons (˝VVar 5) (˝VVar 2))]));
      ([PVar],  (* _1=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PVar],  (* _2=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition zip_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil)]));
      ([(PCons PVar PVar)], (* A=0, As=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* B=0, Bs=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 1])) ((°ECons ((°ETuple [˝VVar 3;˝VVar 1])) (˝VVar 0)))))]));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _3=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition zip3_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil)]))]));
      ([(PCons PVar PVar)], (* A=0, As=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* B=0, Bs=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 7) 
      [([(PCons PVar PVar)], (* C=0, Cs=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (6, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 1])) ((°ECons ((°ETuple [˝VVar 5;˝VVar 3;˝VVar 1])) (˝VVar 0)))))]))]));
      ([PVar], (* _6=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 2;˝VVar 1;˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition zipwith_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)], (* A=0, As=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 6) 
      [([(PCons PVar PVar)], (* B=0, Bs=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 4) [˝VVar 2; ˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (6, 3)) [˝VVar 5; ˝VVar 4; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))))))]));
      ([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil)]));
      ([PVar], (* _6=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_7";˝VVar 1;˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition zipwith3_4 (_0 _1 _2 _3 : Exp) : Exp := 
   ELetRec [(4, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)], (* A=0, As=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 6) 
      [([(PCons PVar PVar)], (* B=0, Bs=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 9) 
      [([(PCons PVar PVar)], (* C=0, Cs=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 6) [˝VVar 4; ˝VVar 2; ˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (8, 4)) [˝VVar 7; ˝VVar 6; ˝VVar 4; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))))))]))]));
      ([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil)]))]));
      ([PVar], (* _8=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar], (* _7=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 7) 
      [([PVar], (* _6=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_9";˝VVar 2;˝VVar 1;˝VVar 0])]))]))]))]))])))]
   (°EApp (˝VFunId (0, 4)) [_0; _1; _2; _3]).

Definition map_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 2) [˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))))));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition mapfoldl_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* Acc0=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 3) [˝VVar 0; ˝VVar 2])) 
      [([(PTuple [PVar;PVar])],  (* R=0, Acc1=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (6, 3)) [˝VVar 5; ˝VVar 1; ˝VVar 3])) 
      [([(PTuple [PVar;PVar])],  (* Rs=0, Acc2=1 *) 
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 2) (˝VVar 0));˝VVar 1]));
      ([PVar],  (* _4=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PVar],  (* _3=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PNil], (*  *) 
      ˝ttrue, 
      (°ETuple [˝VNil;˝VLit "Acc"]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_7";˝VLit "_6";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition mapfoldr_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* Acc0=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VFunId (4, 3)) [˝VVar 3; ˝VVar 2; ˝VVar 1])) 
      [([(PTuple [PVar;PVar])],  (* Rs=0, Acc1=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VVar 5) [˝VVar 2; ˝VVar 1])) 
      [([(PTuple [PVar;PVar])],  (* R=0, Acc2=1 *) 
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 0) (˝VVar 2));˝VVar 1]));
      ([PVar],  (* _4=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PVar],  (* _3=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PNil], (*  *) 
      ˝ttrue, 
      (°ETuple [˝VNil;˝VLit "Acc"]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_7";˝VLit "_6";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition foldl_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 3) [˝VVar 0; ˝VVar 2])) ((°EApp (˝VFunId (5, 3)) [˝VVar 4; ˝VVar 0; ˝VVar 2]))));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VLit "_5";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition foldr_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* Acc=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0);
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 3; ˝VVar 2; ˝VVar 1])) ((°EApp (˝VVar 4) [˝VVar 1; ˝VVar 0]))));
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VLit "_5";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition foreach_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Fun=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VLit "ok");
      ([(PCons PVar PVar)], (* H=0, T=1 *) 
      ˝ttrue, 
      (°ESeq ((°EApp (˝VVar 2) [˝VVar 0])) ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]))));
      ([PVar], (* _2=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_3";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition seq_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* Min=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* Max=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar], (* Inc=0 *) 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 0%Z)])) ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 3; ˝VVar 2])) ((°ECall (˝VLit "erlang") (˝VLit "and") [˝VVar 1; ˝VVar 0]))))), 
      ˝VNil)]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition seq_2 (_0 _1 : Exp) : Exp := 
   seq_3 (_0) (_1) (˝VLit (Integer 1%Z)).


Definition keydelete_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Key=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _X_N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)], (* Tup=0, Tail=1 *) 
      ˝ttrue, 
      ˝VVar 1);
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_7";˝VLit "_6";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition keyfind_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Key=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _X_N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)], (* Tup=0, Tail=1 *) 
      ˝ttrue, 
      ˝VVar 0);
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VLit "_5";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition keymap_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ELetRec [(1, ((°ECase (˝VLit "_5") 
      [([(PCons PVar PVar)],  (* Tup=0, _4=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 5; ˝VVar 0])) ((°ELet 1 ((°EApp (˝VVar 5) [˝VVar 0])) ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "setelement") [˝VVar 7; ˝VVar 2; ˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (5, 1)) [˝VVar 4])) ((°ECons (˝VVar 1) (˝VVar 0)))))))))));
      ([(PCons PVar PVar)],  (* _3=0, _4=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _6=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition keymember_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Key=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _X_N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)], (* Tup=0, Tail=1 *) 
      ˝ttrue, 
      ˝ttrue);
      ([PVar], (* _4=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VLit "_5";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition keyreplace_4 (_0 _1 _2 _3 : Exp) : Exp := 
   ELetRec [(4, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Key=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _X_N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 6) 
      [([PVar], (* _X_NewTuple=0 *) 
      ˝ttrue, 
      ˝VNil)]));
      ([(PCons PVar PVar)], (* Tup=0, Tail=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 8) 
      [([PVar], (* NewTuple=0 *) 
      ˝ttrue, 
      (°ECons (˝VVar 0) (˝VVar 2)))]));
      ([PVar], (* _7=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 7) 
      [([PVar], (* _6=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_9";˝VLit "_8";˝VVar 1;˝VVar 0])]))]))]))]))])))]
   (°EApp (˝VFunId (0, 4)) [_0; _1; _2; _3]).

Definition keytake_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar], (* _X_Key=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _X_N=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)], (* Tup=0, Tail=1 *) 
      ˝ttrue, 
      (°ETuple [˝VLit "value";˝VVar 0;˝VVar 1]));
      ([PVar], (* _5=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_7";˝VLit "_6";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition sort_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* Pivot=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_11") 
      [([(PCons PVar PVar)],  (* X=0, _10=1 *) 
        (°ECall (˝VLit "erlang") (˝VLit "<") [˝VVar 0; ˝VVar 3]), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _9=0, _10=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _12=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 2])))) ((°ELet 1 ((°EApp (˝VFunId (3, 1)) [˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_3") 
      [([(PCons PVar PVar)],  (* X=0, _2=1 *) 
        (°ECall (˝VLit "erlang") (˝VLit ">=") [˝VVar 0; ˝VVar 5]), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _1=0, _2=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _4=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))) ((°ELet 1 ((°EApp (˝VFunId (5, 1)) [˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 2; ˝VVar 0]))))))))));
      ([PVar],  (* _16=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition sort_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 2) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* Pivot=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_14") 
      [([(PCons PVar PVar)],  (* X=0, _13=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VVar 6) [˝VVar 0; ˝VVar 3])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],  (* _17=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "bad_filter";˝VVar 0])]))]));
      ([(PCons PVar PVar)],  (* _12=0, _13=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _15=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 2])))) ((°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 4; ˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_5") 
      [([(PCons PVar PVar)],  (* X=0, _3=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VVar 8) [˝VVar 0; ˝VVar 5])) 
      [([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],  (* _cor_variable=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [˝VLit "badarg"]))]));
      ([(PCons PVar PVar)],  (* _2=0, _3=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _6=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))) ((°ELet 1 ((°EApp (˝VFunId (5, 2)) [˝VVar 6; ˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 2; ˝VVar 0]))))))))));
      ([PVar],  (* _20=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition keysort_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 2) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* Pivot=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_16") 
      [([(PCons PVar PVar)],  (* X=0, _13=1 *) 
        (°ETry ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 6; ˝VVar 0])) ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 7; ˝VVar 4])) ((°ECall (˝VLit "erlang") (˝VLit "<") [˝VVar 1; ˝VVar 0])))))) 1 (˝VVar 0) 2 (˝ffalse)), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _12=0, _13=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _17=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 2])))) ((°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 4; ˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_6") 
      [([(PCons PVar PVar)],  (* X=0, _3=1 *) 
        (°ETry ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 8; ˝VVar 0])) ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 9; ˝VVar 6])) ((°ECall (˝VLit "erlang") (˝VLit ">=") [˝VVar 1; ˝VVar 0])))))) 1 (˝VVar 0) 2 (˝ffalse)), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _2=0, _3=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _7=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))) ((°ELet 1 ((°EApp (˝VFunId (5, 2)) [˝VVar 6; ˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 2; ˝VVar 0]))))))))));
      ([PVar],  (* _21=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition usort_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* Pivot=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_11") 
      [([(PCons PVar PVar)],  (* X=0, _10=1 *) 
        (°ECall (˝VLit "erlang") (˝VLit "<") [˝VVar 0; ˝VVar 3]), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _9=0, _10=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _12=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 2])))) ((°ELet 1 ((°EApp (˝VFunId (3, 1)) [˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_3") 
      [([(PCons PVar PVar)],  (* X=0, _2=1 *) 
        (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VVar 5]), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _1=0, _2=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _4=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))) ((°ELet 1 ((°EApp (˝VFunId (5, 1)) [˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 2; ˝VVar 0]))))))))));
      ([PVar],  (* _16=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition usort_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 2) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* Pivot=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_17") 
      [([(PCons PVar PVar)],  (* X=0, _13=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ECase ((°EApp (˝VVar 6) [˝VVar 0; ˝VVar 3])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "/=") [˝VVar 0; ˝VVar 3]));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        ˝ffalse);
      ([PVar],  (* _14=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "badarg";˝VVar 0])]))])) ((°ECase (˝VVar 0) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 1)) [˝VVar 2])) ((°ECons (˝VVar 2) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (3, 1)) [˝VVar 2]));
      ([PVar],  (* _20=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "bad_filter";˝VVar 0])]))]))));
      ([(PCons PVar PVar)],  (* _12=0, _13=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _18=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 2])))) ((°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 4; ˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_5") 
      [([(PCons PVar PVar)],  (* X=0, _3=1 *) 
        ˝ttrue, 
        (°ECase ((°EApp (˝VVar 8) [˝VVar 0; ˝VVar 5])) 
      [([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],  (* _cor_variable=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [˝VLit "badarg"]))]));
      ([(PCons PVar PVar)],  (* _2=0, _3=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _6=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 4])))) ((°ELet 1 ((°EApp (˝VFunId (5, 2)) [˝VVar 6; ˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 2; ˝VVar 0]))))))))));
      ([PVar],  (* _23=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition ukeysort_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 2) 
      [([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],  (* Pivot=0, T=1 *) 
        ˝ttrue, 
        (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 3; ˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_15") 
      [([(PCons PVar PVar)],  (* X=0, _13=1 *) 
        (°ETry ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 7; ˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "<") [˝VVar 0; ˝VVar 4])))) 1 (˝VVar 0) 2 (˝ffalse)), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _12=0, _13=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _16=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 3])))) ((°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 5; ˝VVar 0])) ((°ELet 1 ((°ELetRec [(1, ((°ECase (˝VLit "_6") 
      [([(PCons PVar PVar)],  (* X=0, _4=1 *) 
        (°ETry ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 9; ˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VVar 6])))) 1 (˝VVar 0) 2 (˝ffalse)), 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PCons PVar PVar)],  (* _3=0, _4=1 *) 
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PNil],  (*  *) 
        ˝ttrue, 
        ˝VNil);
      ([PVar],  (* _7=0 *) 
        ˝ttrue, 
        (°ECall (˝VLit "erlang") (˝VLit "error") [(°ETuple [˝VLit "bad_generator";˝VVar 0])]))])))] ((°EApp (˝VFunId (0, 1)) [˝VVar 5])))) ((°ELet 1 ((°EApp (˝VFunId (6, 2)) [˝VVar 7; ˝VVar 0])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 2; ˝VVar 0]))))))))))));
      ([PVar],  (* _20=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition merge_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 6])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _7=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _8=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition merge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 5) [˝VVar 2; ˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 7])) ((°ECons (˝VVar 3) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 6; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([PVar],  (* _5=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))]));
      ([PVar], (* _10=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).


Definition keymerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 7])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition ukeymerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 5; ˝VVar 2])) ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 6; ˝VVar 1])) ((°ELet 1 ((°EApp (˝VFunId (6, 3)) [˝VVar 7; ˝VVar 5; ˝VVar 9])) ((°ECons (˝VVar 5) (˝VVar 0)))))))))]));
      ([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _13=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).


Definition umerge_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 6])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _8=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _9=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition umerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 1])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition rmerge_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 6])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _7=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _8=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition rmerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 5) [˝VVar 2; ˝VVar 0])) 
      [([(PLit (Atom "true"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 7])) ((°ECons (˝VVar 3) (˝VVar 0)))));
      ([(PLit (Atom "false"))],  (*  *) 
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 6; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([PVar],  (* _5=0 *) 
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))]));
      ([PVar], (* _10=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition rkeymerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 7])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition rumerge_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 6])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _8=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* _9=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition rumerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 1])) ((°ECons (˝VVar 3) (˝VVar 0)))))]));
      ([PVar], (* _11=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition rukeymerge_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 2) 
      [([PNil], (*  *) 
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar], (* L=0 *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar], (* L=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil], (*  *) 
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)], (* H1=0, T1=1 *) 
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([(PCons PVar PVar)], (* H2=0, T2=1 *) 
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 5; ˝VVar 2])) ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "element") [˝VVar 6; ˝VVar 1])) ((°ELet 1 ((°EApp (˝VFunId (6, 3)) [˝VVar 7; ˝VVar 5; ˝VVar 9])) ((°ECons (˝VVar 5) (˝VVar 0)))))))))]));
      ([PVar], (* _12=0 *) 
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar], (* _13=0 *) 
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition module_info_0 : Exp := 
   ELetRec [(0, 
     ((°ECall (˝VLit "erlang") (˝VLit "get_module_info") [˝VLit "std_lists"])))]
   (°EApp (˝VFunId (0, 0)) []).

Definition module_info_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECall (˝VLit "erlang") (˝VLit "get_module_info") [˝VLit "std_lists"; ˝VVar 1])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

(** Test all - inputs: ['FUN',[1,2,3]] *)
Goal ⟨[], all_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 0%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit "true"].
Proof. auto_proove_subst_semantics. Qed.

(** Test any - inputs: ['FUN',[1,2,3]] *)
Goal ⟨[], any_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit "true"].
Proof. auto_proove_subst_semantics. Qed.

(** Test member - inputs: [b,[a,b,c]] *)
Goal ⟨[], member_2 (˝VLit "b") (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VLit "true"].
Proof. auto_proove_subst_semantics. Qed.

(** Test search - inputs: ['FUN',[a,b,c]] *)
Goal ⟨[], search_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0; ˝VLit "b"])) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VTuple [VLit "value"; VLit "b"]].
Proof. auto_proove_subst_semantics. Qed.

(** Test append - inputs: [[1,2],[3,4]] *)
Goal ⟨[], append_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))))].
Proof. auto_proove_subst_semantics. Qed.

(*Handfixed function.*)
Goal ⟨[], join_2 (˝VLit "x") (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
  -->* RValSeq [VCons (VLit "a") (VCons (VLit "x") (VCons (VLit "b") (VCons (VLit "x") (VCons (VLit "c") (VNil)))))].
Proof. auto_proove_subst_semantics. Qed.

(** Test concat - inputs: [[[1,2],[3],[]]] *)
(*TODO gives bad_generator for now*)
Goal ⟨[], concat_1 (˝VCons (VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (VCons (VCons (VLit 3%Z) (VNil)) (VCons (VNil) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil)))].
Proof. auto_proove_subst_semantics. Admitted.

(* * Test delete - inputs: [2,[1,2,3,2]] *)
(*Formalzies wrong*)
Goal ⟨[], delete_2 (˝VLit 2%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 2%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 3%Z) (VCons (VLit 2%Z) (VNil)))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test droplast - inputs: [[1,2,3]] *)
Goal ⟨[], droplast_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test dropwhile - inputs: ['FUN',[4,3,2,1]] *)
(*TODO Badfun*)
Goal ⟨[], dropwhile_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 4%Z) (VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test duplicate - inputs: [3,x] *)
Goal ⟨[], duplicate_2 (˝VLit 3%Z) (˝VLit "x")⟩
   -->* RValSeq [VCons (VLit "x") (VCons (VLit "x") (VCons (VLit "x") (VNil)))].
Proof. auto_proove_subst_semantics. Qed.

(** Test enumerate - inputs: [[a,b,c]] *)
Goal ⟨[], enumerate_1 (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VCons (VTuple [VLit 3%Z; VLit "c"]) (VNil)))].
Proof. auto_proove_subst_semantics. Qed.

(** Test filter - inputs: ['FUN',[1,2,3,4]] *)
Goal ⟨[], filter_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit "=:=") [°ECall (˝VLit "erlang") (˝VLit "rem") [˝VVar 0; ˝VLit (Integer 2%Z)]; ˝VLit (Integer 0%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 2%Z) (VCons (VLit 4%Z) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test filtermap - inputs: ['FUN',[1,2,3]] *)
Goal ⟨[], filtermap_2 (°EFun 1 (°ETuple [˝VLit "true"; ˝VVar 0])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil)))].
Proof. auto_proove_subst_semantics. Qed.

(** Test flatlength - inputs: [[1,[2,3],[],[4]]] *)
(**TODO Error UIndef*)
Goal ⟨[], flatlength_1 (˝VCons (VLit 1%Z) (VCons (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))) (VCons (VNil) (VCons (VCons (VLit 4%Z) (VNil)) (VNil)))))⟩
   -->* RValSeq [VLit 4%Z].
Proof. auto_proove_subst_semantics. Admitted.

(** Test flatmap - inputs: ['FUN',[1,2]] *)
(**TODO Error Bad generator*)

Goal ⟨[], flatmap_2 (°EFun 1 (°ECons (˝VVar 0) (°ECons (˝VVar 0) (˝VNil)))) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 2%Z) (VNil))))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test flatten - inputs: [[1,[2,[3]],4]] *)
(**TODO Error UIndef*)

Goal ⟨[], flatten_1 (˝VCons (VLit 1%Z) (VCons (VCons (VLit 2%Z) (VCons (VCons (VLit 3%Z) (VNil)) (VNil))) (VCons (VLit 4%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test join - inputs: [x,[a,b,c]] *)
(*TODO: Does not finish probably bad formalizatiom*)
Goal ⟨[], join_2 (˝VLit "x") (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VCons (VLit "a") (VCons (VLit "x") (VCons (VLit "b") (VCons (VLit "x") (VCons (VLit "c") (VNil)))))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test last - inputs: [[1,2,3]] *)
Goal ⟨[], last_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit 3%Z].
Proof. auto_proove_subst_semantics. Qed.

(** Test nth - inputs: [2,[a,b,c]] *)
Goal ⟨[], nth_2 (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VLit "b"].
Proof. auto_proove_subst_semantics. Qed.

(** Test nthtail - inputs: [2,[a,b,c,d]] *)
Goal ⟨[], nthtail_2 (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VCons (VLit "d") (VNil)))))⟩
   -->* RValSeq [VCons (VLit "c") (VCons (VLit "d") (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test partition - inputs: ['FUN',[1,2,3,4]] *)
(**TODO Error Bad generator*)

Goal ⟨[], partition_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VTuple [VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)); VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))]].
Proof. auto_proove_subst_semantics. Admitted.

(** Test prefix - inputs: [[1,2],[1,2,3,4]] *)
Goal ⟨[], prefix_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VLit "true"].
Proof. auto_proove_subst_semantics. Qed.

(** Test reverse - inputs: [[1,2,3]] *)
Goal ⟨[], reverse_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil)))].
Proof. auto_proove_subst_semantics. Qed.

(** Test split - inputs: [2,[1,2,3,4]] *)
Goal ⟨[], split_2 (˝VLit 2%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VTuple [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)); VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))]].
Proof. auto_proove_subst_semantics. Qed.

(** Test sublist - inputs: [[a,b,c,d],2,2] *)
(*TODO error IF_cluase**)
Goal ⟨[], sublist_3 (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VCons (VLit "d") (VNil))))) (˝VLit 2%Z) (˝VLit 2%Z)⟩
   -->* RValSeq [VCons (VLit "b") (VCons (VLit "c") (VNil))].
Proof. auto_proove_subst_semantics. Admitted.

  (** Test sum - inputs: [[1,2,3,4]] *)
Goal ⟨[], sum_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VLit 10%Z].
Proof. auto_proove_subst_semantics. Qed.

(** Test takewhile - inputs: ['FUN',[4,3,2,1]] *)
Goal ⟨[], takewhile_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 4%Z) (VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 4%Z) (VCons (VLit 3%Z) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test unzip - inputs: [[{1,a},{2,b}]] *)
Goal ⟨[], unzip_1 (˝VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VNil)))⟩
   -->* RValSeq [VTuple [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)); VCons (VLit "a") (VCons (VLit "b") (VNil))]].
Proof. auto_proove_subst_semantics. Qed.

(** Test unzip3 - inputs: [[{1,a,x},{2,b,y}]] *)
Goal ⟨[], unzip3_1 (˝VCons (VTuple [VLit 1%Z; VLit "a"; VLit "x"]) (VCons (VTuple [VLit 2%Z; VLit "b"; VLit "y"]) (VNil)))⟩
   -->* RValSeq [VTuple [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)); VCons (VLit "a") (VCons (VLit "b") (VNil)); VCons (VLit "x") (VCons (VLit "y") (VNil))]].
Proof. auto_proove_subst_semantics. Qed.

(** Test zip - inputs: [[1,2],[a,b]] *)
Goal ⟨[], zip_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit "a") (VCons (VLit "b") (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test zip3 - inputs: [[1,2],[a,b],[x,y]] *)
Goal ⟨[], zip3_3 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit "a") (VCons (VLit "b") (VNil))) (˝VCons (VLit "x") (VCons (VLit "y") (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"; VLit "x"]) (VCons (VTuple [VLit 2%Z; VLit "b"; VLit "y"]) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test zipwith - inputs: ['FUN',[1,2],[a,b]] *)
Goal ⟨[], zipwith_3 (°EFun 2 (°ETuple [˝VVar 0; ˝VVar 1])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit "a") (VCons (VLit "b") (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test map - inputs: ['FUN',[1,2]] *)
Goal ⟨[], map_2 (°EFun 1 (°ETuple [˝VLit "ok"; ˝VVar 0])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit "ok"; VLit 1%Z]) (VCons (VTuple [VLit "ok"; VLit 2%Z]) (VNil))].
Proof. auto_proove_subst_semantics. Qed.

(** Test foldl - inputs: ['FUN',10,[1,2,3]] *)
Goal ⟨[], foldl_3 (°EFun 2 (°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 1; ˝VVar 0])) (˝VLit 10%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit 4%Z].
Proof. auto_proove_subst_semantics. Qed.

(** Test foldr - inputs: ['FUN',0,[1,2,3]] *)
Goal ⟨[], foldr_3 (°EFun 2 (°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VVar 1])) (˝VLit 0%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit 2%Z].
Proof. auto_proove_subst_semantics. Qed.

(** Test seq - inputs: [1,5] *)
(*Erorr if_clause*)
Goal ⟨[], seq_2 (˝VLit 1%Z) (˝VLit 5%Z)⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VCons (VLit 5%Z) (VNil)))))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test keydelete - inputs: [b,1,[{a,1},{b,2}]] *)
(**TODO Error works bad> wrong lits?*)
Goal ⟨[], keydelete_3 (˝VLit "b") (˝VLit 1%Z) (˝VCons (VTuple [VLit "a"; VLit 1%Z]) (VCons (VTuple [VLit "b"; VLit 2%Z]) (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit "a"; VLit 1%Z]) (VNil)].
Proof. auto_proove_subst_semantics. Admitted.

(** Test keyfind - inputs: [b,1,[{a,1},{b,2}]] *)
(**TODO Error works bad> wrong lits?*)

Goal ⟨[], keyfind_3 (˝VLit "b") (˝VLit 1%Z) (˝VCons (VTuple [VLit "a"; VLit 1%Z]) (VCons (VTuple [VLit "b"; VLit 2%Z]) (VNil)))⟩
   -->* RValSeq [VTuple [VLit "b"; VLit 2%Z]].
Proof. auto_proove_subst_semantics. Admitted.

(** Test keymember - inputs: [b,1,[{a,1},{b,2}]] *)
Goal ⟨[], keymember_3 (˝VLit "b") (˝VLit 1%Z) (˝VCons (VTuple [VLit "a"; VLit 1%Z]) (VCons (VTuple [VLit "b"; VLit 2%Z]) (VNil)))⟩
   -->* RValSeq [VLit "true"].
Proof. auto_proove_subst_semantics. Qed.

(** Test sort - inputs: [[3,1,4,2]] *)
(**TODO Error bad_generator*)
Goal ⟨[], sort_1 (˝VCons (VLit 3%Z) (VCons (VLit 1%Z) (VCons (VLit 4%Z) (VCons (VLit 2%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))))].
Proof. auto_proove_subst_semantics. Admitted.

(** Test merge - inputs: [[1,3,5],[2,4,6]] *)
(**TODO Error if_clause*)
Goal ⟨[], merge_2 (˝VCons (VLit 1%Z) (VCons (VLit 3%Z) (VCons (VLit 5%Z) (VNil)))) (˝VCons (VLit 2%Z) (VCons (VLit 4%Z) (VCons (VLit 6%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VCons (VLit 5%Z) (VCons (VLit 6%Z) (VNil))))))].
Proof. auto_proove_subst_semantics. Admitted.