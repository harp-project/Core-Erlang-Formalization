
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
