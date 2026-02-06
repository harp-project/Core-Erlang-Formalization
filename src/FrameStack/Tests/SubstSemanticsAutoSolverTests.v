
From CoreErlang.FrameStack Require SubstSemantics
CIU SubstSemanticsAutoSolver.
From CoreErlang.FrameStack Require Import Examples.

Open Scope string_scope.

Import FrameStack.SubstSemantics FrameStack.CIU. 
Import FrameStack.SubstSemanticsAutoSolver.
Require Import Coq.Lists.List.
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
 star_step_solver.
Qed.

(*constant function test*)
Goal ⟨[], const_fun (˝VLit 42%Z)⟩ -->* RValSeq [VLit (Atom "ok")].
Proof.
 star_step_solver.
Qed.

(*constant equivalency test*)
Theorem const_equiv :
CIU (const_fun (˝VLit 42%Z)) (const_fun (˝VLit 62%Z)).
Proof.
 pose proof (CIU_eval (const_fun (˝VLit 42%Z)) (RValSeq [VLit (Atom "ok")])).
 pose proof (CIU_eval (const_fun (˝VLit 62%Z)) (RValSeq [VLit (Atom "ok")])).
 destruct H.
 scope_solver.
 star_step_solver.
 destruct H0.
 scope_solver.
 star_step_solver.
 apply (CIU_transitive_closed (const_fun (˝VLit 42%Z)) (RValSeq [VLit (Atom "ok")]) (const_fun (˝VLit 62%Z)));assumption.
Qed. 

(*Addition test*)
Goal ⟨[], add_primitive (˝VLit 1%Z) (˝VLit 2%Z)⟩ -->* RValSeq [VLit 3%Z].
Proof.
 star_step_solver.
Qed.

(*Tuple test*)
Goal ⟨[], make_tuple [˝VLit 1%Z; ˝VLit (Atom "x"%string)]⟩ -->* RValSeq [VTuple [VLit 1%Z; VLit (Atom "x")]].
Proof.
 star_step_solver.
Qed.

(*List test*)
Goal ⟨[], make_list [˝VLit 1%Z; ˝VLit 2%Z]⟩ -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VLit (Atom "nil")))].
Proof.
 star_step_solver.
Qed.

(*Map test*)
Goal ⟨[], make_map [(˝VLit (Atom "a"%string), ˝VLit 1%Z)]⟩ -->* RValSeq [VMap [(VLit (Atom "a"), VLit 1%Z)]].
Proof.
star_step_solver.
Qed.

(*Let test*)
Goal ⟨[], let_binding (add_primitive (˝VLit 5%Z) (˝VLit 7%Z)) (˝VVar 0)⟩ -->* RValSeq [VLit 12%Z].
Proof.
star_step_solver.
Qed.

(*Case test*)
Goal ⟨[], case_expr (˝VLit 1%Z)
    [([PLit (Integer 0)], ˝ttrue, ˝VLit (Atom "zero"%string));
     ([PLit (Integer 1)], ˝ttrue, ˝VLit (Atom "one"%string))]⟩
-->* RValSeq [VLit (Atom "one")].
Proof.
 star_step_solver.
Qed.

(* try/catch tests*)
Goal ⟨[], try_example
(°ECall (˝VLit (Atom "erlang"%string))
     (˝VLit (Atom "error"%string))
     [˝VLit (Atom "oops"%string)])
(°ETuple [˝VLit (Atom "caught"%string); ˝VVar 1])⟩
-->* RValSeq [VTuple [VLit (Atom "caught"%string); VLit (Atom "oops"%string)]].
Proof.
 star_step_solver.
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
 star_step_solver.
Qed.

Goal ⟨[], °ETry
(˝VLit (Atom "success"%string))
1
(˝VVar 0)
3
(°ETuple [˝VLit (Atom "caught"%string); ˝VVar 1])⟩
-->* RValSeq [VLit (Atom "success"%string)].
Proof.
 star_step_solver.
Qed.

(** Test member - element found *)
 Goal ⟨[], member (˝VLit 2%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
   -->* RValSeq [VLit "true"].
 Proof.
   star_step_solver.
 Qed.

 (** Test member - element not found *)
 Goal ⟨[], member (˝VLit 5%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))⟩
   -->* RValSeq [VLit "false"].
 Proof.
   star_step_solver.
 Qed.

 (** Test reverse/1 wrapper *)
 Goal ⟨[], reverse1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
   -->* RValSeq [VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) VNil))].
 Proof.
   star_step_solver.
 Qed.

 (** Test sum/1 wrapper *)
 Goal ⟨[], sum1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) VNil)))⟩
   -->* RValSeq [VLit 6%Z].
 Proof.
   star_step_solver.
 Qed.

 (** Test reverse empty list *)
 Goal ⟨[], reverse1 (˝VNil)⟩ -->* RValSeq [VNil].
 Proof.
   star_step_solver.
 Qed.

 (** Test sum empty list *)
 Goal ⟨[], sum1 (˝VNil)⟩ -->* RValSeq [VLit 0%Z].
 Proof.
   star_step_solver.
 Qed.

 (** Test append *)
 Goal ⟨[], append (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))
                   (˝VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) VNil)))].
 Proof.
   star_step_solver.
 Qed.

 (** Test nth - get first element *)
 Goal ⟨[], nth (˝VLit 1%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") VNil)))⟩
   -->* RValSeq [VLit "a"].
 Proof.
   star_step_solver.
 Qed.

 (** Test nth - get second element *)
 Goal ⟨[], nth (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") VNil)))⟩
   -->* RValSeq [VLit "b"].
 Proof.
   star_step_solver.
 Qed.


 (** Test member - element not found *)
 Goal ⟨[], member (˝VLit 5%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) VNil))⟩
   -->* RValSeq [VLit "false"].
 Proof.
   star_step_solver.
 Qed.

 (*Generated functions and tests*)

Definition all_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝ttrue);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        ˝ffalse);
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition any_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        ˝ttrue);
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition member_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 2; ˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        ˝ttrue);
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition search_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝ffalse);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        (°ETuple [˝VLit "value";˝VVar 0]));
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition append_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([(PCons PVar PVar)],   
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 1; ˝VVar 0]))));
      ([PNil],   
        ˝ttrue, 
        ˝VNil);
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition append_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECall (˝VLit "erlang") (˝VLit "++") [˝VVar 1; ˝VVar 2])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition droplast_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([(PCons PVar PNil)],   
        ˝ttrue, 
        ˝VNil);
      ([(PCons PVar PVar)],   
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (2, 1)) [˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition dropwhile_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([PCons PVar PVar],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        ˝VVar 5);
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition duplicate_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 0%Z))],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar],  
      ˝ttrue, 
      ˝VNil)]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 1; ˝VLit (Integer 0%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 1; ˝VLit (Integer 1%Z)])) ((°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 0; ˝VVar 1])) ((°ECons (˝VVar 2) (˝VVar 0)))))))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition enumerate_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2])) ((°ECons ((°ETuple [˝VVar 4;˝VVar 2])) (˝VVar 0)))))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition enumerate_1 (_0 : Exp) : Exp := 
  enumerate_2 (˝VLit (Integer 1%Z)) (_0).

Definition filter_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition filtermap_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PTuple [(PLit (Atom "true"));PVar])],   
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        (°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition join_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([PCons PVar PNil],  
      ˝ttrue, 
      °ECons (˝VVar 0) (˝VNil));
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) ((°ECons (˝VVar 3) (˝VVar 0)))))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition last_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([(PCons PVar PNil)],   
        ˝ttrue, 
        ˝VVar 0);
      ([(PCons PVar PVar)],   
        ˝ttrue, 
        (°EApp (˝VFunId (2, 1)) [˝VVar 1]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition nth_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 1%Z))],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([(PCons PVar PVar)],  
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)],  
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 1%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2]))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition nthtail_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 0%Z))],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar],  
      ˝ttrue, 
      ˝VVar 0)]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)],  
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 0%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2]))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_4";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition prefix_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar],  
      ˝ttrue, 
      ˝ttrue)]));
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)],  
      (°ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0; ˝VVar 2]), 
      (°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 1]))]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      ˝ffalse)]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition reverse_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar],  
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar],  
      ˝ttrue, 
      (°EApp (˝VFunId (3, 2)) [˝VVar 2; (°ECons (˝VVar 1) (˝VVar 0))]))]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition reverse_1 (_0 : Exp) : Exp := 
   reverse_2 (_0) (˝VNil).

Definition split_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([(PLit (Integer 0%Z))],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar],  
      ˝ttrue, 
      (°ETuple [˝VNil;˝VVar 0]))]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)],  
      (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 0%Z)]), 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) ((°ECase ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2])) 
      [([(PTuple [PVar;PVar])],   
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 3) (˝VVar 0));˝VVar 1]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition sublist_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     (°ECase (EValues [˝VVar 1 ; ˝VVar 2 ; ˝VVar 3])
      [
      ([PNil ; PVar ; PVar], 
        ˝ttrue, 
        ˝VNil); (*case ([], Start, Len)*)
      ([PVar ; PVar ; (PLit (Integer 0%Z))], 
        ˝ttrue, 
        ˝VNil); (*case (List, Start, 0)*)
      ([(PCons PVar PVar) ; (PLit (Integer 1%Z)) ; PVar], (*0 = Head, 1 = Tail , 2 = Len; 3 = letrec, 4 = List, 5 = Start, 6 = Len*)
        ˝ttrue, 
        (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) (*0 = Len - 1 , 1 = Head, 2 = Tail , 3 = Len; 4 = letrec, 5 = List, 6 = Start, 7 = Len*)
          ((°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 2; ˝VLit (Integer 1%Z); ˝VVar 0])) (*0 = letrec(Tail, 1, Len - 1), 1 = Len - 1 , 2 = Head, 3 = Tail , 4 = Len; 5 = letrec, 6 = List, 7 = Start, 8 = Len*)
            ((°ECons (˝VVar 2) (˝VVar 0))))))); (*case ([H | T], 1, Len)*)
      ([(PCons PVar PVar); PVar ; PVar], (*0 = Head, 1 = Tail, 2 = Start , 3 = Len; 4 = letrec, 5 = List, 6 = Start, 7 = Len*)
        (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VLit (Integer 1%Z)]), 
        (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 2; ˝VLit (Integer 1%Z)])) (*0 = Start - 1 , 1 = Head, 2 = Tail, 3 = Start , 4 = Len; 5 = letrec, 6 = List, 7 = Start, 8 = Len*)
          ((°EApp (˝VFunId (5, 3)) [˝VVar 2; ˝VVar 0; ˝VVar 4])))); (*case ([H | T], Start, Len) where Start > 1*)
      ([PVar ; PVar ; PVar],
        ˝ttrue, 
        °EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0;˝VVar 1;˝VVar 2])])]))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition sublist_2 (_0 _1 : Exp) : Exp := 
   sublist_3 (_0) (˝VLit (Integer 1%Z)) (_1).

Definition sum_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PVar],  
      ˝ttrue, 
      ˝VVar 0)]));
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PVar],  
      ˝ttrue, 
      (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 0; ˝VVar 1])) ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 0]))))]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition sum_1 (_0 : Exp) : Exp := 
   sum_2 (_0) (˝VLit (Integer 0%Z)).   

Definition takewhile_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase ((°EApp (˝VVar 2) [˝VVar 0])) 
      [([(PLit (Atom "true"))],   
        ˝ttrue, 
        (°ELet 1 ((°EApp (˝VFunId (3, 2)) [˝VVar 2; ˝VVar 1])) ((°ECons (˝VVar 1) (˝VVar 0)))));
      ([(PLit (Atom "false"))],   
        ˝ttrue, 
        ˝VNil);
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "case_clause";˝VVar 0])]))]));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition unzip_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],   
        ˝ttrue, 
        (°ETuple [˝VNil;˝VNil]));
      ([(PCons (PTuple [PVar;PVar]) PVar)],   
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (3, 1)) [˝VVar 2])) 
      [([(PTuple [PVar;PVar])],   
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 2) (˝VVar 0));(°ECons (˝VVar 3) (˝VVar 1))]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition unzip3_1 (_0 : Exp) : Exp := 
   ELetRec [(1, 
     ((°ECase (˝VVar 1) 
      [([PNil],   
        ˝ttrue, 
        (°ETuple [˝VNil;˝VNil;˝VNil]));
      ([(PCons (PTuple [PVar;PVar;PVar]) PVar)],   
        ˝ttrue, 
        (°ECase ((°EApp (˝VFunId (4, 1)) [˝VVar 3])) 
      [([(PTuple [PVar;PVar;PVar])],   
        ˝ttrue, 
        (°ETuple [(°ECons (˝VVar 3) (˝VVar 0));(°ECons (˝VVar 4) (˝VVar 1));(°ECons (˝VVar 5) (˝VVar 2))]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "badmatch";˝VVar 0])]))]));
      ([PVar],   
        ˝ttrue, 
        (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 0])]))])))]
   (°EApp (˝VFunId (0, 1)) [_0]).

Definition zip_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil)]));
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 1])) ((°ECons ((°ETuple [˝VVar 3;˝VVar 1])) (˝VVar 0)))))]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 1;˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition zip3_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 2) 
      [([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil)]))]));
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 7) 
      [([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (6, 3)) [˝VVar 5; ˝VVar 3; ˝VVar 1])) ((°ECons ((°ETuple [˝VVar 5;˝VVar 3;˝VVar 1])) (˝VVar 0)))))]))]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VVar 2;˝VVar 1;˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition zipwith_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ECase (˝VVar 6) 
      [([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 4) [˝VVar 2; ˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (6, 3)) [˝VVar 5; ˝VVar 4; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))))))]));
      ([PNil],  
      ˝ttrue, 
      (°ECase (˝VVar 4) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil)]));
      ([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_7";˝VVar 1;˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition map_2 (_0 _1 : Exp) : Exp := 
   ELetRec [(2, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PNil],  
      ˝ttrue, 
      ˝VNil);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 2) [˝VVar 0])) ((°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 3; ˝VVar 2])) ((°ECons (˝VVar 1) (˝VVar 0)))))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_5";˝VVar 0])]))]))])))]
   (°EApp (˝VFunId (0, 2)) [_0; _1]).

Definition foldl_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil],  
      ˝ttrue, 
      ˝VVar 0);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VVar 3) [˝VVar 0; ˝VVar 2])) ((°EApp (˝VFunId (5, 3)) [˝VVar 4; ˝VVar 0; ˝VVar 2]))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VLit "_5";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition foldr_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 3) 
      [([PVar],  
      ˝ttrue, 
      (°ECase (˝VVar 5) 
      [([PNil],  
      ˝ttrue, 
      ˝VVar 0);
      ([(PCons PVar PVar)],  
      ˝ttrue, 
      (°ELet 1 ((°EApp (˝VFunId (4, 3)) [˝VVar 3; ˝VVar 2; ˝VVar 1])) ((°EApp (˝VVar 4) [˝VVar 1; ˝VVar 0]))));
      ([PVar],  
      ˝ttrue, 
      (°EPrimOp "match_fail" [(°ETuple [˝VLit "function_clause";˝VLit "_6";˝VLit "_5";˝VVar 0])]))]))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).


Definition seq_3 (_0 _1 _2 : Exp) : Exp := 
   ELetRec [(3, 
     ((°ECase (˝VVar 1) 
      [
      ([PVar], (* Min=0 *) 
      ˝ttrue, 
        (°ECase (˝VVar 3) 
        [([PVar], (* Max=0 *) 
        ˝ttrue, 
          (°ECase (˝VVar 5) 
          [([PVar], (* Inc=0 *) 
          (°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 0%Z)]))
            ((°ELet 1 ((°ECall (˝VLit "erlang") (˝VLit ">=") [˝VVar 2; ˝VVar 3])) 
              ((°ECall (˝VLit "erlang") (˝VLit "and") [˝VVar 1; ˝VVar 0]))))),
              
          (°ELet 1 (°ECall (˝VLit "erlang") (˝VLit "+") [˝VVar 2; ˝VVar 0]) 
            (°ELet 1 ((°EApp (˝VFunId (4, 2)) [˝VVar 0; ˝VVar 2; ˝VVar 1]))
              (°ECons (˝VVar 4) (˝VVar 0)))));
          ([PVar],
           (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 2; ˝VVar 1]),
           ˝VNil
          )
          ]
      ))]))])))]
   (°EApp (˝VFunId (0, 3)) [_0; _1; _2]).

Definition seq_2 (_0 _1 : Exp) : Exp := 
   seq_3 (_0) (_1) (˝VLit (Integer 1%Z)).

(** Test all - inputs: ['FUN',[1,2,3]] *)
Goal ⟨[], all_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 0%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit "true"].
Proof. star_step_solver. Qed.

(** Test any - inputs: ['FUN',[1,2,3]] *)
Goal ⟨[], any_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit "true"].
Proof. star_step_solver. Qed.

(** Test member - inputs: [b,[a,b,c]] *)
Goal ⟨[], member_2 (˝VLit "b") (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VLit "true"].
Proof. star_step_solver. Qed.

(** Test search - inputs: ['FUN',[a,b,c]] *)
Goal ⟨[], search_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit "=:=") [˝VVar 0; ˝VLit "b"])) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VTuple [VLit "value"; VLit "b"]].
Proof. star_step_solver. Qed.

(** Test append - inputs: [[1,2],[3,4]] *)
Goal ⟨[], append_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))))].
Proof. star_step_solver. Qed.

(** Test join - inputs: [x,[a,b,c]] *)
Goal ⟨[], join_2 (˝VLit "x") (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
  -->* RValSeq [VCons (VLit "a") (VCons (VLit "x") (VCons (VLit "b") (VCons (VLit "x") (VCons (VLit "c") (VNil)))))].
Proof. star_step_solver. Qed.

(** Test droplast - inputs: [[1,2,3]] *)
Goal ⟨[], droplast_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))].
Proof. star_step_solver. Qed.

(** Test dropwhile - inputs: ['FUN',[4,3,2,1]] *)
Goal ⟨[], dropwhile_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 4%Z) (VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil))].
Proof. star_step_solver. Qed.

(** Test duplicate - inputs: [3,x] *)
Goal ⟨[], duplicate_2 (˝VLit 3%Z) (˝VLit "x")⟩
   -->* RValSeq [VCons (VLit "x") (VCons (VLit "x") (VCons (VLit "x") (VNil)))].
Proof. star_step_solver. Qed.

(** Test enumerate - inputs: [[a,b,c]] *)
Goal ⟨[], enumerate_1 (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VCons (VTuple [VLit 3%Z; VLit "c"]) (VNil)))].
Proof. star_step_solver. Qed.

(** Test filter - inputs: ['FUN',[1,2,3,4]] *)
Goal ⟨[], filter_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit "=:=") [°ECall (˝VLit "erlang") (˝VLit "rem") [˝VVar 0; ˝VLit (Integer 2%Z)]; ˝VLit (Integer 0%Z)])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 2%Z) (VCons (VLit 4%Z) (VNil))].
Proof. star_step_solver. Qed.

(** Test filtermap - inputs: ['FUN',[1,2,3]] *)
Goal ⟨[], filtermap_2 (°EFun 1 (°ETuple [˝VLit "true"; ˝VVar 0])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil)))].
Proof. star_step_solver. Qed.

(** Test last - inputs: [[1,2,3]] *)
Goal ⟨[], last_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit 3%Z].
Proof. star_step_solver. Qed.

(** Test nth - inputs: [2,[a,b,c]] *)
Goal ⟨[], nth_2 (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil))))⟩
   -->* RValSeq [VLit "b"].
Proof. star_step_solver. Qed.

(** Test nthtail - inputs: [2,[a,b,c,d]] *)
Goal ⟨[], nthtail_2 (˝VLit 2%Z) (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VCons (VLit "d") (VNil)))))⟩
   -->* RValSeq [VCons (VLit "c") (VCons (VLit "d") (VNil))].
Proof. star_step_solver. Qed.

(** Test prefix - inputs: [[1,2],[1,2,3,4]] *)
Goal ⟨[], prefix_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VLit "true"].
Proof. star_step_solver. Qed.

(** Test reverse - inputs: [[1,2,3]] *)
Goal ⟨[], reverse_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil)))].
Proof. star_step_solver. Qed.

(** Test split - inputs: [2,[1,2,3,4]] *)
Goal ⟨[], split_2 (˝VLit 2%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VTuple [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)); VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))]].
Proof. star_step_solver. Qed.

(** Test sublist - inputs: [[a,b,c,d],2,2] *)
Goal ⟨[], sublist_3 (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VCons (VLit "d") (VNil))))) (˝VLit 2%Z) (˝VLit 2%Z)⟩
   -->* RValSeq [VCons (VLit "b") (VCons (VLit "c") (VNil))].
Proof.
    star_step_solver.
Qed.

(** Test sum - inputs: [[1,2,3,4]] *)
Goal ⟨[], sum_1 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil)))))⟩
   -->* RValSeq [VLit 10%Z].
Proof. star_step_solver. Qed.

(** Test takewhile - inputs: ['FUN',[4,3,2,1]] *)
Goal ⟨[], takewhile_2 (°EFun 1 (°ECall (˝VLit "erlang") (˝VLit ">") [˝VVar 0; ˝VLit (Integer 2%Z)])) (˝VCons (VLit 4%Z) (VCons (VLit 3%Z) (VCons (VLit 2%Z) (VCons (VLit 1%Z) (VNil)))))⟩
   -->* RValSeq [VCons (VLit 4%Z) (VCons (VLit 3%Z) (VNil))].
Proof. star_step_solver. Qed.

(** Test unzip - inputs: [[{1,a},{2,b}]] *)
Goal ⟨[], unzip_1 (˝VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VNil)))⟩
   -->* RValSeq [VTuple [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)); VCons (VLit "a") (VCons (VLit "b") (VNil))]].
Proof. star_step_solver. Qed.

(** Test unzip3 - inputs: [[{1,a,x},{2,b,y}]] *)
Goal ⟨[], unzip3_1 (˝VCons (VTuple [VLit 1%Z; VLit "a"; VLit "x"]) (VCons (VTuple [VLit 2%Z; VLit "b"; VLit "y"]) (VNil)))⟩
   -->* RValSeq [VTuple [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)); VCons (VLit "a") (VCons (VLit "b") (VNil)); VCons (VLit "x") (VCons (VLit "y") (VNil))]].
Proof. star_step_solver. Qed.

(** Test zip - inputs: [[1,2],[a,b]] *)
Goal ⟨[], zip_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit "a") (VCons (VLit "b") (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VNil))].
Proof. star_step_solver. Qed.

(** Test zip3 - inputs: [[1,2],[a,b],[x,y]] *)
Goal ⟨[], zip3_3 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit "a") (VCons (VLit "b") (VNil))) (˝VCons (VLit "x") (VCons (VLit "y") (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"; VLit "x"]) (VCons (VTuple [VLit 2%Z; VLit "b"; VLit "y"]) (VNil))].
Proof. star_step_solver. Qed.

(** Test zipwith - inputs: ['FUN',[1,2],[a,b]] *)
Goal ⟨[], zipwith_3 (°EFun 2 (°ETuple [˝VVar 0; ˝VVar 1])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VCons (VLit "a") (VCons (VLit "b") (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit 1%Z; VLit "a"]) (VCons (VTuple [VLit 2%Z; VLit "b"]) (VNil))].
Proof. star_step_solver. Qed.

(** Test map - inputs: ['FUN',[1,2]] *)
Goal ⟨[], map_2 (°EFun 1 (°ETuple [˝VLit "ok"; ˝VVar 0])) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil)))⟩
   -->* RValSeq [VCons (VTuple [VLit "ok"; VLit 1%Z]) (VCons (VTuple [VLit "ok"; VLit 2%Z]) (VNil))].
Proof. star_step_solver. Qed.

(** Test foldl - inputs: ['FUN',10,[1,2,3]] *)
Goal ⟨[], foldl_3 (°EFun 2 (°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 1; ˝VVar 0])) (˝VLit 10%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit 4%Z].
Proof. star_step_solver. Qed.

(** Test foldr - inputs: ['FUN',0,[1,2,3]] *)
Goal ⟨[], foldr_3 (°EFun 2 (°ECall (˝VLit "erlang") (˝VLit "-") [˝VVar 0; ˝VVar 1])) (˝VLit 0%Z) (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VNil))))⟩
   -->* RValSeq [VLit 2%Z].
Proof. star_step_solver. Qed.

(** Test seq - inputs: [1,5] *)
Goal ⟨[], seq_2 (˝VLit 1%Z) (˝VLit 5%Z)⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VCons (VLit 5%Z) (VNil)))))].
Proof. star_step_solver. Qed.

(** Test seq - inputs: [1,5,2] *)
Goal ⟨[], seq_3 (˝VLit 1%Z) (˝VLit 5%Z) (˝VLit 2%Z)⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 3%Z) (VCons (VLit 5%Z) (VNil)))].
Proof. star_step_solver. Qed.

(** Test append - inputs: [[[1,2],[3,4],[5,6]]] *)
Goal ⟨[], append_1 (˝VCons (VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (VCons (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VNil))) (VCons (VCons (VLit 5%Z) (VCons (VLit 6%Z) (VNil))) (VNil))))⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VCons (VLit 3%Z) (VCons (VLit 4%Z) (VCons (VLit 5%Z) (VCons (VLit 6%Z) (VNil))))))].
Proof. star_step_solver. Qed.

(** Test append - inputs: [[[a],[],[b],[]]] *)
Goal ⟨[], append_1 (˝VCons (VCons (VLit "a") (VNil)) (VCons (VNil) (VCons (VCons (VLit "b") (VNil)) (VCons (VNil) (VNil)))))⟩
   -->* RValSeq [VCons (VLit "a") (VCons (VLit "b") (VNil))].
Proof. star_step_solver. Qed.

(** Test append - inputs: [[]] *)
Goal ⟨[], append_1 (˝VNil)⟩
   -->* RValSeq [VNil].
Proof. star_step_solver. Qed.

(** Test sublist - inputs: [[a,b,c,d,e],3] *)
Goal ⟨[], sublist_2 (˝VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VCons (VLit "d") (VCons (VLit "e") (VNil)))))) (˝VLit 3%Z)⟩
   -->* RValSeq [VCons (VLit "a") (VCons (VLit "b") (VCons (VLit "c") (VNil)))].
Proof. star_step_solver. Qed.

(** Test sublist - inputs: [[1,2],5] *)
Goal ⟨[], sublist_2 (˝VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))) (˝VLit 5%Z)⟩
   -->* RValSeq [VCons (VLit 1%Z) (VCons (VLit 2%Z) (VNil))].
Proof. star_step_solver. Qed.

(** Test sublist - inputs: [[x,y,z],0] *)
Goal ⟨[], sublist_2 (˝VCons (VLit "x") (VCons (VLit "y") (VCons (VLit "z") (VNil)))) (˝VLit 0%Z)⟩
   -->* RValSeq [VNil].
Proof. star_step_solver. Qed.


(** Exception and value lists *)
Definition let_exception : Exp :=
  ELet 2 (EValues [˝VLit 10%Z; ˝VLit 0%Z])
    (ECall (˝VLit "erlang") (˝VLit "div") [˝VVar 0; ˝VVar 1]).

Goal exists ex, ⟨[], let_exception⟩ -->* RExc ex.
Proof. eexists. star_step_solver. Qed.
