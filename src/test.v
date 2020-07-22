Require Core_Erlang_Tactics.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.

Import ListNotations.

Import Omega.

Set Ltac Backtrace.

Theorem foo {A B : Type} (a1 : A) (a2 : B) (l1 : list A) (l2 : list B):
length l1 = length l2
->
length (a1 :: l1) = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Goal exists l : list nat, 0 = length l.
Proof.
  Check length_zero_iff_nil.
  eexists.
  empty_list.
Qed.

Goal exists l : list nat, length l = 0.
Proof.
  Check length_zero_iff_nil.
  eexists.
  empty_list.
Qed.


Ltac element_list := 
idtac
.


(**
  Tactic thoughts:
  - first apply the matching derivation rule
  - unfold existential lists
  - solve subgoals recursively
  - cleanup with auto
*)

(* Ltac trial1 :=
first[eapply eval_case;
match goal with
| |- | _, _, _, _ | -e> | _, _, _ | => solve
| _ => idtac
end
; left_tac
 | eapply eval_case;
   match goal with
  | |- | _, _, _, _ | -e> | _, _, _ | => solve
  | _ => idtac
  end
; right_tac
]
with left_tac :=
match goal with
| |- _ < _ => apply foo2; left; reflexivity
| _ => idtac
end
;
reflexivity
with right_tac :=
match goal with
| |- _ < _ => apply foo2; right; eapply foo2; left_tac
| _ => idtac
end
;
reflexivity
. *)

(* Ltac solver :=
match goal with
| |- _ < _ => eapply foo2; left; reflexivity
| _ => idtac
end;
match goal with
| |- _ = _ => reflexivity
end
.

Goal
  exists i : nat, i < 3 /\ i = 2.
Proof.
  eexists. split;
  first[(solver) | idtac].
  apply foo2. 
Qed. *)

(* Ltac trial'' :=
eapply eval_case;
match goal with
| |- | _, _, _, _ | -e> | _, _, _ | => solve
| _ => idtac
end
;
left_tac2
with left_tac2 := 
match goal with
| |- _ < _ => eapply foo2; left; auto
| _ => idtac 123
end. *)

(* Ltac trial'' :=
first [
  match goal with
  | |- | _, _, ECase _ _ , _| -e> | _, _, _| =>
    eapply eval_case; trial''
  | _ =>
    match goal with
    | |- | _, _, _, _ | -e> | _, _, _ | => solve
    | |- _ < _ => eapply foo2; left; auto
    | _ => idtac
    end;
    reflexivity
  end
  | 
  match goal with
  | |- | _, _, ECase _ _ , _| -e> | _, _, _| =>
    eapply eval_case; trial''
  | _ =>
    match goal with
    | |- | _, _, _, _ | -e> | _, _, _ | => solve
    | |- _ < _ => eapply foo2; right; trial''
    | _ => idtac
    end;
    reflexivity
  end
]
. *)

(* Ltac trial' :=
eapply eval_case;
match goal with
| |- | _, _, _, _ | -e> | _, _, _ | => solve
| _ => idtac
end
;
left_tac
with left_tac :=
first 
[match goal with
| |- ?i < _ => instantiate (1 := 0); simpl; auto
| _ => idtac
end
; reflexivity | idtac 122
(* match goal with
| |- _ < _ => instantiate (1 := S ?i'); idtac 123
| _ => idtac
end  *)
]
. *)

Goal True. auto. Qed.

Ltac trial'' :=
eapply eval_case; 
match goal with
| |- | _, _, _, _ | -e> | _, _, _ | => solve
| _ => idtac
end;
left_tac
with left_tac :=
  match goal with
  | |- _ < _ => instantiate (1 := 0); left; auto
      (* eapply foo2; left; auto *)
  | _ => idtac 1
  end;
  simpl;
  match goal with
  | |- Some _ = None => fail 2
  | |- None = Some _ => fail 2
  | |- Some _ = Some _ => reflexivity
  | _ => idtac 2
  end
.


Goal
  |[(inl "X"%string, VEmptyTuple)], 0,
   ECase (EVar "X"%string)
         [(PLit (Integer 5), ELit (Atom "true"%string), ELit (Integer 5)); 
          (PLit (Integer 6), ELit (Atom "true"%string), ELit (Integer 6)); 
          (PVar "Z"%string, ELit (Atom "true"%string), EVar "Z"%string) ]
  , [] |
-e> 
  | 0, inl (VEmptyTuple), []|.
Proof.
  solve.
Qed.


Goal
exists x y z, |[], 0, ELetRec [(("f"%string, 1), (["X"%string],
   ECase (EVar "X"%string)
          [(PLit (Integer 0), ELit (Atom "true"%string), ELit (Integer 5));
           (PLit (Integer 1), ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 0)]);
           (PVar "A"%string, ELit (Atom "true"%string), EApp (EFunId ("f"%string, 1)) [ELit (Integer 1)])]
   ))]
   (ELet [("X"%string, EFun ["F"%string]
       (ELetRec [(("f"%string, 1), (["X"%string], ELit (Integer 0)))] 
          (EApp (EVar "F"%string) [ELit (Integer 2)])
       ))
     ]
    (EApp (EVar "X"%string) [EFunId ("f"%string, 1)])
   ), []|
-e> 
  |x, y, z|.
Proof.
  eexists ?[x]. eexists. eexists.
  Show x.
  solve.

Qed.

Goal 
  |[(inr ("Plus"%string, 2), 
       VClos [] [(0, ("Plus"%string, 2),
                     (["X"%string ; "Y"%string], ELit (Integer 3)))] 
                0 ["X"%string ; "Y"%string] 
                (ELit (Integer 3)))], 1,
   EApp (EFunId ("Plus"%string, 2)) [ELit (Integer 2); ELit (Integer 3)], []|
-e>
  |1, inl ((VLit (Integer 3))), []|.
Proof.
  solve.
Qed.

Goal
  | [], 0, ETuple [], [] | -e> |0, inl (VTuple []), [] |.
Proof.
  solve.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1)], [] | -e> |0, inl (VTuple [VLit (Integer 1)]), [] |.
Proof.
  solve.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1); ELit (Integer 2)], [] | 
-e> 
  |0, inl (VTuple [VLit (Integer 1); VLit (Integer 2)]), [] |.
Proof.
  solve.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1); ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)], [] | 
-e> 
  |0, inl (VTuple [VLit (Integer 1); VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]), [] |.
Proof.
  solve.
Qed.

Goal
  | [], 0, ETuple [ETuple [ELit (Integer 1); ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)]; ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)], [] | 
-e> 
  |0, inl (VTuple [VTuple [VLit (Integer 1); VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]; VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]), [] |.
Proof.
  solve.
Qed.

Goal
  | [], 0, ETuple [ETuple [ELit (Integer 1); ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)]; ELit (Integer 2); ELit (Integer 2); ETuple [ETuple [ELit (Integer 1); ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)]; ELit (Integer 2); ELit (Integer 2); ELit (Integer 2)]], [] | 
-e> 
  |0, inl (VTuple [VTuple [VLit (Integer 1); VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]; VLit (Integer 2); VLit (Integer 2); VTuple [VTuple [VLit (Integer 1); VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]; VLit (Integer 2); VLit (Integer 2); VLit (Integer 2)]]), [] |.
Proof.
  solve.
Qed.


Goal
  | [], 0, ECall "plus"%string [ELit (Integer 1); ELit (Integer 2)], [] | -e> |0, inl (VLit (Integer 3)), [] |.
Proof.
  solve.
Qed.

Goal 
  |[], 0,
   ELet [("X"%string, EFun [] (ELit (Integer 1))); 
         ("Y"%string, EFun [] (ELit (Integer 2))); 
         ("Z"%string, EFun [] (ELit (Integer 3)))]
     (EMap [(EVar "Z"%string, ELit (Integer 10)); 
            (EVar "X"%string, ELit (Integer 11));
            (EVar "Y"%string, ELit (Integer 12)); 
            (EVar "X"%string, ELit (Integer 13))])
  , []| 
-e> 
  | 3, inl (VMap [(VClos [] [] 0 [] (ELit (Integer 1)), VLit (Integer 13));
                  (VClos [] [] 1 [] (ELit (Integer 2)), VLit (Integer 12));
                  (VClos [] [] 2 [] (ELit (Integer 3)), VLit (Integer 10))])
  , []|.
Proof.
  solve.
  (* eapply eval_let; auto.
  * unfold_list.
  * unfold_list.
  * unfold_list.
  * intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5.
    all: simpl; apply eval_fun.
  * one_step_solver. *)
  
  (* eapply eval_map; auto.
    - simpl. auto.
    - unfold_list.
    - unfold_list.
    - unfold_list.
    - unfold_list.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      1-4: finishing_tactic.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      1-4: finishing_tactic.
    - reflexivity.
    - reflexivity.
    - auto. *)
Qed.

Goal 
exists n v eff,
  |[], 0,
   ELet [("X"%string, EFun [] (ELit (Integer 1))); 
         ("Y"%string, EFun [] (ELit (Integer 2))); 
         ("Z"%string, EFun [] (ELit (Integer 3)))]
     (EMap [(EVar "Z"%string, ELit (Integer 10)); 
            (EVar "X"%string, ELit (Integer 11));
            (EVar "Y"%string, ELit (Integer 12)); 
            (EVar "X"%string, ELit (Integer 13))])
  , []| 
-e> 
  | n, v , eff|.
Proof.
  eexists. eexists. eexists.
  solve.
Qed.