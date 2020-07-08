Require Import Core_Erlang_Semantics.

Import Core_Erlang_Environment.Environment.
Import Core_Erlang_Helpers.Helpers.
Import Core_Erlang_Syntax.Syntax.
Import Core_Erlang_Side_Effects.Side_Effects.
Import Core_Erlang_Semantics.Semantics.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Ltac empty_list :=
simpl;
match goal with
| |- 0 = length ?l => instantiate (1 := []); auto
end.

Ltac element_list := 
idtac
.

Goal
  | [], 0, ETuple [], [] | -e> |0, inl (VTuple []), [] |.
Proof.
  eapply eval_tuple; auto.
  * empty_list.
  * empty_list.
  * intros. inversion H.
  * reflexivity.
Qed.

Import Omega.

Theorem alma {A B : Type} (a1 : A) (a2 : B) (l1 : list A) (l2 : list B):
length l1 = length l2
->
length (a1 :: l1) = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Theorem alma2 {B : Type} (a2 : B) (n : nat) (l2 : list B):
n = length l2
->
S n = length (a2 :: l2).
Proof.
  intros. simpl. rewrite H. auto.
Qed.

Goal
  | [], 0, ETuple [ELit (Integer 1)], [] | -e> |0, inl (VTuple [VLit (Integer 1)]), [] |.
Proof.
  eapply eval_tuple with (eff := [[]]); auto.
  * eapply alma. empty_list.
  * intros. inversion H.
    - unfold concatn. simpl. apply eval_lit.
    - inversion H1.
  * auto.
Qed.

Goal
  | [], 0, ECall "plus"%string [ELit (Integer 1); ELit (Integer 2)], [] | -e> |0, inl (VLit (Integer 3)), [] |.
Proof.
  eapply eval_call with (eff := [[];[]]); auto.
  * eapply alma. eapply alma. empty_list.
  * eapply alma. eapply alma. empty_list.
  * intros. inversion H. 2: inversion H1.
    - unfold concatn. simpl. apply eval_lit.
    - unfold concatn. simpl. apply eval_lit.
    - inversion H3.
  * simpl. reflexivity.
  * reflexivity.
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
  eapply eval_let with (eff := [[];[];[]]); auto.
  * repeat (eapply alma). empty_list.
  * repeat (eapply alma). empty_list.
  * intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5.
    all: simpl; apply eval_fun.
  * reflexivity.
  * eapply eval_map with (eff := [[];[];[];[];[];[];[];[]]); auto.
    - simpl. auto.
    - repeat (eapply alma). empty_list.
    - repeat (eapply alma). empty_list.
    - simpl. repeat (eapply alma2). empty_list.
    - shelve.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      1-4: unfold concatn; simpl; apply eval_var; simpl; reflexivity.
    - intros. inversion H. 2: inversion H1. 3: inversion H3. 4: inversion H5. 5: inversion H7.
      1-4: unfold concatn; simpl; apply eval_lit.
    - reflexivity.
    - reflexivity.
    Unshelve.
    reflexivity.
Qed.