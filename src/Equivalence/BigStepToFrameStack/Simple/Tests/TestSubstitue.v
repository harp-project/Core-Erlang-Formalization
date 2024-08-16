From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Import Convert.
From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Import Substitute.
From CoreErlang.BigStep Require Import BigStep.
From CoreErlang.BigStep Require Import Environment.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
From CoreErlang.Equivalence.BigStepToFrameStack Require Import EraseNames.

Require Import Coq.Lists.List.
Require Import Coq.Program.Wf.
Require Import stdpp.list.

Import BigStep.
Import ListNotations.

Open Scope string_scope.

  (*
    env = []
    x
    x
  *)
  Lemma test_subst_env_1 : 
    subst_env 10 
              [] 
              (EVar "x") 
    = 
    EVar "x".
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1]
    x
    1
  *)
  Lemma test_subst_env_2 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1))] 
              (EVar "x") 
    = 
    ELit (Integer 1).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1;
           y = 2;
           z = fun(x) -> x , y]
    <x , y , z>
    <1 , 2 , fun(x) -> x , y>
  *)
  Lemma test_subst_env_3 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1));
               (inl "y" , VLit (Integer 2));
               (inl "z" , VClos [] 
                                [] 
                                0 
                                ["x"] 
                                (EValues [EVar "x"; EVar "y"]) 
                                None)]
              (EValues [EVar "x"; EVar "y"; EVar "z"]) 
    = 
    (EValues [ELit (Integer 1); 
              ELit (Integer 2); 
              EFun ["x"] (EValues [EVar "x"; EVar "y"])]).
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1;
           y = 2;
           z = fun(x) -> x , y]
    x , y , app z [x]
    1 , 2 , app (fun(x) -> x , y) [1]
  *)
  Lemma test_subst_env_4 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1));
               (inl "y" , VLit (Integer 2));
               (inl "z" , VClos [] 
                                [] 
                                0 
                                ["x"] 
                                (EValues [EVar "x"; EVar "y"]) 
                                None)]
              (EValues [EVar "x"; EVar "y"; EApp (EVar "z") [EVar "x"]]) 
    = 
    EValues [ELit (Integer 1); 
             ELit (Integer 2); 
             EApp (EFun ["x"] 
                        (EValues [EVar "x"; EVar "y"])) 
                  [ELit (Integer 1)]].
  Proof.
    cbn. reflexivity.
  Qed.



  (*
    env = [x = 1;
           y = 2;
           z/1 = fun(x) -> x , y]
    x , y , app z/1 [x]
    1 , 2 , app (fun(x) -> x , y) [1]
  *)
  Lemma test_subst_env_5 : 
    subst_env 10 
              [(inl "x" , VLit (Integer 1));
               (inl "y" , VLit (Integer 2));
               (inr ("z" , 1) , VClos [] 
                                      [] 
                                      0 
                                      ["x"] 
                                      (EValues [EVar "x"; EVar "y"]) 
                                      None)]
              (EValues [EVar "x"; EVar "y"; EApp (EFunId ("z" , 1)) [EVar "x"]]) 
    = 
    EValues [ELit (Integer 1); 
             ELit (Integer 2); 
             EApp (EFun ["x"] 
                        (EValues [EVar "x"; EVar "y"])) 
                  [ELit (Integer 1)]].
  Proof.
    cbn. reflexivity.
  Qed.
