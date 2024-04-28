Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Program.Wf.

Definition rem_fst (l : list nat) : list nat :=
  match l with
  | [] => []
  | hd :: tl => tl
  end.

Fixpoint clear (l : list nat) : list nat :=
  match l with
  | [] => []
  | hd :: tl => clear (rem_fst (hd :: tl))
  end.

Definition sub_list (l : list nat) : list nat :=
  match l with
  | [] => []
  | 0 :: tl => tl
  | S n :: tl => n :: tl
  end.

(*
Fixpoint total_sub (l : list nat) : list nat :=
  match l with
  | [] => []
  | hd :: tl => total_sub (sub_list (hd :: tl))
  end.
*)

Fixpoint mesure_sub_list (l : list nat) : nat :=
  match l with
  | [] => 0
  | n :: tl => n + (mesure_sub_list tl)
  end.

Program Fixpoint total_sub (l : list nat) {measure (mesure_sub_list l)} : list nat :=
    match l with
    | [] => []
    | hd :: tl => total_sub (sub_list (hd :: tl))
    end.

Inductive SomeThing :=
  | A : nat -> SomeThing
  | B : list SomeThing -> SomeThing.

Fixpoint mesure_something (s : SomeThing) : nat :=
  let mesure_something_list (l : list SomeThing) : nat :=
    fold_left Nat.add (map mesure_something l) 0
  in 
    match s with
    | A n => n
    | B l => mesure_something_list l
    end.

Definition Myfirst {A B C : Set} (tri : A * B * C) : A :=
  match tri with
  | (a, b, c) => a
  end.