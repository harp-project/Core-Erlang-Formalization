Require Core_Erlang_Environment.

(** The side-effects of Core Erlang *)
Module Side_Effects.

Export Core_Erlang_Syntax.Syntax.
Export Core_Erlang_Helpers.Helpers.

Import ListNotations.

Inductive SideEffectId : Set :=
| Input
| Output
.

Definition SideEffectList : Type := list (SideEffectId * list Value).

(* Definition concatn (def : SideEffectList) (l : list SideEffectList) (n : nat) : SideEffectList :=
   def ++ concat (firstn n l).


Compute concatn [(Input, [VLit (Atom "a"%string)] )] 
                [ [(Input, [VLit (Atom "a"%string)] )];
                  [(Input, [VLit (Atom "b"%string)] )]; 
                  [(Input, [VLit (Atom "c"%string)] )] ] 
                0. *)

Definition nth_def {A : Type} (l : list A) (def err : A) (i : nat) :=
match i with
| 0 => def
| S i' => nth i' l err
end.

Compute nth_def [4; 7; 8] 3 0 2 = 7.
Compute nth_def [ [(Input, [VLit (Atom "a"%string)] )];
                  [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] )]; 
                  [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] ); (Input, [VLit (Atom "c"%string)] )]] [] [] 2 = [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] )].

Import Omega.

Lemma nth_def_eq {A : Type} (l : list A) (i : nat) (e1 def err : A):
  nth_def (e1::l) def err (S i) = nth_def l e1 err i.
Proof.
  simpl. destruct i.
  * simpl. reflexivity.
  * simpl. reflexivity.
Qed.

Theorem last_nth_equal {A : Type} (l : list A) (def err : A) :
  last l def = nth_def l def err (length l).
Proof.
  induction l.
  * auto.
  * simpl. rewrite IHl. destruct l.
    - auto.
    - simpl. auto.
Qed.

End Side_Effects.