Require Core_Erlang_Environment.

(** The side-effects of Core Erlang *)
Module Side_Effects.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Syntax.Syntax.

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

Definition nth_def {A : Type} (l : list A) (def : A) (i : nat) :=
match i with
| 0 => def
| S i' => nth i' l def
end.

Compute nth_def [4; 7; 8] 3 2 = 7.
Compute nth_def [ [(Input, [VLit (Atom "a"%string)] )];
                  [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] )]; 
                  [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] ); (Input, [VLit (Atom "c"%string)] )]] [] 2 = [(Input, [VLit (Atom "a"%string)] ); (Input, [VLit (Atom "b"%string)] )].

End Side_Effects.