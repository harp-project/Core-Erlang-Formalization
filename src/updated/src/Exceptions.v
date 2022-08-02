Require Export ExpSyntax.

(** Exception representation *)
Inductive ExceptionClass : Type :=
| Error | Throw | Exit.

(** Exception class to value converter *)
Definition exclass_to_value (ex : ExceptionClass) : ValueExpression :=
match ex with
| Error => VLit (Atom "error"%string)
| Throw => VLit (Atom "throw"%string)
| Exit => VLit (Atom "exit"%string)
end.

Definition pp_exception_class (cl : ExceptionClass) : string :=
match cl with
| Error => "error"
| Throw => "throw"
| Exit  => "exit"
end.


(** Exception class, 1st Value : cause, 2nd Value : further details *)
Definition Exception : Type := ExceptionClass * ValueExpression * ValueExpression.

(*
Definition pp_exception (e : Exception) : string :=
match e with
| (class, reason, info) => "{" ++ pp_exception_class class  ++ "," ++
                                  pretty_print_value reason ++ "," ++
                                  pretty_print_value info   ++ "}"
end.
*)