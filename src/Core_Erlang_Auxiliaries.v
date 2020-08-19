Require Core_Erlang_Side_Effects.

Module Auxiliaries.

Export Core_Erlang_Side_Effects.Side_Effects.

Import ListNotations.

(** For biuilt-in arithmetic calls *)
Definition eval_arith (fname : string) (params : list Value) :  ValueSequence + Exception :=
match fname, params with
(** addition *)
| "+"%string, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a + b))]
| "+"%string, [a; b]                               => inr (badarith (VCons a b))
(** subtraction *)
| "-"%string, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a - b))]
| "-"%string, [a; b]                               => inr (badarith (VCons a b))
(** unary minus *)
| "-"%string, [VLit (Integer a)]                   => inl [VLit (Integer (0 - a))]
| "-"%string, [a]                                  => inr (badarith a)
(** multiplication *)
| "*"%string, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a * b))]
| "*"%string, [a; b]                               => inr (badarith (VCons a b))
(** division *)
| "/"%string, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (a / b))]
| "/"%string, [a; b]                               => inr (badarith (VCons a b))
(** rem *)
| "rem"%string, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (Z.rem a b))]
| "rem"%string, [a; b]                               => inr (badarith (VCons a b))
(** div *)
| "div"%string, [VLit (Integer a); VLit (Integer b)] => inl [VLit (Integer (Z.div a b))]
| "div"%string, [a; b]                               => inr (badarith (VCons a b))
(** anything else *)
| _         , _                                    => inr (undef (VLit (Atom fname)))
end.

(** For IO maniputaion: *)
Definition eval_io (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((ValueSequence + Exception) * SideEffectList) :=
match fname, length params, params with
(** writing *)
| "fwrite"%string, 1, _ => (inl [ok]                                  , eff ++ [(Output, params)])
(** reading *)
| "fread"%string , 2, e => (inl [VTuple [ok; nth 1 params ErrorValue]], eff ++ [(Input, params)])
(** anything else *)
| _              , _, _ => (inr (undef (VLit (Atom fname)))           , eff)
end.

Definition eval_logical (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
(** logical and *)
| "and"%string, [a; b] => 
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => inl [ffalse]
   | VLit (Atom "true") , VLit (Atom "false")   => inl [ffalse]
   | VLit (Atom "false"), VLit (Atom "false")   => inl [ffalse]
   | _                         , _              => inr (badarg (VCons a b))
   end
(** logical or *)
| "or"%string, [a; b] =>
   match a, b with
   | VLit (Atom "true") , VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "true")    => inl [ttrue]
   | VLit (Atom "true") , VLit (Atom "false")   => inl [ttrue]
   | VLit (Atom "false"), VLit (Atom "false")   => inl [ffalse]
   | _                         , _              => inr (badarg (VCons a b))
   end
(** logical not *)
| "not"%string, [a] =>
   match a with
   | VLit (Atom "true")  => inl [ffalse]
   | VLit (Atom "false") => inl [ttrue]
   | _                   => inr (badarg a)
   end
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_equality (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
| "=="%string,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| "=:="%string, [v1; v2] => if Value_eqb v1 v2 then inl [ttrue] else inl [ffalse]
| "/="%string,  [v1; v2] (* TODO: with floats, this one should be adjusted *)
| "=/="%string, [v1; v2] => if Value_eqb v1 v2 then inl [ffalse] else inl [ttrue]
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint is_shallow_proper_list (v : Value) : bool :=
match v with
| VNil => true
| VCons x y => is_shallow_proper_list y
| _ => false
end.

Fixpoint eval_append (v1 v2 : Value) : ValueSequence + Exception :=
match v1, v2 with
| VNil, VNil => inl [VNil]
| VNil, VCons x y => inl [VCons x y]
| VCons x y, VNil => inl [VCons x y]
| VCons x y, VCons x' y' =>
  match y with
  | VCons z w => match eval_append y (VCons x' y') with
                 | inr ex => inr ex
                 | inl [res] => inl [VCons x res]
                 | _ => inr (badarg (VCons v1 v2))
                 end
  | VNil      => inl [VCons x (VCons x' y')]
  | z         => inr (badarg (VCons v1 v2))
  end
| _, _ => inr (badarg (VCons v1 v2))
end.

Fixpoint subtract_elem (v1 v2 : Value) : Value :=
match v1 with
| VNil => VNil
| VCons x y =>
  match y with
  | VNil => if Value_eqb x v2 then VNil else VCons x y
  | VCons z w => if Value_eqb x v2 then y else VCons x (subtract_elem y v2)
  | z => if Value_eqb x v2 then VCons z VNil else if Value_eqb z v2 then VCons x VNil else VCons x y
  end
| _ => ErrorValue
end.

Fixpoint eval_subtract (v1 v2 : Value) : ValueSequence + Exception :=
if andb (is_shallow_proper_list v1) (is_shallow_proper_list v2) then
  match v1, v2 with
  | VNil, VNil => inl [VNil]
  | VNil, VCons x y => inl [VNil]
  | VCons x y, VNil => inl [VCons x y]
  | VCons x y, VCons x' y' => 
     match y' with
     | VNil => inl [subtract_elem (VCons x y) x']
     | VCons z w => eval_subtract (subtract_elem (VCons x y) x') y'
     | z => inl [subtract_elem (subtract_elem (VCons x y) x') z]
     end
  | _        , _         => inr (badarg (VCons v1 v2))
  end
else
  inr (badarg (VCons v1 v2)).

Definition eval_transform_list (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
| "++"%string, [v1; v2] => eval_append v1 v2
| "--"%string, [v1; v2] => eval_subtract v1 v2
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition transform_tuple (v : Value) : ValueSequence + Exception :=
match v with
| VTuple l => inl [((fix unfold_list l :=
                   match l with
                   | [] => VNil
                   | x::xs => VCons x (unfold_list xs)
                   end) l)]
| _        => inr (badarg v)
end.

Fixpoint transform_list (v : Value) : list Value + Exception :=
match v with
| VNil      => inl []
| VCons x y => match y with
               | VNil => inl [x]
               | VCons z w => match (transform_list y) with
                              | inr ex => inr ex
                              | inl res => inl (x::res)
                              end
               | z => inr (badarg v)
               end
| _         => inr (badarg v)
end.

Definition eval_list_tuple (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
| "tuple_to_list"%string, [v] => transform_tuple v
| "list_to_tuple"%string, [v] => match (transform_list v) with
                                 | inr ex => inr ex
                                 | inl l => inl [VTuple l]
                                 end
| _                     , _   => inr (undef (VLit (Atom fname)))
end.

Definition eval_cmp (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
| "<"%string,  [v1; v2] => if Value_ltb v1 v2 then inl [ttrue] else inl [ffalse]
| "=<"%string, [v1; v2] => if orb (Value_ltb v1 v2) (Value_eqb v1 v2) 
                           then inl [ttrue] else inl [ffalse]
| ">"%string,  [v1; v2] => if Value_ltb v2 v1 then inl [ttrue] else inl [ffalse]
| ">="%string, [v1; v2] => if orb (Value_ltb v2 v1) (Value_eqb v1 v2) 
                           then inl [ttrue] else inl [ffalse]
(** anything else *)
| _ , _ => inr (undef (VLit (Atom fname)))
end.

Definition eval_length (params : list Value) : ValueSequence + Exception :=
match params with
| [v] => let res :=
          (fix len val := match val with
                         | VNil => inl Z.zero
                         | VCons x y => let res := len y in
                                          match res with
                                          | inl n => inl (Z.add 1 n)
                                          | inr _ => res
                                          end
                         | _ => inr (badarg v)
                         end) v in
        match res with
        | inl n => inl [VLit (Integer n)]
        | inr ex => inr ex
        end
| _ => inr (undef (VLit (Atom "length")))
end.

Definition eval_tuple_size (params : list Value) : ValueSequence + Exception :=
match params with
| [VTuple l] => inl [VLit (Integer (Z.of_nat (length l)))]
| [v] => inr (badarg v)
| _ => inr (undef (VLit (Atom "tuple_size")))
end.

Definition eval_hd_tl (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
| "hd"%string, [VCons x y] => inl [x]
| "hd"%string, [v] => inr (badarg v)
| "tl"%string, [VCons x y] => inl [y]
| "tl"%string, [v] => inr (badarg v)
| _, _ => inr (undef (VLit (Atom fname)))
end.

Fixpoint replace_nth_error {A : Type} (l : list A) (i : nat) (e : A) : option (list A) :=
match i, l with
| 0, x::xs => Some (e::xs)
| _, [] => None
| S n, x::xs => match (replace_nth_error xs n e) with
               | None => None
               | Some l' => Some (x::l')
               end
end.

Definition eval_elem_tuple (fname : string) (params : list Value) : ValueSequence + Exception :=
match fname, params with
| "element"%string, [VLit (Integer i); VTuple l] =>
    match i with
    | Z.pos p => match nth_error l (pred (Pos.to_nat p)) with
                 | None   => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
                 | Some v => inl [v]
                 end
    | _       => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
    end
| "element"%string, [v1; v2] => inr (badarg (VCons v1 v2))
| "setelement"%string, [VLit (Integer i); VTuple l; val] =>
    match i with
    | Z.pos p => match replace_nth_error l (pred (Pos.to_nat p)) val with
                 | None    => inr (badarg (VCons (VLit (Integer i)) (VCons (VTuple l) val)))
                 | Some l' => inl [VTuple l']
                 end
    | _       => inr (badarg (VCons (VLit (Integer i)) (VTuple l)))
    end
| "setelement"%string, [v1; v2; v3] => inr (badarg (VCons v1 (VCons v2 v3)))
| _, _ => inr (undef (VLit (Atom fname)))
end.

(* TODO: Always can be extended, this function simulates inter-module calls *)
Definition eval (fname : string) (params : list Value) (eff : SideEffectList) 
   : ((ValueSequence + Exception) * SideEffectList) :=
match fname with
| "+"%string      | "-"%string
| "*"%string      | "/"%string
| "rem"%string    | "div"%string   => (eval_arith fname params, eff)
| "fwrite"%string | "fread"%string => eval_io fname params eff
| "and"%string    | "or"%string
| "not"%string                     => (eval_logical fname params, eff)
| "=="%string     | "=:="%string
| "/="%string     | "=/="%string   => (eval_equality fname params, eff)
| "++"%string     | "--"%string    => (eval_transform_list fname params, eff)
| "tuple_to_list"%string
| "list_to_tuple"%string           => (eval_list_tuple fname params, eff)
| "<"%string      | ">"%string 
| "=<"%string     | ">="%string    => (eval_cmp fname params, eff)
| "length"%string                  => (eval_length params, eff)
| "tuple_size"%string              => (eval_tuple_size params, eff)
| "hd"%string     | "tl"%string    => (eval_hd_tl fname params, eff)
| "element"%string
| "setelement"%string              => (eval_elem_tuple fname params, eff)
(** anything else *)
| _                                => (inr (undef (VLit (Atom fname))), eff)
end.

End Auxiliaries.

Section Tests.

Import Auxiliaries.
Import ListNotations.

(** Tests *)

Compute (eval "+" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl [VLit (Integer 3)], []).
Compute (eval "-" [VLit (Integer 1); VLit (Integer 2)]) [] = (inl [VLit (Integer (-1))], []).
Compute (eval "+" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VCons (VLit (Atom "foo")) (VLit (Integer 2)))), []).
Compute (eval "+" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VCons (VLit (Integer 2)) (VLit (Atom "foo")))), []).
Compute (eval "-" [VLit (Atom "foo"); VLit (Integer 2)]) [] 
    = (inr (badarith (VCons (VLit (Atom "foo")) (VLit (Integer 2)))), []).
Compute (eval "-" [VLit (Integer 1); VLit (Atom "foo")]) [] 
    = (inr (badarith (VCons (VLit (Integer 2)) (VLit (Atom "foo")))), []).
Compute (eval "-" [VLit (Atom "foo")]) [] 
    = (inr (badarith (VLit (Atom "foo"))), []).
Compute (eval "+" [VLit (Atom "foo")]) [] 
    = (inr (undef (VLit (Atom "+"))), []).

Compute (eval "not" [ttrue]) [] = (inl [ffalse], []).
Compute (eval "not" [ffalse]) [] = (inl [ttrue], []).
Compute (eval "not" [VLit (Integer 5)]) [] = (inr (badarg (VLit (Integer 5))), []).
Compute (eval "not" [VLit (Integer 5); VEmptyTuple]) [] = (inr (undef (VLit (Atom "not"))), []).

Compute (eval "and" [ttrue; ttrue]) [] = (inl [ttrue], []).
Compute (eval "and" [ttrue; ffalse]) [] = (inl [ffalse], []).
Compute (eval "and" [ffalse; ttrue]) [] = (inl [ffalse], []).
Compute (eval "and" [ffalse; ffalse]) [] = (inl [ffalse], []).
Compute (eval "and" [ttrue; VEmptyTuple]) [] = (inr (badarg (VCons (VLit (Atom "true")) (VTuple []))), []).
Compute (eval "and" [ttrue]) [] = (inr (undef (VLit (Atom "and"))), []).

Compute (eval "or" [ttrue; ttrue]) [] = (inl [ttrue], []).
Compute (eval "or" [ttrue; ffalse]) [] = (inl [ttrue], []).
Compute (eval "or" [ffalse; ttrue]) [] = (inl [ttrue], []).
Compute (eval "or" [ffalse; ffalse]) [] = (inl [ffalse], []).
Compute (eval "or" [ttrue; VEmptyTuple]) [] = (inr (badarg (VCons (VLit (Atom "true")) (VTuple []))), []).
Compute (eval "or" [ttrue]) [] = (inr (undef (VLit (Atom "or"))), []).

Compute (eval "fwrite" [ttrue]) [] = (inl [ok], [(Output, [ttrue])]).
Compute (eval "fwrite" [VMap [(ttrue, ttrue)]]) [] = (inl [ok], [(Output, [VMap [(ttrue, ttrue)]])]).
Compute (eval "fwrite" []) [] = (inr (undef (VLit (Atom "fwrite"))), []).

Compute (eval "fread" [VLit (Atom "foo.txt"); ttrue]) [] = 
   (inl [VTuple [ok; ttrue]], [(Input, [VLit (Atom "foo.txt"); ttrue])]).
Compute (eval "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]]) [] = 
   (inl [VTuple [ok; VMap [(ttrue, ttrue)]]], [(Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])]).
Compute (eval "fread" []) [] = (inr (undef (VLit (Atom "fread"))), []).

Compute (eval "==" [ttrue; ttrue]) [] = (inl [ttrue], []).
Compute (eval "==" [ttrue; ffalse]) [] = (inl [ffalse], []).
Compute (eval "==" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl [ffalse], []).
Compute (eval "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ffalse], []).
Compute (eval "==" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).

Compute (eval "/=" [ttrue; ttrue]) [] = (inl [ffalse], []).
Compute (eval "/=" [ttrue; ffalse]) [] = (inl [ttrue], []).
Compute (eval "/=" [VClos [] [] 1 [] EEmptyMap; ttrue]) [] = (inl [ttrue], []).
Compute (eval "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval "/=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).
Compute (eval "/=" [ttrue]) [] = (inr (undef (VLit (Atom "/="))), []).

Definition l1 : Value := VCons ttrue VNil.
Definition l2 : Value := VCons ttrue ttrue.
Definition l3 : Value := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Value := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Value := VCons ttrue (VCons ttrue ttrue).

Compute (eval "++" [ttrue; ttrue]) [] = (inr (badarg _), []).
Compute (eval "++" [l1; l1]) [].
Compute (eval "++" [l1; l2]) [].
Compute (eval "++" [l1; l3]) [].
Compute (eval "++" [l3; l3]) [].

Compute (eval "--" [ttrue; ttrue]) [] = (inr (badarg _), []).
Compute (eval "--" [l1; l1]) [].
Compute (eval "--" [l1; l2]) [].
Compute (eval "--" [l1; l3]) [].
Compute (eval "--" [l3; l3]) [].
Compute (eval "--" [l3; l1]) [].
Compute (eval "--" [l4; l4]) [].

Compute (eval "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] []).
Compute (eval "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] []).
Compute (eval "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] []).
Compute (eval "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] []).
Compute (eval "tuple_to_list" [ttrue] []).

Compute (eval "list_to_tuple" [l1] []).
Compute (eval "list_to_tuple" [l2] []).
Compute (eval "list_to_tuple" [l3] []).
Compute (eval "list_to_tuple" [l4] []).
Compute (eval "list_to_tuple" [l5] []).

Compute (eval "<" [ttrue; ttrue]) [] = (inl [ffalse], []).
Compute (eval "<" [ttrue; ffalse]) [] = (inl [ffalse], []).
Compute (eval "<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl [ttrue], []).
Compute (eval "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval "<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).

Compute (eval "=<" [ttrue; ttrue]) [] = (inl [ttrue], []).
Compute (eval "=<" [ttrue; ffalse]) [] = (inl [ffalse], []).
Compute (eval "=<" [VClos [] [] 1 [] EEmptyMap; VEmptyMap]) [] = (inl [ttrue], []).
Compute (eval "=<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 2 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval "=<" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).

Compute (eval ">" [ttrue; ttrue]) [] = (inl [ffalse], []).
Compute (eval ">" [ffalse; ttrue]) [] = (inl [ffalse], []).
Compute (eval ">" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval ">" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval ">" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ffalse], []).

Compute (eval ">=" [ttrue; ttrue]) [] = (inl [ttrue], []).
Compute (eval ">=" [ffalse; ttrue]) [] = (inl [ffalse], []).
Compute (eval ">=" [VEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval ">=" [VClos [] [] 2 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).
Compute (eval ">=" [VClos [] [] 1 [] EEmptyMap; VClos [] [] 1 [] EEmptyMap]) [] = (inl [ttrue], []).

End Tests.