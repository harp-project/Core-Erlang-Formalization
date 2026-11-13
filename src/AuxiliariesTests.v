From CoreErlang Require Export Auxiliaries.
Import Notations.

Goal eval "erlang" "+" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer (-1))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "+" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "+" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "-" [VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "-"); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "+" [VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "+"); VLit (Atom "foo")])), None).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal eval "erlang" "bsl" [VLit (Integer 10); VLit (Integer 20)] = Some (RValSeq [VLit (Integer 10485760)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Integer 10); VLit (Integer 20)] = Some (RValSeq [VLit (Integer 0)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsl" [VLit (Atom "foo"); VLit (Integer 2)] 
    = Some (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsl" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bsl"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bsr"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bsl" [VLit (Atom "foo")]
    = Some (RExc (undef (VLit (Atom "bsl"))), None).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.
Goal eval "erlang" "bsr" [VLit (Atom "foo")]
    = Some (RExc (undef (VLit (Atom "bsr"))), None).
Proof. unfold eval, eval_arith. simpl. reflexivity. Qed.

Goal eval "erlang" "band" [VLit (Integer 12); VLit (Integer 10)] = Some (RValSeq [VLit (Integer 8)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Integer (-1)); VLit (Integer 5)] = Some (RValSeq [VLit (Integer 5)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "band"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "band"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "band" [VLit (Integer 1)]
    = Some (RExc (undef (VLit (Atom "band"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "bor" [VLit (Integer 12); VLit (Integer 10)] = Some (RValSeq [VLit (Integer 14)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Integer (-8)); VLit (Integer 3)] = Some (RValSeq [VLit (Integer (-5))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "bor"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bor"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bor" [VLit (Integer 1)]
    = Some (RExc (undef (VLit (Atom "bor"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "bxor" [VLit (Integer 12); VLit (Integer 10)] = Some (RValSeq [VLit (Integer 6)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Integer (-1)); VLit (Integer 5)] = Some (RValSeq [VLit (Integer (-6))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Atom "foo"); VLit (Integer 2)]
    = Some (RExc (badarith (VTuple [VLit (Atom "bxor"); VLit (Atom "foo"); VLit (Integer 2)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Integer 1); VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bxor"); VLit (Integer 1); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bxor" [VLit (Integer 1)]
    = Some (RExc (undef (VLit (Atom "bxor"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "bnot" [VLit (Integer 5)] = Some (RValSeq [VLit (Integer (-6))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bnot" [VLit (Integer (-1))] = Some (RValSeq [VLit (Integer 0)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bnot" [VLit (Atom "foo")]
    = Some (RExc (badarith (VTuple [VLit (Atom "bnot"); VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "bnot" [VLit (Integer 1); VLit (Integer 2)]
    = Some (RExc (undef (VLit (Atom "bnot"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "not" [ttrue] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "not" [ffalse] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "not" [VLit (Integer 5)] = Some (RExc (badarg (VTuple [VLit (Atom "not"); VLit (Integer 5)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "not" [VLit (Integer 5); VEmptyTuple] = Some (RExc (undef (VLit (Atom "not"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "and" [ttrue; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ttrue; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ffalse; ttrue] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ffalse; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "and" [ttrue; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "and"); ttrue; VTuple []])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "and" [ttrue]) = Some (RExc (undef (VLit (Atom "and"))), None). Proof. reflexivity. Qed.

Goal eval "erlang" "or" [ttrue; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ttrue; ffalse] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ffalse; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ffalse; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ttrue; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "or"); ttrue; VTuple []])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "or" [ttrue] = Some (RExc (undef (VLit (Atom "or"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "xor" [ttrue; ttrue] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ttrue; ffalse] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ffalse; ttrue] = Some (RValSeq [ttrue], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ffalse; ffalse] = Some (RValSeq [ffalse], None). Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ttrue; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "xor"); ttrue; VTuple []])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ffalse; VEmptyTuple] = Some (RExc (badarg (VTuple [VLit (Atom "xor"); ffalse; VTuple []])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [VEmptyTuple; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "xor"); VTuple []; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "xor" [ttrue] = Some (RExc (undef (VLit (Atom "xor"))), None).
Proof. reflexivity. Qed.

Goal eval "io" "fwrite" [ttrue] = Some (RValSeq [ok], (Some (Output, [ttrue]))).
Proof. reflexivity. Qed.
Goal eval "io" "fwrite" [VMap [(ttrue, ttrue)]] = Some (RValSeq [ok], Some (Output, [VMap [(ttrue, ttrue)]])).
Proof. reflexivity. Qed.
Goal eval "io" "fwrite" [] = Some (RExc (undef (VLit (Atom "fwrite"))), None).
Proof. reflexivity. Qed.

Goal eval "io" "fread" [VLit (Atom "foo.txt"); ttrue] = Some 
   (RValSeq [VTuple [ok; ttrue]], Some (Input, [VLit (Atom "foo.txt"); ttrue])).
Proof. reflexivity. Qed.
Goal eval "io" "fread" [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]] = Some 
   (RValSeq [VTuple [ok; VMap [(ttrue, ttrue)]]], Some (Input, [VLit (Atom "foo.txt"); VMap [(ttrue, ttrue)]])).
Proof. reflexivity. Qed.
Goal eval "io" "fread" [] = Some (RExc (undef (VLit (Atom "fread"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "==" [ttrue; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [ttrue; ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [VClos [] 1 0 EEmptyMap; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "==" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "/=" [ttrue; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [ttrue; ffalse] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed. 
Goal eval "erlang" "/=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "/=" [ttrue] = Some (RExc (undef (VLit (Atom "/="))), None).
Proof. reflexivity. Qed.

Definition l1 : Val := VCons ttrue VNil.
Definition l2 : Val := VCons ttrue ttrue.
Definition l3 : Val := VCons (VCons ttrue ttrue) ttrue.
Definition l4 : Val := VCons ttrue (VCons ttrue (VCons ttrue VNil)).
Definition l5 : Val := VCons ttrue (VCons ttrue ttrue).

Goal eval "erlang" "++" [ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "++"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l1; l1] = Some (RValSeq [VCons ttrue (VCons ttrue VNil)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l1; l2] = Some
  (RValSeq [VCons ttrue (VCons ttrue ttrue)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l1; l3] = Some
  (RValSeq [VCons ttrue (VCons (VCons ttrue ttrue) ttrue)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "++" [l3; l3] = Some
  (RExc (badarg (VTuple [VLit (Atom "++"); VCons (VCons ttrue ttrue) ttrue; VCons (VCons ttrue ttrue) ttrue])), None).
Proof.  unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal eval "erlang" "++" [l1; ErrorVal] = Some (RValSeq [VCons ttrue ErrorVal], None).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.

Goal eval "lists" "split" [VLit (Integer 0); VNil] = Some (RValSeq [VTuple [VNil; VNil]], None).
Proof. reflexivity. Qed.
Goal eval "lists" "split" [VLit (Integer 0); VCons ttrue (VCons ttrue VNil)] = Some (RValSeq [VTuple [VNil; VCons ttrue (VCons ttrue VNil)]], None).
Proof. cbn. reflexivity. Qed.
Goal exists x, (eval "lists" "split" [VLit (Integer 4); VCons ttrue (VCons ttrue VNil)]) = Some (RExc (badarg x), None).
Proof. eexists. reflexivity. Qed.
Goal eval "lists" "split" [VLit (Integer 4); VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue VNil)))))] = Some (RValSeq [VTuple [VCons ttrue (VCons ttrue (VCons ttrue (VCons ttrue VNil))); VCons ttrue (VCons ttrue VNil)]], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "--" [ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "--"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l1; l1] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l1; l2] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons ttrue ttrue])), None).
Proof. unfold eval, eval_transform_list. simpl. reflexivity. Qed.
Goal eval "erlang" "--" [l1; l3] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons ttrue VNil; VCons (VCons ttrue ttrue) ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l3; l3] = Some
  (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue;
                        VCons (VCons ttrue ttrue) ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l3; l1] =
  Some (RExc (badarg (VTuple [VLit (Atom "--"); VCons (VCons ttrue ttrue) ttrue; VCons ttrue VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [l4; l4] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "--" [VCons (VLit (Integer 0)) (VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) (VCons VNil VNil))));
  VCons VNil (VCons (VLit (Integer 0)) VNil)
]
=
  Some (RValSeq [(VCons (VLit (Atom "HIGH")) (VCons ffalse (VCons (VLit (Atom "FERTILE")) VNil)))], None).
Proof. unfold eval, eval_transform_list, eval_subtract. simpl. reflexivity. Qed.

Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; ttrue; l1]] =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l5; l1]] =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue (VCons ttrue ttrue)) 
                                 (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; l3; ttrue; l1]] =
  Some (RValSeq [VCons ttrue (VCons (VCons (VCons ttrue ttrue) ttrue) (VCons ttrue (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [VTuple [ttrue; ttrue; l2; l1]] =
  Some (RValSeq [VCons ttrue (VCons ttrue (VCons (VCons ttrue ttrue) (VCons (VCons ttrue VNil) VNil)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_to_list" [ttrue] = Some
  (RExc (badarg (VTuple [VLit (Atom "tuple_to_list"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "list_to_tuple" [l1] = Some (RValSeq [VTuple [VLit (Atom "true")]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l2] =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons ttrue ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l3] =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); VCons (VCons ttrue ttrue) ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l4] =
  Some (RValSeq [VTuple [VLit (Atom "true"); VLit (Atom "true"); VLit (Atom "true")]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_tuple" [l5] =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_tuple"); l5])), None).
Proof. cbn. reflexivity. Qed.

Definition hello_list : Val :=
  VCons (VLit 104%Z) (VCons (VLit 101%Z) (VCons (VLit 108%Z) (VCons (VLit 108%Z) (VCons (VLit 111%Z) (VNil))))).
Definition not_a_char_list : Val := VCons (VLit (Atom "hello")) (VNil).
Definition improper_l1 : Val := VCons (VCons (VLit 104%Z) (VLit 101%Z)) (VLit 108%Z).
Definition improper_l2 : Val := VCons (VLit 104%Z) (VCons (VLit 101%Z) (VLit 108%Z)).

Goal (eval "erlang" "list_to_atom" [VNil]) = Some (RValSeq [VLit (Atom "")], Some (AtomCreation, [VLit (Atom "")])).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [hello_list]) = Some (RValSeq [VLit (Atom "hello")], Some (AtomCreation, [VLit (Atom "hello")])).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [not_a_char_list]) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); not_a_char_list])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [improper_l1]) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); improper_l1])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "list_to_atom" [improper_l2]) =
  Some (RExc (badarg (VTuple [VLit (Atom "list_to_atom"); improper_l2])), None).
Proof. reflexivity. Qed.

Goal (eval "erlang" "list_to_atom" [VNil]) = Some (RValSeq [VLit (Atom "")], Some (AtomCreation, [VLit (Atom "")])).
Proof. reflexivity. Qed.
Goal (eval "erlang" "integer_to_list" [VLit (Integer 10)]) = Some
  (RValSeq [VCons (VLit 49%Z) (VCons (VLit 48%Z) VNil)], None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "integer_to_list" [VLit (Atom "apple")]) = Some
  (RExc (badarg (VTuple [VLit "integer_to_list"%string; VLit "apple"%string])), None).
Proof. reflexivity. Qed.
Goal (eval "erlang" "integer_to_list" []) = Some
  (RExc (undef (VLit "integer_to_list"%string)), None).
Proof. reflexivity. Qed.

Goal (eval "erlang" "<" [ttrue; ttrue]) = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [ttrue; ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "=<" [ttrue; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [ttrue; ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 2 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "=<" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.

Goal eval "erlang" ">" [ttrue; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [ffalse; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [VEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.

Goal eval "erlang" ">=" [ttrue; ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [ffalse; ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [VEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [VClos [] 2 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" ">=" [VClos [] 1 0 EEmptyMap; VClos [] 1 0 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.

Goal eval "erlang" "length" [l1] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "length" [l2] = Some (RExc (badarg (VTuple [VLit (Atom "length");l2])), None).
Proof. cbn. reflexivity. Qed.
Goal eval "erlang" "length" [l3] = Some (RExc (badarg (VTuple [VLit (Atom "length");l3])), None).
Proof. cbn. reflexivity. Qed.
Goal eval "erlang" "length" [l4] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "length" [l5] = Some (RExc (badarg (VTuple [VLit (Atom "length");l5])), None).
Proof. cbn. reflexivity. Qed.
Goal eval "erlang" "length" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "length");ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "length" [l5;l3] = Some (RExc (undef (VLit (Atom "length"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "tuple_size" [l3] = Some (RExc (badarg (VTuple [VLit (Atom "tuple_size");l3])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_size" [VTuple []] = Some (RValSeq [VLit (Integer 0)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tuple_size" [VTuple [ttrue;ttrue;ttrue]; ErrorVal] = Some (RExc (undef (VLit (Atom "tuple_size"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "hd" [l1] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [VNil] = Some (RExc (badarg (VTuple [VLit (Atom "hd");VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l2] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l3] = Some (RValSeq [(VCons ttrue ttrue)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l4] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l5] = Some (RValSeq [ttrue], None).
Proof. unfold l5. reflexivity. Qed.
Goal eval "erlang" "hd" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "hd");ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "hd" [l5;l3] = Some (RExc (undef (VLit (Atom "hd"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "tl" [l1] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [VNil] = Some (RExc (badarg (VTuple [VLit (Atom "tl");VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l2] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l3] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l4] = Some (RValSeq [(VCons ttrue (VCons ttrue VNil))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l5] = Some (RValSeq [VCons ttrue ttrue], None).
Proof. unfold l5. reflexivity. Qed.
Goal eval "erlang" "tl" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "tl");ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "tl" [l5;l3] = Some (RExc (undef (VLit (Atom "tl"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "element" [VLit (Integer 2); VTuple [ttrue]] = Some (RExc (badarg (VTuple [VLit (Atom "element"); VLit (Integer 2); VTuple [ttrue]])), None).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal eval "erlang" "element" [VLit (Integer 1); VTuple [ttrue]] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "element" [ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "element"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "element" [ttrue] = Some (RExc (undef (VLit (Atom "element"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "setelement" [VLit (Integer 2); VTuple [ttrue]; ffalse] = Some (RExc (badarg (VTuple [VLit (Atom "setelement"); VLit (Integer 2); VTuple [ttrue]; ffalse])), None).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal eval "erlang" "setelement" [VLit (Integer 1); VTuple [ttrue]; ffalse] = Some (RValSeq [VTuple [ffalse]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "setelement" [ttrue; ttrue; ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "setelement"); ttrue; ttrue; ttrue])), None).
Proof. unfold eval, eval_elem_tuple. simpl. reflexivity. Qed.
Goal eval "erlang" "setelement" [ttrue] = Some (RExc (undef (VLit (Atom "setelement"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_number" [VLit (Integer 2)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_number" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_number"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [VLit (Integer 2)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_integer" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_integer"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Integer 2)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [VLit (Atom "foo")] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_atom" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_atom"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [VLit (Integer 2)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_boolean" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_boolean"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VNil] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VCons ttrue (VCons ttrue VNil)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VCons ttrue ttrue] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [VTuple []] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_list" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_list"))), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [VTuple []] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [VTuple [ttrue; ffalse]] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [VNil] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_tuple" [ffalse; ffalse] = Some (RExc (undef (VLit (Atom "is_tuple"))), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; VLit (Integer 2)] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; VLit (Integer 3)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [ttrue; VLit (Integer 2)] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; VLit (Integer (-1))]
    = Some (RExc (badarg (VTuple [VLit (Atom "is_function"); VClos [] 1 2 EEmptyMap; VLit (Integer (-1))])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_function" [VClos [] 1 2 EEmptyMap; ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "is_function"); VClos [] 1 2 EEmptyMap; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_map" [VMap [(ttrue, ttrue)]] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_map" [VNil] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_pid" [VPid 1] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_pid" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_port" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "is_port" [ttrue; ttrue] = Some (RExc (undef (VLit (Atom "is_port"))), None).
Proof. reflexivity. Qed.

(** Binaries used in the tests below: "12" and "-5" as 16 bit binaries, "ff", and a bitstring of 3 bits *)
Local Definition bin_12 : Val := VBitstring (bv_to_bvn (Z_to_bv 16 12594)).
Local Definition bin_m5 : Val := VBitstring (bv_to_bvn (Z_to_bv 16 11573)).
Local Definition bin_ff : Val := VBitstring (bv_to_bvn (Z_to_bv 16 26214)).
Local Definition bits_3 : Val := VBitstring (bv_to_bvn (Z_to_bv 3 5)).

Goal eval "erlang" "list_to_integer" [string_to_vcons "123"] = Some (RValSeq [VLit (Integer 123)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "-45"] = Some (RValSeq [VLit (Integer (-45))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "+7"] = Some (RValSeq [VLit (Integer 7)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "--"]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "--"])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "12a"]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "12a"])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "ff"; VLit (Integer 16)] = Some (RValSeq [VLit (Integer 255)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "1010"; VLit (Integer 2)] = Some (RValSeq [VLit (Integer 10)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "-0a"; VLit (Integer 16)] = Some (RValSeq [VLit (Integer (-10))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "10"; VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "10"; VLit (Integer 1)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_integer" [string_to_vcons "12"; VLit (Integer 2)]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_integer"); string_to_vcons "12"; VLit (Integer 2)])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "integer_to_list" [VLit (Integer 255); VLit (Integer 16)] = Some (RValSeq [string_to_vcons "FF"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [VLit (Integer (-10)); VLit (Integer 2)] = Some (RValSeq [string_to_vcons "-1010"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [VLit (Integer 0); VLit (Integer 10)] = Some (RValSeq [string_to_vcons "0"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [VLit (Integer 5); VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); VLit (Integer 5); VLit (Integer 1)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "integer_to_list" [ttrue; VLit (Integer 10)]
    = Some (RExc (badarg (VTuple [VLit (Atom "integer_to_list"); ttrue; VLit (Integer 10)])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "binary_to_integer" [bin_12] = Some (RValSeq [VLit (Integer 12)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bin_m5] = Some (RValSeq [VLit (Integer (-5))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bin_ff; VLit (Integer 16)] = Some (RValSeq [VLit (Integer 255)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bits_3]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_integer"); bits_3])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_integer"); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_integer" [bin_12; VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_integer"); bin_12; VLit (Integer 1)])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "atom_to_list" [VLit (Atom "abc")] = Some (RValSeq [string_to_vcons "abc"], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "atom_to_list" [VLit (Integer 1)]
    = Some (RExc (badarg (VTuple [VLit (Atom "atom_to_list"); VLit (Integer 1)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_atom" [bin_12; VLit (Atom "utf8")]
    = Some (RValSeq [VLit (Atom "12")], Some (AtomCreation, [VLit (Atom "12")])).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_atom" [bin_12; VLit (Atom "foo")]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_atom"); bin_12; VLit (Atom "foo")])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "binary_to_atom" [bits_3; VLit (Atom "utf8")]
    = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_atom"); bits_3; VLit (Atom "utf8")])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "list_to_binary" [VCons (VLit (Integer 1)) (VCons (VLit (Integer 2)) VNil)]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 16 258))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [VNil]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 0 0))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [VCons (VLit (Integer 1)) (VCons bin_12 (VCons (VCons (VLit (Integer 2)) VNil) VNil))]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 32 (1 * 2^24 + 12594 * 2^8 + 2)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [VCons (VLit (Integer 256)) VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_binary"); VCons (VLit (Integer 256)) VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "list_to_binary" [bin_12]
    = Some (RExc (badarg (VTuple [VLit (Atom "list_to_binary"); bin_12])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_to_binary" [bin_12] = Some (RValSeq [bin_12], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_to_binary" [VCons bin_12 bin_12]
    = Some (RValSeq [VBitstring (bv_to_bvn (Z_to_bv 32 (12594 * 2^16 + 12594)))], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_to_binary" [bits_3]
    = Some (RExc (badarg (VTuple [VLit (Atom "iolist_to_binary"); bits_3])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_size" [VCons (VLit (Integer 1)) (VCons bin_12 VNil)] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "iolist_size" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "iolist_size"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "delete_element" [VLit (Integer 2); VTuple [ttrue; ffalse; VNil]] = Some (RValSeq [VTuple [ttrue; VNil]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "delete_element" [VLit (Integer 0); VTuple [ttrue]]
    = Some (RExc (badarg (VTuple [VLit (Atom "delete_element"); VLit (Integer 0); VTuple [ttrue]])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "delete_element" [VLit (Integer 2); VTuple [ttrue]]
    = Some (RExc (badarg (VTuple [VLit (Atom "delete_element"); VLit (Integer 2); VTuple [ttrue]])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "delete_element" [ttrue; VTuple [ttrue]]
    = Some (RExc (badarg (VTuple [VLit (Atom "delete_element"); ttrue; VTuple [ttrue]])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 1); VTuple [ttrue; ffalse]; VNil] = Some (RValSeq [VTuple [VNil; ttrue; ffalse]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 3); VTuple [ttrue; ffalse]; VNil] = Some (RValSeq [VTuple [ttrue; ffalse; VNil]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 4); VTuple [ttrue; ffalse]; VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "insert_element"); VLit (Integer 4); VTuple [ttrue; ffalse]; VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "insert_element" [VLit (Integer 0); VTuple [ttrue; ffalse]; VNil]
    = Some (RExc (badarg (VTuple [VLit (Atom "insert_element"); VLit (Integer 0); VTuple [ttrue; ffalse]; VNil])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "make_tuple" [VLit (Integer 3); ttrue] = Some (RValSeq [VTuple [ttrue; ttrue; ttrue]], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "make_tuple" [VLit (Integer 0); ttrue] = Some (RValSeq [VTuple []], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "make_tuple" [VLit (Integer (-1)); ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "make_tuple"); VLit (Integer (-1)); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [VTuple [ttrue; ffalse]] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [bin_12] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [bits_3] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "size" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "size"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "map_size" [VMap [(ttrue, ttrue); (ffalse, ttrue)]] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "map_size" [ttrue] = Some (RExc (badmap ttrue), None).
Proof. reflexivity. Qed.
Goal eval "maps" "from_keys" [VCons (VLit (Integer 2)) (VCons (VLit (Integer 1)) VNil); ttrue]
    = Some (RValSeq [VMap [(VLit (Integer 1), ttrue); (VLit (Integer 2), ttrue)]], None).
Proof. reflexivity. Qed.
Goal eval "maps" "from_keys" [VNil; ttrue] = Some (RValSeq [VMap []], None).
Proof. reflexivity. Qed.
Goal eval "maps" "from_keys" [ttrue; ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "from_keys"); ttrue; ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "max" [VLit (Integer 2); VLit (Integer 1)] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "max" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "min" [VLit (Integer 2); VLit (Integer 1)] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "min" [VLit (Integer 1); VLit (Integer 2)] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity. Qed.
Goal eval "erlang" "min" [VLit (Integer 1)] = Some (RExc (undef (VLit (Atom "min"))), None).
Proof. reflexivity. Qed.

Goal match eval "erlang" "split_binary" [bin_12; VLit (Integer 1)] with
     | Some (RValSeq [VTuple [VBitstring a; VBitstring b]], None) =>
         bvn_eqb a (bv_to_bvn (Z_to_bv 8 49)) && bvn_eqb b (bv_to_bvn (Z_to_bv 8 50))
     | _ => false
     end = true.
Proof. reflexivity. Qed.
Goal match eval "erlang" "split_binary" [bin_12; VLit (Integer 0)] with
     | Some (RValSeq [VTuple [VBitstring a; VBitstring b]], None) =>
         bvn_eqb a (bv_to_bvn (Z_to_bv 0 0)) && bvn_eqb b (bv_to_bvn (Z_to_bv 16 12594))
     | _ => false
     end = true.
Proof. reflexivity. Qed.
Goal eval "erlang" "split_binary" [bin_12; VLit (Integer 3)]
    = Some (RExc (badarg (VTuple [VLit (Atom "split_binary"); bin_12; VLit (Integer 3)])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "split_binary" [ttrue; VLit (Integer 0)]
    = Some (RExc (badarg (VTuple [VLit (Atom "split_binary"); ttrue; VLit (Integer 0)])), None).
Proof. reflexivity. Qed.

Local Definition int_list : Val := VCons (VLit (Integer 2)) (VCons (VLit (Integer 1)) VNil).
Local Definition tuple_list : Val := VCons (VTuple [VLit (Integer 1); VLit (Integer 10)])
                                       (VCons (VTuple [VLit (Integer 2); VLit (Integer 20)]) VNil).

Goal eval "lists" "member" [VLit (Integer 1); int_list] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "lists" "member" [VLit (Integer 3); int_list] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "lists" "member" [VLit (Integer 1); ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "member"); VLit (Integer 1); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 2); VLit (Integer 1); tuple_list]
    = Some (RValSeq [VTuple [VLit (Integer 2); VLit (Integer 20)]], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 20); VLit (Integer 2); tuple_list]
    = Some (RValSeq [VTuple [VLit (Integer 2); VLit (Integer 20)]], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 3); VLit (Integer 1); tuple_list] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 1); VLit (Integer 0); tuple_list]
    = Some (RExc (badarg (VTuple [VLit (Atom "keyfind"); VLit (Integer 1); VLit (Integer 0); tuple_list])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "keyfind" [VLit (Integer 1); ttrue; tuple_list]
    = Some (RExc (badarg (VTuple [VLit (Atom "keyfind"); VLit (Integer 1); ttrue; tuple_list])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "keymember" [VLit (Integer 2); VLit (Integer 1); tuple_list] = Some (RValSeq [ttrue], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keymember" [VLit (Integer 3); VLit (Integer 1); tuple_list] = Some (RValSeq [ffalse], None).
Proof. reflexivity. Qed.
Goal eval "lists" "keymember" [VLit (Integer 1); VLit (Integer 1); ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "keymember"); VLit (Integer 1); VLit (Integer 1); ttrue])), None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [int_list]
    = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 2)) VNil)], None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [VNil] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [int_list; VLit (Integer 3)]
    = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 2)) (VLit (Integer 3)))], None).
Proof. reflexivity. Qed.
Goal eval "lists" "reverse" [ttrue]
    = Some (RExc (badarg (VTuple [VLit (Atom "reverse"); ttrue])), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "error" [ffalse; ffalse] = Some (RExc (Error, ffalse, ffalse), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [ffalse] = Some (RExc (Error, ffalse, VNil), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "error" [] = Some (RExc (undef ErrorVal), None).
Proof. reflexivity. Qed.

Goal eval "erlang" "fun_info" [ffalse; ffalse] = Some (RExc (badarg (VTuple [VLit "fun_info"%string; ffalse; ffalse])), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "fun_info" [ffalse] = Some (RExc (undef (VLit "fun_info"%string)), None).
Proof. reflexivity. Qed.
Goal eval "erlang" "fun_info" [VClos [] 0 2 (˝VNil); VLit "arity"%string] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.

Goal eval "maps" "get" [VNil; VMap [(VNil, VNil)]] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VLit 2%Z; VMap [(VLit 1%Z, VLit 1%Z);(VLit 2%Z, VLit 2%Z);(VLit 3%Z, VLit 3%Z)]] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VLit 1%Z, VNil)]] = Some (RExc (badkey VNil), None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VNil, VNil)];VTuple []] = Some (RValSeq [VNil], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VLit 2%Z; VMap [(VLit 1%Z, VLit 1%Z);(VLit 2%Z, VLit 2%Z);(VLit 3%Z, VLit 3%Z)];VTuple []] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VLit 1%Z, VNil)];VTuple []] = Some (RValSeq [VTuple []], None).
Proof. reflexivity. Qed.


Goal eval "maps" "put" [VNil; VNil; VMap [(VNil, VLit 1%Z)]] = Some (RValSeq [VMap [(VNil, VNil)]], None).
Proof. cbn. reflexivity. Qed.
Goal eval "maps" "get" [VLit 2%Z; VMap [(VLit 1%Z, VLit 1%Z);(VLit 2%Z, VLit 2%Z);(VLit 3%Z, VLit 3%Z)]] = Some (RValSeq [VLit 2%Z], None).
Proof. reflexivity. Qed.
Goal eval "maps" "get" [VNil; VMap [(VLit 1%Z, VNil)]] = Some (RExc (badkey VNil), None).
Proof. reflexivity. Qed.


(** Bitstring/binary tests.
    b16 = <<433:16>>       = <<1,177>>       (byte-aligned, 16 bits)
    b19 = <<433:16,3:3>>   = <<1,177,3:3>>   (not byte-aligned, 19 bits)
    b3  = <<3:3>>          (shorter than one byte, 3 bits)

    `bv`/`bvn` bundle their value with a `Qed`-opaque well-formedness proof,
    so plain `reflexivity` can get stuck comparing two `VBitstring`s whose
    underlying values are equal but were constructed via `Z_to_bv` with
    different (though equally-wrapping) raw arguments. `bv_eq`/`bvn_eq`
    (from stdpp) reduce that comparison to just the `bv_unsigned`/
    `bvn_unsigned` value, sidestepping the opaque proof entirely. *)
Ltac reflexivity_upto_bv :=
  vm_compute;
  repeat first
    [ reflexivity
    | apply bv_eq;  reflexivity
    | apply bvn_eq; split; reflexivity
    | f_equal ].

Local Definition b16 : Val := VBitstring (Z_to_bv 16 433).
Local Definition b19 : Val := VBitstring (Z_to_bv 19 3467).
Local Definition b3  : Val := VBitstring (Z_to_bv 3 3).

Goal eval "erlang" "bit_size" [b19] = Some (RValSeq [VLit (Integer 19)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [b16] = Some (RValSeq [VLit (Integer 16)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [b3] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "bit_size"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bit_size" [] = Some (RExc (undef (VLit (Atom "bit_size"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "byte_size" [b19] = Some (RValSeq [VLit (Integer 3)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [b16] = Some (RValSeq [VLit (Integer 2)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [b3] = Some (RValSeq [VLit (Integer 1)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [ttrue] = Some (RExc (badarg (VTuple [VLit (Atom "byte_size"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "byte_size" [] = Some (RExc (undef (VLit (Atom "byte_size"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "is_binary" [b16] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [b19] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [b3] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_binary" [ttrue; ttrue] = Some (RExc (undef (VLit (Atom "is_binary"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "is_bitstring" [b19] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [b16] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [b3] = Some (RValSeq [ttrue], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [ttrue] = Some (RValSeq [ffalse], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "is_bitstring" [] = Some (RExc (undef (VLit (Atom "is_bitstring"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "bitstring_to_list" [b19]
  = Some (RValSeq [VCons (VLit (Integer 1))
                  (VCons (VLit (Integer 177))
                  (VCons (VBitstring (Z_to_bv 3 3)) VNil))], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [b16]
  = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 177)) VNil)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [b3]
  = Some (RValSeq [VCons (VBitstring (Z_to_bv 3 3)) VNil], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [ttrue]
  = Some (RExc (badarg (VTuple [VLit (Atom "bitstring_to_list"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "bitstring_to_list" [] = Some (RExc (undef (VLit (Atom "bitstring_to_list"))), None).
Proof. reflexivity_upto_bv. Qed.

Goal eval "erlang" "binary_to_list" [b16]
  = Some (RValSeq [VCons (VLit (Integer 1)) (VCons (VLit (Integer 177)) VNil)], None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "binary_to_list" [b19]
  = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_list"); b19])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "binary_to_list" [ttrue]
  = Some (RExc (badarg (VTuple [VLit (Atom "binary_to_list"); ttrue])), None).
Proof. reflexivity_upto_bv. Qed.
Goal eval "erlang" "binary_to_list" [] = Some (RExc (undef (VLit (Atom "binary_to_list"))), None).
Proof. reflexivity_upto_bv. Qed.

