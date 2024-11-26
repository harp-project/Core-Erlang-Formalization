(**
  This file contains unit tests for the big-step and functional big-step
  semantics. The file contains examples about impure evaluation.
*)

From CoreErlang Require Export Tactics.
From CoreErlang Require Export FunctionalBigStep.

Import ListNotations.

Open Scope string_scope.

(** 
  Every first example: functional big-step semantics
  Every second example: big-step semantics
*)
Example tuple_eff_fbs :
  fbs_expr 1000 [] [] "" 0 (ETuple [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")];
               ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")];
               ECall (ELit (Atom "io" )) (ELit (Atom "fread" )) [ELit (Atom "") ; ELit (Atom "c")]]) []
=
  Result 0 (inl [VTuple [ok;ok; VTuple [ok; VLit (Atom "c")]]]) 
     [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]);
      (Input, [VLit (Atom ""); VLit (Atom "c")])].
Proof.
  auto.
Qed.

Example tuple_eff :
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ETuple [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")];
               ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")];
               ECall (ELit (Atom "io" )) (ELit (Atom "fread" )) [ELit (Atom "") ; ELit (Atom "c")]], []|
-e>
  |0, inl [VTuple [ok;ok; VTuple [ok; VLit (Atom "c")]]], 
     [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]);
      (Input, [VLit (Atom ""); VLit (Atom "c")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example list_eff_fbs :
  fbs_expr 1000 [] [] "" 0 (ECons (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")])
             (ECons (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")]) ENil)) []
=
  Result 0 (inl [VCons ok (VCons ok VNil)])
     [(Output, [VLit (Atom "b")]); (Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example list_eff :
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ECons (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")])
             (ECons (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")]) ENil), []|
-e> 
  | 0, inl [VCons ok (VCons ok VNil)], 
     [(Output, [VLit (Atom "b")]); (Output, [VLit (Atom "a")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example case_eff_fbs : 
  fbs_expr 1000 [] [] "" 0 (ECase (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")])
      [([PVar "X"], ELit (Atom "false"), (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")])); 
       ([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 2)); 
       ([PVar "Y"], ELit (Atom "true"), (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "c")]))]) []
=
  Result 0 (inl [ok]) [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])].
Proof.
  auto.
Qed.

Example case_eff : 
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ECase (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")])
      [([PVar "X"], ELit (Atom "false"), (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")])); 
       ([PLit (Integer 5)], ELit (Atom "true"), ELit (Integer 2)); 
       ([PVar "Y"], ELit (Atom "true"), (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "c")]))]
  , []|
-e>
  |0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example call_eff_fbs :
  fbs_expr 1000 [] [] "" 0 (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]]) []
=
  Result 0 (inl [ok]) [(Output, [VLit (Atom "a")]); (Output, [ok])].
Proof.
  auto.
Qed.


Example call_eff :
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]], []|
-e>
  | 0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [ok])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example apply_eff_fbs : 
  fbs_expr 1000 [(inl "Y", VClos [] [] 0 ["Z"] (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "c")]))] [] "" 1
    (EApp (ELet ["X"] (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]) 
             (EVar "Y"))
           [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")] ]) []
=
  Result 1 (inl [ok]) 
   [(Output, [VLit (Atom "a")]);
    (Output, [VLit (Atom "b")]);
    (Output, [VLit (Atom "c")])].
Proof.
  auto.
Qed.

Example apply_eff : 
  forall modules,
  valid_modules modules ->
  |[(inl "Y", VClos [] [] 0 ["Z"] (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "c")]))], [], "", 1, 
    EApp (ELet ["X"] (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]) 
             (EVar "Y"))
           [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")] ], []|
-e>
  |1, inl [ok], 
   [(Output, [VLit (Atom "a")]);
    (Output, [VLit (Atom "b")]);
    (Output, [VLit (Atom "c")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example let_eff_fbs : 
  fbs_expr 1000 [] [] "" 0 (ELet ["X"; "Y"] 
     (EValues [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]; EFun [] (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")])])
          (EApp (EVar "Y") [])) []
=
  Result 1 (inl [ok]) [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])].
Proof.
  auto.
Qed.

Example let_eff : 
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ELet ["X"; "Y"] 
     (EValues [ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]; EFun [] (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")])])
          (EApp (EVar "Y") []), []|
-e>
  |1, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example letrec_eff_fbs : 
  fbs_expr 1000 [] [] "" 0 (ELetRec [(("f1", 0), ([], ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]))]
           (EApp (EFunId ("f1", 0)) [])) []
=
  Result 1 (inl [ok]) [(Output, [VLit (Atom "a")])].
Proof.
  auto.
Qed.

Example letrec_eff : 
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ELetRec [(("f1", 0), ([], ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")]))]
           (EApp (EFunId ("f1", 0)) []), []|
-e>
  |1, inl [ok], [(Output, [VLit (Atom "a")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example map_eff_fbs : 
  fbs_expr 1000 [] [] "" 0 
         (EMap [(ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")], ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")]);
                (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "c")], ELit (Integer 5))]) [] 
=
  Result 0 (inl [VMap [(ok, VLit (Integer 5))]])
      [(Output, [VLit (Atom "a")]);
       (Output, [VLit (Atom "b")]);
       (Output, [VLit (Atom "c")])].
Proof.
  auto.
Qed.

Example map_eff : 
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, EMap [(ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")], ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")]);
                (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "c")], ELit (Integer 5))]
  , []| 
-e> 
  | 0, inl [VMap [(ok, VLit (Integer 5))]],
      [(Output, [VLit (Atom "a")]);
       (Output, [VLit (Atom "b")]);
       (Output, [VLit (Atom "c")])]|.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.

Example seq_eff_fbs :
  fbs_expr 1000 [] [] "" 0 (ESeq (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")])
                (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")]))
    []
=
  Result 0 (inl [ok]) [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] .
Proof.
  auto.
Qed.

Example seq_eff :
  forall modules,
  valid_modules modules ->
  |[], [], "", 0, ESeq (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "a")])
                (ECall (ELit (Atom "io" )) (ELit (Atom "fwrite" )) [ELit (Atom "b")])
   , [] |
-e>
  | 0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] |.
Proof.
  intros.
  solve.
  all:
 
  inversion H; inversion H1; unfold get_modfunc; simpl; try rewrite H0; try rewrite H2; auto.
Qed.
