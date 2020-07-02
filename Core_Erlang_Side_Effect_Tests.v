Load Core_Erlang_Semantics.

Module Core_Erlang_Side_Effect_Tests.

Import Reals.
Import Strings.String.
Import Lists.List.
Import ListNotations.

Import Core_Erlang_Environment.
Import Core_Erlang_Helpers.
Import Core_Erlang_Syntax.
Import Core_Erlang_Side_Effects.
Import Core_Erlang_Semantics.


Example tuple_eff :
  |[], ETuple [ECall "fwrite"%string [ELit (Atom "a"%string)];
               ECall "fwrite"%string [ELit (Atom "b"%string)];
               ECall "fread"%string [ELit (Atom ""%string) ; ELit (Atom "c"%string)]], []|
-e>
  |inl (VTuple [ok;ok; VTuple [ok; VLit (Atom "c"%string)]]), 
   [(Output, [VLit (Atom "a"%string)]); (Output, [VLit (Atom "b"%string)]);
    (Input, [VLit (Atom ""%string); VLit (Atom "c"%string)])]|.
Proof.
  apply eval_tuple with (eff := [[(Output, [VLit (Atom "a"%string)])]; 
                                 [(Output, [VLit (Atom "b"%string)])]; 
                                 [(Input, [VLit (Atom ""%string); 
                                           VLit (Atom "c"%string)])]]).
  * reflexivity.
  * simpl. reflexivity.
  * intros. inversion H.
    - subst. simpl. apply eval_call with (vals := [VLit (Atom ""%string); 
                                                   VLit (Atom "c"%string)])
                                         (eff := [ []; [] ]).
      + reflexivity.
      + reflexivity.
      + intros. inversion H0.
        ** subst. unfold concatn. simpl. apply eval_lit. 
        ** inversion H2.
          -- apply eval_lit.
          -- inversion H4.
      + unfold concatn. simpl. reflexivity.
    - inversion H1. simpl. apply eval_call with (vals := [VLit (Atom "b"%string)])
                                                (eff := [[]]).
      + reflexivity.
      + reflexivity.
      + intros. inversion H2.
        ** apply eval_lit.
        ** inversion H5.
      + simpl. reflexivity.
      + inversion H3. simpl. apply eval_call with (vals := [VLit (Atom "a"%string)])
                                                  (eff := [[]]).
        ** reflexivity.
        ** reflexivity.
        ** intros. inversion H4.
          -- apply eval_lit.
          -- inversion H7.
        ** simpl. reflexivity.
        ** inversion H5.
  * unfold concatn. simpl. reflexivity.
Qed.

Example list_eff :
  |[], ECons (ECall "fwrite"%string [ELit (Atom "a")])
             (ECons (ECall "fwrite"%string [ELit (Atom "b")]) ENil), []|
-e> 
  |inl (VCons ok (VCons ok VNil)), 
   [(Output, [VLit (Atom "b")]); (Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_list with (eff2 := [(Output, [VLit (Atom "b")])]).
  * simpl. reflexivity.
  * simpl. eapply eval_list with (eff2 := []).
    - simpl. reflexivity.
    - apply eval_emptylist.
    - eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [[]]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
  * simpl. eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]).
    - reflexivity.
    - reflexivity.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - reflexivity.
Qed.

Example case_eff : 
  |[], ECase (ECall "fwrite"%string [ELit (Atom "a")])
           [PVar "X"%string; PLit (Integer 5); PVar "Y"%string]
           [ELit (Atom "false"); ELit (Atom "true"); 
            ELit (Atom "true")]
           [(ECall "fwrite"%string [ELit (Atom "b")]); 
            ELit (Integer 2); 
            (ECall "fwrite"%string [ELit (Atom "c")])]
  , []|
-e>
  |inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_case with (i := 2); auto.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff :=[[]]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - simpl. reflexivity.
  * simpl. reflexivity.
  * intros. inversion H. 2: inversion H2. 3: inversion H4.
    - subst. inversion H0.
    - subst. inversion H0. apply eval_lit.
  * simpl. reflexivity.
  * simpl. apply eval_lit.
  * simpl. eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. unfold concatn. simpl. apply eval_lit.
Qed.

Example call_eff :
  |[], ECall "fwrite"%string [ECall "fwrite"%string [ELit (Atom "a")]], []|
-e>
  |inl ok, [(Output, [VLit (Atom "a")]); (Output, [ok])]|.
Proof.
  eapply eval_call with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")])]]); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. unfold concatn. simpl. apply eval_lit.
Qed.

Example apply_eff : 
  |[(inl "Y"%string, VClos [] [] 0 ["Z"%string] (ECall "fwrite"%string [ELit (Atom "c")]))], 
    EApp (ELet ["X"%string] [ECall "fwrite"%string [ELit (Atom "a")]] 
             (EVar "Y"%string))
           [ECall "fwrite" [ELit (Atom "b")] ], []|
-e>
  |inl ok, 
   [(Output, [VLit (Atom "a")]);
    (Output, [VLit (Atom "b")]);
    (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_apply with (vals := [ok]) (eff := [[(Output, [VLit (Atom "b")])]]) 
                         (ref := []) (ext := []) (var_list := ["Z"%string]) (n := 0)
                         (body := ECall "fwrite"%string [ELit (Atom "c")]).
  * reflexivity.
  * eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")])]]).
    - reflexivity.
    - reflexivity.
    - intros. inversion H. 2: inversion H1. 
      eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]); auto.
      + intros. inversion H0. 2: inversion H3. apply eval_lit.
    - unfold concatn. simpl. reflexivity.
    - simpl. apply eval_var.
  * reflexivity.
  * reflexivity.
  * intros. inversion H. 2: inversion H1. unfold concatn. simpl. 
    apply eval_call with (vals := [VLit (Atom "b")]) (eff := [[]]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * unfold concatn. simpl. reflexivity.
  * simpl. eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[]]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example let_eff : 
  |[], ELet ["X"%string; "Y"%string] [ECall "fwrite"%string [ELit (Atom "a")]; 
                                      EFun [] (ECall "fwrite"%string [ELit (Atom "b")])]
          (EApp (EVar "Y"%string) []), []|
-e>
  |inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_let with (vals := [ok;
                                 VClos [] [] 0 [] (ECall "fwrite"%string [ELit (Atom "b")])])
                       (eff := [[(Output, [VLit (Atom "a")])]; []]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - simpl. apply eval_fun.
    - simpl. eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]); auto.
      + intros. inversion H2. 2: inversion H5. apply eval_lit. 
  * unfold concatn. simpl. reflexivity.
  * eapply eval_apply with (vals := []) (var_list := []) 
                           (ref := []) (ext := []) (n := 0)
                           (body := ECall "fwrite"%string [ELit (Atom "b")]) 
                           (eff := []); auto.
    - simpl. apply eval_var.
    - intros. inversion H.
    - simpl. reflexivity.
    - simpl. eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [[]]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example letrec_eff : 
  |[], ELetRec [("f1"%string, 0)] [[]] 
              [ECall "fwrite"%string [ELit (Atom "a")]]
        (EApp (EFunId ("f1"%string, 0)) []), []|
-e>
  |inl ok, [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_letrec; auto.
  2 : reflexivity.
  * simpl. eapply eval_apply with (vals := []) (eff := []) (ref := []) 
                                  (ext := [("f1"%string, 0, ([], ECall "fwrite" 
                                                                 [ELit (Atom "a")]))]) 
                                  (var_list := []) (n := 0)
                                  (body := ECall "fwrite"%string [ELit (Atom "a")]); auto.
    - apply eval_funid.
    - intros. inversion H.
    - simpl. reflexivity.
    - simpl. apply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example map_eff : 
  |[], EMap [ECall "fwrite"%string [ELit (Atom "a"%string)];
             ECall "fwrite"%string [ELit (Atom "c"%string)]]
            [ECall "fwrite"%string [ELit (Atom "b"%string)];
             ELit (Integer 5)], []| 
-e> 
  | inl (VMap [ok] [VLit (Integer 5)]),
    [(Output, [VLit (Atom "a"%string)]);
     (Output, [VLit (Atom "b"%string)]);
     (Output, [VLit (Atom "c"%string)])]|.
Proof.
  apply eval_map with (kvals := [ok; ok]) (vvals := [ok; VLit (Integer 5)])
                      (eff := [[(Output, [VLit (Atom "a")])]; 
                               [(Output, [VLit (Atom "b")])]; 
                               [(Output, [VLit (Atom "c")])]; 
                               []]).
  * reflexivity.
  * reflexivity.
  * reflexivity.
  * reflexivity.
  * simpl. reflexivity.
  * unfold concatn. intros. inversion H.
    - apply eval_call with (vals := [VLit (Atom "c")]) (eff := [[]]).
      + reflexivity.
      + reflexivity.
      + intros. inversion H0.
        ** unfold concatn. simpl. apply eval_lit.
        ** inversion H3.
      + unfold concatn. simpl. reflexivity.
    - inversion H1.
      + simpl. apply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]).
        ** reflexivity.
        ** reflexivity.
        ** intros. inversion H2. 2: inversion H5. simpl. apply eval_lit.
        ** unfold concatn. simpl. reflexivity.
      + inversion H3.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1.
      + apply eval_call with (vals := [VLit (Atom "b")]) (eff := [[]]).
        ** reflexivity.
        ** reflexivity.
        ** intros. inversion H2. 2: inversion H5. simpl. apply eval_lit.
        ** simpl. reflexivity.
      + inversion H3.
  * unfold concatn. simpl. reflexivity.
Qed.

End Core_Erlang_Side_Effect_Tests.