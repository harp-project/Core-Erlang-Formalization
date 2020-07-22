Require Core_Erlang_Semantics.

Module Side_Effect_Tests.

Import Core_Erlang_Semantics.Semantics.

Import ListNotations.



Example tuple_eff :
  |[], 0, ETuple [ECall "fwrite"%string [ELit (Atom "a"%string)];
               ECall "fwrite"%string [ELit (Atom "b"%string)];
               ECall "fread"%string [ELit (Atom ""%string) ; ELit (Atom "c"%string)]], []|
-e>
  |0, inl (VTuple [ok;ok; VTuple [ok; VLit (Atom "c"%string)]]), 
     [(Output, [VLit (Atom "a"%string)]); (Output, [VLit (Atom "b"%string)]);
      (Input, [VLit (Atom ""%string); VLit (Atom "c"%string)])]|.
Proof.
  apply eval_tuple with (eff := [[(Output, [VLit (Atom "a"%string)])]; 
                                 [(Output, [VLit (Atom "a")]); 
                                  (Output, [VLit (Atom "b"%string)])]; 
                                 [(Output, [VLit (Atom "a")]);
                                  (Output, [VLit (Atom "b")]);
                                  (Input, [VLit (Atom ""%string); 
                                           VLit (Atom "c"%string)])]])
                        (ids := [0;0;0]); auto.
  * intros. inversion H.
    - subst. simpl. apply eval_call with (vals := [VLit (Atom ""%string); 
                                                   VLit (Atom "c"%string)])
                                         (eff := [ [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]; 
                                                   [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] ])
                                         (ids := [0 ; 0]); auto.
      + intros. inversion H0.
        ** subst. simpl. apply eval_lit. 
        ** inversion H2.
          -- simpl. apply eval_lit.
          -- inversion H4.
    - inversion H1. simpl. apply eval_call with (vals := [VLit (Atom "b"%string)])
                                                (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
      + intros. inversion H2.
        ** apply eval_lit.
        ** inversion H5.
      + inversion H3. simpl. apply eval_call with (vals := [VLit (Atom "a"%string)])
                                                  (eff := [[]]) (ids := [0]); auto.
        ** intros. inversion H4.
          -- apply eval_lit.
          -- inversion H7.
        ** inversion H5.
Qed.

Example list_eff :
  |[], 0, ECons (ECall "fwrite"%string [ELit (Atom "a")])
             (ECons (ECall "fwrite"%string [ELit (Atom "b")]) ENil), []|
-e> 
  | 0, inl (VCons ok (VCons ok VNil)), 
     [(Output, [VLit (Atom "b")]); (Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_cons with (eff2 := [(Output, [VLit (Atom "b")])]).
  * simpl. eapply eval_cons with (eff2 := []).
    - apply eval_nil.
    - eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [[]]) (ids := [0]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
  * simpl. eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[(Output, [VLit (Atom "b")])]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example case_eff : 
  |[], 0, ECase (ECall "fwrite"%string [ELit (Atom "a")])
      [(PVar "X"%string, ELit (Atom "false"), (ECall "fwrite"%string [ELit (Atom "b")])); 
       (PLit (Integer 5), ELit (Atom "true"), ELit (Integer 2)); 
       (PVar "Y"%string, ELit (Atom "true"), (ECall "fwrite"%string [ELit (Atom "c")]))]
  , []|
-e>
  |0, inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_case with (i := 2); auto.
  * eapply eval_call with (vals := [VLit (Atom "a")]) (eff :=[[]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. apply eval_lit.
    - simpl. reflexivity.
  * simpl. reflexivity.
  * intros. inversion H. 2: inversion H2. 3: inversion H4.
    - subst. inversion H0.
    - subst. inversion H0. apply eval_lit.
  * simpl. apply eval_lit.
  * simpl. eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
    - intros. inversion H. 2: inversion H1. simpl. apply eval_lit.
Qed.

Example call_eff :
  |[], 0, ECall "fwrite"%string [ECall "fwrite"%string [ELit (Atom "a")]], []|
-e>
  | 0, inl ok, [(Output, [VLit (Atom "a")]); (Output, [ok])]|.
Proof.
  eapply eval_call with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
  * intros. inversion H. 2: inversion H1. simpl. 
    eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
Qed.

Example apply_eff : 
  |[(inl "Y"%string, VClos [] [] 0 ["Z"%string] (ECall "fwrite"%string [ELit (Atom "c")]))], 1, 
    EApp (ELet [("X"%string, ECall "fwrite"%string [ELit (Atom "a")])] 
             (EVar "Y"%string))
           [ECall "fwrite" [ELit (Atom "b")] ], []|
-e>
  |1, inl ok, 
   [(Output, [VLit (Atom "a")]);
    (Output, [VLit (Atom "b")]);
    (Output, [VLit (Atom "c")])]|.
Proof.
  eapply eval_app with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]]) 
                       (ref := []) (ext := []) (var_list := ["Z"%string]) (n := 0)
                       (body := ECall "fwrite"%string [ELit (Atom "c")]) (ids := [1]); auto.
  * eapply eval_let with (vals := [ok]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [1]); auto.
    - intros. inversion H. 2: inversion H1. 
      eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [1]); auto.
      + intros. inversion H0. 2: inversion H3. apply eval_lit.
    - simpl. apply eval_var. reflexivity.
  * intros. inversion H. 2: inversion H1. simpl. 
    apply eval_call with (vals := [VLit (Atom "b")]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [1]); auto.
    - intros. inversion H0. 2: inversion H3. simpl. apply eval_lit.
  * simpl. eapply eval_call with (vals := [VLit (Atom "c")]) (eff := [[(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]]) (ids := [1]); auto.
    - intros. inversion H. 2: inversion H1. simpl. apply eval_lit.
Qed.

Example let_eff : 
  |[], 0, ELet [("X"%string, ECall "fwrite"%string [ELit (Atom "a")]); 
                ("Y"%string, EFun [] (ECall "fwrite"%string [ELit (Atom "b")]))]
          (EApp (EVar "Y"%string) []), []|
-e>
  |1, inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  eapply eval_let with (vals := [ok;
                                 VClos [] [] 0 [] (ECall "fwrite"%string [ELit (Atom "b")])])
                       (eff := [[(Output, [VLit (Atom "a")])]; [(Output, [VLit (Atom "a")])]])
                       (ids := [0;1]); auto.
  * intros. inversion H. 2: inversion H1. 3: inversion H3.
    - simpl. apply eval_fun.
    - simpl. eapply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [0]); auto.
      + intros. inversion H2. 2: inversion H5. apply eval_lit.
  * eapply eval_app with (vals := []) (var_list := []) (ids := [])
                         (ref := []) (ext := []) (n := 0)
                         (body := ECall "fwrite"%string [ELit (Atom "b")]) 
                         (eff := []); auto.
    - simpl. apply eval_var. reflexivity.
    - intros. inversion H.
    - simpl. eapply eval_call with (vals := [VLit (Atom "b")]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [1]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example letrec_eff : 
  |[], 0, ELetRec [(("f1"%string, 0), ([], ECall "fwrite"%string [ELit (Atom "a")]))]
           (EApp (EFunId ("f1"%string, 0)) []), []|
-e>
  |1, inl ok, [(Output, [VLit (Atom "a")])]|.
Proof.
  eapply eval_letrec; auto.
  * simpl. eapply eval_app with (vals := []) (eff := []) (ref := []) (ids := [])
                                (ext := [(0, ("f1"%string, 0),
                                          ([], ECall "fwrite" [ELit (Atom "a")]))]) 
                                (var_list := []) (n := 0)
                                (body := ECall "fwrite"%string [ELit (Atom "a")]); auto.
    - apply eval_funid. reflexivity.
    - intros. inversion H.
    - simpl. apply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]]) (ids := [1]); auto.
      + intros. inversion H. 2: inversion H1. apply eval_lit.
Qed.

Example map_eff : 
  |[], 0, EMap [(ECall "fwrite"%string [ELit (Atom "a"%string)], ECall "fwrite"%string [ELit (Atom "b"%string)]);
                (ECall "fwrite"%string [ELit (Atom "c"%string)], ELit (Integer 5))]
  , []| 
-e> 
  | 0, inl (VMap [(ok, VLit (Integer 5))]),
      [(Output, [VLit (Atom "a"%string)]);
       (Output, [VLit (Atom "b"%string)]);
       (Output, [VLit (Atom "c"%string)])]|.
Proof.
  eapply eval_map with (kvals := [ok; ok]) (vvals := [ok; VLit (Integer 5)])
                       (eff := [[(Output, [VLit (Atom "a")])]; 
                                [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]; 
                                [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); (Output, [VLit (Atom "c")])]; 
                                [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]); (Output, [VLit (Atom "c")])]])
                       (ids := [0;0;0;0]); auto.
  * intros. inversion H.
    - apply eval_call with (vals := [VLit (Atom "c")]) (eff := 
           [[(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]]) (ids := [0]); auto.
      + intros. inversion H0.
        ** simpl. apply eval_lit.
        ** inversion H3.
    - inversion H1.
      + simpl. apply eval_call with (vals := [VLit (Atom "a")]) (eff := [[]])
                                    (ids := [0]); auto.
        ** intros. inversion H2. 2: inversion H5. simpl. apply eval_lit.
      + inversion H3.
  * intros. inversion H.
    - simpl. apply eval_lit.
    - inversion H1.
      + apply eval_call with (vals := [VLit (Atom "b")]) (eff := [[(Output, [VLit (Atom "a")])]]) (ids := [0]); auto.
        ** intros. inversion H2. 2: inversion H5. simpl. apply eval_lit.
      + inversion H3.
  * reflexivity.
  * reflexivity.
  * simpl. auto.
Qed.

End Side_Effect_Tests.