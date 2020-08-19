Require Core_Erlang_Tactics.

Module Automated_Side_Effect_Tests.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.

Import ListNotations.

Open Scope string_scope.

Example tuple_eff :
  |[], 0, ETuple [^ECall "fwrite" [^ELit (Atom "a")];
               ^ECall "fwrite" [^ELit (Atom "b")];
               ^ECall "fread" [^ELit (Atom "") ; ^ELit (Atom "c")]], []|
-e>
  |0, inl [VTuple [ok;ok; VTuple [ok; VLit (Atom "c")]]], 
     [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")]);
      (Input, [VLit (Atom ""); VLit (Atom "c")])]|.
Proof.
  solve.
Qed.

Example list_eff :
  |[], 0, ECons (ECall "fwrite" [^ELit (Atom "a")])
             (ECons (ECall "fwrite" [^ELit (Atom "b")]) ENil), []|
-e> 
  | 0, inl [VCons ok (VCons ok VNil)], 
     [(Output, [VLit (Atom "b")]); (Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example case_eff : 
  |[], 0, ECase (ECall "fwrite" [^ELit (Atom "a")])
      [([PVar "X"], ^ELit (Atom "false"), ^(ECall "fwrite" [^ELit (Atom "b")])); 
       ([PLit (Integer 5)], ^ELit (Atom "true"), ^ELit (Integer 2)); 
       ([PVar "Y"], ^ELit (Atom "true"), ^(ECall "fwrite" [^ELit (Atom "c")]))]
  , []|
-e>
  |0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "c")])]|.
Proof.
  solve.
Qed.

Example call_eff :
  |[], 0, ECall "fwrite" [^ECall "fwrite" [^ELit (Atom "a")]], []|
-e>
  | 0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [ok])]|.
Proof.
  solve.
Qed.

Example apply_eff : 
  |[(inl "Y", VClos [] [] 0 ["Z"] (ECall "fwrite" [^ELit (Atom "c")]))], 1, 
    EApp (ELet ["X"] (ECall "fwrite" [^ELit (Atom "a")]) 
             (EVar "Y"))
           [^ECall "fwrite" [^ELit (Atom "b")] ], []|
-e>
  |1, inl [ok], 
   [(Output, [VLit (Atom "a")]);
    (Output, [VLit (Atom "b")]);
    (Output, [VLit (Atom "c")])]|.
Proof.
  solve.
Qed.

Example let_eff : 
  |[], 0, ELet ["X"; "Y"] 
     (EValues [ECall "fwrite" [^ELit (Atom "a")]; EFun [] (ECall "fwrite" [^ELit (Atom "b")])])
          (EApp (EVar "Y") []), []|
-e>
  |1, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  solve.
Qed.

Example letrec_eff : 
  |[], 0, ELetRec [(("f1", 0), ([], ^ECall "fwrite" [^ELit (Atom "a")]))]
           (EApp (EFunId ("f1", 0)) []), []|
-e>
  |1, inl [ok], [(Output, [VLit (Atom "a")])]|.
Proof.
  solve.
Qed.

Example map_eff : 
  |[], 0, EMap [(^ECall "fwrite" [^ELit (Atom "a")], ^ECall "fwrite" [^ELit (Atom "b")]);
                (^ECall "fwrite" [^ELit (Atom "c")], ^ELit (Integer 5))]
  , []| 
-e> 
  | 0, inl [VMap [(ok, VLit (Integer 5))]],
      [(Output, [VLit (Atom "a")]);
       (Output, [VLit (Atom "b")]);
       (Output, [VLit (Atom "c")])]|.
Proof.
  solve.
Qed.

Example seq_eff :
  | [], 0, ESeq (ECall "fwrite" [^ELit (Atom "a")])
                (ECall "fwrite" [^ELit (Atom "b")])
   , [] |
-e>
  | 0, inl [ok], [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] |.
Proof.
  solve.
Qed.

End Automated_Side_Effect_Tests.