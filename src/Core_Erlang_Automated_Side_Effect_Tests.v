Require Core_Erlang_Tactics.

Module Automated_Side_Effect_Tests.

Import Core_Erlang_Semantics.Semantics.
Import Core_Erlang_Tactics.Tactics.

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
  try(timeout 5 solve).
Qed.

Example list_eff :
  |[], 0, ECons (ECall "fwrite"%string [ELit (Atom "a")])
             (ECons (ECall "fwrite"%string [ELit (Atom "b")]) ENil), []|
-e> 
  | 0, inl (VCons ok (VCons ok VNil)), 
     [(Output, [VLit (Atom "b")]); (Output, [VLit (Atom "a")])]|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example call_eff :
  |[], 0, ECall "fwrite"%string [ECall "fwrite"%string [ELit (Atom "a")]], []|
-e>
  | 0, inl ok, [(Output, [VLit (Atom "a")]); (Output, [ok])]|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example let_eff : 
  |[], 0, ELet [("X"%string, ECall "fwrite"%string [ELit (Atom "a")]); 
                ("Y"%string, EFun [] (ECall "fwrite"%string [ELit (Atom "b")]))]
          (EApp (EVar "Y"%string) []), []|
-e>
  |1, inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])]|.
Proof.
  try(timeout 5 solve).
Qed.

Example letrec_eff : 
  |[], 0, ELetRec [(("f1"%string, 0), ([], ECall "fwrite"%string [ELit (Atom "a")]))]
           (EApp (EFunId ("f1"%string, 0)) []), []|
-e>
  |1, inl ok, [(Output, [VLit (Atom "a")])]|.
Proof.
  try(timeout 5 solve).
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
  try(timeout 5 solve).
Qed.

Example seq_eff :
  | [], 0, ESeq (ECall "fwrite"%string [ELit (Atom "a"%string)])
                (ECall "fwrite"%string [ELit (Atom "b"%string)])
   , [] |
-e>
  | 0, inl ok, [(Output, [VLit (Atom "a")]); (Output, [VLit (Atom "b")])] |.
Proof.
  try(timeout 5 solve).
Qed.

End Automated_Side_Effect_Tests.