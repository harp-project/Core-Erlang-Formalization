From CoreErlang.Equivalence.BigStepToFrameStack.Simple Require Import Substitute.
From CoreErlang.FrameStack Require Import SubstSemanticsLemmas.
Require Import stdpp.list.

Import BigStep.

Open Scope string_scope.






Section BigStepValToExp.






  Section EFun.



    Section Simple.

      (*
        env = []
        fun() -> 1
        fun() -> 1
      *)
      Lemma test_bval_to_bexp_1 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            []
            []
            0
            []
            (ELit (Integer 1))
            None)
        =
        EFun
          []
          (ELit (Integer 1)).
      Proof.
        by simpl.
      Qed.

      (*
        env = []
        fun(x) -> y
        fun(x) -> y
      *)
      Lemma test_bval_to_bexp_2 :
        bval_to_bexp
          (subst_env 10)
           (VClos
            []
            []
            0
            ["x"]
            (EVar "y")
            None)
        =
        EFun
          ["x"]
          (EVar "y").
      Proof.
        by simpl.
      Qed.

      (*
        env = [y = 1]
        fun(x) -> y
        fun(x) -> 1
      *)
      Lemma test_bval_to_bexp_3 :
        bval_to_bexp 
          (subst_env 10)
            (VClos
              [(inl "y" , VLit (Integer 1))]
              []
              0
              ["x"]
              (EVar "y")
              None)
        =
        EFun
          ["x"]
          (ELit (Integer 1)).
      Proof.
        by simpl.
      Qed.

      (*
        env = [x = 1]
        fun(x) -> x
        fun(x) -> x
      *)
      Lemma test_bval_to_bexp_4 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inl "x" , VLit (Integer 1))]
            []
            0
            ["x"]
            (EVar "x")
            None)
        =
        EFun
          ["x"]
          (EVar "x").
      Proof.
        by simpl.
      Qed.

      (*
        env = [x = 1; y = 1]
        fun(x) -> x , y
        fun(x) -> x , 1
      *)
      Lemma test_bval_to_bexp_5 :
        bval_to_bexp
          (subst_env 10)
            (VClos
              [(inl "x" , VLit (Integer 1));
              (inl "y" , VLit (Integer 1))]
              []
              0
              ["x"]
              (EValues [EVar "x"; EVar "y"])
              None)
        =
        EFun
          ["x"]
          (EValues [EVar "x"; ELit (Integer 1)]).
      Proof.
        by simpl.
      Qed.

      (*
        env = [x = 1; y = 1]
        fun(x) -> x + y
        fun(x) -> x + 1
      *)
      Lemma test_bval_to_bexp_6 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inl "x" , VLit (Integer 1));
            (inl "y" , VLit (Integer 1))]
            []
            0
            ["x"]
            (ECall
              (ELit (Atom "erlang"))
              (ELit (Atom "+"))
              [EVar "x"; EVar "y"])
            None)
        =
        EFun
          ["x"]
          (ECall
            (ELit (Atom "erlang"))
            (ELit (Atom "+"))
            [EVar "x"; ELit (Integer 1)]).
      Proof.
        by simpl.
      Qed.

      (*
        env = [x = 1; y = 1]
        fun(x,y) -> x + y
        fun(x,y) -> x + y
      *)
      Lemma test_bval_to_bexp_7 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inl "x" , VLit (Integer 1));
            (inl "y" , VLit (Integer 1))]
            []
            0
            ["x"; "y"]
            (ECall
              (ELit (Atom "erlang"))
              (ELit (Atom "+"))
              [EVar "x"; EVar "y"])
            None)
        =
        EFun
          ["x"; "y"]
          (ECall
            (ELit (Atom "erlang"))
            (ELit (Atom "+"))
            [EVar "x"; EVar "y"]).
      Proof.
        by simpl.
      Qed.

      End Simple.



      Section WithVar.

      (*
        env = [y = fun(z) -> z]
        fun(x) -> y
        fun(x) -> (fun(z) -> z)
      *)
      Lemma test_bval_to_bexp_8 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inl "y" , (VClos
              []
              []
              0
              ["z"]
              (EVar "z")
              None))]
            []
            0
            ["x"]
            (EVar "y")
            None)
        =
        EFun
          ["x"]
          (EFun ["z"] (EVar "z")).
      Proof.
        by simpl.
      Qed.

      (*
        env = [y = fun(x) -> x; z = 1; x = 2]
        fun(x) -> z , y , x
        fun(x) -> 1 , (fun(x) -> x) , x
      *)
      Lemma test_bval_to_bexp_9 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inl "y" , (VClos
              []
              []
              0
              ["x"]
              (EVar "x")
              None));
            (inl "z" , VLit (Integer 1));
            (inl "x" , VLit (Integer 2))]
            []
            0
            ["x"]
            (EValues [EVar "z"; EVar "y"; EVar "x"])
            None)
        =
        EFun
          ["x"]
          (EValues
            [ELit (Integer 1);
            EFun ["x"] (EVar "x");
            EVar "x"]).
      Proof.
        by simpl.
      Qed.

      (*
        env = [y = fun(x) -> (x , z); z = 1; x = 2]
        fun(x) -> z , y , x
        fun(x) -> 1 , (fun(x) -> (x , z)) , x
      *)
      Lemma test_bval_to_bexp_10 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inl "y" , (VClos
              []
              []
              0
              ["x"]
              (EValues [EVar "x"; EVar "z"])
              None));
            (inl "z" , VLit (Integer 1));
            (inl "x" , VLit (Integer 2))]
            []
            0
            ["x"]
            (EValues [EVar "z"; EVar "y"; EVar "x"])
            None)
        =
        EFun
          ["x"]
          (EValues
            [ELit (Integer 1);
            EFun ["x"] (EValues [EVar "x"; EVar "z"]);
            EVar "x"]).
      Proof.
        by simpl.
      Qed.

    End WithVar.



    Section WithFunId.

      (*
        env = [f/1 = fun(z) -> z]
        fun(x) -> f/1
        fun(x) -> (fun(z) -> z)
      *)
      Lemma test_bval_to_bexp_11 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inr ("f" , 1) , (VClos
              []
              []
              0
              ["z"]
              (EVar "z")
              None))]
            []
            0
            ["x"]
            (EFunId ("f" , 1))
            None)
        =
        EFun
          ["x"]
          (EFun ["z"] (EVar "z")).
      Proof.
        by simpl.
      Qed.

      (*
        env = [f/1 = fun(x) -> x; z = 1; x = 2]
        fun(x) -> z , f/1 , x
        fun(x) -> 1 , (fun(x) -> x) , x
      *)
      Lemma test_bval_to_bexp_12 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inr ("f" , 1) , (VClos
                []
                []
                0
                ["x"]
                (EVar "x")
                None));
            (inl "z" , VLit (Integer 1));
            (inl "x" , VLit (Integer 2))]
            []
            0
            ["x"]
            (EValues [EVar "z"; EFunId ("f" , 1); EVar "x"])
            None)
        =
        EFun
          ["x"]
          (EValues
            [ELit (Integer 1);
            EFun ["x"] (EVar "x");
            EVar "x"]).
      Proof.
        by simpl.
      Qed.

      (*
        env = [f/1 = fun(x) -> (x , z); z = 1; x = 2]
        fun(x) -> z , f/1 , x
        fun(x) -> 1 , (fun(x) -> (x , z)) , x
      *)
      Lemma test_bval_to_bexp_13 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inr ("f" , 1) , (VClos
              []
              []
              0
              ["x"]
              (EValues [EVar "x"; EVar "z"])
              None));
            (inl "z" , VLit (Integer 1));
            (inl "x" , VLit (Integer 2))]
            []
            0
            ["x"]
            (EValues [EVar "z"; EFunId ("f" , 1); EVar "x"])
            None)
        =
        EFun
          ["x"]
          (EValues
            [ELit (Integer 1);
            EFun ["x"] (EValues [EVar "x"; EVar "z"]);
            EVar "x"]).
      Proof.
        by simpl.
      Qed.

      (*
        env = [f/1 = fun(z,y) -> (z , y , x) [y = 1; x = 3]; z = 1; x = 2]
        fun(x) -> z , f/2 , x
        fun(x) -> 1 , (fun(z,y) -> (z , y , 3)) , x
      *)
      Lemma test_bval_to_bexp_14 :
        bval_to_bexp
          (subst_env 10)
          (VClos
            [(inr ("f" , 2) , (VClos
              [(inl "y" , VLit (Integer 1));
              (inl "x" , VLit (Integer 3))]
              []
              0
              ["z"; "y"]
              (EValues [EVar "z"; EVar "y"; EVar "x"])
              None));
            (inl "z" , VLit (Integer 1));
            (inl "x" , VLit (Integer 2))]
            []
            0
            ["x"]
            (EValues [EVar "z"; EFunId ("f" , 2); EVar "x"])
            None)
        =
        EFun
          ["x"]
          (EValues
            [ELit (Integer 1);
            EFun
              ["z"; "y"]
              (EValues
                [EVar "z";
                EVar "y";
                ELit (Integer 3)]);
            EVar "x"]).
      Proof.
        by simpl.
      Qed.

    End WithFunId.



  End EFun.






  Section LetRec.



    (* -- Recurzive *)



    (*
      env = []
      f/1 = fun(x) -> x
      f/1 = fun(x) -> x
    *)
    Lemma test_bval_to_bexp_15 :
      bval_to_bexp
        (subst_env 10)
        (VClos
          []
          [(1 , ("f" , 1) , (["x"] , (EVar "x")))]
          0
          []
          (ENil)
          (Some ("f" , 1)))
      =
      ELetRec
        [("f", 1, (["x"], EVar "x"))]
        (EFunId ("f", 1)).
    Proof.
      by simpl.
    Qed.



    (*
      env = []
      f/1 = fun(x) -> x , i/1, f/2, f/1 , g/1
      g/1 = fun(x) -> y , x , g/1 , h/1
      h/1 = fun(x) -> y , x , f/1 , h/1
      -
      f/1 = fun(x) -> x , i/1, f/2, f/1 , g/1
      g/1 = fun(x) -> y , x , g/1 , h/1
      h/1 = fun(x) -> y , x , f/1 , h/1
    *)
    Lemma test_bval_to_bexp_16 :
      bval_to_bexp
        (subst_env 10)
        (VClos
          []
          [(1 , ("f" , 1) , (["x"] , (EValues
            [EVar "x";
            EFunId ("i" , 1);
            EFunId ("f" , 2);
            EFunId ("f" , 1);
            EFunId ("g" , 1)])));
          (2 , ("g" , 1) , (["x"] , (EValues
            [EVar "y";
            EVar "x";
            EFunId ("g" , 1);
            EFunId ("h" , 1)])));
          (3 , ("h" , 1) , (["y"] , (EValues 
            [EVar "y";
            EVar "x";
            EFunId ("f" , 1);
            EFunId ("h" , 1)])))]
          0
          []
          (ENil)
          (Some ("f" , 1)))
      =
      ELetRec
        [("f", 1, (["x"], EValues
          [EVar "x";
          EFunId ("i", 1);
          EFunId ("f", 2);
          EFunId ("f", 1);
          EFunId ("g", 1)]));
        ("g", 1, (["x"], EValues
          [EVar "y";
          EVar "x";
          EFunId ("g", 1);
          EFunId ("h", 1)]));
        ("h", 1, (["y"], EValues
          [EVar "y";
          EVar "x";
          EFunId ("f", 1);
          EFunId ("h", 1)]))]
        (EFunId ("f", 1)).
    Proof.
      by simpl.
    Qed.



    (*
      env = [x = 1; 
             y = 2; 
             z = 3;
             f/1 = fun(z) -> z; 
             g/1 = fun(z) -> z;
             h/1 = fun(z) -> z;
             i/1 = fun(z) -> z
             f/2 = fun(x,y) -> x , y , z]
      f/1 = fun(x) -> x , i/1, f/2, f/1 , g/1
      g/1 = fun(x) -> y , x , g/1 , h/1
      h/1 = fun(y) -> y , x , f/1 , h/1
      -
      f/1 = fun(x) -> x , (fun(z) -> z), (fun(x,y) -> x , y , z), f/1 , g/1
      g/1 = fun(x) -> 2 , x , g/1 , h/1
      h/1 = fun(y) -> y , 1 , f/1 , h/1
    *)
    Lemma test_bval_to_bexp_17 :
      bval_to_bexp
        (subst_env 10)
        (VClos
          [(inl "x" , VLit (Integer 1));
          (inl "y" , VLit (Integer 2));
          (inl "z" , VLit (Integer 3));
          (inr ("f" , 1) , (VClos
            []
            []
            0
            ["z"]
            (EVar "z")
            None));
          (inr ("g" , 1) , (VClos
            []
            []
            0
            ["z"]
            (EVar "z")
            None));
          (inr ("h" , 1) , (VClos
            []
            []
            0
            ["z"]
            (EVar "z")
            None));
          (inr ("i" , 1) , (VClos
            []
            []
            0
            ["z"]
            (EVar "z")
            None));
          (inr ("f" , 2) , (VClos
            []
            []
            0
            ["x"; "y"]
            (EValues [EVar "x"; EVar "y"; EVar "z"])
            None))]
          [(1 , ("f" , 1) , (["x"] , (EValues
            [EVar "x";
            EFunId ("i" , 1);
            EFunId ("f" , 2);
            EFunId ("f" , 1);
            EFunId ("g" , 1)])));
          (2 , ("g" , 1) , (["x"] , (EValues
            [EVar "y";
            EVar "x";
            EFunId ("g" , 1);
            EFunId ("h" , 1)])));
          (3 , ("h" , 1) , (["y"] , (EValues
            [EVar "y";
            EVar "x";
            EFunId ("f" , 1);
            EFunId ("h" , 1)])))]
          0
          []
          (ENil)
          (Some ("f" , 1)))
      =
      ELetRec
        [("f", 1, (["x"], EValues
          [EVar "x";
          EFun ["z"] (EVar "z");
          EFun ["x"; "y"] (EValues [EVar "x"; EVar "y"; EVar "z"]);
          EFunId ("f", 1);
          EFunId ("g", 1)]));
        ("g", 1, (["x"], EValues
          [ELit (Integer 2);
          EVar "x";
          EFunId ("g", 1);
          EFunId ("h", 1)]));
        ("h", 1, (["y"], EValues
          [EVar "y";
          ELit (Integer 1);
          EFunId ("f", 1);
          EFunId ("h", 1)]))]
        (EFunId ("f", 1)).
    Proof.
      by simpl.
    Qed.



  End LetRec.






End BigStepValToExp.












Section FrameStackExpToVal.



Section VVal.

Compute fexp_to_fval
  (˝ Syntax.VNil).
Compute fexp_to_fval
  (˝ Syntax.VLit 1%Z).
Compute fexp_to_fval
  (˝ Syntax.VPid 1).
Compute fexp_to_fval
  (˝ Syntax.VCons (Syntax.VLit 1%Z) (Syntax.VNil)).
Compute fexp_to_fval
  (˝ Syntax.VTuple [Syntax.VLit 1%Z; Syntax.VNil]).
Compute fexp_to_fval
  (˝ Syntax.VMap [(Syntax.VLit 1%Z, Syntax.VNil)]).
Compute fexp_to_fval
  (˝ Syntax.VVar 0).
Compute fexp_to_fval
  (˝ Syntax.VFunId (0 , 0)).
Compute fexp_to_fval
  (˝ Syntax.VClos [] 0 0 (˝ Syntax.VLit 1%Z)).

End VVal.



Section VExp.

Compute fexp_to_fval
  (° Syntax.EFun 0 (˝ Syntax.VLit 1%Z)).
Compute fexp_to_fval
  (° Syntax.EValues [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]).
Compute fexp_to_fval
  (° Syntax.ECons (˝ Syntax.VLit 1%Z) (˝ Syntax.VNil)).
Compute fexp_to_fval
  (° Syntax.ETuple [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]).
Compute fexp_to_fval
  (° Syntax.EMap [(˝ Syntax.VLit 1%Z, ˝ Syntax.VNil)]).
Compute fexp_to_fval
  (° Syntax.ECall (˝ Syntax.VLit 1%Z) (˝ Syntax.VLit 1%Z) [˝ Syntax.VNil]).
Compute fexp_to_fval
  (° Syntax.EPrimOp "" [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]).
Compute fexp_to_fval
  (° Syntax.EApp (˝ Syntax.VLit 1%Z) [˝ Syntax.VNil]).
Compute fexp_to_fval
  (° Syntax.ECase
    (˝ Syntax.VLit 1%Z)
    [([], ˝ Syntax.VLit 1%Z, ˝ Syntax.VLit 1%Z)]).
Compute fexp_to_fval
  (° Syntax.ELet 0 (˝ Syntax.VLit 1%Z) (˝ Syntax.VVar 0)).
Compute fexp_to_fval
  (° Syntax.ESeq (˝ Syntax.VLit 1%Z) (˝ Syntax.VLit 1%Z)).
Compute fexp_to_fval
  (° Syntax.ELetRec [(0, (˝ Syntax.VLit 1%Z))] (˝ Syntax.VVar 0)).
Compute fexp_to_fval
  (° Syntax.ETry
    (˝ Syntax.VLit 1%Z) 0
    (˝ Syntax.VLit 1%Z) 0
    (˝ Syntax.VLit 1%Z)).

End VExp.



End FrameStackExpToVal.












Section BigStepToFrameStack.



Section Result.

(*
  VNil
    ->
  Some [Syntax.VNil]
*)
Compute bres_to_fred
  (fun _ => 0)
  subst_env
  (inl [VNil]).

(*
  VLit (Integer 1)
    ->
  Some [Syntax.VLit 1%Z]
*)
Compute bres_to_fred
  (fun _ => 0)
  subst_env 
  (inl [VLit (Integer 1)]).

(*
  VCons (VLit (Integer 1)) (VNil)
    ->
  Some [Syntax.VCons (Syntax.VLit 1%Z) Syntax.VNil]
*)
Compute bres_to_fred
  (fun _ => 0)
  subst_env
  (inl [VCons (VLit (Integer 1)) (VNil)]).

(*
  VTuple [VLit (Integer 1); VNil]
    ->
  Some [Syntax.VTuple [Syntax.VLit 1%Z; Syntax.VNil]]
*)
Compute bres_to_fred
  (fun _ => 0)
  subst_env
  (inl [VTuple [VLit (Integer 1); VNil]]).

(*
  VMap [(VLit (Integer 1) , VNil)]
    ->
  Some [Syntax.VMap [(Syntax.VLit 1%Z, Syntax.VNil)]]
*)
Compute bres_to_fred
  (fun _ => 0)
  subst_env
  (inl [VMap [(VLit (Integer 1) , VNil)]]).

(*
  VClos [] [] 0 [] (ELit (Integer 1)) None
    ->
  Some [Syntax.VClos [] 0 0 (˝ Syntax.VLit 1%Z)]
*)

Compute bres_to_fred
  (fun _ => 0)
  subst_env
  (inl [VClos [] [] 0 [] (ELit (Integer 1)) None]).

End Result.



Section ValueSequence.



(*
  VNil
    ->
  Some [Syntax.VNil]
*)
Compute bvs_to_fvs
  (fun _ => 0)
  subst_env
  [VNil].

(*
  VLit (Integer 1) 
    ->
  Some [Syntax.VLit 1%Z]
*)
Compute bvs_to_fvs
  (fun _ => 0)
  subst_env
  [VLit (Integer 1)].

(*
  VCons (VLit (Integer 1)) (VNil)
    ->
  Some [Syntax.VCons (Syntax.VLit 1%Z) Syntax.VNil]
*)

Compute bvs_to_fvs
  (fun _ => 0)
  subst_env
  [VCons (VLit (Integer 1)) (VNil)].

(*
  VTuple [VLit (Integer 1); VNil]
    ->
  Some [Syntax.VTuple [Syntax.VLit 1%Z; Syntax.VNil]]

  Error!!!
*)

Compute bvs_to_fvs
  (fun _ => 0) 
  subst_env
  [VTuple [VLit (Integer 1); VNil]].

(*
  VMap [(VLit (Integer 1) , VNil)]
    ->
  Some [Syntax.VMap [(Syntax.VLit 1%Z, Syntax.VNil)]]
*)

Compute bvs_to_fvs
  (fun _ => 0)
  subst_env
  [VMap [(VLit (Integer 1) , VNil)]].

(*
  VClos [] [] 0 [] (ELit (Integer 1)) None
    ->
  Some [Syntax.VClos [] 0 0 (˝ Syntax.VLit 1%Z)]
*)

Compute bvs_to_fvs
  (fun _ => 0)
  subst_env
  [VClos [] [] 0 [] (ELit (Integer 1)) None].

End ValueSequence.



Section Exp.

(*
  VNil
    ->
  ˝ Syntax.VNil
*)
Compute bexp_to_fexp
  (fun _ => 0)
  (bval_to_bexp
    (subst_env 100) 
    VNil).

(*
  VLit (Integer 1)
    ->
  ˝ Syntax.VLit 1%Z
*)
Compute bexp_to_fexp
  (fun _ => 0)
  (bval_to_bexp
    (subst_env 100)
    (VLit (Integer 1))).

(*
  VCons (VLit (Integer 1)) (VNil)
    ->
  ° Syntax.ECons (˝ Syntax.VLit 1%Z) (˝ Syntax.VNil)
*)
Compute bexp_to_fexp
  (fun _ => 0)
  (bval_to_bexp
    (subst_env 100)
    (VCons (VLit (Integer 1)) VNil)).

(*
  VTuple [VLit (Integer 1); VNil])
    ->
  ° Syntax.ETuple [˝ Syntax.VLit 1%Z; ˝ Syntax.VNil]
*)
Compute bexp_to_fexp
  (fun _ => 0)
  (bval_to_bexp
    (subst_env 100)
    (VTuple [VLit (Integer 1); VNil])).

(*
  VMap [(VLit (Integer 1) , VNil)]
    ->
  ° Syntax.EMap [(˝ Syntax.VLit 1%Z, ˝ Syntax.VNil)]
*)
Compute bexp_to_fexp
  (fun _ => 0)
  (bval_to_bexp
    (subst_env 100)
    (VMap [(VLit (Integer 1) , VNil)])).

(*
  VClos [] [] 0 [] (ELit (Integer 1)) None
    ->
  ° Syntax.EFun 0 (˝ Syntax.VLit 1%Z)
*)
Compute bexp_to_fexp
  (fun _ => 0)
  (bval_to_bexp
    (subst_env 100)
    (VClos [] [] 0 [] (ELit (Integer 1)) None)).

End Exp.



End BigStepToFrameStack.