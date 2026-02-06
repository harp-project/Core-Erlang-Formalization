Require Stdlib.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.
From CoreErlang.Interpreter.ExampleASTs.rocqAST Require Import decode fib huff length length2 length_c length_u life life2 life3 mean_nnc nrev qsort ring smith stable stable2 tak zip_nnc life4 pmap length3.

Definition examplePrograms : list NonVal :=
[testdecode; testfib; testhuff; testlength; testlength2;
 testlength_c; testlength_u; testlife; testlife2; testlife3;
 testmean_nnc; testnrev; testqsort; testring; testsmith; 
 teststable; teststable2; testtak; testzip_nnc; testlife4; testpmap; testlength3].

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

(* Unfortunately the extraction does not allow ommitting definitions,
   so the type definitions are mapped to their counterparts in the
   imported file. Not that the import needs to be done by hand
   in the extracted file.
 *)
Extract Inductive Lit => Lit [Atom Integer].
Extract Inductive Pat => Pat [PVar PLit PCons PTuple PMap PNil].
Extract Inductive Exp => Exp [VVal EExp].
Extract Inductive Val => Val [VNil VLit VPid VCons VTuple VMap VVar VFunId VClos].
Extract Inductive NonVal => NonVal 
  [EFun EValues ECons ETuple EMap ECall EPrimOp EApp ECase ELet ESeq ELetRec ETry].
Extract Inlined Constant PID => PID.
Extract Inlined Constant FunId => FunId.
Extract Inlined Constant Var => Var.

Extraction "HaskellSrc/exe/ExampleProgs.hs" examplePrograms.
