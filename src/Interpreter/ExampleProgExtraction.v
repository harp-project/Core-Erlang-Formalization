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
   imported file. Note that the import needs to be done by hand
   in the extracted file: in "ExampleProgs.hs", the line
   "import RocqExtraction" needs to be inserted after importing prelude.
 *)
Extract Inductive Lit => Lit [Atom Integer].
Extract Inductive BinType => BinType [IntType FloatType BinaryType BitstringType Utf8Type Utf16Type Utf32Type].
Extract Inductive BinSign => BinSign [Signed Unsigned].
Extract Inductive BinEnd => BinEnd [BigEndian LittleEndian NativeEndian].
Extract Inductive Pat => Pat [PVar PLit PCons PTuple PMap PNil PBin].
Extract Inductive Exp => Exp [VVal EExp].
Extract Inductive Val => Val [VNil VLit VPid VCons VTuple VMap VVar VFunId VClos VBitstring].
Extract Inductive NonVal => NonVal 
  [EFun EValues ECons ETuple EMap ECall EPrimOp EApp ECase ELet ESeq ELetRec ETry EBin ESeg].
Extract Inlined Constant PID => PID.
Extract Inlined Constant FunId => FunId.
Extract Inlined Constant Var => Var.
(* `N`, `bv`, `bvn` and `Segment` are inductive types, so they need
   `Extract Inductive` (`Extract Inlined Constant` only works for constants,
   and errors out with "N is not a constant"). The names must match the
   definitions in "RocqExtraction.hs". Without these, the type declarations
   would be duplicated in "ExampleProgs.hs". *)
Extract Inductive N => N [N0 Npos].
Extract Inductive bvn => Bvn [Bv_to_bvn].
Extract Inductive Segment => Segment [Build_Segment].
Extract Inductive bv => Bv [BV].

Extraction "HaskellSrc/exe/ExampleProgs.hs" examplePrograms.
