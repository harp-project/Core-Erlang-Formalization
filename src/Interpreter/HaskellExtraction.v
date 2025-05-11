Require Coq.extraction.Extraction.
Extraction Language Haskell.

From CoreErlang.Interpreter Require Import StepFunctions.
From CoreErlang.Interpreter Require Import Scheduler.

Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Extraction "HaskellCode/CoqExtraction.hs"
  nodeSimpleStep makeInitialNodeConf ex_Process 
  isDead isTotallyDead
  currPID nextConf newConfByAction delCurrFromConf.
