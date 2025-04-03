# Eqvivalence Proof of Big-step and Frame Stack Semantics

## Tactics

Shorten version of old tactics, they only consists of 3 letters. Some has extra function to their original counter parts. Tactics with multiple parameters don't use comma fore separation.

- `src/Eqvivalence/Tactics/T1ParamZero.v`: tactics with zero parameters;
- `src/Eqvivalence/Tactics/T2ParamSingle.v`: tactics with one parameters;
- `src/Eqvivalence/Tactics/T3ParamMultiple.v`: tactics with multiple parameters;
- `src/Eqvivalence/Tactics/T4Name.v`: tactics which include renaming;
- `src/Eqvivalence/Tactics/T5Transform.v`: tactics which transforms terms by rewrite, specify or pose;
- `src/Eqvivalence/Tactics/T6Clear.v`: tactics which include clear;
- `src/Eqvivalence/Tactics/T7Solve.v`: tactics which include solve.

## Basics

Defining the basics needs of both sides of the implications.

- `src/Eqvivalence/E1Induction.v`: induction for value and expression in both syntax;
- `src/Eqvivalence/E2WellFormedMap.v`: a map is well formed if all values are sorted;
- `src/Eqvivalence/E3Notations.v`: getter functions and notations, most of then is not used;
- `src/Eqvivalence/E3Basics.v`: basics lemmas and theorems, most of them is about list.

... Ongoing


## Big-step implies Frame Stack Semantics

## Frame Stack implies Big-Step Semantics 

# Basics Files Detailed 
