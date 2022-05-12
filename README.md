# Core Erlang Formalisation

In this repository you can find the formalisation of a sequential subset of Core Erlang in Coq Proof Assistant. The formalisation also includes a definition of the module system in Core Erlang.

# Compilation process

Necessary requirements: Coq v8.15.0 and Erlang/OTP v22.0. The files should be compiled in the following order (by `make` or manually):

1. `Core_Erlang_Syntax.v`: The abstract syntax;
2. `Core_Erlang_Induction.v`: Induction principles for patterns, expressions and values;
3. `Core_Erlang_Equalities.v`: Decidable and Boolean equalities and comparisons;
4. `Core_Erlang_Helpers.v`: Helpers functions for the semantics;
5. `Core_Erlang_Environment.v`: Variable environment;
6. `Core_Erlang_Side_Effects.v`: Side effect concepts;
7. `Core_Erlang_Auxiliaries.v`: The semantics of natively implemented functions and primitive operations;
8. `Core_Erlang_Module_Auxiliaries`: Auxiliary definitions for handling modules;
9. `Core_Erlang_Functional_Big_Step.v`: An initial functional big-step semantics for testing purposes;
10. `Core_Erlang_Semantics.v`: The traditional natural semantics itself;
11. `Core_Erlang_Coverage.v`: The previous functional big-step semantics equipped with an additional configuration cell to enable coverage measuring;
12. `Core_Erlang_Tactics.v`: Evaluation tactic for the traditional big-step semantics.

The tests (with the `Automated` substring) can be proved after compiling the semantics in any order.

The proofs about the semantics should be compiled in the following order after compiling the semantics:

1. `Core_Erlang_Determinism_Helpers.v`: Helper lemmas for the proof of determinism;
2. `Core_Erlang_Proofs.v`: Some proofs about the properties of the semantics (e.g. determinism);
3. `Core_Erlang_Equivalence_Proofs.v`: Expression pattern equivalences;
4. `Core_Erlang_Semantics_Equivalence.v`: Proof of equivalence of big-step and functional big-step semantics.

# Published Papers and Related Work

- Péter Bereczky, Dániel Horpácsi and Simon Thompson, A Proof Assistant Based Formalisation of Core Erlang, 2020, https://doi.org/10.1007/978-3-030-57761-2_7
- Péter Bereczky, Dániel Horpácsi and Simon Thompson, Machine-Checked Natural Semantics for Core Erlang: Exceptions and Side Effects, 2020, In Proceedings of the 19th ACM SIGPLAN International Workshop on Erlang, https://doi.org/10.1145/3406085.3409008
- Péter Bereczky, Dániel Horpácsi, Judit Kőszegi, Soma Szeier, and Simon Thompson, Validating Formal Semantics by Property-Based Cross-Testing, 2020, In Proceedings of the 32nd Symposium on Implementation and Application of Functional Languages (IFL 2020). Association for Computing Machinery, New York, NY, USA, 150–161. https://doi.org/10.1145/3462172.3462200
- Péter Bereczky, Semantics comparison, 2020, https://github.com/harp-project/Semantics-comparison

# Acknowledgement

This project has been supported by the European Union, co-financed by the European Social fund (EFOP-3.6.2-16-2017-00013, Thematic Fundamental Research Collaborations Grounding Innovation in Informatics and Infocommunications).

Supported by the project "Integrált kutatói utánpótlás-képzési program az informatika és számítástudomány diszciplináris területein (Integrated program for training new generation of researchers in the disciplinary fields of computer science)", No.  EFOP-3.6.3-VEKOP-16-2017-00002. The project has been supported by the European Union and co-funded by the European Social Fund.

