# Core Erlang Formalisation

In this repository you can find the formalisation of a sequential subset of Core Erlang in Coq Proof Assistant. There is also a study about this formal definition, you can find it inside the Documentation folder.

# Compilation process

Necessary requirements: Coq v8.11.2. and Erlang/OTP v22.3. The files should be compiled in the following order:

1. `Core_Erlang_Syntax.v`: The abstract syntax;
2. `Core_Erlang_Equalities.v`: Decidable and Boolean equalities and comparisons;
3. `Core_Erlang_Helpers.v`: Helpers functions for the semantics;
4. `Core_Erlang_Environment.v`: Variable environment;
5. `Core_Erlang_Side_Effects.v`: Side effect concepts;
6. `Core_Erlang_Semantics.v`: The natural semantics itself.

The tests (`Core_Erlang_Tests.v`, `Core_Erlang_Exception_Tests.v`, `Core_Erlang_Side_Effect_Tests.v`, `Core_Erlang_Side_Effect_Exception_Tests.v`) can be proved after compiling the semantics in any order.

The proofs about the semantics should be compiled in the following order after compiling the semantics:

1. `Core_Erlang_Determinism_Helpers.v`: Helper lemmas for the proof of determinism;
2. `Core_Erlang_Proofs.v`: Some proofs about the properties of the semantics (e.g. determinism);
3. `Core_Erlang_Equivalence_Proofs.v`: Expression pattern equivalences.

# Acknowledgement

This project has been supported by the European Union, co-financed by the European Social fund (EFOP-3.6.2-16-2017-00013, Thematic Fundamental Research Collaborations Grounding Innovation in Informatics and Infocommunications).
