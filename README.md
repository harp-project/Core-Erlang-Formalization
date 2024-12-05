# Core Erlang Formalisation

In this repository you can find the formalisation of a sequential subset of Core Erlang in Coq Proof Assistant. The formalisation also includes a definition of the module system in Core Erlang.

# Compilation process

Necessary requirements: Coq v8.20.0, stdpp v1.11.0 and Erlang/OTP v23.0 (not necessary for the Coq developments). The library is compilable by using `make`. In the following list, we give a brief description about the contents of the files.

The main module `CoreErlang` includes the common features for all semantics:

- `src/Basics.v`: fundamental types, and lemmas about them and the built-in features of Coq;
- `src/Syntax.v`: the abstract syntax of Core Erlang;
- `src/Induction.v`: induction principles for the syntax;
- `src/Equalities.v`: decidable and boolean equalities and comparison based on the abstract syntax;
- `src/SideEffects.v`: side effect tracing concepts;
- `src/Scoping.v`: the static semantics (scoping relation) of Core Erlang;
- `src/Auxiliaries.v`: functions simulating built-in features of the standard library of Erlang, and corresponding tests and lemmas;
- `src/Maps.v`: concepts supporting the syntax of Core Erlang's maps;
- `src/Manipulation.v`: definition of substitution, and corresponding theorems;
- `src/ScopingLemmas.v`: theorems and lemmas about the connection between the static semantics and substitutions;
- `src/Matching.v`: concepts describing pattern matching for Core Erlang.

The submodule `FrameStack` includes a frame stack semantics for Core Erlang:

- `src/FrameStack/Frames.v`: the syntax of frames (which express continuation);
- `src/FrameStack/SubstSemantics.v`: the definition of a substitution-based frame stack semantics;
- `src/FrameStack/Tests/Tests.v`: tests about the frame stack semantics;
- `src/FrameStack/Tests/ExceptionTests.v`: tests about the frame stack semantics;
- `src/FrameStack/Termination.v`: the definition of an inductive frame stack termination relation;
- `src/FrameStack/SubstSemanticsLemmas.v`: lemmas and theorems about the properties of the semantics and termination;
- `src/FrameStack/LogRel.v`: the definition of program equivalence based on logical relations;
- `src/FrameStack/Compatibility.v`: the compatibility property (a form of congruence) of the logical relations;
- `src/FrameStack/CIU.v`: the definition of CIU equivalence, and a proof that this definition coincides with the definition based on logical relations;
- `src/FrameStack/Examples.v`: example program equivalence proofs (based on CIU equivalence);
- `src/FrameStack/CTX.v`: the definition of contextual equivalence.

Natural and functional big-step semantics are included in the submodule `BigStep`. We note that in the future the syntax for the big-step semantics (listed below) will be removed, and these semantics will also use the syntax defined in the main module.

- `src/BigStep/Syntax.v`: the abstract syntax of Core Erlang for the big-step approaches;
- `src/BigStep/Induction.v`: the induction principle for this syntax;
- `src/BigStep/Equalities.v`: decidable and boolean equalities and comparison based on the abstract syntax;
- `src/BigStep/Helpers.v`: helper functions for the semantics;
- `src/BigStep/Environment.v`: evaluation environment;
- `src/BigStep/SideEffects.v`: side effect concepts;
- `src/BigStep/Auxiliaries.v`: the semantics of natively implemented functions and primitive operations;
- `src/BigStep/ModuleAuxiliaries.v`: auxiliary definitions for handling modules;
- `src/BigStep/FunctionalBigStep.v`: a functional big-step semantics for testing purposes;
- `src/BigStep/BigStep.v`: the traditional natural semantics itself;
- `src/BigStep/Coverage.v`: the previous functional big-step semantics equipped with an additional configuration cell to enable coverage measuring;
- `src/BigStep/Tactics.v`: evaluation tactic for the traditional big-step semantics.
- `src/BigStep/DeterminismHelpers.v`: helper lemmas for the proof of determinism;
- `src/BigStep/SemanticsProofs.v`: some proofs about the properties of the big-step semantics (e.g. determinism);
- `src/BigStep/SemanticsEquivalence.v`: proof of equivalence of big-step and functional big-step semantics.
- `src/BigStep/FullEquivalence.v`: a strict program equivalence concept;
- `src/BigStep/WeakEquivalence.v`: a weakened program equivalence concept;
- `src/BigStep/WeakEquivalenceExamples.v`: example program equivalences;
- `src/BigStep/EquivalenceProofs.v`: further example program equivalences.

Tests about the natural and functional big-step semantics:

- `src/BigStep/Tests/AutomatedTests.v`;
- `src/BigStep/Tests/AutomatedSideEffectTests.v`;
- `src/BigStep/Tests/AutomatedExceptionTests.v`;
- `src/BigStep/Tests/AutomatedSideEffectExceptionTests.v`.

Concurrent semantics based on the sequential semantics of `FrameStack` is defined in the submodule `Concurrent`.

- `src/Concurrent/PIDRenaming.v`: the defintion of renaming for process identifiers and theorems about its properties (w.r.t. the sequential semantics);
- `src/Concurrent/ProcessSemantics.v`: the semantics for processes (process-local semantics) based on actions propagated from the inter-process semantics;
- `src/Concurrent/NodeSemantics.v`: the semantics of nodes consisting of processes (inter-process semantics);
- `src/Concurrent/NodeSemanticsLemmas.v`: theorems about the properties of the concurrent (both process-local and inter-process) semantics;
- `src/Concurrent/StrongBisim.v`: a definition of program equivalence based on strong bisimulation;
- `src/Concurrent/WeakBisim.v`: a definition of program equivalence based on weak bisimulation;
- `src/Concurrent/BarbedBisim.v`: a definition of program equivalence expressed as a barbed bisimulation (which is less restrictive than weak bisimulations);
- `src/Concurrent/BisimRenaming.v`: a proof that process idenfier renaming is a barbed bisimulation;
- `src/Concurrent/BisimReductions.v`: further properties of barbed bisimulations, proof of silent evaluation being a bisimulation;
- `src/Concurrent/MapPmap.v`: a case study about the equivalence of sequential and concurrent list transformation;
- experimental/work-in progress features are included in `src/Concurrent/Experimental`.

# Published Papers and Related Work

- Péter Bereczky, Dániel Horpácsi and Simon Thompson, A Proof Assistant Based Formalisation of Core Erlang, 2020, https://doi.org/10.1007/978-3-030-57761-2_7
- Péter Bereczky, Dániel Horpácsi and Simon Thompson, Machine-Checked Natural Semantics for Core Erlang: Exceptions and Side Effects, 2020, In Proceedings of the 19th ACM SIGPLAN International Workshop on Erlang, https://doi.org/10.1145/3406085.3409008
- Péter Bereczky, Dániel Horpácsi, Judit Kőszegi, Soma Szeier, and Simon Thompson, Validating Formal Semantics by Property-Based Cross-Testing, 2020, In Proceedings of the 32nd Symposium on Implementation and Application of Functional Languages (IFL 2020). Association for Computing Machinery, New York, NY, USA, 150–161. https://doi.org/10.1145/3462172.3462200
- Péter Bereczky, Dániel Horpácsi, Simon Thompson, A Comparison of Big-step Semantics Definition Styles, 2024, http://ac.inf.elte.hu/Vol_057_2024/117_57.pdf
- Dániel Horpácsi, Péter Bereczky, Simon Thompson, Program equivalence in an untyped, call-by-value functional language with uncurried functions, 2023, Journal of Logical and Algebraic Methods in Programming, Volume 132, 100857, https://doi.org/10.1016/j.jlamp.2023.100857
- Péter Bereczky, Dániel Horpácsi, Simon Thompson, A Formalisation of Core Erlang, a Concurrent Actor Language, 2024, Acta Cybernetica, https://doi.org/10.14232/actacyb.298977
- Péter Bereczky, Dániel Horpácsi, Simon Thompson, A frame stack semantics for sequential Core Erlang, 2023, https://doi.org/10.1145/3652561.3652566
- Péter Bereczky, Dániel Horpácsi, Simon Thompson, Program Equivalence in the Erlang Actor Model, 2024, https://doi.org/10.3390/computers13110276

# Acknowledgement

This project has been supported by the European Union, co-financed by the European Social fund (EFOP-3.6.2-16-2017-00013, Thematic Fundamental Research Collaborations Grounding Innovation in Informatics and Infocommunications).

Supported by the project "Integrált kutatói utánpótlás-képzési program az informatika és számítástudomány diszciplináris területein (Integrated program for training new generation of researchers in the disciplinary fields of computer science)", No.  EFOP-3.6.3-VEKOP-16-2017-00002. The project has been supported by the European Union and co-funded by the European Social Fund.

The project has been supported by ÚNKP-21-3, ÚNKP-22-3 and ÚNKP-23-3 New National Excellence Program of the Ministry for Innovation of Hungary.
