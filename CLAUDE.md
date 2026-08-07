# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Project overview

A formalisation of a subset of Core Erlang in Rocq (Coq). It defines the abstract syntax, a static
(scoping) semantics, several dynamic semantics (big-step, functional big-step, frame-stack, and a
concurrent extension of the frame-stack semantics), program-equivalence theories (logical relations,
CIU, contextual, bisimulation), and a formally-based interpreter extracted to Haskell/OCaml. There is
no separate application code: the repository *is* the proof development, under the `CoreErlang` Rocq
namespace (`-R src CoreErlang`, see `_CoqProject`).

Because this is a proof development, "compiling" a file **is** checking every proof in it — a file that
fails to compile means a broken/incomplete proof, not a build/lint issue in the usual sense.

## Build

Requirements: Rocq ≥ 9.1, stdpp ≥ 1.12.0 (installable via opam, see `coq-core-erlang-formalization.opam`).

```bash
make                    # builds everything listed in _CoqProject, in dependency order
```

`make` regenerates `CoqMakefile` from `_CoqProject` via `rocq makefile` and delegates to it, so any new
file must be added to `_CoqProject` (and, for reference, `compilationorder.txt` lists the equivalent raw
`coqc` invocations in build order).

To compile/check a single file (and everything it transitively depends on that isn't already built):

```bash
make src/Manipulation.v          # or the corresponding .vo target: make src/Manipulation.vo
rocq compile -R src CoreErlang src/Manipulation.v   # direct invocation, same effect, no dependency tracking
```

`make clean` cleans build artifacts (`.vo`/`.vos`/`.vok`/`.glob`).

## Tests

There is no separate test runner. Tests are Rocq `Example`/`Goal ... Proof. ... Qed.` files that only
compile if the stated fact actually holds; running `make`/`rocq compile` on them *is* running the tests.
Relevant test files: `src/FrameStack/Tests/*.v`, `src/Interpreter/Tests.v`,
`src/FrameStack/Tests/SubstSemanticsAutoSolverTests.v`, `src/BigStep/Tests/*.v`. To "run" one, just
compile it (e.g. `make src/FrameStack/Tests/Tests.v`); a `Qed.` that goes through is a pass, an error is
a failure.

## Architecture

### Nameless syntax, one mutual type

`src/Syntax.v` defines the whole abstract syntax — `Exp`, `Val`, `NonVal`, and `Pat` — as a *single*
mutually-recursive `Inductive ... with ...` block, using a nameless (de Bruijn-index) variable
representation throughout (no `PVar name`, just position-based binding). `Pat` is mutually recursive
with `Exp` because bitstring pattern segments (`PBin`) carry a `Segment Pat Exp` size field that is a
real runtime expression, not a syntactic literal — so renaming/substitution genuinely has to walk into
patterns, and patterns can't be defined independently of `Exp`. Don't try to "simplify" this by pulling
`Pat` out into its own non-mutual type; that was tried and reverted for exactly this reason.

### Why there's a whole file of hand-written induction schemes

Because `Exp`/`Val`/`NonVal`/`Pat` are mutually recursive and parametric over nested lists (`list Exp`,
`list (Pat * Pat)`, `list (Segment Pat Exp)`, ...), Rocq's auto-derived `Exp_ind` etc. are too weak (no
usable induction hypothesis for elements buried inside those lists). `src/Induction.v` hand-derives the
real combined scheme (`Exp_ind` from `Exp_ind2`/`NVal_ind2`/`Val_ind2`/`Pat_ind2`, plus a
`Pat`-only `Pat_ind_weakened` for proofs that don't need to touch `Exp` at all, e.g. `PatVars`
invariance lemmas). Most other files layer their *own* combined scheme on top of their own inductive
relation the same way — e.g. `src/Scoping.v`'s `scoped_ind` is `Combined Scheme ... from
ExpScoped_ind2, ValScoped_ind2, NonValScoped_ind2, PatScoped_ind2`.

**Consequence for editing:** adding a constructor, or adding a premise to an existing constructor, in one
of these mutually-defined types/relations changes the arity of the corresponding combined scheme. Every
`eapply Exp_ind with (Q := ...) (QV := ...) ...`-style proof downstream gets one more motive to supply
and one more goal in the bullet (`*`/`-`/`+`) sequence; existing bullets can silently misalign (Rocq
reports a bullet-mismatch or a `rewrite`/`apply` that can't find its target, often several bullets away
from the actual cause). When this happens, don't guess at hypothesis names — probe the actual goal state
(e.g. `Show.`/`Show 1. Show 2. ...` inserted into a scratch copy of the proof, or step through with
`rocq_start`/`rocq_check` if the `rocq-mcp` tools are available) rather than pattern-matching blindly
against a similar-looking bullet elsewhere.

### The recurring "mutual theorem" pattern

`src/Manipulation.v` and `src/ScopingLemmas.v` are full of theorems shaped like:

```coq
Theorem foo :
     (forall e ..., <property about Exp>)
  /\ (forall e ..., <property about NonVal>)
  /\ (forall e ..., <property about Val>)
  /\ (forall p ..., <property about Pat>).
Proof.
  eapply Exp_ind with
    (Q := ...) (QV := ...) (R := ...) (RV := ...) (VV := ...) (W := ...) (Z := ...)
    (PQ := ...) (PR := ...) (PT := ...);
  intros.
  (* Exp *) * ... * ...
  (* Val *) * ... (10 constructors)
  (* NonVal *) * ... (15 constructors)
  (* Pattern *) * ... (7 constructors)
  (* List *) * ... (nil/cons pair per list-motive, ~10 pairs)
Qed.
```

one motive per recursively-visited list shape, one bullet per constructor in a fixed order, then one
nil/cons bullet pair per list motive at the end. Downstream code destructures the resulting N-way
conjunction positionally, e.g. `pose proof foo as [H1 [H2 [H3 H4]]]` or `proj1 (proj2 (proj2 foo))` —
these are arity-sensitive and silently grab the wrong (often a stale compound) hypothesis if the
conjunction's shape changed upstream without updating every call site.

### Module layering

Within `src/` (core, syntax-level):
`Basics` → `Syntax` → `Induction` → `Equalities`/`SideEffects` → `Scoping` (static semantics /
well-scopedness judgement, `EXP Γ ⊢ e` notation) → `Auxiliaries`/`Maps` → `Manipulation` (renaming and
substitution + their algebraic properties) → `ScopingLemmas` (proves the static semantics and
substitution commute, e.g. substituting a well-scoped closing substitution into a well-scoped term
preserves well-scopedness) → `Matching` (pattern matching) → `StrictEqualities`.

On top of that:
- **`FrameStack/`** — the primary sequential semantics (substitution-based, reduction/frame-stack style)
  and the equivalence theory built on it: `LogRel` (logical relations) → `Compatibility` → `CIU` → `CTX`,
  plus `Termination.v` and example equivalence proofs in `Examples.v`.
- **`Concurrent/`** — node/process semantics built on top of `FrameStack`, plus bisimulation-based
  equivalence (`StrongBisim`/`WeakBisim`/`BarbedBisim`) and PID-renaming theory. `Experimental/` holds
  work-in-progress variants not wired into the main development.
- **`BigStep/`** — an older natural/functional big-step semantics with its **own separate copy of the
  syntax** (`BigStep/Syntax.v`, distinct from `src/Syntax.v`). Per the README this is being phased out in
  favour of the shared syntax used everywhere else; don't assume `BigStep` types are interchangeable with
  the main `Exp`/`Val`/`Pat` types.
- **`Interpreter/`** — a function-based reimplementation of the frame-stack step relation
  (`StepFunctions.v`), proved equivalent to the relational semantics (`Equivalences.v`), extracted to
  Haskell (`HaskellExtraction.v`) and OCaml (`OCamlExtraction.v`) for the executable interpreter in
  `HaskellSrc/`/`OCamlSrc/`.
- **`Symbolic/`** — symbolic execution tactics and theorems layered on the frame-stack semantics.

### stdpp

The development leans heavily on `stdpp` (`From stdpp Require ...`) rather than only vanilla Rocq
stdlib — e.g. `Forall`/list lemmas, `bvn`/bitvector support for bitstrings, and its `Scheme All for`
mechanism (used in `Syntax.v` for `list`/`prod`/`Segment`) to get nested-container induction hypotheses
where possible.

### Rocq-mcp

AI-based development should heavily utilize features of rocq-mcp, especially in large proofs where interactive proof development is much more advantageous than proof generation and recompilation.

