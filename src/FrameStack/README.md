# Core Erlang frame stack semantics

This part of the repository contains the frame stack semantics of Core Erlang. It also includes different approaches to define the syntax, static semantics, and equivalence definitions.

# Compilation

To compile this part of the project, simply use `make`.

If the above does not work, compile each of the files with `coqc` in the order they have been defined in `_CoqProject` with the `-R src Core_Erlang` parameters.

