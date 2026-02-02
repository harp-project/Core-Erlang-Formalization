# Interpreter

Using the interpreter in its current state is not the most straightforward. 
A number of things are hard-coded in, and they need to be replaced by hand. 
The Pretty-printer currently cannot translate into Haskell code directly, 
which is why a fresh extraction needs to be performed. In the future we 
want to convert into Haskell directly, which would eliminate performing 
steps 5-12 altogether. The current process is as follows:

1. Build the whole project using `make`. Note that installing **std++** is required. This only needs to be done once.
2. Since the module system is not formalized yet, every instance of `spawn/3` needs to be replaced with a 2 parameter spawn (that does not actually exist in the Erlang system). In Erlang source files, replace every instance of `spawn(?MODULE, function, args)` with `spawn(fun (...) -> function (...) end, args)`, passing parameters to the function if needed.
3. Convert the Erlang source file to the Coq representation using the Pretty-printer. The Pretty-printer can be found in this repository: [erlang-semantics-testing](https://github.com/harp-project/erlang-semantics-testing/)
    1. Navigate to the converter folder
    2. Start the Erlang shell with `erl`
    3. Compile cst\_to\_ast with `c(cst_to_ast).`
    4. Compile pretty\_printer\_fs with `c(pretty_printer_fs).`
    5. Convert the source to the Coq representation. The input and output file names need to be given. The input Erlang/Core Erlang file should contain a function `main/1`!
        - From an Erlang source file: `cst_to_ast:from_erl("example.erl", frameStack, "example.v").`
        - From a Core Erlang source file: `cst_to_ast:from_core("example.core", frameStack, "example.v").`
    6. If the Pretty-printer gives warnings, the source code contains currently unsupported language features
4. Move the converted Erlang source file into src/Interpreter/ExampleASTs/coqAST
5. Open the file in Coqide and rename the definition, e.g. to `testexample`
6. Compile the file in Coqide
7. In src/Interpreter (this folder), open ExampleProgExtraction.v with Coqide
8. Put the file name in line 6 next to the other import files, without the **.v** extension
9. Put `; testexample` (replaced with the real program name given in point 4) in the list of example programs (starting at line 8)
10. Compile ExampleProgExtraction.v in Coqide
11. Navigate to src/Interpreter/HaskellSrc inside a terminal window
12. In exe/ExampleProgs.hs, put in the line `import CoqExtraction` after the import of Prelude
13. Inside exe/Interpreter.hs, the definition `exampleForExec` (starting at line 12) can be changed to the program we want to run (e.g. `testexample`)
14. Build the Interpreter by running `cabal build Interpreter`
15. The interpreter can now be ran using `cabal run Interpreter`

The interpreter will run the `main` function defined in the original Erlang source file, with an empty list of arguments.

## TreeMaker

As of now, the TreeMaker is similar to the Interpreter in a sense that it isn't user-friendly and requires some steps to run.

0. In case you didn't play around with the Interpreter beforehand, perform steps 1-12 from the Interpreter's above how-to guide.
1. In the TreeMaker source file you can change configurable parameters (these being the Erlang program under test, tau step limit, and graph depth limit). Search for `-- configurable` comments to locate them.
2. You can also configure the intermediate output of the TreeMaker by commenting/uncommenting output segments in the main function (starts from line 267).
3. Build and run the TreeMaker (assuming you cwd is `./HaskellSrc`)
```bash
cabal build TreeMaker
cabal run TreeMaker
```
4. By the end the process should write `input.json` to `exe/tree-maker/graph-drawer` directory. In this directory you can also see `index.html`, which you can open in the browser
5. Having loaded the page, provide the generated `input.json` to see and interact with the graph. We do not guarantee an aesthetic layout. Styles can be configured in `exe/tree-maker/graph-drawer/js/main.js`.

## Re-extraction

This section provides technical details for re-extraction in case changes were made to the semantics. Before the new extraction, ensure the following:

- In case an auxiliary function was redefined, InterpreterAux.v and InterpreterAuxLemmas.v may need to be changed.
- In case reduction steps were redefined, StepFunctions.v and Equivalences.v definitely need to be changed.
- If the change in the semantics envolves gmap or gset operations, make sure to use the wrapped definitions in InterpreterAux.v, at least for the extracted version. The interpreter **will not work** if this is not done.

If the project compiles without errors, re-extracting the interpreter can be performed:

1. Compile HaskellExtraction.v in Coqide. This should generate a new CoqExtraction.hs file in `src/Interpreter/HaskellSrc/exe`
2. Navigate to src/Interpreter/HaskellSrc in a terminal window
3. Run the `./preprocess.sh exe/CoqExtraction.hs`

With these steps, the interpreter is ready to be re-built and run. However, this version does not include improved substitutions. These functions need to be replaced by hand. Steps 4-7 are optional, but improved substitutions give a big performance boost (~50%). The original CoqExtraction.hs file in this repo already uses improved substitutions.

4. Open exe/CoqExtraction.hs in a text editor
5. Delete every type and function definition from the definitions of renamings (`type Renaming = ...`) to list substitutions (`list_subst :: ...`)
6. Insert the contents of exe/subst\_replacement in the place of the deleted definitions
7. Replace all instances of the strings "list\_subst" and "idsubst" with blank strings ("")

Lastly, use cabal to build the project again.

8. Run `cabal build Interpreter`

It is normal for cabal to give warnings about bindings being shadowed in lambda expressions. These warnings usually come from `nat` and `Z` replacement, defined in `ExtrHaskellNatInteer` and `ExtrHaskellZInteger`.
