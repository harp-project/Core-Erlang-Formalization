# Interpreter

Using the interpreter in it's current state is not the most straightforward. 
A number of things are hard-coded in, and they need to be replaced by hand. 
The Pretty-printer currently cannot translate into Haskell code directly, 
which is why a fresh extraction needs to be performed. In the future we 
want to convert into Haskell directly, which would eliminate performing 
steps 5-12 altogether. The current process is as follows:

1. Build the whole project using `make`. Note that installing **std++** is required. This only needs to be done once.
2. Since the module system is not formalized yet, every instance of `spawn/3` needs to be replaced with a 2 parameter spawn (that does not actually exist in the Erlang system). In Erlang source files, replace every instance of `spawn(?MODULE, function, args)` with `spawn(fun (...) -> function (...) end, args)`, passing parameters to the function if needed.
3. Convert the Erlang source file to the Coq representation using the Pretty-printer. The Pretty-printer can be found in this repository: [erlang-semantics-testing](https://github.com/harp-project/erlang-semantics-testing/tree/frame-stack)
    1. Navigate to the converter folder
    2. Start the Erlang shell with `erl`
    3. Compile cst\_to\_ast with `c(cst_to_ast).`
    4. Compile pretty\_printer\_fs with `c(pretty_printer_fs).`
    5. Convert the source to the Coq representation. The input and output files need to be given.
        - From an Erlang source file: `cst_to_ast:from_erl("example.erl", frameStack, "example.v").`
        - From a Core Erlang source file: `cst_to_ast:from_core("example.core", frameStack, "example.v").`
    6. If the Pretty-printer gives warnings, the source code contains currently unsupported language features
4. Move the converted Erlang source file into src/Interpreter/ExampleASTs/coqAST
5. Open the file in Coqide and rename the definition, e.g. to `testexample`
6. Compile the file in Coqide
7. In src/Interpreter (this folder), open HaskellExtraction with Coqide
8. Put the file name in line 6 next to the other import files, without the **.v** extension
9. Put `;RExp testexample` (replaced with the real program name given in point 4) in the list of redexes in line 9
10. Compile HaskellExtraction.v in Coqide
11. Navigate to src/Interpreter/HaskellSrc inside a terminal window
12. Run `./preprocess.sh exe/CoqExtraction.hs`
13. Inside exe/Interpreter.hs, the end of line 14 can be changed to the program we want to run (e.g. `testexample`)
14. Build the Interpreter by running `cabal build Interpreter`
15. The interpreter can now be ran using `cabal run Interpreter`

The interpreter will run the `main` function defined in the original Erlang source file, with an empty list of arguments.
