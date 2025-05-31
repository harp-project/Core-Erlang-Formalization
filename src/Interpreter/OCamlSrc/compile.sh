#!/bin/bash

ocamlc -i interpreter.ml > interpreter.mli

ocamlc -c utils.mli
ocamlc -c utils.ml
ocamlc -c CoqExtraction.mli
ocamlc -c CoqExtraction.ml
ocamlc -c interpreter.mli
ocamlc -c interpreter.ml

ocamlopt utils.cmx CoqExtraction.cmx interpreter.cmx -o Interpreter 
