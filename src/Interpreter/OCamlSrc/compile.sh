#!/bin/bash

ocamlc -i utils.ml > utils.mli
ocamlc -i CoqExtraction.ml > CoqExtraction.mli
ocamlc -i interpreter.ml > interpreter.mli

ocamlc -c utils.mli
ocamlc -c utils.ml
ocamlc -c CoqExtraction.mli
ocamlc -c CoqExtraction.ml
ocamlc -c interpreter.mli
ocamlc -c interpreter.ml

ocamlc utils.cmo CoqExtraction.cmo interpreter.cmo -o Interpreter 
