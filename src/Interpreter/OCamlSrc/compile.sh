#!/bin/bash

ocamlc -i utils.ml > utils.mli
ocamlc -i RocqExtraction.ml > RocqExtraction.mli
ocamlc -i interpreter.ml > interpreter.mli

ocamlc -c utils.mli
ocamlc -c utils.ml
ocamlc -c RocqExtraction.mli
ocamlc -c RocqExtraction.ml
ocamlc -c interpreter.mli
ocamlc -c interpreter.ml

ocamlc utils.cmo RocqExtraction.cmo interpreter.cmo -o Interpreter 
