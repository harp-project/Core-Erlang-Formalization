# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := CoqMakefile extra-stuff extra-stuff2 extract
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

####################################################################
##                      Your targets here                         ##
####################################################################

# Extracts the interpreter and the example programs to Haskell, preprocesses
# the result, and builds the Haskell project with cabal:
#   src/Interpreter/HaskellSrc/exe/RocqExtraction.hs
#   src/Interpreter/HaskellSrc/exe/ExampleProgs.hs
# The extractions are always run from the project root (the output paths in
# HaskellExtraction.v and ExampleProgExtraction.v are relative to it), and the
# raw extracted RocqExtraction.hs is always preprocessed exactly once, right
# after being generated.
EXAMPLE_ASTS := $(wildcard src/Interpreter/ExampleASTs/rocqAST/*.v)
EXAMPLE_VOS  := $(EXAMPLE_ASTS:.v=.vo)
HSSRC        := src/Interpreter/HaskellSrc

# the example ASTs are not part of _CoqProject
$(EXAMPLE_VOS): %.vo: %.v
	$(COQBIN)rocq compile -R src CoreErlang $<

.PHONY: extract
extract: CoqMakefile
	$(MAKE) --no-print-directory -f CoqMakefile src/Syntax.vo src/Interpreter/StepFunctions.vo src/Interpreter/Scheduler.vo
	$(MAKE) --no-print-directory $(EXAMPLE_VOS)
	tmp=$$(mktemp -d) && \
	  $(COQBIN)rocq compile -R src CoreErlang -o $$tmp/HaskellExtraction.vo src/Interpreter/HaskellExtraction.v && \
	  $(COQBIN)rocq compile -R src CoreErlang -o $$tmp/ExampleProgExtraction.vo src/Interpreter/ExampleProgExtraction.v; \
	  status=$$?; rm -rf $$tmp; exit $$status
	cd $(HSSRC) && ./preprocess.sh exe/RocqExtraction.hs
	grep -q '^import RocqExtraction' $(HSSRC)/exe/ExampleProgs.hs || \
	  sed -i 's/^import qualified Prelude$$/import qualified Prelude\nimport RocqExtraction/' $(HSSRC)/exe/ExampleProgs.hs
	cd $(HSSRC) && cabal build

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
