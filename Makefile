# Contains the list of all the Coq modules
include Makefile.coq_modules

COQ_FILES = $(addprefix coq/,$(MODULES:%=%.v))

all: coq # ocaml

coq: Makefile.coq
	@$(MAKE) -f Makefile.coq

Makefile.coq: Makefile Makefile.coq_modules $(COQ_FILES)
	@coq_makefile -f _CoqProject $(COQ_FILES) -o Makefile.coq

ocaml: coq
	@$(MAKE) -C ocaml native

clean-coq:
	- @$(MAKE) -f Makefile.coq clean

clean-ocaml:
	@$(MAKE) -C ocaml clean


COQ_FILES_FOR_DOC = $(MODULES:%=%.v)
GLOB_FILES_FOR_DOC = $(MODULES:%=%.glob)

doc: coq
	mkdir -p documentation/html
	rm -f documentation/html/*.html
	cd coq && coq2html -d ../documentation/html -base FormalML -external http://coquelicot.saclay.inria.fr/html/ Coquelicot $(COQ_FILES_FOR_DOC) $(GLOB_FILES_FOR_DOC)

test: coq ocaml
	./bin/nnopt

clean: clean-coq clean-ocaml
	rm -rf documentation/html

.PHONY: all ocaml clean clean-coq coq test doc
