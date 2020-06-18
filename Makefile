# Contains the list of all the Coq modules
include Makefile.coq_modules

FILES = $(addprefix coq/,$(MODULES:%=%.v))

all: coq ocaml

coq: Makefile.coq
	@$(MAKE) -f Makefile.coq

Makefile.coq: Makefile Makefile.coq_modules $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

ocaml: coq
	@$(MAKE) -C ocaml native

clean-coq:
	- @$(MAKE) -f Makefile.coq clean

clean-ocaml:
	@$(MAKE) -C ocaml clean

clean: clean-coq clean-ocaml

.PHONY: all ocaml clean clean-coq coq 
