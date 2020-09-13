# Contains the list of all the Coq modules
include Makefile.coq_modules

COQ_FILES = $(addprefix coq/,$(MODULES:%=%.v))
GLOB_FILES = $(addprefix coq/,$(MODULES:%=%.glob))

all: coq ocaml

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


doc: coq
	mkdir -p documentation/html
	rm -f documentation/html/*.html
	coq2html -d documentation/html -base FormalML $(COQ_FILES) $(GLOB_FILES)

test: coq ocaml
	./bin/nnopt

clean: clean-coq clean-ocaml
	rm -rf documentation/html

.PHONY: all ocaml clean clean-coq coq test doc
