# Contains the list of all the Coq modules
include Makefile.coq_modules

FILES = $(addprefix coq/,$(MODULES:%=%.v))

all: coq

coq: Makefile.coq
	@$(MAKE) -f Makefile.coq

Makefile.coq: Makefile Makefile.coq_modules $(FILES)
	@coq_makefile -f _CoqProject $(FILES) -o Makefile.coq

clean-coq:
	- @$(MAKE) -f Makefile.coq clean

clean: clean-coq

.PHONY: all clean clean-coq coq 
