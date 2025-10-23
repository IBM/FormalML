# Contains the list of all the Coq modules
include Makefile.rocq_modules

ROCQ_FILES = $(addprefix coq/,$(MODULES:%=%.v))

all: rocq

rocq: Makefile.rocq
	@$(MAKE) -f Makefile.rocq

Makefile.rocq: Makefile Makefile.rocq_modules $(ROCQ_FILES)
	@rocq makefile -f _RocqProject $(ROCQ_FILES) -o Makefile.rocq

clean-rocq:
	- @$(MAKE) -f Makefile.rocq clean


ROCQ_FILES_FOR_DOC = $(MODULES:%=%.v)
GLOB_FILES_FOR_DOC = $(MODULES:%=%.glob)

doc: rocq
	mkdir -p documentation/html
	rm -f documentation/html/*.html
	cd coq && coq2html -d ../documentation/html -base FormalML -external http://coquelicot.saclay.inria.fr/html/ Coquelicot $(ROCQ_FILES_FOR_DOC) $(GLOB_FILES_FOR_DOC)

clean: clean-rocq
	rm -rf documentation/html

.PHONY: all clean clean-rocq rocq doc
