#
# Copyright 2015-2016 IBM Corporation
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
# http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# User-level configuration
# include ../Makefile.config
# Contains the list of all the Coq modules
include ../Makefile.coq_modules

## Configuraton
NNOPT_HOME=$(CURDIR)/..

############# Shouldn't have to be changed after this
OCAMLBUILD= ocamlbuild \
		-no-links -classic-display \
		-tags annot -use-ocamlfind -package unix -package base64 -package csv

MENHIRFLAG=-use-menhir
#MENHIRFLAG=

## Mains
MAIN=nnopt

TARGET=native

## Toplevel
all: ../bin/$(MAIN)

native: ../bin/$(MAIN) 

## Extraction
VO_FILES = $(MODULES:%=../coq/%.vo)

extracted: extracted/StaticConfig.ml extracted/NnoptExtracted.ml extracted/NnoptExtracted.mli

extracted/StaticConfig.ml extracted/NnoptExtracted.ml extracted/NnoptExtracted.mli : $(VO_FILES) NnoptExtraction.v
	rm -rf extracted
	mkdir -p extracted
	echo "(* This file is generated *)" > extracted/StaticConfig.ml
	echo "let nnopt_home = \"$(NNOPT_HOME)\"" >> extracted/StaticConfig.ml
	(coqc -R ../coq FormalML NnoptExtraction.v)

## Native
../bin/$(MAIN): extracted $(MAIN).$(TARGET) ../bin
	cp _build/$(MAIN).$(TARGET) ../bin/$(MAIN)

../bin:
	@mkdir -p ../bin

$(MAIN).$(TARGET): extracted
	$(OCAMLBUILD) $(MENHIRFLAG) -Is extracted -Is src $(MAIN).$(TARGET)

## Clean

clean:
	ocamlbuild -clean -no-log
	rm -rf _build
	rm -f ../bin/$(MAIN) 

cleanall: clean
	rm -f NnoptExtraction.glob NnoptExtraction.vo .NnoptExtraction.aux
	rm -rf extracted
	rm -rf *~

.NOTPARALLEL: 

