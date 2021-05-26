 # Formal_ML [![Build Status](https://github.com/IBM/FormalML/workflows/Tests/badge.svg?branch=master)](https://github.com/IBM/FormalML/actions?query=workflow%3ATests+branch%3Amaster)
 Formalization of Machine Learning Theory with Applications to Program Synthesis

 This repository contains
  - a partial formalization of key results from https://arxiv.org/abs/1804.07795
  - The CertRL library as reported in https://arxiv.org/abs/2009.11403

 ## Getting Started

 To compile the Coq code in this repository,
  - first install opam [opam (ocaml package manager)](https://opam.ocaml.org/).
  - Add support for coq ocaml repositories: `opam repo add coq-released --set-default https://coq.inria.fr/opam/released`.
  - If you want to create a local environment (switch), you can run `opam switch create nnsopt 4.07.0`.
  - Next, run `opam install . --deps-only`.  This should install all the dependencies needed, including Coq.
  - Once the prerequisites are installed, run `make` to compile it.

 Alternatively, the included Docker file can be built using Docker to compile the coq code in a suitable environment.
 `docker build --build-arg=coq_image="coqorg/coq:8.8.2" --pull -t nn_sopt .`

### note: on this branch, you will need to run `bash fetch_Lint_p.sh` to get and fix the `Lint_p` library code used on this branch.

 ## License
 This repository is distributed under the terms of the Apache 2.0 License, see LICENSE.txt.
 It is currently in an Alpha release, without warranties of any kind.  Keep in mind that this is an active exploratory research project.

  