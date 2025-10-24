 # Formal_ML [![Build Status](https://github.com/IBM/FormalML/workflows/Tests/badge.svg?branch=master)](https://github.com/IBM/FormalML/actions?query=workflow%3ATests+branch%3Amaster)
 Formalization of Machine Learning Theory with Applications to Program Synthesis

 This repository contains
  - a partial formalization of key results from https://arxiv.org/abs/1804.07795
  - The CertRL library as reported in https://arxiv.org/abs/2009.11403
  - a formalization of Dvoretzky's stochastic approximation theorem as reported in https://arxiv.org/abs/2202.05959

 ## Getting Started

 To compile the [Rocq](https://rocq-prover.org/) (previously known as Coq) code in this repository, [Install Rocq](https://rocq-prover.org/install).  For example:
  - first install opam [opam (ocaml package manager)](https://opam.ocaml.org/).
  - Add support for rocq ocaml repositories: `opam repo add rocq-released https://rocq-prover.org/opam/released`
  - If you want to create a local environment (switch), you can run `opam switch create formalml 4.14.2`.
  - Next, run `opam install . --deps-only`.  This should install all the dependencies needed, including Rocq.
  - Once the prerequisites are installed, run `make` to compile it.

 Alternatively, the included Docker file can be built using Docker to compile the rocq code in a suitable environment.
 `docker build --pull -t formalml .`

 ## License
 This repository is distributed under the terms of the Apache 2.0 License, see LICENSE.txt.
 It is currently in an Alpha release, without warranties of any kind.  Keep in mind that this is an active exploratory research project.
