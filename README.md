# Formal_ML [![Build Status](https://travis.ibm.com/formal-ml/Formal_ML.svg?token=XczbKxqtWXAe2zryXPvK&branch=master)](https://travis.ibm.com/formal-ml/Formal_ML)
Formalization of Machine Learning Theory with Applications to Program Synthesis

This repository contains a partial formalization of key results from https://arxiv.org/pdf/1804.07795.pdf

## Getting Started

To compile the Coq code in this repository, first install opam [opam (ocaml package manager)](https://opam.ocaml.org/).
Add support for coq ocaml repositories: `opam repo add coq-released --set-default https://coq.inria.fr/opam/released`.
If you want to create a local environment (switch), you can run `opam switch create nnsopt 4.07.0`.
Next, run `opam install . --deps-only`.  This should install all the dependencies needed, including Coq.

Once the prerequisites are installed, run `make` to compile it.

Alternatively, the included Docker file can be built using Docker to compile the coq code in a suitable environment.
`docker build --build-arg=coq_image="coqorg/coq:8.8.2" --pull -t nn_sopt .`


This repository is distributed under the terms of the Apache 2.0 License, see LICENSE.txt.
It is currently in an Alpha release, without warranties of any kind.  Keep in mind that this is an active exploratory research project.
