# Formal_ML [![Build Status](https://travis.ibm.com/formal-ml/Formal_ML.svg?token=XczbKxqtWXAe2zryXPvK&branch=master)](https://travis.ibm.com/formal-ml/Formal_ML)
Formalization of Machine Learning Theory with Applications to Program Synthesis

This repository contains a partial formalization of key results from https://arxiv.org/pdf/1804.07795.pdf

## Getting Started

To compile the Coq code in this repository, first install Coq, then install Coqlic.
This can be done by installing [opam (ocaml package manager)](https://opam.ocaml.org/) and running `opam install coq-coquelicot`

Once the prerequisites are installed, run `make` to compile it

Alternatively, the included Docker file can be built using Docker to compile the coq code in a suitable environment.
`docker build --build-arg=coq_image="coqorg/coq:8.8.2" --pull -t nn_sopt .`
