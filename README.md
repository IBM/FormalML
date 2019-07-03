# Formal_ML [![Build Status](https://travis.ibm.com/IBM-Research-AI/Formal_ML.svg?token=XczbKxqtWXAe2zryXPvK&branch=master)](https://travis.ibm.com/IBM-Research-AI/Formal_ML)
Formalization of Machine Learning Theory with Applications to Program Synthesis

## Getting Started

To compile the Coq code in this repository, first install Coq, then run `make`

Alternatively, the included Docker file can be built using Docker to compile the coq code in a suitable environment.
`docker build --build-arg=coq_image="coqorg/coq:8.8.2" --pull -t nn_sopt .`
