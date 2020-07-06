ARG coq_image="coqorg/coq:8.9.1"
FROM ${coq_image}

WORKDIR /home/coq

COPY --chown=coq:coq Formal_ML.opam ./

RUN ["/bin/bash", "--login", "-c", "set -x \
  && if [ -n \"${COMPILER_EDGE}\" ]; then opam switch ${COMPILER_EDGE} && eval $(opam env); fi \
  && opam update -y \
  && opam install -y -j ${NJOBS} . \
  && opam clean -a -c -s --logs"]


COPY --chown=coq:coq _CoqProject Makefile Makefile.coq_modules ./
COPY --chown=coq:coq coq coq
COPY --chown=coq:coq ocaml ocaml

RUN ["/bin/bash", "--login", "-c", "set -x \
      && make coq"]

RUN ["/bin/bash", "--login", "-c", "set -x \
      && make"]