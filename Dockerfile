ARG coq_image="coqorg/coq:8.9.1"
FROM ${coq_image}

RUN ["/bin/bash", "--login", "-c", "set -x \
  && if [ -n \"${COMPILER_EDGE}\" ]; then opam switch ${COMPILER_EDGE} && eval $(opam env); fi \
  && opam update -y \
  && opam install -y -j ${NJOBS} coq-mathcomp-ssreflect coq-coquelicot coq-flocq coq-interval ocamlbuild base64 menhir csv \ 
  && opam config list && opam repo list && opam list \
  && opam clean -a -c -s --logs"]

WORKDIR /home/coq

COPY --chown=coq:coq _CoqProject Makefile Makefile.coq_modules ./
COPY --chown=coq:coq coq coq
COPY --chown=coq:coq ocaml ocaml

RUN ["/bin/bash", "--login", "-c", "set -x \
      && make coq"]

RUN ["/bin/bash", "--login", "-c", "set -x \
      && make"]
