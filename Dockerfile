ARG coq_image="coqorg/coq:dev"
FROM ${coq_image}

RUN ["/bin/bash", "--login", "-c", "set -x \
  && if [ -n \"${COMPILER_EDGE}\" ]; then opam switch ${COMPILER_EDGE} && eval $(opam env); fi \
  && opam update -y \
  && opam install -y -j ${NJOBS} coq-mathcomp-ssreflect \
  && opam config list && opam repo list && opam list \
  && opam clean -a -c -s --logs"]

WORKDIR /home/coq

COPY _CoqProject Makefile Makefile.coq_modules ./
COPY coq coq

RUN ["/bin/bash", "--login", "-c", "set -x \
  && sudo chown -R coq:coq /home/coq \
  && make coq"]