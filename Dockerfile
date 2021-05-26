ARG coq_image="coqorg/coq:8.11.2"
FROM ${coq_image}

MAINTAINER Avi Shinnar "shinnar@us.ibm.com"

# needs to be a subdirectory to avoid causing problems with
# the /home/coq/.opam directory (and probably other stuff)
WORKDIR /home/coq

COPY --chown=coq:coq Formal_ML.opam ./formal_ml/

RUN ["/bin/bash", "--login", "-c", "set -x \
  && if [ -n \"${COMPILER_EDGE}\" ]; then opam switch ${COMPILER_EDGE} && eval $(opam env); fi \
  && opam update -y \
  && opam install --deps-only --with-test --with-doc -y -j ${NJOBS} ./formal_ml \
  && opam clean -a -c -s --logs"]


COPY --chown=coq:coq breast-cancer-wisconsin.data breast-cancer-wisconsin.names ./formal_ml/
COPY --chown=coq:coq _CoqProject Makefile Makefile.coq_modules ./formal_ml/
COPY --chown=coq:coq coq ./formal_ml/coq
COPY --chown=coq:coq ocaml ./formal_ml/ocaml

RUN ["/bin/bash", "--login", "-c", "set -x \
  && if [ -n \"${COMPILER_EDGE}\" ]; then opam switch ${COMPILER_EDGE} && eval $(opam env); fi \
  && cd ./formal_ml && bash fetch_Lint_p.sh"]



RUN ["/bin/bash", "--login", "-c", "set -x && cd formal_ml && \
     make && make doc"]

CMD ["/bin/bash", "--login", "-c", "set -x && cd formal_ml && \
    make test"]