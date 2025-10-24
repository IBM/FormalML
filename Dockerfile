ARG rocq_image="rocq/rocq-prover:9.0.1"
FROM ${rocq_image}

MAINTAINER Avi Shinnar "shinnar@us.ibm.com"

# needs to be a subdirectory to avoid causing problems with
# the /home/rocq/.opam directory (and probably other stuff)
WORKDIR /home/rocq

COPY --chown=rocq:rocq Formal_ML.opam ./formal_ml/

RUN ["/bin/bash", "--login", "-c", "set -x \
  && if [ -n \"${COMPILER_EDGE}\" ]; then opam switch ${COMPILER_EDGE} && eval $(opam env); fi \
  && opam update -y \
  && opam install --deps-only --with-test --with-doc -y -j ${NJOBS} ./formal_ml \
  && opam clean -a -c -s --logs"]


COPY --chown=rocq:rocq _RocqProject Makefile Makefile.rocq_modules ./formal_ml/
COPY --chown=rocq:rocq coq ./formal_ml/coq

RUN ["/bin/bash", "--login", "-c", "set -x && cd formal_ml && \
     make && make doc"]
