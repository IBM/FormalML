This subdirectory contains the [`elfic`](https://www.lri.fr/~sboldo/elfic/) library, which provided a [formal proof of the Lax-Milgram theorem](https://hal.inria.fr/hal-01391578/document). 

In particular, we use the Banach Fixed Point theorem as proven in the file `fixed_point.v`. 

We use this library as a dependency for our project.  For historical
reasons, it is currently copied into this repository.  Now that an
official gitlab repository is available at
https://depot.lipn.univ-paris13.fr/mayero/coq-num-analysis/ and there
are plans on an OPAM release, this code will likely be replaced with
a normal dependency in the future.
