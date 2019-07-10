Require Import Rbase Ranalysis.
Require Import ProbSpace SigmaAlgebras.

(* specialized for R *)

Instance borel_sa : SigmaAlgebra R
  := generated_sa open_set.
