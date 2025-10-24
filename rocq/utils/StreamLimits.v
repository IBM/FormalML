Require Import Streams.
Require Import Rbase Rlimit.

Require Import StreamAdd.

Definition Stream_limit {A} (f:list A -> R) (s:Stream A) (l:R)
  := forall eps : R,
    (eps > 0)%R ->
    exists N : nat, forall n : nat, n >= N -> (Rfunctions.R_dist (f (firstn n s)) l < eps)%R.

