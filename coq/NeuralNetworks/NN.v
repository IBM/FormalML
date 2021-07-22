Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Arith.
Require Import String.
Require Import Vector.

Require Import AxiomaticNormedRealVectorSpace.

Module NN.

Section SeriesDivergence.

Definition converges (s: nat -> R) :=
  exists sum:R, infinite_sum s sum.

Definition diverges (s: nat -> R) : Prop :=
  ~(converges s).

Definition diverges_right (s: nat -> R) : Prop :=
  forall m: R,
    exists N: nat,
      forall n: nat, 
        n >= N -> Rgt (s n) m.

Definition diverges_left (s: nat -> R) : Prop :=
  forall m: R,
    exists N: nat,
      forall n:nat, 
        n >= N -> Rlt (s n) m.

End SeriesDivergence.

Section AssumptionC.

Local Open Scope R_scope.
Definition Assumption_C_1 (ak : nat -> R) : Prop :=
  let 
    ak_squared (n : nat) := (ak n)^2
  in
    (forall n, ak n >= 0) /\
    diverges_right ak /\
    converges ak_squared.

Definition Assumption_C_2 (s: Set) (x: nat -> rvector s) : Prop :=
  exists M : R,
    forall k: nat, norm s (x k) < M.

(* TODO *)
Definition Assumption_C_3 (zeta: nat -> R) : Prop :=
  ZeroMeanBoundedVariance zeta.

Definition Assumption_C (s: Set) (zeta: nat -> R) (alpha: nat -> R) (x : nat -> rvector s) : Prop :=
  Assumption_C_1 alpha /\ Assumption_C_2 s x /\ Assumption_C_3 zeta.

Local Close Scope R_scope.

End AssumptionC.

End NN.
