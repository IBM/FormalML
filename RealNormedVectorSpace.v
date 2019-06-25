(*using definitions from http://www.math.ucla.edu/~tao/resource/general/121.1.00s/vector_axioms.html *)

Require Import Reals.Rbase.
Require Import Reals.Rfunctions.

Module AxiomaticNormedRealVectorSpace.

Inductive rvector : Set :=
| zero
| add (x y : rvector)
| inverse (x: rvector)
| smult (r:R) (x: rvector).

Axiom rv_axiom_additive : forall (x y z : rvector),
  (add x y) = (add y x) /\
  (add (add x y) z) = (add x (add y z)) /\
  (add zero x) = (add x zero) /\
  (add x zero) = x /\
  (add (inverse x) x) = (add x (inverse x)) /\
  (add x (inverse x)) = zero.

Axiom rv_axiom_multiplicaive : forall (x : rvector), forall (c d : R),
  smult R0 x = zero /\
  smult R1 x = x /\
  smult (Rmult c d) x = smult c (smult d x).

Axiom rv_axiom_distributive : forall (x y : rvector), forall (c d : R),
  smult c (add x y) = add (smult c x) (smult c y) /\
  smult (Rplus c d) x = add (smult c x) (smult d x).

Definition norm (v: rvector) : R := R0.

Axiom norm_axiom_zero : forall (x:rvector), (norm zero) = R0 <-> x=zero.

Axiom norm_axiom_abs : forall (x: rvector), forall (c:R), 
  norm (smult c x) = Rmult (Rabs c) (norm x).

Axiom norm_axiom_add : forall (x y : rvector),
  norm (add x y) = Rplus (norm x) (norm y).

End AxiomaticNormedRealVectorSpace.