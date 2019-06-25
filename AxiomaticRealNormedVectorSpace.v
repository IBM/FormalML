(*using definitions from http://www.math.ucla.edu/~tao/resource/general/121.1.00s/vector_axioms.html *)

Require Import Reals.Rbase.
Require Import Reals.Rfunctions.

Module AxiomaticNormedRealVectorSpace.

Inductive rvector (s: Set) : Set :=
| zero
| add (x y : rvector s)
| inverse (x: rvector s)
| smult (r:R) (x: rvector s).

Axiom rv_axiom_additive : forall s: Set, forall (x y z : (rvector s)),
  (add s x y) = (add s y x)  /\
  (add s (add s x y) z) = (add s x (add s y z)) /\
  (add s (zero s) x) = (add s x (zero s)) /\
  (add s x (zero s)) = x /\
  (add s (inverse s x) x) = (add s x (inverse s x)) /\
  (add s x (inverse s x)) = zero s.

Axiom rv_axiom_multiplicaive : forall s : Set, forall (x : rvector s), forall (c d : R),
  smult s R0 x = zero s /\
  smult s R1 x = x /\
  smult s (Rmult c d) x = smult s c (smult s d x).

Axiom rv_axiom_distributive : forall s: Set, forall (x y : rvector s), forall (c d : R),
  smult s c (add s x y) = add s (smult s c x) (smult s c y) /\
  smult s (Rplus c d) x = add s (smult s c x) (smult s d x).

(* todo implement a concrete norm and then these axioms should become lemmas. *)
Axiom norm : forall s, rvector s -> R.

Axiom norm_axiom_zero : forall s: Set, forall (x:rvector s), (norm s (zero s)) = R0 <-> x=zero s.

Axiom norm_axiom_abs : forall s: Set, forall (x: rvector s), forall (c:R), 
  norm s (smult s c x) = Rmult (Rabs c) (norm s x).

Axiom norm_axiom_add : forall s:Set, forall (x y : rvector s),
  norm s (add s x y) = Rplus (norm s x) (norm s y).

End AxiomaticNormedRealVectorSpace.