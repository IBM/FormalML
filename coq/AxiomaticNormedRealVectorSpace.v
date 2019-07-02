(*using definitions from http://www.math.ucla.edu/~tao/resource/general/121.1.00s/vector_axioms.html *)

Require Import Reals.Rbase.
Require Import Reals.Rfunctions.

Module AxiomaticNormedRealVectorSpace.

Inductive rvector (d: nat) : Set :=
| zero
| add (x y : rvector d)
| inverse (x: rvector d)
| smult (r:R) (x: rvector d).

Class NormedVectorSpace (d: nat) :=
  {
    norm:  rvector d -> R;

    rv_axiom_additive : forall x y z : rvector d,
    (add d x y) = (add d y x)  /\
    (add d (add d x y) z) = (add d x (add d y z)) /\
    (add d (zero d) x) = (add d x (zero d)) /\
    (add d x (zero d)) = x /\
    (add d (inverse d x) x) = (add d x (inverse d x)) /\
    (add d x (inverse d x)) = zero d;

    rv_axiom_multiplicaive : forall (x : rvector d), forall (b c : R),
    smult d R0 x = zero d /\
    smult d R1 x = x /\
    smult d (Rmult b c) x = smult d b (smult d c x);

    rv_axiom_distributive : forall (x y : rvector d), forall (a b : R),
    smult d b (add d x y) = add d (smult d b x) (smult d b y) /\
    smult d (Rplus a b) x = add d (smult d a x) (smult d b x);

    norm_axiom_zero : forall (x:rvector d),
          norm (zero d) = R0 <-> x=zero d;

    norm_axiom_abs : forall (x: rvector d), forall (a:R), 
    norm (smult d a x) = Rmult (Rabs a) (norm x);

    norm_axiom_add : forall (x y : rvector d),
    norm (add d x y) = Rplus (norm x) (norm y);
  }.

End AxiomaticNormedRealVectorSpace.
