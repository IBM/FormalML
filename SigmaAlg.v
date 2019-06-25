Require Import Ensembles.
Require Import Arith.

Module SigmaAlg.

(* If U -> Prop defines a set S, then U->Prop->Prop will be a subset of the powerset of S. *)
Record SigmaAlgebra (U: Type) : Type := mkRat {
  X: U -> Prop;

  Sigma: (U -> Prop) -> Prop;

  X_in_Sigma: 
    exists A: U -> Prop, Sigma A /\ forall u:U, X u <-> A u;

  Closed_Under_Intersection:
    forall A_1 A_2 : U -> Prop, exists A_3 : U -> Prop,
      (Sigma A_1 /\ Sigma A_2) -> (
        forall u:U, (A_1 u /\ A_2 u) <-> A_3 u
      );

  Closed_Under_Complement:
    forall A: U -> Prop, Sigma A ->
      exists A_Complement : U -> Prop,
        Sigma A_Complement /\
        forall u:U, A u <-> ~(A_Complement u)
}.


End SigmaAlg.