Require Import Ensembles.
Require Import Arith.

Module SigmaAlg.

Definition SigmaAlgebra (U: Type) := (U -> Prop) -> Prop.

Definition complement (U: Type) (A: U -> Prop) : U -> Prop :=
  fun u:U => ~(A u).

Definition intersection (U: Type) (A_1 : U -> Prop) (A_2 : U -> Prop) : U -> Prop :=
  fun u:U => A_1 u /\ A_2 u.

Axiom Closed_Under_Intersection:
  forall U: Type,
    forall sa: SigmaAlgebra U,
      forall A_1 A_2 : U -> Prop, 
        sa A_1 /\ sa A_2 -> sa (intersection U A_1 A_2).

Axiom Closed_Under_Complement:
  forall U: Type,
    forall sa: SigmaAlgebra U,
      forall A : U -> Prop, 
          sa A -> sa (complement U A).

End SigmaAlg.