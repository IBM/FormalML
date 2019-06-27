Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.

Module ProbabilitySpace.

Record ProbSpace := mkProbSpace {
  T: Type;
  Sigma: (T -> Prop) -> Prop;
  P: (T -> Prop) -> R;
}.
Definition Omega (ps: ProbSpace) := (fun o:ps.(T) => True).

(* TODO : should all these axioms be components of the record instead of defined at the top level? I guess it doesn't matter... *)
Axiom Sample_space_nonnegative :
  forall (ps: ProbSpace),
    exists t:ps.(T), ps.(Omega) t.

Definition complement (U: Type) (A: U -> Prop) : U -> Prop :=
  fun u:U => ~(A u).

Definition intersection (U: Type) (A_1 : U -> Prop) (A_2 : U -> Prop) : U -> Prop :=
  fun u:U => A_1 u /\ A_2 u.

Section SigmaAlgebraAxioms.

Axiom ps_sa_closed_under_intersections :
  forall ps: ProbSpace,
    forall A_1 A_2: (ps.(T) -> Prop),
      ps.(Sigma) A_1 /\ ps.(Sigma) A_2 -> ps.(Sigma) (intersection ps.(T) A_1 A_2).

Axiom ps_sa_closed_under_complements :
  forall ps: ProbSpace,
    forall A_1 : (ps.(T) -> Prop),
      ps.(Sigma) A_1 -> ps.(Sigma) (complement ps.(T) A_1).

Axiom ps_sa_contains_sample_space : 
  forall ps: ProbSpace,
    ps.(Sigma) ps.(Omega).

End SigmaAlgebraAxioms.

Section ProbabilityMeasureAxioms.

(* Collections are *countable* sequences of subsets of the powerset of T. *)

Definition collection_is_pairwise_disjoint (T: Type) (collection: nat -> (T -> Prop)) :=
  forall n1 n2 : nat, 
    forall x : T, (collection n1) x <-> ~((collection n2) x).

(* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
Definition union_of_collection (T: Type) (collection: nat -> (T -> Prop)) :=
  fun t:T => (exists n, (collection n) t).

(* Prop: the sum of probabilities for everything in the collection == R. *)
Definition sum_of_probs_equals (ps: ProbSpace) (collection: nat -> (ps.(T) -> Prop)) (result: R) :=
  infinite_sum (fun n:nat => ps.(P) (collection n)) result.

Axiom P_is_a_probability_measure :
  forall ps: ProbSpace,
    forall collection: nat -> (ps.(T) -> Prop),
      (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
      (forall n:nat, ps.(Sigma) (collection n)) 
      /\ 
      collection_is_pairwise_disjoint ps.(T) collection 
      ->
        let
          prob_of_union := ps.(P) (union_of_collection ps.(T) collection)
        in
          sum_of_probs_equals ps collection prob_of_union /\ ps.(P) ps.(Omega) = R1.

End ProbabilityMeasureAxioms.

Section RandomVariable1.

(* A sigma algebra **over the same domain T as the ProbSpace! *)
Record SigmaAlgebra := mkSigmaAlgebra {
  sT: Type;
  sSigma : (sT -> Prop) -> Prop;
}.
Definition sOmega (sa: SigmaAlgebra) := fun t:(sa.(sT)) => True.

(* Sigma algebra axioms copy-pasted from above. TODO : I tried re-using the sigma algebra strcutre but ran into problems... *)
Axiom sa_closed_under_intersections :
  forall sa: SigmaAlgebra,
    forall A_1 A_2: (sa.(sT) -> Prop),
      sa.(sSigma) A_1 /\ sa.(sSigma) A_2 -> sa.(sSigma) (intersection sa.(sT) A_1 A_2).

Axiom sa_closed_under_complements :
  forall sa: SigmaAlgebra,
    forall A_1 : (sa.(sT) -> Prop),
      sa.(sSigma) A_1 -> sa.(sSigma) (complement sa.(sT) A_1).

Axiom sa_contains_sample_space : 
  forall sa: SigmaAlgebra,
    sa.(sSigma) sa.(sOmega).

(* and now I give up on a proper measure-theoretic definition because I don't think we'll be able to do anything with it... *)
Record RandomVariable1 := mkRandomVariable {
  dom: ProbSpace;
  cod: SigmaAlgebra;

  (* convert between types... this should not be necessary at all! *)
  dom_to_cod: dom.(T) -> cod.(sT);
  cod_to_dom: cod.(sT) -> dom.(T);
  coercions_preserve_eq : (forall t:dom.(T), forall s:cod.(sT), (dom_to_cod t) = s <-> (cod_to_dom s) = t);

  (* the actual variable. *)
  rv: dom.(T) -> cod.(sT);

  (* now state that the preimgae of every B in cod.sSigma is in dom.Sigma, requiring lots of coercions. *)
}.

End RandomVariable1.

Section RandomVariable2.

Record RandomVariable2 := mkRanadomVariable2 {
  probSpace: ProbSpace;
  fn: probSpace.(T) -> R;
}.

(* TODO now how do we define mean unless we make assumptions on countability... *)

End RandomVariable2.

End ProbabilitySpace.
