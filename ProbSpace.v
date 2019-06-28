Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.

Module ProbabilitySpace.

Definition complement {U: Type} (A: U -> Prop) : U -> Prop :=
  fun u:U => ~(A u).

Definition intersection {U: Type} (A_1 : U -> Prop) (A_2 : U -> Prop) : U -> Prop :=
  fun u:U => A_1 u /\ A_2 u.

(* Collections are *countable* sequences of subsets of the powerset of T. *)

Definition collection_is_pairwise_disjoint (T: Type) (collection: nat -> (T -> Prop)) :=
  forall n1 n2 : nat, 
    forall x : T, (collection n1) x <-> ~((collection n2) x).

(* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
Definition union_of_collection (T: Type) (collection: nat -> (T -> Prop)) :=
  fun t:T => (exists n, (collection n) t).

Class SigmaAlgebra (T:Set) := {
 sa_sigma : (T -> Prop) -> Prop;

 sa_closed_under_intersections :
    forall A_1 A_2: (T -> Prop),
      sa_sigma A_1 /\ sa_sigma A_2 -> sa_sigma (intersection A_1 A_2) ;

 sa_closed_under_complements :
    forall A_1 : (T -> Prop),
      sa_sigma A_1 -> sa_sigma (complement A_1) ;

 sa_contains_sample_space :
    sa_sigma (fun x:T => True) 
                          
                             }.

Definition Omega T := (fun o:T => True).

(* Prop: the sum of probabilities for everything in the collection == R. *)
Definition sum_of_probs_equals {T:Type}
           (p : (T -> Prop) -> R)
           (collection: nat -> (T -> Prop)) (result: R) :=
  infinite_sum (fun n:nat => p (collection n)) result.

Class ProbSpace {T:Set} (S:SigmaAlgebra T) := {
  ps_P: (T -> Prop) -> R;

  ps_P_is_a_probability_measure :=
    forall collection: nat -> (T -> Prop),
      (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
      (forall n:nat, sa_sigma (collection n)) 
      /\ 
      collection_is_pairwise_disjoint T collection 
      ->
        let
          prob_of_union := ps_P (union_of_collection T collection)
        in
        sum_of_probs_equals ps_P collection prob_of_union /\ ps_P (Omega T) = R1;

  ps_sample_space_nonnegative :
    inhabited T
                                             }.

Section RandomVariable.

(* A sigma algebra **over the same domain T as the ProbSpace! *)

(* and now I give up on a proper measure-theoretic definition because I don't think we'll be able to do anything with it... *)
  Class RandomVariable {Ts:Set} {Td:Set}
        {doms: SigmaAlgebra Ts}
        (dom: ProbSpace doms)
        (cod: SigmaAlgebra Td) := {

  (* the actual variable. *)
  rv_X: Ts -> Td

  (* now state that the preimgae of every B in cod.sa_sigma is in dom.Sigma, requiring lots of coercions. *)
}.

  Definition Pr {Ts:Set} {Td:Set}
        {doms: SigmaAlgebra Ts}
        {dom: ProbSpace doms}
        {cod: SigmaAlgebra Td}
        (rv:RandomVariable dom cod)
        (S:Td->Prop)
    := @sa_sigma _ doms (fun x:Ts => S (rv_X x)).

  End RandomVariable.
  
  
End ProbabilitySpace.
