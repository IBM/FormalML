Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.

Module ProbabilitySpace.

Definition complement {U: Type} (A: U -> Prop) : U -> Prop :=
  fun u:U => ~(A u).

Definition intersection {U: Type} (A_1 : U -> Prop) (A_2 : U -> Prop) : U -> Prop :=
  fun u:U => A_1 u /\ A_2 u.

Class ProbSpace (T:Set) := {
  ps_Sigma: (T -> Prop) -> Prop;
  ps_P: (T -> Prop) -> R;
  ps_sa_closed_under_intersections :
    forall A_1 A_2: (T -> Prop),
      ps_Sigma A_1 /\ ps_Sigma A_2 -> ps_Sigma (intersection A_1 A_2);
  
  ps_sa_closed_under_complements :
    forall A_1 : (T -> Prop),
      ps_Sigma A_1 -> ps_Sigma (complement A_1);
  
  ps_sa_contains_sample_space : 
    ps_Sigma (fun x:T => True) ;

  Sample_space_nonnegative :
    inhabited T

  }.

Definition Omega {T} (ps: ProbSpace T) := (fun o:T => True).

Section ProbabilityMeasureAxioms.

(* Collections are *countable* sequences of subsets of the powerset of T. *)

Definition collection_is_pairwise_disjoint (T: Type) (collection: nat -> (T -> Prop)) :=
  forall n1 n2 : nat, 
    forall x : T, (collection n1) x <-> ~((collection n2) x).

(* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
Definition union_of_collection (T: Type) (collection: nat -> (T -> Prop)) :=
  fun t:T => (exists n, (collection n) t).

(* Prop: the sum of probabilities for everything in the collection == R. *)
Definition sum_of_probs_equals `{ps: ProbSpace} (collection: nat -> (T -> Prop)) (result: R) :=
  infinite_sum (fun n:nat => ps_P (collection n)) result.

Class MeasureSpace {T:Set} {ps:ProbSpace T} := {
  P_is_a_probability_measure :=
    forall collection: nat -> (T -> Prop),
      (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
      (forall n:nat, ps_Sigma (collection n)) 
      /\ 
      collection_is_pairwise_disjoint T collection 
      ->
        let
          prob_of_union := ps_P (union_of_collection T collection)
        in
        sum_of_probs_equals collection prob_of_union /\ ps_P ps.(Omega) = R1
  }.

Section RandomVariable1.

(* A sigma algebra **over the same domain T as the ProbSpace! *)
Class SigmaAlgebra (T:Set) := {
 sSigma : (T -> Prop) -> Prop;

 sa_closed_under_intersections :
    forall A_1 A_2: (T -> Prop),
      sSigma A_1 /\ sSigma A_2 -> sSigma (intersection A_1 A_2) ;

 sa_closed_under_complements :
    forall A_1 : (T -> Prop),
      sSigma A_1 -> sSigma (complement A_1) ;

 sa_contains_sample_space :
    sSigma (fun x:T => True) 
                          
}.

Definition sOmega {T} (sa: SigmaAlgebra T) := fun t:T => True.

(* and now I give up on a proper measure-theoretic definition because I don't think we'll be able to do anything with it... *)
Class RandomVariable1 (T) {dom: ProbSpace} {cod: SigmaAlgebra} :=

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
