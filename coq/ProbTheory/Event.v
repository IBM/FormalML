Require Import Program.Basics.
Require Import Classical.
Require Import QArith Coq.Reals.Rbase Coq.Reals.RList.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.Rprod Coq.Reals.ROrderedType.
Require Import Ranalysis_reg.
Require Import Coquelicot.Coquelicot.
Require Import Lia Lra.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List.

Require Import Program.Basics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.
Require ClassicalDescription.

Require Import Lra Lia.
Require Import List Permutation.

Require Import Morphisms EquivDec.

Require Import Classical ClassicalFacts.
Require Ensembles.

Require Import Utils DVector.
Import ListNotations.

Set Bullet Behavior "Strict Subproofs".

Declare Scope prob.

Section pre_ev.
  Definition pre_event T := T -> Prop.

  Definition pre_event_sub {T} (A B:pre_event T) := forall x, A x -> B x.
  Definition pre_event_equiv {T} (A B:pre_event T) := forall x, A x <-> B x.
  
  Global Instance pre_event_equiv_equiv {T} : Equivalence (@pre_event_equiv T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_equiv_sub {T} : subrelation pre_event_equiv (@pre_event_sub T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_sub_pre {T} : PreOrder (@pre_event_sub T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_sub_part {T} : PartialOrder pre_event_equiv (@pre_event_sub T).
  Proof.
    firstorder.
  Qed.

  Definition pre_Ω {T} : pre_event T   (* \Lia *)
    := fun x: T => True. 

  Definition pre_event_none {T} : pre_event T
    := fun x: T => False.

  Definition pre_event_singleton {T} (m:T) : pre_event T
    := fun x => x=m.
  
  Definition pre_event_union {T} (A B:pre_event T) : pre_event T
    := fun x:T => A x \/ B x.
  
  Definition pre_event_inter {T} (A B:pre_event T) : pre_event T
    := fun x:T => A x /\ B x.
  
  Definition pre_event_complement {T} (A:pre_event T) : pre_event T
    := fun x:T => not (A x).

  Definition pre_event_diff {T} (A B:pre_event T) : pre_event T
    := fun x:T => A x /\ not (B x).

  Definition pre_event_lem {T} (A:pre_event T) : Prop
    := forall x, A x \/ ~ A x.

  Definition pre_event_disjoint {T} (A B:pre_event T) : Prop
    := forall x, A x -> B x -> False.

  Local Notation "∅" := pre_event_none : prob. (* \emptyset *)
  Local Notation "a ∪ b" := (pre_event_union a b) (at level 50) : prob. (* \cup *)
  Local Notation "a ∩ b" := (pre_event_inter a b) (at level 50) : prob. (* \cap *)
  Local Notation "¬ a" := (pre_event_complement a) (at level 20) : prob. (* \neg *)
  Local Notation "a \ b" := (pre_event_diff a b) (at level 50) : prob.
  Local Notation "a ≤ b" := (pre_event_sub a b) (at level 70) : prob. (* \leq *) 

  Local Open Scope prob.

  Global Instance pre_event_disjoint_symm {T}: Symmetric (@pre_event_disjoint T).
  Proof.
    firstorder.
  Qed.
  
  Global Instance pre_event_union_proper {T} :
    Proper (pre_event_equiv ==> pre_event_equiv ==> pre_event_equiv) (@pre_event_union T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_inter_proper {T} :
    Proper (pre_event_equiv ==> pre_event_equiv ==> pre_event_equiv) (@pre_event_inter T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_complement_proper {T} :
    Proper (pre_event_equiv ==> pre_event_equiv) (@pre_event_complement T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_diff_proper {T} :
    Proper (pre_event_equiv ==> pre_event_equiv ==> pre_event_equiv) (@pre_event_diff T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_union_sub_proper {T} :
    Proper (pre_event_sub ==> pre_event_sub ==> pre_event_sub) (@pre_event_union T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_inter_sub_proper {T} :
    Proper (pre_event_sub ==> pre_event_sub ==> pre_event_sub) (@pre_event_inter T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_complement_sub_proper {T} :
    Proper (pre_event_sub --> pre_event_sub) (@pre_event_complement T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_diff_sub_proper {T} :
    Proper (pre_event_sub ==> pre_event_sub --> pre_event_sub) (@pre_event_diff T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_disjoint_proper {T} :
    Proper (pre_event_sub --> pre_event_sub --> impl) (@pre_event_disjoint T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_event_disjoint_eq_proper {A} : Proper (pre_event_equiv ==> pre_event_equiv ==> iff) (@pre_event_disjoint A).
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_diff_derived {T} (A B:T->Prop) : A \ B === A ∩ ¬B.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_disjoint_inter {T} (A B:pre_event T) :
    pre_event_disjoint A B <-> A ∩ B === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_disjoint_diff {T} (A B:pre_event T) : pre_event_disjoint A (B \ A).
  Proof.
    firstorder.
  Qed.

  Hint Resolve pre_event_disjoint_diff : prob.

  Lemma pre_event_disjoint_complement {T} (A:pre_event T) : pre_event_disjoint A (¬ A).
  Proof.
    firstorder.
  Qed.

  Hint Resolve pre_event_disjoint_complement : prob.

  Lemma pre_event_sub_true {T} (A:pre_event T) : A ≤ pre_Ω.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_false_sub {T} (A:pre_event T) : ∅ ≤ A.
  Proof.
    firstorder.
  Qed.

  Hint Resolve pre_event_sub_true pre_event_false_sub : prob.

  Lemma pre_event_sub_union_l {T} (A B:pre_event T) : A ≤ A ∪ B.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_sub_union_r {T} (A B:pre_event T) : B ≤ A ∪ B.
  Proof.
    firstorder.
  Qed.

  Hint Resolve pre_event_sub_union_l pre_event_sub_union_r : prob.

  Lemma pre_event_inter_sub_l {T} (A B:pre_event T) : A ∩ B ≤ A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_sub_r {T} (A B:pre_event T) : A ∩ B ≤ B.
  Proof.
    firstorder.
  Qed.

  Hint Resolve pre_event_inter_sub_l pre_event_inter_sub_r : prob.

  Lemma pre_event_sub_inter {T} (A B C:pre_event T) : A ≤ B -> A ≤ C -> A ≤ B ∩ C.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_true_l {T} (A:pre_event T) : pre_Ω ∪ A === pre_Ω.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_true_r {T} (A:pre_event T) : A ∪ pre_Ω === pre_Ω.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_union_true_l @pre_event_union_true_r : prob.

  Lemma pre_event_union_false_l {T} (A:pre_event T) : ∅ ∪ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_false_r {T} (A:pre_event T) : A ∪ ∅ === A.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_union_false_l @pre_event_union_false_r : prob.

  Lemma pre_event_union_complement {T} (A:pre_event T) :
    pre_event_lem A ->
    A ∪ ¬ A === pre_Ω.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_true_l {T} (A:pre_event T) : pre_Ω ∩ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_true_r {T} (A:pre_event T) : A ∩ pre_Ω === A.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_inter_true_l @pre_event_inter_true_r : prob.

  Lemma pre_event_inter_false_l {T} (A:pre_event T) : ∅ ∩ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_false_r {T} (A:pre_event T) : A ∩ ∅ === ∅.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_inter_false_l @pre_event_inter_false_r : prob.

  Lemma pre_event_inter_complement {T} (A:pre_event T) :
    A ∩ ¬ A === ∅.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_inter_complement : prob.

  Lemma pre_event_diff_true_l {T} (A:pre_event T) : pre_Ω \ A === ¬ A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_diff_true_r {T} (A:pre_event T) : A \ pre_Ω === ∅.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_diff_true_l @pre_event_diff_true_r : prob.

  Lemma pre_event_diff_false_l {T} (A:pre_event T) : ∅ \ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_diff_false_r {T} (A:pre_event T) : A \ ∅ === A.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_diff_false_l @pre_event_diff_false_r : prob.


  Lemma pre_event_diff_sub {T:Type} (x y:pre_event T) : x \ y ≤ x.
  Proof.
    firstorder.
  Qed.

  Hint Resolve pre_event_diff_sub : prob.

  Lemma pre_event_union_comm {T} (A B:pre_event T) : A ∪ B === B ∪ A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_comm {T} (A B:pre_event T) : A ∩ B === B ∩ A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_self {T} (A:pre_event T) : A ∪ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_self {T} (A:pre_event T) : A ∩ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_diff_self {T} (A:pre_event T) : A \ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_not_self {T} (A:pre_event T) :
    pre_event_lem A ->
    A ∪ ¬ A === pre_Ω.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_union_self @pre_event_inter_self @pre_event_diff_self : prob.

  Lemma pre_event_complement_swap {T} (A B:pre_event T) :
    pre_event_lem A ->
    pre_event_lem B ->
    ¬ A === B <-> A === ¬ B.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_not_not {T} (A:pre_event T) :
    pre_event_lem A ->
    ¬ (¬ A) === A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_not_all {T} :
    ¬ (@pre_Ω T) === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_not_none {T} :
    ¬ ∅ === (@pre_Ω T).
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_not_all @pre_event_not_none : prob.

  Lemma pre_event_inter_not_self {T} (A B:pre_event T) : A ∩ ¬ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_assoc {T} (A B C:pre_event T) : A ∪ (B ∪ C) === (A ∪ B) ∪ C.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_assoc {T} (A B C:pre_event T) : A ∩ (B ∩ C) === (A ∩ B) ∩ C.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_inter_distr {T} (A B C:pre_event T) : A ∪ (B ∩ C) === (A ∪ B) ∩ (A ∪ C).
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_union_distr {T} (A B C:pre_event T) : A ∩ (B ∪ C) === (A ∩ B) ∪ (A ∩ C).
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @pre_event_union_self @pre_event_inter_self @pre_event_inter_not_self : prob.

  Lemma pre_event_union_diff {T:Type} (A B:pre_event T) :
    pre_event_lem A ->
    A ∪ (B \ A) === A ∪ B.
  Proof.
    intros.
    rewrite pre_event_diff_derived.
    rewrite pre_event_union_inter_distr.
    rewrite pre_event_union_not_self by trivial.
    autorewrite with prob.
    reflexivity.
  Qed.

  Lemma pre_event_union_sub_l {T:Type} (A B:pre_event T) :
    B ≤ A -> A ∪ B === A.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_sub_r {T:Type} (A B:pre_event T) :
    A ≤ B -> A ∪ B === B.
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_union_diff_sub {T:Type} (A B:pre_event T) :
    pre_event_lem A ->
    A ≤ B -> A ∪ (B \ A) === B.
  Proof.
    intros.
    rewrite pre_event_union_diff by trivial.
    apply pre_event_union_sub_r; trivial.
  Qed.


  Lemma pre_event_complement_inj {A} (x y:pre_event A) :
    pre_event_equiv (pre_event_complement x) (pre_event_complement y) ->
    pre_event_equiv x y.
  Proof.
    unfold pre_event_equiv, pre_event_complement.
    intros ??.
    split; intros.
    - destruct (classic (y x0)); firstorder.
    - destruct (classic (x x0)); firstorder.
  Qed.

  (* Collections are *countable* sequences of subsets of the powerset of T. *)

  Definition pre_collection_is_pairwise_disjoint {T: Type} (collection: nat -> pre_event T) :=
    forall n1 n2 : nat, n1 <> n2 ->
                 pre_event_disjoint (collection n1) (collection n2).

  Global Instance pre_collection_is_pairwise_disjoint_pre_event_sub_proper {T: Type}:
    Proper (pointwise_relation _ pre_event_sub  --> impl) (@pre_collection_is_pairwise_disjoint T).
  Proof.
    unfold Proper, pointwise_relation, impl, respectful, pre_collection_is_pairwise_disjoint, pre_event_sub.
    intros ??? disj; intros; red; intros.
    eapply disj; eauto. 
  Qed.

  Global Instance pre_collection_is_pairwise_disjoint_pre_event_equiv_proper {T: Type}:
    Proper (pointwise_relation _ pre_event_equiv  --> iff) (@pre_collection_is_pairwise_disjoint T).
  Proof.
    unfold Proper, iff, respectful; intros.
    split; intros HH
    ; eapply pre_collection_is_pairwise_disjoint_pre_event_sub_proper; eauto
    ; unfold flip in *
    ; unfold pointwise_relation, pre_event_equiv, pre_event_sub in *; firstorder.
  Qed.

  (* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
  Definition pre_union_of_collection {T: Type} (collection: nat -> pre_event T) : pre_event T :=
    fun t:T => (exists n, (collection n) t).

  Definition pre_inter_of_collection {T: Type} (collection: nat -> pre_event T) : pre_event T :=
    fun t:T => (forall n, (collection n) t).


  Global Instance pre_union_of_collection_proper {T:Type} : Proper (pointwise_relation _ pre_event_equiv ==> pre_event_equiv) (@pre_union_of_collection T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_union_of_collection_sub_proper {T:Type} : Proper (pointwise_relation _ pre_event_sub ==> pre_event_sub) (@pre_union_of_collection T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_inter_of_collection_proper {T:Type} : Proper (pointwise_relation _ pre_event_equiv ==> pre_event_equiv) (@pre_inter_of_collection T).
  Proof.
    firstorder.
  Qed.

  Global Instance pre_inter_of_collection_sub_proper {T:Type} : Proper (pointwise_relation _ pre_event_sub ==> pre_event_sub) (@pre_inter_of_collection T).
  Proof.
    firstorder.
  Qed.

  Lemma pre_union_of_collection_const {T:Type} (c:pre_event T) : pre_event_equiv (pre_union_of_collection (fun _ => c)) c.
  Proof.
    unfold pre_union_of_collection.
    red; intros.
    split; [intros [_ HH] | intros HH]; trivial.
    now exists 0%nat.
  Qed.
  
  Hint Rewrite @pre_union_of_collection_const : prob.

  Lemma pre_collection_is_pairwise_disjoint_sub {T:Type} (coll:nat -> pre_event T) (f:pre_event T -> pre_event T):
    (forall a, f a ≤ a) ->
    pre_collection_is_pairwise_disjoint coll ->
    pre_collection_is_pairwise_disjoint (fun n => f (coll n)).
  Proof.
    intros subs disj n1 n2 neq.
    specialize (disj _ _ neq).
    repeat rewrite subs; trivial.
  Qed.  

  Lemma pre_event_complement_union {T:Type} (E1 E2:pre_event T) :
    pre_event_equiv (pre_event_complement (pre_event_union E1 E2))
                    (pre_event_inter (pre_event_complement E1) (pre_event_complement E2)).
  Proof.
    red; intros.
    split; intros.
    - now apply not_or_and.
    - now apply and_not_or.
  Qed.

  Lemma pre_event_complement_inter {T:Type} (E1 E2:pre_event T) :
    pre_event_equiv (pre_event_complement (pre_event_inter E1 E2))
                    (pre_event_union (pre_event_complement E1) (pre_event_complement E2)).
  Proof.
    red; intros.
    split; intros.
    - now apply not_and_or.
    - now apply or_not_and.
  Qed.

  Lemma pre_event_complement_union_of_collection {T:Type} (E : nat -> pre_event T) :
    pre_event_equiv (pre_event_complement (pre_union_of_collection E))
                    (pre_inter_of_collection (fun n => pre_event_complement (E n))).
  Proof.
    intros ?.
    unfold pre_event_complement, pre_inter_of_collection, pre_union_of_collection.
    firstorder.
  Qed.

  Lemma pre_event_inter_diff' {T:Type} (a b c:pre_event T) :
    pre_event_equiv (pre_event_inter a (pre_event_diff b c))
                    (pre_event_diff (pre_event_inter a b) (pre_event_inter a c)).
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_diff {T:Type} (a b c:pre_event T) :
    pre_event_equiv (pre_event_inter a (pre_event_diff b c))
                    (pre_event_diff (pre_event_inter a b) c).
  Proof.
    repeat rewrite pre_event_diff_derived.
    now rewrite <- pre_event_inter_assoc.
  Qed.

  Lemma pre_event_inter_countable_union_distr {T} (A:pre_event T) (coll:nat->pre_event T) :
    A ∩ pre_union_of_collection coll === pre_union_of_collection (fun n => A ∩ (coll n)).
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_countable_inter_distr {T} (A:pre_event T) (coll:nat->pre_event T) :
    A ∩ pre_inter_of_collection coll === pre_inter_of_collection (fun n => A ∩ (coll n)).
  Proof.
    intros ?.
    split.
    - intros [??] ?.
      now split.
    - intros ?.
      destruct (H 0%nat) as [??].
      split; trivial.
      intros n.
      now destruct (H n).
  Qed.

  Lemma pre_event_diff_countable_union_distr {T} (A:pre_event T) (coll:nat->pre_event T) :
    A \ pre_union_of_collection coll === pre_inter_of_collection (fun n => A \ (coll n)).
  Proof.
    rewrite pre_event_diff_derived, pre_event_complement_union_of_collection.
    rewrite pre_event_inter_countable_inter_distr.
    apply pre_inter_of_collection_proper; intros ?.
    now rewrite pre_event_diff_derived.
  Qed.

  Lemma pre_event_countable_union_diff_distr {T} (A:pre_event T) (coll:nat->pre_event T) :
    (pre_union_of_collection coll) \ A === pre_union_of_collection (fun n => (coll n) \ A).
  Proof.
    firstorder.
  Qed.

  Definition pre_event_preimage {Ts: Type} {Td: Type}
             (X: Ts -> Td)
             (B: pre_event Td)
    := fun omega: Ts => B (X omega).

  Global Instance pre_event_preimage_proper {Ts: Type} {Td: Type} :
    Proper (rv_eq ==> pre_event_equiv ==> pre_event_equiv) (@pre_event_preimage Ts Td).
  Proof.
    intros ???????.
    unfold pre_event_preimage.
    rewrite H.
    apply H0.
  Qed.

  Class SigmaAlgebra (T:Type) :=
    {
    sa_sigma : pre_event T -> Prop;
    
    sa_countable_union (collection: nat -> pre_event T) :
      (forall n, sa_sigma (collection n)) ->
      sa_sigma (pre_union_of_collection collection);
    
    sa_complement (A:pre_event T) :
      sa_sigma A -> sa_sigma (pre_event_complement A) ;
    
    sa_all : sa_sigma pre_Ω 
                      
    }.

  Lemma sa_pre_dec {T} (A:pre_event T) : pre_event_lem A.
  Proof.
    red; intros.
    apply classic.
  Qed.

  Global Instance sa_proper {T} (s: SigmaAlgebra T) : Proper (pre_event_equiv ==> iff) sa_sigma.
  Proof.
    intros ?? eqq.
    red in eqq.
    cut (x = y); [intros; subst; intuition | ].
    apply Ensembles.Extensionality_Ensembles.
    unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In.
    firstorder.
  Qed.

  Hint Resolve sa_pre_dec : prob.

  Definition sa_sub {T} (s1 s2:SigmaAlgebra T) : Prop
    := pre_event_sub (sa_sigma (SigmaAlgebra := s1)) (sa_sigma (SigmaAlgebra := s2)).

  Definition sa_equiv {T} (s1 s2:SigmaAlgebra T) : Prop
    := pre_event_equiv (sa_sigma (SigmaAlgebra := s1)) (sa_sigma (SigmaAlgebra := s2)).

  Global Instance sa_equiv_equiv T : Equivalence (@sa_equiv T).
  Proof.
    firstorder.
  Qed.

  Global Instance sa_equiv_sub {T} : subrelation sa_equiv (@sa_sub T).
  Proof.
    firstorder.
  Qed.

  Global Instance sa_sub_pre {T} : PreOrder (@sa_sub T).
  Proof.
    firstorder.
  Qed.

  Global Instance sa_sub_part {T} : PartialOrder sa_equiv (@sa_sub T).
  Proof.
    firstorder.
  Qed.

  Lemma sa_equiv_subs {T} (s1 s2:SigmaAlgebra T)
    : sa_equiv s1 s2 <-> (sa_sub s1 s2 /\ sa_sub s2 s1).
  Proof.
    firstorder.
  Qed.

  (* restate some lemmas that rely on lem unconditionally *)
  Lemma ps_pre_event_union_complement {T} {s : SigmaAlgebra T} (A:pre_event T) :
    sa_sigma A ->
    A ∪ ¬ A === pre_Ω.
  Proof.
    intros.
    apply pre_event_union_complement.
    now eapply sa_pre_dec.
  Qed.

  Lemma ps_pre_event_union_not_self {T} {s : SigmaAlgebra T} (A:pre_event T) :
    sa_sigma A ->
    A ∪ ¬ A === pre_Ω.
  Proof.
    intros.
    apply pre_event_union_not_self.
    now eapply sa_pre_dec.
  Qed.

  Lemma ps_pre_event_union_diff {T:Type} {s : SigmaAlgebra T} (A B:pre_event T) : sa_sigma A ->
                                                                                  A ∪ (B \ A) === A ∪ B.
  Proof.
    intros.
    apply pre_event_union_diff.
    now eapply sa_pre_dec.
  Qed.

  Lemma ps_pre_event_union_diff_sub {T:Type} {s : SigmaAlgebra T} (A B:pre_event T) : sa_sigma A ->
                                                                                      A ≤ B -> A ∪ (B \ A) === B.
  Proof.
    intros.
    apply pre_event_union_diff_sub; trivial.
    now apply sa_pre_dec.
  Qed.

  Hint Resolve ps_pre_event_union_complement ps_pre_event_union_not_self ps_pre_event_union_diff ps_pre_event_union_diff_sub : prob.

  Lemma sa_notnot {T} {s: SigmaAlgebra T} (A:pre_event T) : sa_sigma A -> forall x, ~ ~ A x -> A x.
  Proof.
    intros.
    destruct (sa_pre_dec A x); intuition.
  Qed.

  Lemma sa_none {T} {s: SigmaAlgebra T} : sa_sigma (∅).
  Proof.
    eapply sa_proper
    ; [ | eapply sa_complement; eapply sa_all].
    firstorder.
  Qed.

  Hint Resolve sa_all sa_none sa_complement : prob.

  Lemma sa_sigma_const {T} (s: SigmaAlgebra T) {P} (Plem:P\/~P) : sa_sigma (fun _ : T => P).
  Proof.
    destruct Plem.
    - eapply sa_proper; [| apply sa_all].
      red; unfold pre_Ω; intuition.
    - eapply sa_proper; [| apply sa_none].
      red; unfold pre_Ω; intuition.
  Qed.

  Lemma  sa_sigma_const_classic {T} (s: SigmaAlgebra T) P : sa_sigma (fun _ : T => P).
  Proof.
    apply sa_sigma_const.
    apply classic.
  Qed.

  Lemma sa_pre_countable_inter {T} {s: SigmaAlgebra T} (collection: nat -> pre_event T) :
    (forall n, sa_sigma (collection n)) ->
    sa_sigma (pre_inter_of_collection collection).
  Proof.
    intros H.
    generalize (sa_countable_union (fun n => pre_event_complement (collection n)))
    ; intros HH.
    cut_to HH.
    - unfold pre_inter_of_collection, pre_union_of_collection in *.
      apply sa_complement in HH.
      eapply sa_proper; [| eapply HH]; intros x.
      unfold pre_event_complement in *.
      split; intros.
      + intros [n ncoll].
        intuition.
      + destruct (sa_pre_dec (collection n) x); trivial.
        elim H0; eauto.
    - intros.
      apply sa_complement; auto.
  Qed.

  Definition pre_list_collection {T} (l:list (pre_event T)) (d:pre_event T) : nat -> pre_event T
    := fun n => nth n l d.

  Definition pre_list_union {T} (l:list (pre_event T)) : pre_event T
    := fun x => exists a, In a l /\ a x.

  Definition pre_list_inter {T}  (l:list (pre_event T)) : pre_event T
    := fun x => forall a, In a l -> a x.

  Lemma pre_event_inter_pre_list_union_distr {T} (A:pre_event T) (l: list (pre_event T)) :
    A ∩ pre_list_union l === pre_list_union (map (pre_event_inter A) l).
  Proof.
    unfold pre_list_union; intros.
    intros x; simpl.
    simpl; split; intros HH.
    - destruct HH as [ax [B [Bin Bx]]].
      exists (pre_event_inter A B).
      split.
      + apply in_map_iff.
        eauto.
      + firstorder.
    - destruct HH as [Bi [Biin Bix]].
      apply in_map_iff in Biin.
      destruct Biin as [B [Bieq Bin]]; subst.
      firstorder.
  Qed.

  Lemma pre_event_union_diff_distr {T} (A:pre_event T) (l: list (pre_event T)) :
    pre_list_union l \ A === pre_list_union (map (fun x => x \ A) l).
  Proof.
    unfold equiv, pre_event_equiv, pre_union_of_collection, pre_list_collection, pre_list_union.
    intros x.
    split.
    - intros [[?[??]] ?].
      exists (x0 \ A); split.
      + apply in_map_iff.
        eauto.
      + firstorder.
    - intros [?[??]].
      apply in_map_iff in H.
      destruct H as [?[??]]; subst.
      apply pre_event_diff_derived in H0.
      destruct H0.
      apply pre_event_diff_derived.
      split; eauto.
  Qed.

  Lemma pre_list_union_union {T} (l:list (pre_event T)) :
    pre_union_of_collection (pre_list_collection l ∅) === pre_list_union l.
  Proof.
    unfold equiv, pre_event_equiv, pre_union_of_collection, pre_list_collection, pre_list_union.
    intros x.
    split; intros H.
    - destruct H as [n nnth].
      destruct (nth_in_or_default n l ∅).
      + eauto.
      + rewrite e in nnth.
        red in nnth; intuition.
    - destruct H as [a [inn ax]].
      eapply In_nth in inn.
      destruct inn as [n [_ nnth]].
      exists n.
      rewrite nnth.
      trivial.
  Qed.

  Lemma pre_list_inter_inter {T} (l:list (pre_event T)) :
    pre_inter_of_collection (pre_list_collection l pre_Ω) === pre_list_inter l.
  Proof.
    unfold equiv, pre_event_equiv, pre_inter_of_collection, pre_list_collection, pre_list_inter.
    intros x.
    split; intros H.
    - intros a inn.
      eapply In_nth in inn.
      destruct inn as [n [_ nnth]].
      rewrite <- nnth.
      eauto.
    - intros n.
      destruct (nth_in_or_default n l pre_Ω).
      + eapply H; eauto.
      + rewrite e; vm_compute; trivial.
  Qed.

  Lemma pre_list_union_nil {T:Type} :
    @pre_list_union T [] === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma pre_list_union_cons {T} (x1 : pre_event T) (l:list (pre_event T)):
    pre_list_union (x1::l) === x1 ∪ (pre_list_union l).
  Proof.
    unfold equiv, pre_event_equiv, pre_list_union, pre_event_union; simpl; intros.
    split.
    - intros [?[??]].
      intuition (congruence || eauto).
    - intros [?|[??]]; intuition eauto.
  Qed.

  Hint Rewrite @pre_list_union_nil @pre_list_union_cons : prob.

  Lemma pre_list_union_singleton {T} (En:pre_event T) :
    pre_list_union [En] === En.
  Proof.
    rewrite pre_list_union_cons, pre_list_union_nil, pre_event_union_false_r.
    reflexivity.
  Qed.

  Hint Rewrite @pre_list_union_singleton : prob.

  Lemma pre_list_union_app {T} (l1 l2:list (pre_event T)):
    pre_list_union (l1 ++ l2) === (pre_list_union l1) ∪ (pre_list_union l2).
  Proof.
    induction l1.
    - simpl.
      autorewrite with prob.
      reflexivity.
    - simpl.
      autorewrite with prob.
      rewrite IHl1.
      rewrite pre_event_union_assoc.
      reflexivity.
  Qed.

  Hint Rewrite @pre_list_union_app : prob.

  Lemma pre_list_union2 {T} (x1 x2 : pre_event T) :
    pre_list_union [x1 ; x2] === x1 ∪ x2.
  Proof.
    autorewrite with prob.
    reflexivity.
  Qed.

  Lemma pre_list_inter_nil {T:Type} :
    @pre_list_inter T [] === pre_Ω.
  Proof.
    firstorder.
  Qed.

  Lemma pre_list_inter_cons {T} (x1 : pre_event T) (l:list (pre_event T)):
    pre_list_inter (x1::l) === x1 ∩ (pre_list_inter l).
  Proof.
    unfold equiv, pre_event_equiv, pre_list_union, pre_event_inter; simpl; intros.
    split.
    - intros.
      generalize (H x1); simpl; intros HH.
      intuition.
      intros a inn.
      generalize (H a); simpl.
      intuition eauto.
    - intros [??] a; simpl.
      red in H0.
      intuition.
      + congruence.
      + eapply H0; eauto.
  Qed.

  Hint Rewrite @pre_list_inter_nil @pre_list_inter_cons : prob.

  Lemma pre_list_inter_singleton {T} (En:pre_event T) :
    pre_list_inter [En] === En.
  Proof.
    rewrite pre_list_inter_cons, pre_list_inter_nil, pre_event_inter_true_r.
    reflexivity.
  Qed.

  Hint Rewrite @pre_list_inter_singleton : prob.

  Lemma pre_list_inter_app {T} (l1 l2:list (pre_event T)):
    pre_list_inter (l1 ++ l2) === (pre_list_inter l1) ∩ (pre_list_inter l2).
  Proof.
    induction l1.
    - simpl.
      autorewrite with prob.
      reflexivity.
    - simpl.
      autorewrite with prob.
      rewrite IHl1.
      rewrite pre_event_inter_assoc.
      reflexivity.
  Qed.

  Hint Rewrite @pre_list_inter_app : prob.

  Lemma pre_list_inter2 {T} (x1 x2 : pre_event T) :
    pre_list_inter [x1 ; x2] === x1 ∩ x2.
  Proof.
    autorewrite with prob.
    reflexivity.
  Qed.

  Lemma pre_event_complement_list_union {T:Type} (E:list (pre_event T)) :
    pre_event_equiv (pre_event_complement (pre_list_union E))
                    (pre_list_inter (map pre_event_complement E)).
  Proof.
    induction E; simpl.
    - rewrite pre_list_union_nil, pre_list_inter_nil.
      apply pre_event_not_none.
    - rewrite pre_list_union_cons, pre_list_inter_cons.
      rewrite pre_event_complement_union.
      now rewrite IHE.
  Qed.

  Lemma pre_event_complement_list_inter {T:Type} (E:list (pre_event T)) :
    pre_event_equiv (pre_event_complement (pre_list_inter E))
                    (pre_list_union (map pre_event_complement E)).
  Proof.
    induction E; simpl.
    - rewrite pre_list_union_nil, pre_list_inter_nil.
      apply pre_event_not_all.
    - rewrite pre_list_union_cons, pre_list_inter_cons.
      rewrite pre_event_complement_inter.
      now rewrite IHE.
  Qed.

  Lemma pre_list_union_concat {T} (l:list (list (pre_event T))) :
    pre_event_equiv (pre_list_union (concat l)) (pre_list_union (map pre_list_union l)).
  Proof.
    induction l; simpl.
    - reflexivity.
    - rewrite pre_list_union_app, pre_list_union_cons.
      now rewrite IHl.
  Qed.

  Lemma pre_list_collection_disjoint {T} (l:list (pre_event T)) :
    ForallOrdPairs pre_event_disjoint l <->
    pre_collection_is_pairwise_disjoint (pre_list_collection l ∅).
  Proof.
    unfold pre_collection_is_pairwise_disjoint, pre_event_disjoint, pre_event_none, pre_list_collection.
    split.
    - induction l; simpl; intros.
      + simpl in H1.
        destruct n1; simpl in *; tauto.
      + inversion H; subst; clear H.
        specialize (IHl H6).
        simpl in *.
        destruct n1.
        * destruct n2; simpl; [tauto | ].
          { destruct (nth_in_or_default n2 l (fun _ : T => False)).
            - rewrite Forall_forall in H5.
              eapply H5; eauto.
            - rewrite e in H2; tauto.

          }
        * { destruct n2.
            - destruct (nth_in_or_default n1 l (fun _ : T => False)).
              + rewrite Forall_forall in H5.
                specialize (H5 _ i _ H2); tauto.
              + rewrite e in H1; tauto.
            - eauto.
          }
    - induction l; simpl; intros.
      + constructor. 
      + constructor.
        * apply Forall_forall.
          intros x xinn t.
          destruct (In_nth _ _ (fun _ : T => False) xinn) as [b [??]].
          specialize (H 0%nat (S b)).
          cut_to H; [| congruence].
          specialize (H t).
          simpl in H.
          now rewrite <- H1.
        * apply IHl; intros.
          specialize (H (S n1) (S n2)).
          cut_to H.
          -- specialize (H x); simpl in H.
             eauto.
          -- congruence.
  Qed.

  Lemma pre_list_collection_sigma {T} {s : SigmaAlgebra T} (l:list (pre_event T)) (d:pre_event T) :
    ((forall x : pre_event T, In x l -> sa_sigma x) /\ sa_sigma d) <->
    (forall n : nat, sa_sigma (pre_list_collection l d n)).
  Proof.
    unfold pre_list_collection.
    split; intros.
    - destruct H.
      destruct (nth_in_or_default n l d).
      + eauto.
      + rewrite e.
        trivial.
    - split; intros.
      + eapply In_nth in H0.
        destruct H0 as [n [_ nnth]].
        specialize (H n).
        rewrite nnth in H; trivial.
      + specialize (H (length l)).
        rewrite nth_overflow in H; auto.
  Qed.

  Lemma sa_pre_list_union {T} {s: SigmaAlgebra T} (l:list (pre_event T)) :
    (forall x, In x l -> sa_sigma x) ->
    sa_sigma (pre_list_union l).
  Proof.
    intros.
    rewrite <- pre_list_union_union.
    apply sa_countable_union.
    apply pre_list_collection_sigma.
    auto with prob.
  Qed.

  Lemma sa_pre_list_inter {T} {s: SigmaAlgebra T} (l:list (pre_event T)) :
    (forall x, In x l -> sa_sigma x) ->
    sa_sigma (pre_list_inter l).
  Proof.
    intros.
    rewrite <- pre_list_inter_inter.
    apply sa_pre_countable_inter.
    apply pre_list_collection_sigma.
    auto with prob.
  Qed.

  Lemma sa_union {T} {s: SigmaAlgebra T} {A₁ A₂} :
    sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ ∪ A₂).
  Proof.
    intros.
    rewrite <- pre_list_union2.
    apply sa_pre_list_union.
    simpl; intuition congruence.
  Qed.

  Lemma sa_inter {T} {s: SigmaAlgebra T} {A₁ A₂} :
    sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ ∩ A₂).
  Proof.
    intros.
    rewrite <- pre_list_inter2.
    apply sa_pre_list_inter.
    simpl; intuition congruence.
  Qed.

  Hint Resolve sa_union sa_inter : prob.

  Lemma sa_diff {T} {s: SigmaAlgebra T} {A₁ A₂} :
    sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ \ A₂).
  Proof.
    intros.
    rewrite pre_event_diff_derived.
    auto with prob.
  Qed.

  Hint Resolve sa_diff : prob.

  Lemma pre_union_of_collection_sup {T} (coll:nat->pre_event T) n : (coll n) ≤ (pre_union_of_collection coll).
  Proof.
    unfold pre_event_sub, pre_union_of_collection.
    eauto.
  Qed.

(* by a chance of index, the union of any countably indexed collection
   of things in the sigma algebra are in the sigma algebra *)
Lemma sa_countable_union_iso {T : Type} (SigmaAlgebra : SigmaAlgebra T) {Index: Type} {iso:Isomorphism Index nat}
      (collection : Index -> pre_event T) :
  (forall i, sa_sigma (collection i)) -> sa_sigma (fun omega => exists i:Index, collection i omega).
Proof.
  intros.
  assert (eqq1:pre_event_equiv
                 (fun omega : T => exists i:Index, collection i omega)
                 (fun omega : T => exists n:nat, collection (iso_f n) omega)).
  {
    split; intros [j ?].
    - exists (iso_b j).
      now rewrite iso_f_b.
    - eauto.    
  }
  rewrite eqq1.
  now apply sa_countable_union.
Qed.

(* by a chance of index, the union of any countably indexed collection
   of things in the sigma algebra are in the sigma algebra *)
Lemma sa_pre_countable_inter_iso {T : Type} (SigmaAlgebra : SigmaAlgebra T) {Index: Type} {iso:Isomorphism Index nat}
      (collection : Index -> pre_event T) :
  (forall i, sa_sigma (collection i)) -> sa_sigma (fun omega => forall i:Index, collection i omega).
Proof.
  intros.
  assert (eqq1:pre_event_equiv
                 (fun omega : T => forall i:Index, collection i omega)
                 (fun omega : T => forall n:nat, collection (iso_f n) omega)).
  {
    intros x.
    split; intros cx j.
    - apply cx.
    - specialize (cx (iso_b j)).
      now rewrite iso_f_b in cx.
  }
  rewrite eqq1.
  now apply sa_pre_countable_inter.
Qed.
  
End pre_ev.

Section event.
  Context {T:Type}.

  Definition event (σ:SigmaAlgebra T) := {e : pre_event T | sa_sigma e}.

  Definition event_pre {σ:SigmaAlgebra T} : event σ -> (T->Prop)
    := fun e => proj1_sig e.

  Lemma sa_sigma_event_pre {σ : SigmaAlgebra T} (E:event σ): sa_sigma (event_pre E).
  Proof.
    now destruct E; simpl.
  Qed.

  Context {σ:SigmaAlgebra T}.
  
  Program Definition event_sub (x y:event σ) := pre_event_sub x y.

  Program Definition event_equiv (x y:event σ) := pre_event_equiv x y.
  
  Global Instance event_equiv_equiv  : Equivalence event_equiv.
  Proof.
    firstorder.
  Qed.

  Global Instance event_equiv_sub  : subrelation event_equiv event_sub.
  Proof.
    firstorder.
  Qed.

  Global Instance event_sub_pre  : PreOrder event_sub.
  Proof.
    firstorder.
  Qed.

  Global Instance event_sub_part  : PartialOrder event_equiv event_sub.
  Proof.
    firstorder.
  Qed.

  Definition Ω : event σ
    := exist _ _ sa_all.

  Definition event_none : event σ
    := exist _ _ sa_none.

  Program Definition event_singleton  (m:T) : sa_sigma (pre_event_singleton m) -> event σ
    := fun sa => exist _ _ sa.
  
  Definition event_union  (A B:event σ) : event σ
    := exist _ _ (sa_union (proj2_sig A) (proj2_sig B)).
  
  Definition event_inter  (A B:event σ) : event σ
    := exist _ _ (sa_inter (proj2_sig A) (proj2_sig B)).
  
  Definition event_complement  (A:event σ) : event σ
    := exist _ _ (sa_complement _ (proj2_sig A)).

  Definition event_diff  (A B:event σ) : event σ
    := exist _ _ (sa_diff (proj2_sig A) (proj2_sig B)).

  Program Definition event_lem  (A:event σ) : Prop
    := pre_event_lem A.

  Program Definition event_disjoint  (A B:event σ) : Prop
    := pre_event_disjoint A B.

  Notation "∅" := event_none : prob. (* \emptyset *)
  Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
  Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
  Notation "¬ a" := (event_complement a) (at level 20) : prob. (* \neg *)
  Notation "a \ b" := (event_diff a b) (at level 50) : prob.
  Notation "a ≤ b" := (event_sub a b) (at level 70) : prob. (* \leq *) 

  Local Open Scope prob.

  Global Instance event_union_proper  :
    Proper (event_equiv ==> event_equiv ==> event_equiv) event_union.
  Proof.
    firstorder.
  Qed.

  Global Instance event_inter_proper  :
    Proper (event_equiv ==> event_equiv ==> event_equiv) event_inter.
  Proof.
    firstorder.
  Qed.

  Global Instance event_complement_proper  :
    Proper (event_equiv ==> event_equiv) event_complement.
  Proof.
    firstorder.
  Qed.

  Global Instance event_diff_proper  :
    Proper (event_equiv ==> event_equiv ==> event_equiv) event_diff.
  Proof.
    firstorder.
  Qed.

  Global Instance event_union_sub_proper  :
    Proper (event_sub ==> event_sub ==> event_sub) event_union.
  Proof.
    firstorder.
  Qed.

  Global Instance event_inter_sub_proper  :
    Proper (event_sub ==> event_sub ==> event_sub) event_inter.
  Proof.
    firstorder.
  Qed.

  Global Instance event_complement_sub_proper  :
    Proper (event_sub --> event_sub) event_complement.
  Proof.
    firstorder.
  Qed.

  Global Instance event_diff_sub_proper  :
    Proper (event_sub ==> event_sub --> event_sub) event_diff.
  Proof.
    firstorder.
  Qed.

  Global Instance event_disjoint_proper  :
    Proper (event_sub --> event_sub --> impl) event_disjoint.
  Proof.
    firstorder.
  Qed.


  Lemma event_diff_derived  (A B:event σ) : A \ B === A ∩ ¬B.
  Proof.
    firstorder.
  Qed.

  Lemma event_disjoint_inter  (A B:event σ) :
    event_disjoint A B <-> A ∩ B === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma event_disjoint_diff  (A B:event σ) : event_disjoint A (B \ A).
  Proof.
    firstorder.
  Qed.

  Hint Resolve event_disjoint_diff : prob.

  Lemma event_disjoint_complement  (A:event σ) : event_disjoint A (¬ A).
  Proof.
    firstorder.
  Qed.

  Hint Resolve event_disjoint_complement : prob.

  Global Instance event_disjoint_sym : Symmetric event_disjoint.
  Proof.
    unfold event_disjoint, pre_event_disjoint; intros [??][??]; simpl; eauto.
  Qed.

  Instance event_disjoint_proper' : 
    Proper (event_equiv ==> event_equiv ==> impl) event_disjoint.
  Proof.
    unfold Proper, respectful, event_disjoint, pre_event_disjoint, impl, event_equiv, pre_event_equiv; intros.
    eapply H1.
    - apply H; eauto.
    - apply H0; eauto.
  Qed.

  Lemma event_sub_true  (A:event σ) : A ≤ Ω.
  Proof.
    firstorder.
  Qed.

  Lemma event_false_sub  (A:event σ) : ∅ ≤ A.
  Proof.
    firstorder.
  Qed.

  Hint Resolve event_sub_true event_false_sub : prob.

  Lemma event_sub_union_l  (A B:event σ) : A ≤ A ∪ B.
  Proof.
    firstorder.
  Qed.

  Lemma event_sub_union_r  (A B:event σ) : B ≤ A ∪ B.
  Proof.
    firstorder.
  Qed.

  Hint Resolve event_sub_union_l event_sub_union_r : prob.

  Lemma event_inter_sub_l  (A B:event σ) : A ∩ B ≤ A.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_sub_r  (A B:event σ) : A ∩ B ≤ B.
  Proof.
    firstorder.
  Qed.

  Hint Resolve event_inter_sub_l event_inter_sub_r : prob.

  Lemma event_sub_inter  (A B C:event σ) : A ≤ B -> A ≤ C -> A ≤ B ∩ C.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_true_l  (A:event σ) : Ω ∪ A === Ω.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_true_r  (A:event σ) : A ∪ Ω === Ω.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_union_true_l @event_union_true_r : prob.

  Lemma event_union_false_l  (A:event σ) : ∅ ∪ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_false_r  (A:event σ) : A ∪ ∅ === A.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_union_false_l @event_union_false_r : prob.

  Lemma event_union_complement  (A:event σ) :
    event_lem A ->
    A ∪ ¬ A === Ω.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_true_l  (A:event σ) : Ω ∩ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_true_r  (A:event σ) : A ∩ Ω === A.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_inter_true_l @event_inter_true_r : prob.

  Lemma event_inter_false_l  (A:event σ) : ∅ ∩ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_false_r  (A:event σ) : A ∩ ∅ === ∅.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_inter_false_l @event_inter_false_r : prob.

  Lemma event_inter_complement  (A:event σ) :
    A ∩ ¬ A === ∅.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_inter_complement : prob.

  Lemma event_diff_true_l  (A:event σ) : Ω \ A === ¬ A.
  Proof.
    firstorder.
  Qed.

  Lemma event_diff_true_r  (A:event σ) : A \ Ω === ∅.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_diff_true_l @event_diff_true_r : prob.

  Lemma event_diff_false_l  (A:event σ) : ∅ \ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma event_diff_false_r  (A:event σ) : A \ ∅ === A.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_diff_false_l @event_diff_false_r : prob.


  Lemma event_diff_sub (x y:event σ) : x \ y ≤ x.
  Proof.
    firstorder.
  Qed.

  Hint Resolve event_diff_sub : prob.

  Lemma event_union_comm  (A B:event σ) : A ∪ B === B ∪ A.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_comm  (A B:event σ) : A ∩ B === B ∩ A.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_self  (A:event σ) : A ∪ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_self  (A:event σ) : A ∩ A === A.
  Proof.
    firstorder.
  Qed.

  Lemma event_diff_self  (A:event σ) : A \ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_not_self  (A:event σ) :
    event_lem A ->
    A ∪ ¬ A === Ω.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_union_self @event_inter_self @event_diff_self : prob.

  Lemma event_complement_swap  (A B:event σ) :
    event_lem A ->
    event_lem B ->
    ¬ A === B <-> A === ¬ B.
  Proof.
    firstorder.
  Qed.

  Lemma event_not_not  (A:event σ) :
    event_lem A ->
    ¬ (¬ A) === A.
  Proof.
    firstorder.
  Qed.

  Lemma event_not_all  :
    ¬ Ω === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma event_not_none  :
    ¬ ∅ === Ω.
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_not_all @event_not_none : prob.

  Lemma event_inter_not_self  (A B:event σ) : A ∩ ¬ A === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_assoc  (A B C:event σ) : A ∪ (B ∪ C) === (A ∪ B) ∪ C.
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_assoc  (A B C:event σ) : A ∩ (B ∩ C) === (A ∩ B) ∩ C.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_inter_distr  (A B C:event σ) : A ∪ (B ∩ C) === (A ∪ B) ∩ (A ∪ C).
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_union_distr  (A B C:event σ) : A ∩ (B ∪ C) === (A ∩ B) ∪ (A ∩ C).
  Proof.
    firstorder.
  Qed.

  Hint Rewrite @event_union_self @event_inter_self @event_inter_not_self : prob.

  Lemma event_union_diff (A B:event σ) :
    event_lem A ->
    A ∪ (B \ A) === A ∪ B.
  Proof.
    intros.
    rewrite event_diff_derived.
    rewrite event_union_inter_distr.
    rewrite event_union_not_self by trivial.
    autorewrite with prob.
    reflexivity.
  Qed.

  Lemma event_union_sub_l (A B:event σ) :
    B ≤ A -> A ∪ B === A.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_sub_r (A B:event σ) :
    A ≤ B -> A ∪ B === B.
  Proof.
    firstorder.
  Qed.

  Lemma event_union_diff_sub (A B:event σ) :
    event_lem A ->
    A ≤ B -> A ∪ (B \ A) === B.
  Proof.
    intros.
    rewrite event_union_diff by trivial.
    apply event_union_sub_r; trivial.
  Qed.


  Lemma event_complement_inj (x y:event σ) :
    event_equiv (event_complement x) (event_complement y) ->
    event_equiv x y.
  Proof.
    unfold event_equiv, event_complement.
    intros ??.
    split; intros.
    - destruct (classic (proj1_sig y x0)); firstorder.
    - destruct (classic (proj1_sig x x0)); firstorder.
  Qed.

  (* Collections are *countable* sequences of subsets of the powerset of T. *)

  Program Definition collection_pre (collection: nat -> event σ) : nat -> pre_event T
    := fun n => collection n.

  Lemma sa_collection_pre  (collection: nat -> event σ) n :
    sa_sigma (collection_pre collection n).
  Proof.
    unfold collection_pre.
    now destruct (collection n).
  Qed.
  
  Definition collection_is_pairwise_disjoint (collection: nat -> event σ) :=
    forall n1 n2 : nat, n1 <> n2 -> event_disjoint (collection n1) (collection n2).

  Lemma collection_is_pairwise_disjoint_pre collection :
    collection_is_pairwise_disjoint collection <->
    pre_collection_is_pairwise_disjoint (collection_pre collection).
  Proof.
    firstorder.
  Qed.


  Global Instance collection_is_pairwise_disjoint_event_sub_proper :
    Proper (pointwise_relation _ event_sub  --> impl) (@collection_is_pairwise_disjoint).
  Proof.
    unfold Proper, pointwise_relation, impl, respectful, event_sub; intros.
    apply -> collection_is_pairwise_disjoint_pre in H0.
    apply <- collection_is_pairwise_disjoint_pre.
    eapply pre_collection_is_pairwise_disjoint_pre_event_sub_proper; eauto.
    intros ???.
    apply H; eauto.
  Qed.

  (* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
  Program Definition union_of_collection (collection: nat -> event σ) : event σ :=
    fun t => (exists n, (collection n) t).
  Next Obligation.
    apply sa_countable_union; intros.
    destruct (collection n); simpl.
    apply s.
  Qed.

  Program Definition inter_of_collection (collection: nat -> event σ) : event σ :=
    fun t => (forall n, (collection n) t).
  Next Obligation.
    apply sa_pre_countable_inter; intros.
    destruct (collection n); simpl.
    apply s.
  Qed.

  Global Instance union_of_collection_proper : Proper (pointwise_relation _ event_equiv ==> event_equiv) union_of_collection.
  Proof.
    firstorder.
  Qed.

  Global Instance union_of_collection_sub_proper : Proper (pointwise_relation _ event_sub ==> event_sub) union_of_collection.
  Proof.
    firstorder.
  Qed.

  Global Instance inter_of_collection_proper : Proper (pointwise_relation _ event_equiv ==> event_equiv) inter_of_collection.
  Proof.
    firstorder.
  Qed.

  Global Instance inter_of_collection_sub_proper : Proper (pointwise_relation _ event_sub ==> event_sub) inter_of_collection.
  Proof.
    firstorder.
  Qed.

  Program Definition union_of_collection_pre (collection: nat -> (event σ)) : event σ
    := exist _ (pre_union_of_collection (collection_pre collection)) _.
  Next Obligation.
    apply sa_countable_union; intros.
    apply sa_collection_pre.
  Qed.

  Program Definition inter_of_collection_pre (collection: nat -> (event σ)) : event σ
    := exist _ (pre_inter_of_collection (collection_pre collection)) _.
  Next Obligation.
    apply sa_pre_countable_inter; intros.
    apply sa_collection_pre.
  Qed.

  Lemma union_of_collection_as_pre (collection: nat -> (event σ)) :
    event_equiv (union_of_collection collection) (union_of_collection_pre collection).
  Proof.
    intros ?; reflexivity.
  Qed.

  Lemma pre_of_union_of_collection (E:nat -> event σ) :
    pre_event_equiv (event_pre (union_of_collection E)) (pre_union_of_collection (fun n => event_pre (E n))).
  Proof.
    reflexivity.
  Qed.

  Lemma inter_of_collection_as_pre  (collection: nat -> (event σ)) :
    event_equiv (inter_of_collection collection) (inter_of_collection_pre collection).
  Proof.
    intros ?; reflexivity.
  Qed.

  Lemma union_of_collection_const (c:event σ) : event_equiv (union_of_collection (fun _ => c)) c.
  Proof.
    unfold union_of_collection.
    red; intros.
    split; [intros [_ HH] | intros HH]; trivial.
    now exists 0%nat.
  Qed.

  Lemma union_of_collection_complement (coll : nat -> event σ) :
    event_equiv (¬ union_of_collection coll) (inter_of_collection (fun n => ¬ (coll n))).
  Proof.
    firstorder.
  Qed.

  Lemma inter_of_collection_complement (coll : nat -> event σ) :
    event_equiv (¬ inter_of_collection coll) (union_of_collection (fun n => ¬ (coll n))).
  Proof.
    repeat red; firstorder; now apply not_all_ex_not.
  Qed.

  Hint Rewrite @union_of_collection_const : prob.
  Hint Rewrite @union_of_collection_complement : prob.
  Hint Rewrite @inter_of_collection_complement : prob.

  Lemma collection_is_pairwise_disjoint_sub (coll:nat -> event σ) (f:event σ -> event σ):
    (forall a, f a ≤ a) ->
    collection_is_pairwise_disjoint coll ->
    collection_is_pairwise_disjoint (fun n => f (coll n)).
  Proof.
    intros subs disj n1 n2 neq.
    specialize (disj _ _ neq).
    repeat rewrite subs; trivial.
  Qed.  

  Lemma event_inter_countable_union_distr  (A:event σ) (coll:nat->event σ) :
    A ∩ union_of_collection coll === union_of_collection (fun n => A ∩ (coll n)).
  Proof.
    firstorder.
  Qed.

  Lemma event_inter_countable_union_distr_r  (A:event σ) (coll:nat->event σ) :
    union_of_collection coll ∩ A === union_of_collection (fun n => (coll n) ∩ A).
  Proof.
    firstorder.
  Qed.

  Lemma sa_dec (A:event σ) : event_lem A.
  Proof.
    red; intros.
    apply sa_pre_dec.
  Qed.

  (* restate some lemmas that rely on lem unconditionally *)
  Lemma ps_event_union_complement (A:event σ) :
    A ∪ ¬ A === Ω.
  Proof.
    intros.
    apply pre_event_union_complement.
    now eapply sa_dec.
  Qed.

  Lemma ps_event_union_not_self  (A:event σ) :
    A ∪ ¬ A === Ω.
  Proof.
    intros.
    apply pre_event_union_not_self.
    now eapply sa_dec.
  Qed.

  Lemma ps_event_union_diff {s : SigmaAlgebra T} (A B:event σ) :
    A ∪ (B \ A) === A ∪ B.
  Proof.
    intros.
    apply pre_event_union_diff.
    now eapply sa_dec.
  Qed.

  Lemma ps_event_union_diff_sub (A B:event σ) :
    A ≤ B -> A ∪ (B \ A) === B.
  Proof.
    intros.
    apply pre_event_union_diff_sub; trivial.
    now apply sa_dec.
  Qed.

  Hint Resolve ps_event_union_complement ps_event_union_not_self ps_event_union_diff ps_event_union_diff_sub : prob.

  Lemma event_notnot (A:event σ) : event_complement (event_complement A) === A.
  Proof.
    destruct A.
    intros ?; simpl.
    unfold pre_event_complement.
    split; [| firstorder].
    intros HH.
    destruct (sa_pre_dec x x0); firstorder.
  Qed.

  Hint Resolve sa_all sa_none sa_complement : prob.

  Definition event_const P : event σ
    := exist _ _ (sa_sigma_const σ (classic P)).

  Definition list_collection  (l:list (event σ)) (d:event σ) : nat -> event σ
    := fun n => nth n l d.

  Lemma collection_pre_list_collection (l:list (event σ)) d :
    pointwise_relation _ pre_event_equiv 
                       (collection_pre (list_collection l d)) (pre_list_collection (map (@proj1_sig _ _) l) (proj1_sig d)).
  Proof.
    intros ??.
    unfold list_collection, collection_pre, pre_list_collection.
    now rewrite map_nth.
  Qed.

  Program Definition list_union  (l:list (event σ)) : event σ
    := fun x => exists a, In a l /\ a x.
  Next Obligation.
    eapply sa_proper
    ; try apply (sa_pre_list_union (map (@proj1_sig _ _) l)).
    - unfold pre_list_union; simpl.
      intros ?.
      split.
      + intros [?[??]].
        eexists.
        split; try eassumption.
        now apply in_map.
      + intros [?[??]].
        apply in_map_iff in H.
        destruct H as [?[??]]; subst.
        eauto.
    - intros.
      apply in_map_iff in H.
      now destruct H as [[??][??]]; subst; simpl.
  Qed.

  Program Definition list_inter (l:list (event σ)) : event σ
    := fun x => forall a, In a l -> a x.
  Next Obligation.
    eapply sa_proper
    ; try apply (sa_pre_list_inter (map (@proj1_sig _ _) l)).
    - unfold pre_list_inter; simpl.
      intros ?.
      split.
      + intros.
        apply in_map_iff in H0.
        destruct H0 as [?[??]]; subst.
        eauto.
      + intros.
        apply H.
        now apply in_map.
    - intros.
      apply in_map_iff in H.
      now destruct H as [[??][??]]; subst; simpl.
  Qed.

  Program Definition list_union_pre (l:list (event σ)) : event σ
    := exist _ (pre_list_union (map (@proj1_sig _ _) l)) _.
  Next Obligation.
    apply sa_pre_list_union; intros.
    apply in_map_iff in H.
    now destruct H as [[??][??]]; subst; simpl.
  Qed.

  Program Definition list_inter_pre (l:list (event σ)) : event σ
    := exist _ (pre_list_inter (map (@proj1_sig _ _) l)) _.
  Next Obligation.
    apply sa_pre_list_inter; intros.
    apply in_map_iff in H.
    now destruct H as [[??][??]]; subst; simpl.
  Qed.

  Lemma list_union_as_pre (l:list (event σ)) :
    event_equiv (list_union l) (list_union_pre l).
  Proof.
    unfold list_union, list_union_pre, pre_list_union.
    intros ?; simpl.
    split.
    - intros [?[??]].
      eexists; split; try eassumption.
      now apply in_map.
    - intros [?[??]].
      apply in_map_iff in H.
      destruct H as [?[??]]; subst.
      eauto.
  Qed.

  Lemma list_inter_as_pre (l:list (event σ)) :
    event_equiv (list_inter l) (list_inter_pre l).
  Proof.
    unfold list_inter, list_inter_pre, pre_list_inter.
    intros ?; simpl.
    split.
    - intros.
      apply in_map_iff in H0.
      destruct H0 as [?[??]]; subst.
      eauto.
    - intros.
      apply H.
      now apply in_map.
  Qed.

  Lemma event_inter_list_union_distr  (A:event σ) (l: list (event σ)) :
    A ∩ list_union l === list_union (map (event_inter A) l).
  Proof.
    repeat rewrite list_union_as_pre.
    red; unfold event_equiv.
    simpl.
    rewrite pre_event_inter_pre_list_union_distr; simpl.
    now repeat rewrite map_map; simpl.
  Qed.

  Lemma list_union_union  (l:list (event σ)) :
    union_of_collection (list_collection l ∅) === list_union l.
  Proof.
    red.
    rewrite union_of_collection_as_pre, list_union_as_pre.
    red; simpl.
    rewrite <- pre_list_union_union.
    unfold collection_pre, list_collection, pre_list_collection.
    replace pre_event_none with (proj1_sig event_none) by reflexivity.
    apply pre_union_of_collection_proper .
    apply collection_pre_list_collection.
  Qed.

  Lemma list_inter_inter  (l:list (event σ)) :
    inter_of_collection (list_collection l Ω) === list_inter l.
  Proof.
    red.
    rewrite inter_of_collection_as_pre, list_inter_as_pre.
    red; simpl.
    rewrite <- pre_list_inter_inter.
    unfold collection_pre, list_collection, pre_list_collection.
    replace pre_Ω with (proj1_sig Ω) by reflexivity.
    apply pre_inter_of_collection_proper.
    apply collection_pre_list_collection.
  Qed.

  Lemma list_union_nil :
    list_union [] === ∅.
  Proof.
    firstorder.
  Qed.

  Lemma list_union_cons  (x1 : event σ) (l:list (event σ)):
    list_union (x1::l) === x1 ∪ (list_union l).
  Proof.
    repeat rewrite list_union_as_pre.
    apply pre_list_union_cons.
  Qed.

  Hint Rewrite @list_union_nil @list_union_cons : prob.

  Lemma list_union_singleton  (En:event σ) :
    list_union [En] === En.
  Proof.
    rewrite list_union_cons, list_union_nil, event_union_false_r.
    reflexivity.
  Qed.

  Hint Rewrite @list_union_singleton : prob.

  Lemma list_union_app  (l1 l2:list (event σ)):
    list_union (l1 ++ l2) === (list_union l1) ∪ (list_union l2).
  Proof.
    induction l1.
    - simpl.
      autorewrite with prob.
      reflexivity.
    - simpl.
      autorewrite with prob.
      rewrite IHl1.
      rewrite event_union_assoc.
      reflexivity.
  Qed.

  Hint Rewrite @list_union_app : prob.

  Lemma list_union2  (x1 x2 : event σ) :
    list_union [x1 ; x2] === x1 ∪ x2.
  Proof.
    autorewrite with prob.
    reflexivity.
  Qed.

  Lemma list_inter_nil :
    list_inter [] === Ω.
  Proof.
    firstorder.
  Qed.

  Lemma list_inter_cons  (x1 : event σ) (l:list (event σ)):
    list_inter (x1::l) === x1 ∩ (list_inter l).
  Proof.
    repeat rewrite list_inter_as_pre.
    apply pre_list_inter_cons.
  Qed.

  Hint Rewrite @list_inter_nil @list_inter_cons : prob.

  Lemma list_inter_singleton  (En:event σ) :
    list_inter [En] === En.
  Proof.
    rewrite list_inter_cons, list_inter_nil, event_inter_true_r.
    reflexivity.
  Qed.

  Hint Rewrite @list_inter_singleton : prob.

  Lemma list_inter_app  (l1 l2:list (event σ)):
    list_inter (l1 ++ l2) === (list_inter l1) ∩ (list_inter l2).
  Proof.
    induction l1.
    - simpl.
      autorewrite with prob.
      reflexivity.
    - simpl.
      autorewrite with prob.
      rewrite IHl1.
      rewrite event_inter_assoc.
      reflexivity.
  Qed.

  Hint Rewrite @list_inter_app : prob.

  Lemma list_inter2  (x1 x2 : event σ) :
    list_inter [x1 ; x2] === x1 ∩ x2.
  Proof.
    autorewrite with prob.
    reflexivity.
  Qed.

  Lemma list_collection_disjoint  (l:list (event σ)) :
    ForallOrdPairs event_disjoint l <->
    collection_is_pairwise_disjoint (list_collection l ∅).
  Proof.
    rewrite collection_is_pairwise_disjoint_pre.
    rewrite collection_pre_list_collection.
    rewrite <- pre_list_collection_disjoint.
    now rewrite ForallOrdPairs_map.
  Qed.

  Lemma union_of_collection_sup (coll:nat->event σ) n : (coll n) ≤ (union_of_collection coll).
  Proof.
    unfold event_sub, union_of_collection, pre_event_sub; simpl.
    eauto.
  Qed.

  Lemma list_union_cons_proper x y l1 l2 :
    event_equiv x y ->
    event_equiv (list_union l1) (list_union l2) ->
    event_equiv (list_union (x::l1)) (list_union (y::l2)).
  Proof.
    unfold list_union, pre_list_union, event_equiv, pre_event_equiv; simpl; intros.
    destruct (H0 x0) as [HH1 HH2].
    split; intros [?[[?|?]?]]; subst.
    - apply H in H2.
      eauto.
    - destruct HH1; eauto.
      exists x2; tauto.
    - apply H in H2.
      eauto.
    - destruct HH2; eauto.
      exists x2; tauto.
  Qed.

  Global Instance list_union_perm :
    Proper (@Permutation _ ==> event_equiv) list_union.
  Proof.
    intros x y perm.
    induction perm.
    - reflexivity.
    - now apply list_union_cons_proper.
    - unfold list_union, pre_list_union, event_equiv, pre_event_equiv; simpl.
      firstorder.
    - etransitivity; eauto.
  Qed.


  Global Instance list_union_Forall2_prop :
    Proper (Forall2 event_equiv ==> event_equiv) list_union.
  Proof.
    intros x y F2.
    induction F2.
    - reflexivity.
    - now apply list_union_cons_proper.
  Qed.

  Lemma diff_inter_compl (A B : event σ) :
    (event_equiv (event_diff A B) 
                 (event_inter A (event_complement B))).
  Proof.
    firstorder.
  Qed.
  
  Lemma union_diff (A B : event σ) :
    event_equiv A (event_union (event_diff A B) (event_inter A B)).
  Proof.
    unfold event_union, event_diff, event_inter, event_equiv.
    unfold pre_event_union, pre_event_diff, pre_event_inter.
    repeat red; simpl; intros.
    tauto.
  Qed.

  Lemma sub_diff_union (A B : event σ) :
    event_sub B A ->
    event_equiv A (event_union (event_diff A B) B).
  Proof.
    unfold event_union, event_diff, event_inter, event_equiv, event_sub.
    unfold pre_event_union, pre_event_diff, pre_event_inter, pre_event_sub.
    repeat red; simpl; intros.
    split; intros.
    - destruct (classic (proj1_sig B x)); tauto.
    - intuition.
  Qed.

  Lemma union_diff_inter (A:event σ) (E : nat -> event σ) :
        event_equiv (union_of_collection (fun n : nat => event_diff A (E n)))
                    (event_diff A (inter_of_collection E)).
  Proof.
    unfold event_equiv, union_of_collection, event_diff, inter_of_collection.
    unfold pre_event_equiv, pre_union_of_collection, pre_event_equiv, pre_inter_of_collection; simpl.
    intros.
    split; [firstorder |]; intros.
    destruct H.
    apply not_all_ex_not in H0.
    firstorder.
  Qed.

  Section take.
  (* define primitives for taking a prefix of a collection *)
  Definition collection_take {A} (En : nat -> A) (n:nat) := map En (seq 0 n).

  Lemma collection_take_length {A} (En : nat -> A) (n:nat) :
    length (collection_take En n) = n.
  Proof.
    unfold collection_take.
    now rewrite map_length, seq_length.
  Qed.

  Lemma collection_take_nth_in a En n x:
    proj1_sig (nth a (collection_take En n) event_none) x <->
    (a < n /\ proj1_sig (En a) x)%nat.
  Proof.
    unfold collection_take.
    split.
    - intros na.
      destruct (lt_dec a n).
      + split; trivial.
        destruct (map_nth_in_exists En (seq 0 n) event_none a).
        * now rewrite seq_length.
        * rewrite H in na.
          rewrite seq_nth in na by trivial.
          now simpl in na.
      + rewrite nth_overflow in na.
        * red in na; tauto.
        * rewrite map_length, seq_length.
          lia.
    - intros [alt Ea].
      destruct (map_nth_in_exists En (seq 0 n) event_none a).
      + now rewrite seq_length.
      + rewrite H.
        rewrite seq_nth by trivial.
        now simpl.
  Qed.

  Lemma In_collection_take {A} (En : nat -> A) a n:
    In a (collection_take En n) ->
    exists m, (m < n)%nat /\ a = En m.
  Proof.
    intros inn.
    unfold collection_take in *.
    rewrite in_map_iff in inn.
    destruct inn as [m [eqq inn]].
    apply in_seq in inn.
    eexists; split; eauto.
    destruct inn as [??].
    now simpl in H0.
  Qed.
  
  Lemma collection_take_Sn {A} n (En : nat -> A) :
    (collection_take En (S n)) = collection_take En n ++ (En n::nil).
  Proof.
    unfold collection_take.
    rewrite seq_Sn, map_app.
    reflexivity.
  Qed.

  Lemma collection_take1 {A} (En : nat -> A) : collection_take En 1 = [En 0%nat].
  Proof.
    reflexivity.
  Qed.

  Lemma collection_take_sub (En:nat -> event σ) n :
    pointwise_relation _ event_sub (list_collection (collection_take En n) event_none) En.
  Proof.
    repeat red; intros.
    red in H.
    apply collection_take_nth_in in H.
    tauto.
  Qed.

  Lemma collection_take_preserves_disjoint En n:
    collection_is_pairwise_disjoint En ->
    ForallOrdPairs event_disjoint (collection_take En n).
  Proof.
    intros disj.
    apply list_collection_disjoint.
    eapply collection_is_pairwise_disjoint_event_sub_proper; eauto.
    apply collection_take_sub.
  Qed.

  Lemma pre_union_of_collection_as_ascending_equiv {E} (an : nat -> pre_event E) :
    pre_event_equiv (pre_union_of_collection an)
      (pre_union_of_collection (fun n : nat => pre_list_union (collection_take an (S n)))).
  Proof.
    intros e.
    split; intros [n ?].
    - exists n, (an n).
      split; trivial.
      apply in_map.
      apply in_seq; lia.
    - destruct H as [n2 [??]].
      apply In_collection_take in H.
      destruct H as [? [??]]; subst.
      now exists x.
  Qed.

  Lemma pre_inter_of_collection_as_ascending_equiv {E} (an : nat -> pre_event E) :
    pre_event_equiv (pre_inter_of_collection an)
      (pre_inter_of_collection (fun n : nat => pre_list_inter (collection_take an (S n)))).
  Proof.
    intros e.
    split.
    - intros HH n a inn.
      apply In_collection_take in inn.
      destruct inn as [? [??]]; subst.
      apply HH.
    - intros HH n.
      apply (HH n (an n)).
      apply in_map.
      apply in_seq; lia.
  Qed.

  Lemma union_of_collection_as_ascending_equiv (an : nat -> event σ) :
    event_equiv (union_of_collection an)
      (union_of_collection (fun n : nat => list_union (collection_take an (S n)))).
  Proof.
    intros e.
    split; intros [n ?].
    - exists n, (an n).
      split; trivial.
      apply in_map.
      apply in_seq; lia.
    - destruct H as [n2 [??]].
      apply In_collection_take in H.
      destruct H as [? [??]]; subst.
      now exists x.
  Qed.

  Lemma inter_of_collection_as_ascending_equiv (an : nat -> event σ) :
    event_equiv (inter_of_collection an)
      (inter_of_collection (fun n : nat => list_inter (collection_take an (S n)))).
  Proof.
    intros e.
    split.
    - intros HH n a inn.
      apply In_collection_take in inn.
      destruct inn as [? [??]]; subst.
      apply HH.
    - intros HH n.
      apply (HH n (an n)).
      apply in_map.
      apply in_seq; lia.
  Qed.

  End take.

  Lemma event_union_list_union (c:nat->event σ) :
    event_equiv 
      (union_of_collection
         (fun n => list_union
                  (collection_take c (S n))))
      (union_of_collection c).
  Proof.
    apply antisymmetry.
    - intros x [n [a [inn ax]]].
      simpl.
      apply In_collection_take in inn.
      destruct inn as [?[??]]; subst.
      eauto.
    - apply union_of_collection_sub_proper.
      intros n m cnm.
      eexists; split; eauto.
      rewrite collection_take_Sn, in_app_iff; simpl.
      tauto.
  Qed.

  Lemma inter_of_collection_nested_collapse (P:nat -> event σ) (f:nat->nat->nat)
    (fsurj:forall x, exists a b, f a b = x) :
    event_equiv
      (inter_of_collection
         (fun n =>
            (inter_of_collection
               (fun m => P (f m n)))))
      (inter_of_collection P).
  Proof.
    split; simpl; intros.
    - destruct (fsurj n) as [a [b ?]]; subst.
      eauto.
    - apply H.
  Qed.

  Corollary inter_of_collection_nested_plus (P:nat -> event σ) :
    event_equiv
      (inter_of_collection
         (fun n =>
            (inter_of_collection
               (fun m => P (m + n)%nat))))
      (inter_of_collection P).
  Proof.
    apply inter_of_collection_nested_collapse; intros.
    exists x; exists 0%nat; lia.
  Qed.

End event.


Definition event_preimage {Ts: Type} {Td: Type} {σ:SigmaAlgebra Td}
           (X: Ts -> Td)
           (B: event σ) : pre_event Ts
  := fun omega: Ts => proj1_sig B (X omega).

Global Instance event_preimage_proper{Ts: Type} {Td: Type} {σ:SigmaAlgebra Td} :
  Proper (rv_eq ==> event_equiv ==> pre_event_equiv) (@event_preimage Ts Td σ).
Proof.
  intros ???????.
  unfold event_preimage.
  rewrite H.
  apply H0.
Qed.

Section vec.

  (* vectors *)

  Definition pre_bounded_inter_of_pre_collection {T} {n} (collection: forall i (pf:(i<n)%nat), pre_event T)
  : pre_event T
    := fun t => forall i pf, collection i pf t.

  Definition pre_bounded_inter_of_pre_collection_unbound {T} {n} (collection: forall i (pf:(i<n)%nat), pre_event T)
    : pre_event T
    := pre_inter_of_collection
         (fun i => match lt_dec i n with
                | left pf => collection i pf
                | right _ => pre_Ω
                end).

  Lemma pre_bounded_inter_of_pre_collection_unbound_eq {T} {n} (collection: forall i (pf:(i<n)%nat), pre_event T) :
    pre_bounded_inter_of_pre_collection collection === pre_bounded_inter_of_pre_collection_unbound collection.
  Proof.
    intros x.
    unfold pre_bounded_inter_of_pre_collection_unbound, pre_bounded_inter_of_pre_collection.
    split; intros.
    - intros i.
      match_destr.
      now red.
    - specialize (H i).
      simpl in H.
      match_destr_in H; try lia.
      now replace pf with l by apply le_uniqueness_proof.
  Qed.

  Lemma sa_pre_bounded_inter {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), pre_event T) :
    (forall n pf, sa_sigma (collection n pf)) ->
    sa_sigma (pre_bounded_inter_of_pre_collection collection).
  Proof.
    intros.
    rewrite pre_bounded_inter_of_pre_collection_unbound_eq.
    unfold pre_bounded_inter_of_pre_collection_unbound.
    apply sa_pre_countable_inter; intros.
    match_destr.
    apply sa_all.
  Qed.

  Definition pre_bounded_inter_of_collection {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event σ)
  : pre_event T
    := fun t => forall i pf, proj1_sig (collection i pf) t.

  Definition bounded_inter_of_collection_unbound {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event σ)
    : event σ
    := inter_of_collection
         (fun i => match lt_dec i n with
                | left pf => collection i pf
                | right _ => Ω
                end).

  Lemma pre_bounded_inter_of_collection_unbound_eq {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event σ) :
    pre_bounded_inter_of_collection collection === proj1_sig (bounded_inter_of_collection_unbound collection).
  Proof.
    intros x.
    unfold bounded_inter_of_collection_unbound, pre_bounded_inter_of_collection.
    split; intros.
    - intros i.
      match_destr.
      now red.
    - specialize (H i).
      simpl in H.
      match_destr_in H; try lia.
      now replace pf with l by apply le_uniqueness_proof.
  Qed.

  Lemma sa_bounded_inter {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event σ) :
    sa_sigma (pre_bounded_inter_of_collection collection).
  Proof.
    intros.
    rewrite pre_bounded_inter_of_collection_unbound_eq.
    apply proj2_sig.
  Qed.

  Definition bounded_inter_of_collection {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event σ)
    : event σ
    := exist _ _ (sa_bounded_inter collection).

  Lemma bounded_inter_of_collection_unbound_eq {T} {n} {σ: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event σ) :
    bounded_inter_of_collection collection === bounded_inter_of_collection_unbound collection.
  Proof.
    intros x.
    apply pre_bounded_inter_of_collection_unbound_eq.
  Qed.

End vec.

Section dec.

  Definition dec_pre_event {T} (P:T->Prop) := forall x, {P x} + {~ P x}.

  Context {T:Type} {σ:SigmaAlgebra T}.

  Definition dec_event (a:event σ) := forall x, {proj1_sig a x} + {~ proj1_sig a x}.

  Lemma dec_event_inter {a b:event σ} :
    dec_event a -> dec_event b -> dec_event (event_inter a b).
  Proof.
    intros ???.
    apply sumbool_and; trivial.
  Defined.

  Lemma dec_event_union {a b:event σ} :
    dec_event a -> dec_event b -> dec_event (event_union a b).
  Proof.
    unfold event_union, pre_event_union.
    intros d1 d2 x.
    destruct (d1 x).
    - left; simpl; eauto.
    - destruct (d2 x).
      + left; simpl; eauto.
      + right.
        simpl; tauto.
  Defined.
  
  Record dec_sa_event :=
    {
    dsa_event : event σ
    ; dsa_dec :  dec_event dsa_event
    }.

  Definition dsa_equiv (x y : dec_sa_event) : Prop
    := event_equiv (dsa_event x) (dsa_event y).

  Global Instance dsa_equiv_equiv : Equivalence dsa_equiv.
  Proof.
    unfold dsa_equiv.
    apply Equivalence_pullback.
    apply event_equiv_equiv.
  Qed.
  
  Program Definition dsa_Ω : dec_sa_event
    := {| dsa_event := Ω |}.
  Next Obligation.
    left; now red.
  Defined.


  Program Definition dsa_none : dec_sa_event
    := {| dsa_event := event_none |}.
  Next Obligation.
    right; now red.
  Defined.

  Definition dec_sa_event_inter (e1 e2 : dec_sa_event) : dec_sa_event :=
    {| dsa_event := (event_inter (dsa_event e1) (dsa_event e2))
       ; dsa_dec := dec_event_inter (dsa_dec e1) (dsa_dec e2)
    |} .

  Definition dec_sa_event_union (e1 e2 : dec_sa_event) : dec_sa_event :=
    {| dsa_event := (event_union (dsa_event e1) (dsa_event e2))
       ; dsa_dec := dec_event_union (dsa_dec e1) (dsa_dec e2)
    |} .
  
  Definition refine_dec_sa_event (e : dec_sa_event) (l : list (dec_sa_event)) :=
    map (fun e2 => dec_sa_event_inter e e2) l.

  Definition refine_dec_sa_partitions (l1 l2 : list dec_sa_event) :=
    flat_map (fun e1 => refine_dec_sa_event e1 l2) l1.

  Global Instance dec_sa_event_inter_proper :
    Proper (dsa_equiv ==> dsa_equiv ==> dsa_equiv) dec_sa_event_inter.
  Proof.
    unfold dec_sa_event_inter, dsa_equiv.
    intros ??????; simpl.
    now apply event_inter_proper.
  Qed.

  Global Instance dec_sa_event_union_proper :
    Proper (dsa_equiv ==> dsa_equiv ==> dsa_equiv) dec_sa_event_union.
  Proof.
    unfold dec_sa_event_union, dsa_equiv.
    intros ??????; simpl.
    now apply event_union_proper.
  Qed.

  Global Instance refine_dec_sa_event_proper :
    Proper (dsa_equiv ==> Forall2 dsa_equiv ==> Forall2 dsa_equiv) refine_dec_sa_event.
  Proof.
    intros ????? F2.
    unfold refine_dec_sa_event.
    rewrite <- Forall2_map.
    revert F2.
    apply Forall2_incl; intros.
    now apply dec_sa_event_inter_proper.
  Qed.

  Global Instance refine_dec_sa_partitions_proper :
    Proper (Forall2 dsa_equiv ==> Forall2 dsa_equiv ==> Forall2 dsa_equiv) refine_dec_sa_partitions.
  Proof.
    unfold refine_dec_sa_partitions.
    intros ?? F21.
    induction F21; intros ?? F22; simpl; trivial.
    apply Forall2_app.
    - now apply refine_dec_sa_event_proper.
    - now apply IHF21.
  Qed.

  Lemma events_disjoint_refine_event (a : dec_sa_event) (l : list dec_sa_event) :
    ForallOrdPairs event_disjoint (map dsa_event l) ->
    ForallOrdPairs event_disjoint (map dsa_event (refine_dec_sa_event a l)).
  Proof.
    induction l; simpl; trivial; intros F1.
    invcs F1.
    constructor; [| auto].
    rewrite Forall_forall; intros ? inn.
    unfold refine_dec_sa_event, dec_sa_event_inter in inn.
    rewrite map_map in inn.
    simpl in inn.
    apply in_map_iff in inn.
    destruct inn as [? [??]]; subst.
    unfold event_disjoint, pre_event_disjoint, event_inter, pre_event_inter
    ; simpl; intros.
    rewrite Forall_forall in H1.
    destruct H; destruct H3.
    eapply (H1 (dsa_event x0)).
    - apply in_map_iff; eauto.
    - eauto.
    - eauto.
  Qed.

  Lemma events_disjoint_refine (l1 l2 : list dec_sa_event) :
    ForallOrdPairs event_disjoint (map dsa_event l1) ->
    ForallOrdPairs event_disjoint (map dsa_event l2) ->
    ForallOrdPairs event_disjoint
                   (map dsa_event (flat_map (fun e1 : dec_sa_event => refine_dec_sa_event e1 l2) l1)).
  Proof.
    revert l2.
    induction l1; simpl; trivial.
    intros l2 F1 F2.
    rewrite map_app.
    invcs F1.
    apply ForallOrdPairs_app.
    - now apply events_disjoint_refine_event.
    - auto.
    - intros x y xinn yinn.
      unfold refine_dec_sa_event, dec_sa_event_inter in xinn, yinn.
      rewrite map_map in xinn.
      simpl in xinn.
      apply in_map_iff in xinn.
      destruct xinn as [?[??]]; subst.
      apply in_map_iff in yinn.
      destruct yinn as [?[??]]; subst.
      apply in_flat_map in H3.
      destruct H3 as [?[??]].
      apply in_map_iff in H3.
      destruct H3 as [?[??]]; subst.
      simpl.
      rewrite Forall_forall in H1.
      specialize (H1 (dsa_event x1)).
      cut_to H1.
      + firstorder.
      + apply in_map_iff; eauto.
  Qed.        

  Lemma refine_dec_sa_partitions_symm (l1 l2 : list dec_sa_event) :
    exists l',
      Permutation (refine_dec_sa_partitions l1 l2) l' /\
      Forall2 dsa_equiv l' (refine_dec_sa_partitions l2 l1).
  Proof.
    exists (concat
         (map
            (fun x : dec_sa_event =>
               map (fun y : dec_sa_event => (dec_sa_event_inter y x)) l1) l2)).
    unfold refine_dec_sa_partitions, refine_dec_sa_event.
    repeat rewrite flat_map_concat_map.
    split.
    - apply concat_map_swap_perm. 
    - apply Forall2_concat.
      apply Forall2_map_f.
      apply Forall2_refl.
      intros ?.
      apply Forall2_map_f.
      apply Forall2_refl.
      intros ?.
      red; simpl.
      apply event_inter_comm.
  Qed.
  
  Lemma event_equiv_list_union_refine_event a l :
    event_equiv (list_union (map dsa_event l)) Ω ->
    event_equiv (list_union (map dsa_event (refine_dec_sa_event a l))) (dsa_event a).
  Proof.
    unfold event_equiv, refine_dec_sa_event, list_union, dec_sa_event_inter; intros.
    rewrite map_map; simpl.
    split; intros.
    - destruct H0 as [?[??]].
      apply in_map_iff in H0.
      destruct H0 as [?[??]]; subst.
      firstorder.
    - destruct (H x).
      cut_to H2; [| now red].
      destruct H2 as [? [??]].
      apply in_map_iff in H2.
      destruct H2 as [?[??]]; subst.
      exists (event_inter (dsa_event a) (dsa_event x1)).
      split.
      + apply in_map_iff.
        eauto.
      + simpl. red; tauto.
  Qed.

  Lemma event_equiv_list_union_refine_all l1 l2 :
    event_equiv (list_union (map dsa_event l2)) Ω ->
    event_equiv
      (list_union (map dsa_event (flat_map (fun e1 : dec_sa_event => refine_dec_sa_event e1 l2) l1)))
      (list_union (map dsa_event l1)).
  Proof.
    revert l2.
    induction l1; simpl; trivial; intros l2 E.
    - reflexivity.
    - rewrite map_app.
      rewrite list_union_app, list_union_cons.
      apply event_union_proper.
      + now apply event_equiv_list_union_refine_event.
      + now apply IHl1.
  Qed.

  Definition classic_dec (P : pre_event T) : dec_pre_event P
    := (fun a => ClassicalDescription.excluded_middle_informative (P a)).

End dec.

Section sa_sub.

  Context {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          {dom2 : SigmaAlgebra Ts}
          (sub : sa_sub dom2 dom).
  
  Definition event_sa_sub 
             (x:event dom2) : event dom
    := exist _ (event_pre x) (sub _ (proj2_sig x)).

  Global Instance event_sa_sub_equiv_proper :
    Proper (event_equiv ==> event_equiv) event_sa_sub.
  Proof.
    repeat red; intros.
    simpl.
    specialize (H x0).
    destruct x; destruct y; simpl in *.
    intuition.
  Qed.

  Lemma collection_is_pairwise_disjoint_sa_sub collection :
    collection_is_pairwise_disjoint collection ->
    collection_is_pairwise_disjoint (fun n : nat => event_sa_sub (collection n)).
  Proof.
    unfold collection_is_pairwise_disjoint; intros.
    unfold event_disjoint; simpl.
    now apply H.
  Qed.

  Lemma union_of_collection_sa_sub collection :
    event_equiv
      (event_sa_sub (union_of_collection collection))
      (union_of_collection (fun n : nat => event_sa_sub (collection n))).
  Proof.
    intros x; simpl.
    reflexivity.
  Qed.

End sa_sub.

Section pre_make_disjoint.
  Context {T:Type}.
  
  Definition make_pre_collection_disjoint (coll:nat->pre_event T) : nat -> pre_event T
    := fun x => pre_event_diff (coll x) ((pre_union_of_collection (fun y =>
                                                                  if lt_dec y x
                                                                  then coll y
                                                                  else pre_event_none))).

  Lemma make_pre_collection_disjoint_sub (En:nat -> pre_event T) n : pre_event_sub (make_pre_collection_disjoint En n) (En n).
  Proof.
    now intros x [??].
  Qed.

  Lemma make_pre_collection_disjoint0 (En:nat -> pre_event T) :
    pre_event_equiv (make_pre_collection_disjoint En 0) (En 0%nat).
  Proof.
    unfold make_pre_collection_disjoint.
    red; intros.
    split; intros.
    - destruct H; trivial.
    - split; trivial.
      unfold pre_union_of_collection.
      intros [? HH].
      match_destr_in HH.
      lia.
  Qed.

  Hint Rewrite @make_pre_collection_disjoint0 : prob.

  Lemma make_pre_collection_disjoint_in (coll:nat->pre_event T) (x:nat) (e:T) :
    make_pre_collection_disjoint coll x e <->
      (coll x) e /\ forall y, (y < x)%nat -> ~ (coll y) e.
  Proof.
    split.
    - unfold make_pre_collection_disjoint; intros HH.
      destruct HH as [H1 H2].
      split; trivial.
      intros y ylt cy.
      apply H2.
      exists y.
      destruct (lt_dec y x); intuition.
    - intros [ce fce].
      unfold make_pre_collection_disjoint.
      split; trivial.
      unfold pre_union_of_collection.
      intros [n Hn].
      destruct (lt_dec n x); trivial.
      eapply fce; eauto.
  Qed.
  
  Lemma make_pre_collection_disjoint_disjoint (coll:nat->pre_event T) :
    pre_collection_is_pairwise_disjoint (make_pre_collection_disjoint coll).
  Proof.
    intros x y xyneq e e1 e2.
    apply make_pre_collection_disjoint_in in e1.
    apply make_pre_collection_disjoint_in in e2.
    destruct e1 as [H11 H12].
    destruct e2 as [H21 H22].
    destruct (not_eq _ _ xyneq) as [xlt|ylt].
    - eapply H22; eauto.
    - eapply H12; eauto.
  Qed.

  
  Lemma make_pre_collection_disjoint_union (coll:nat->pre_event T) :
    pre_event_equiv (pre_union_of_collection coll)
                    (pre_union_of_collection (make_pre_collection_disjoint coll)).
  Proof.
    unfold pre_union_of_collection.
    intros t.
    split; intros [n Hn].
    - simpl.
      generalize (excluded_middle_entails_unrestricted_minimization classic (fun n => coll n t))
      ; intros HH.
      specialize (HH _ Hn).
      destruct HH as [m mmin].
      exists m.
      destruct mmin.
      unfold make_pre_collection_disjoint.
      split; trivial.
      unfold pre_union_of_collection.
      intros [nn Hnn].
      destruct (lt_dec nn m); [ | tauto].
      specialize (H0 _ Hnn).
      lia.
    - apply make_pre_collection_disjoint_in in Hn.
      exists n; tauto.
  Qed.

End pre_make_disjoint.


Section more_pre_props.  
  Lemma pre_list_union_map_none {A B} (l:list A) :
    pre_event_equiv (pre_list_union (map (fun _  => pre_event_none) l)) (@pre_event_none B).
  Proof.
    induction l; simpl.
    - now rewrite pre_list_union_nil.
    - now rewrite pre_list_union_cons, IHl, pre_event_union_false_l.
  Qed.

  Global Instance pre_list_union_sub_proper {A} :
    Proper (Forall2 pre_event_sub ==> pre_event_sub) (@pre_list_union A).
  Proof.
    intros ????[?[??]].
    red.
    destruct (Forall2_In_l H H0) as [? [??]].
    eauto.
  Qed.

  Global Instance pre_list_inter_sub_proper {A} :
    Proper (Forall2 pre_event_sub ==> pre_event_sub) (@pre_list_inter A).
  Proof.
    intros ???????.
    destruct (Forall2_In_r H H1) as [? [??]].
    red in H0.
    apply H3.
    apply H0; simpl; eauto.
  Qed.

  Global Instance pre_list_union_proper {A} :
    Proper (Forall2 pre_event_equiv ==> pre_event_equiv) (@pre_list_union A).
  Proof.
    intros ????.
    split.
    - apply pre_list_union_sub_proper; trivial.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
    - apply pre_list_union_sub_proper; trivial.
      symmetry in H.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
  Qed.

  Global Instance pre_list_inter_proper {A} :
    Proper (Forall2 pre_event_equiv ==> pre_event_equiv) (@pre_list_inter A).
  Proof.
    intros ????.
    split.
    - apply pre_list_inter_sub_proper; trivial.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
    - apply pre_list_inter_sub_proper; trivial.
      symmetry in H.
      eapply Forall2_incl; try eapply H; intros.
      firstorder.
  Qed.

  Lemma pre_collection_take_nth_in {A} a (En:nat -> pre_event A) n x:
    nth a (collection_take En n) pre_event_none x <->
      (a < n /\ (En a) x)%nat.
  Proof.
    unfold collection_take.
    split.
    - intros na.
      destruct (lt_dec a n).
      + split; trivial.
        destruct (map_nth_in_exists En (seq 0 n) pre_event_none a).
        * now rewrite seq_length.
        * rewrite H in na.
          rewrite seq_nth in na by trivial.
          now simpl in na.
      + rewrite nth_overflow in na.
        * red in na; tauto.
        * rewrite map_length, seq_length.
          lia.
    - intros [alt Ea].
      destruct (map_nth_in_exists En (seq 0 n) pre_event_none a).
      + now rewrite seq_length.
      + rewrite H.
        rewrite seq_nth by trivial.
        now simpl.
  Qed.

  Lemma pre_collection_take_sub {A} (En:nat -> pre_event A) n :
    pointwise_relation _ pre_event_sub (pre_list_collection (collection_take En n) pre_event_none) En.
  Proof.
    repeat red; intros.
    apply pre_collection_take_nth_in in H.
    tauto.
  Qed.

  Lemma pre_collection_take_preserves_disjoint {A} (En:nat -> pre_event A) n:
    pre_collection_is_pairwise_disjoint En ->
    ForallOrdPairs pre_event_disjoint (collection_take En n).
  Proof.
    intros disj.
    apply pre_list_collection_disjoint.
    eapply pre_collection_is_pairwise_disjoint_pre_event_sub_proper; eauto.
    apply pre_collection_take_sub.
  Qed.

  Lemma pre_list_union_take_collection_sub {A} (E:nat->pre_event A) n :
    pre_event_sub (pre_list_union (collection_take E n)) (pre_union_of_collection E).
  Proof.
    rewrite <- pre_list_union_union.

    apply pre_union_of_collection_sub_proper.
    apply pre_collection_take_sub.
  Qed.

  Lemma pre_event_diff_diff_l {A} (a b c : pre_event A) :
    pre_event_equiv (pre_event_diff (pre_event_diff a b) c) (pre_event_diff a (pre_event_union b c)).
  Proof.
    firstorder.
  Qed.

  Lemma pre_union_of_collection_lt_S {A} (E:nat->pre_event A) n :
    pre_event_equiv (pre_union_of_collection (fun y : nat => if lt_dec y (S n) then E y else pre_event_none))
                    (pre_event_union (E n) (pre_union_of_collection (fun y : nat => if lt_dec y n then E y else pre_event_none))).
  Proof.
    intros ?; split.
    - intros [? HH].
      match_destr_in HH; try contradiction.
      destruct (Nat.eq_dec x0 n).
      * subst.
        now left.
      * right.
        exists x0.
        match_destr.
        lia.
    - intros [|[??]].
      + exists n.
        match_destr; try lia.
      + match_destr_in H; try contradiction.
        exists x0.
        match_destr.
        lia.
  Qed.

  Lemma pre_collection_is_pairwise_disjoint_inter {T} (an:nat->pre_event T) (a:pre_event T) :
    pre_collection_is_pairwise_disjoint an ->
    pre_collection_is_pairwise_disjoint (fun n : nat => pre_event_inter a (an n)).
  Proof.
    firstorder.
  Qed.

  Lemma pre_event_inter_sub_l_equiv {A:Type} (a b:pre_event A) :
    pre_event_sub a b ->
    pre_event_equiv (pre_event_inter a b) a.
  Proof.
    firstorder.
  Qed.

  Lemma pre_list_disjoint_inter {A} (a:pre_event A) (l:list (pre_event A)) :
    ForallOrdPairs pre_event_disjoint l ->
    ForallOrdPairs pre_event_disjoint (map (pre_event_inter a) l).
  Proof.
    intros HH.
    induction HH.
    - constructor.
    - simpl.
      constructor; trivial.
      apply Forall_map.
      revert H.
      apply Forall_impl; intros ? disj ? [??] [??].
      eapply disj; eauto.
  Qed.

End more_pre_props.

Section event_impl_theory.

  Definition pre_event_impl {A}  (a b : pre_event A) : pre_event A
    := fun x => a x -> b x.

  Program Definition event_impl {A} {σ : SigmaAlgebra A} (a b : event σ) : event σ
    := pre_event_impl (event_pre a) (event_pre b).
  Next Obligation.
    generalize (proj2_sig (event_union (event_complement a) b)).
    apply sa_proper.
    intros ?; simpl.
    unfold pre_event_impl, pre_event_union, pre_event_complement.
    destruct (classic (event_pre a x)); firstorder.
  Qed.
End event_impl_theory.

Section eventually_event.

  Import Coquelicot.Hierarchy.

  Definition pre_event_pre_eventually {A} (pe: nat -> pre_event A): pre_event A
    := fun a => eventually (fun n => pe n a).

  Program Definition event_eventually {A} {σ: SigmaAlgebra A} (pe: nat -> event σ): event σ
    := fun a => eventually (fun n => event_pre (pe n) a).
  Next Obligation.
    apply (proj2_sig
                  (union_of_collection
                     (fun n =>
                        inter_of_collection
                          (fun i =>
                             event_impl (event_const (n <= i)%nat) (pe i))))).
  Qed.

  Lemma event_sub_eventually {A} {σ: SigmaAlgebra A} (pe: nat -> event σ):
    forall n,
      event_sub (inter_of_collection (fun n0 => pe (n + n0)%nat))
        (event_eventually pe).
  Proof.
    intros ???.
    exists n.
    intros.
    specialize (H (n0 - n)%nat).
    simpl in H.
    now replace (n + (n0 - n))%nat with n0 in H by lia.
  Qed.

End eventually_event.

Coercion event_pre : event >-> Funclass.

Notation "∅" := event_none : prob. (* \emptyset *)
Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
Notation "¬ a" := (event_complement a) (at level 20) : prob. (* \neg *)
Notation "a \ b" := (event_diff a b) (at level 50) : prob.
Notation "a ≤ b" := (event_sub a b) (at level 70) : prob. (* \leq *) 

Hint Resolve event_disjoint_diff : prob.
Hint Resolve event_disjoint_complement : prob.
Hint Resolve event_sub_true event_false_sub : prob.
Hint Resolve event_sub_union_l event_sub_union_r : prob.
Hint Resolve event_inter_sub_l event_inter_sub_r : prob.
Hint Rewrite @event_union_true_l @event_union_true_r : prob.
Hint Rewrite @event_union_false_l @event_union_false_r : prob.
Hint Rewrite @event_inter_true_l @event_inter_true_r : prob.
Hint Rewrite @event_inter_false_l @event_inter_false_r : prob.
Hint Rewrite @event_inter_complement : prob.
Hint Rewrite @event_diff_true_l @event_diff_true_r : prob.
Hint Rewrite @event_diff_false_l @event_diff_false_r : prob.
Hint Resolve event_diff_sub : prob.
Hint Rewrite @event_union_self @event_inter_self @event_diff_self : prob.
Hint Rewrite @event_not_all @event_not_none : prob.
Hint Rewrite @event_union_self @event_inter_self @event_inter_not_self : prob.
Hint Rewrite @union_of_collection_const : prob.
Hint Resolve ps_event_union_complement ps_event_union_not_self ps_event_union_diff ps_event_union_diff_sub : prob.
Hint Resolve sa_all sa_none sa_complement : prob.
Hint Rewrite @list_union_nil @list_union_cons : prob.
Hint Rewrite @list_union_singleton : prob.
Hint Rewrite @list_union_app : prob.
Hint Rewrite @list_inter_nil @list_inter_cons : prob.
Hint Rewrite @list_inter_singleton : prob.
Hint Rewrite @list_inter_app : prob.

Global Arguments sa_sigma {T}.
