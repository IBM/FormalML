Require Import Program.Basics.
Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.

Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.

Require Import Classical ClassicalFacts.
Require Ensembles.

Require Import Utils DVector.
Import ListNotations.

Declare Scope prob.

Section ev.
  Definition event T := T -> Prop.

  Definition event_sub {T} (A B:event T) := forall x, A x -> B x.
  Definition event_equiv {T} (A B:event T) := forall x, A x <-> B x.
  
  Global Instance event_equiv_equiv {T} : Equivalence (@event_equiv T).
  Proof.
    firstorder.
  Qed.

  Global Instance event_equiv_sub {T} : subrelation event_equiv (@event_sub T).
  Proof.
    firstorder.
  Qed.

  Global Instance event_sub_pre {T} : PreOrder (@event_sub T).
  Proof.
    firstorder.
  Qed.

  Global Instance event_sub_part {T} : PartialOrder event_equiv (@event_sub T).
  Proof.
    firstorder.
  Qed.

  Definition Ω {T} : event T   (* \Lia *)
    := fun x: T => True. 

  Definition event_none {T} : event T
    := fun x: T => False.

  Definition event_singleton {T} (m:T) : event T
    := fun x => x=m.
  
  Definition event_union {T} (A B:event T) : event T
    := fun x:T => A x \/ B x.
  
  Definition event_inter {T} (A B:event T) : event T
    := fun x:T => A x /\ B x.
  
  Definition event_complement {T} (A:event T) : event T
    := fun x:T => not (A x).

  Definition event_diff {T} (A B:event T) : event T
    := fun x:T => A x /\ not (B x).

  Definition event_lem {T} (A:event T) : Prop
    := forall x, A x \/ ~ A x.
End ev.

Definition event_disjoint {T} (A B:event T) : Prop
  := forall x, A x -> B x -> False.

Notation "∅" := event_none : prob. (* \emptyset *)
Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
Notation "¬ a" := (event_complement a) (at level 20) : prob. (* \neg *)
Notation "a \ b" := (event_diff a b) (at level 50) : prob.
Notation "a ≤ b" := (event_sub a b) (at level 70) : prob. (* \leq *) 

Local Open Scope prob.

Global Instance event_union_proper {T} :
  Proper (event_equiv ==> event_equiv ==> event_equiv) (@event_union T).
Proof.
  firstorder.
Qed.

Global Instance event_inter_proper {T} :
  Proper (event_equiv ==> event_equiv ==> event_equiv) (@event_inter T).
Proof.
  firstorder.
Qed.

Global Instance event_complement_proper {T} :
  Proper (event_equiv ==> event_equiv) (@event_complement T).
Proof.
  firstorder.
Qed.

Global Instance event_diff_proper {T} :
  Proper (event_equiv ==> event_equiv ==> event_equiv) (@event_diff T).
Proof.
  firstorder.
Qed.

Global Instance event_union_sub_proper {T} :
  Proper (event_sub ==> event_sub ==> event_sub) (@event_union T).
Proof.
  firstorder.
Qed.

Global Instance event_inter_sub_proper {T} :
  Proper (event_sub ==> event_sub ==> event_sub) (@event_inter T).
Proof.
  firstorder.
Qed.

Global Instance event_complement_sub_proper {T} :
  Proper (event_sub --> event_sub) (@event_complement T).
Proof.
  firstorder.
Qed.

Global Instance event_diff_sub_proper {T} :
  Proper (event_sub ==> event_sub --> event_sub) (@event_diff T).
Proof.
  firstorder.
Qed.

Global Instance event_disjoint_proper {T} :
  Proper (event_sub --> event_sub --> impl) (@event_disjoint T).
Proof.
  firstorder.
Qed.


Lemma event_diff_derived {T} (A B:T->Prop) : A \ B === A ∩ ¬B.
Proof.
  firstorder.
Qed.

Lemma event_disjoint_inter {T} (A B:event T) :
  event_disjoint A B <-> A ∩ B === ∅.
Proof.
  firstorder.
Qed.

Lemma event_disjoint_diff {T} (A B:event T) : event_disjoint A (B \ A).
Proof.
  firstorder.
Qed.

Hint Resolve event_disjoint_diff : prob.

Lemma event_disjoint_complement {T} (A:event T) : event_disjoint A (¬ A).
Proof.
  firstorder.
Qed.

Hint Resolve event_disjoint_complement : prob.

Lemma event_sub_true {T} (A:event T) : A ≤ Ω.
Proof.
  firstorder.
Qed.

Lemma event_false_sub {T} (A:event T) : ∅ ≤ A.
Proof.
  firstorder.
Qed.

Hint Resolve event_sub_true event_false_sub : prob.

Lemma event_sub_union_l {T} (A B:event T) : A ≤ A ∪ B.
Proof.
  firstorder.
Qed.

Lemma event_sub_union_r {T} (A B:event T) : B ≤ A ∪ B.
Proof.
  firstorder.
Qed.

Hint Resolve event_sub_union_l event_sub_union_r : prob.

Lemma event_inter_sub_l {T} (A B:event T) : A ∩ B ≤ A.
Proof.
  firstorder.
Qed.

Lemma event_inter_sub_r {T} (A B:event T) : A ∩ B ≤ B.
Proof.
  firstorder.
Qed.

Hint Resolve event_inter_sub_l event_inter_sub_r : prob.

Lemma event_union_true_l {T} (A:event T) : Ω ∪ A === Ω.
Proof.
  firstorder.
Qed.

Lemma event_union_true_r {T} (A:event T) : A ∪ Ω === Ω.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_union_true_l @event_union_true_r : prob.

Lemma event_union_false_l {T} (A:event T) : ∅ ∪ A === A.
Proof.
  firstorder.
Qed.

Lemma event_union_false_r {T} (A:event T) : A ∪ ∅ === A.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_union_false_l @event_union_false_r : prob.

Lemma event_union_complement {T} (A:event T) :
  event_lem A ->
  A ∪ ¬ A === Ω.
Proof.
  firstorder.
Qed.

Lemma event_inter_true_l {T} (A:event T) : Ω ∩ A === A.
Proof.
  firstorder.
Qed.

Lemma event_inter_true_r {T} (A:event T) : A ∩ Ω === A.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_inter_true_l @event_inter_true_r : prob.

Lemma event_inter_false_l {T} (A:event T) : ∅ ∩ A === ∅.
Proof.
  firstorder.
Qed.

Lemma event_inter_false_r {T} (A:event T) : A ∩ ∅ === ∅.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_inter_false_l @event_inter_false_r : prob.

Lemma event_inter_complement {T} (A:event T) :
  A ∩ ¬ A === ∅.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_inter_complement : prob.

Lemma event_diff_true_l {T} (A:event T) : Ω \ A === ¬ A.
Proof.
  firstorder.
Qed.

Lemma event_diff_true_r {T} (A:event T) : A \ Ω === ∅.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_diff_true_l @event_diff_true_r : prob.

Lemma event_diff_false_l {T} (A:event T) : ∅ \ A === ∅.
Proof.
  firstorder.
Qed.

Lemma event_diff_false_r {T} (A:event T) : A \ ∅ === A.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_diff_false_l @event_diff_false_r : prob.


Lemma event_diff_sub {T:Type} (x y:event T) : x \ y ≤ x.
Proof.
  firstorder.
Qed.

Hint Resolve event_diff_sub : prob.

Lemma event_union_comm {T} (A B:event T) : A ∪ B === B ∪ A.
Proof.
  firstorder.
Qed.

Lemma event_inter_comm {T} (A B:event T) : A ∩ B === B ∩ A.
Proof.
  firstorder.
Qed.

Lemma event_union_self {T} (A:event T) : A ∪ A === A.
Proof.
  firstorder.
Qed.

Lemma event_inter_self {T} (A:event T) : A ∩ A === A.
Proof.
  firstorder.
Qed.

Lemma event_diff_self {T} (A:event T) : A \ A === ∅.
Proof.
  firstorder.
Qed.

Lemma event_union_not_self {T} (A:event T) :
  event_lem A ->
  A ∪ ¬ A === Ω.
Proof.
  firstorder.
Qed.

Hint Rewrite @event_union_self @event_inter_self @event_diff_self : prob.

Lemma event_complement_swap {T} (A B:event T) :
      event_lem A ->
      event_lem B ->
      ¬ A === B <-> A === ¬ B.
Proof.
  firstorder.
Qed.

Lemma event_not_not {T} (A:event T) :
  event_lem A ->
  ¬ (¬ A) === A.
Proof.
  firstorder.
Qed.

Lemma event_not_all {T} :
  ¬ (@Ω T) === ∅.
Proof.
  firstorder.
Qed.

Lemma event_not_none {T} :
  ¬ ∅ === (@Ω T).
Proof.
  firstorder.
Qed.

Hint Rewrite @event_not_all @event_not_none : prob.

Lemma event_inter_not_self {T} (A B:event T) : A ∩ ¬ A === ∅.
Proof.
  firstorder.
Qed.

Lemma event_union_assoc {T} (A B C:event T) : A ∪ (B ∪ C) === (A ∪ B) ∪ C.
Proof.
  firstorder.
Qed.

Lemma event_inter_assoc {T} (A B C:event T) : A ∩ (B ∩ C) === (A ∩ B) ∩ C.
Proof.
  firstorder.
Qed.

Lemma event_union_inter_distr {T} (A B C:event T) : A ∪ (B ∩ C) === (A ∪ B) ∩ (A ∪ C).
Proof.
  firstorder.
Qed.

Lemma event_inter_union_distr {T} (A B C:event T) : A ∩ (B ∪ C) === (A ∩ B) ∪ (A ∩ C).
Proof.
  firstorder.
Qed.

Hint Rewrite @event_union_self @event_inter_self @event_inter_not_self : prob.

Lemma event_union_diff {T:Type} (A B:event T) :
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

Lemma event_union_sub_l {T:Type} (A B:event T) :
  B ≤ A -> A ∪ B === A.
Proof.
  firstorder.
Qed.

Lemma event_union_sub_r {T:Type} (A B:event T) :
  A ≤ B -> A ∪ B === B.
Proof.
  firstorder.
Qed.

Lemma event_union_diff_sub {T:Type} (A B:event T) :
  event_lem A ->
  A ≤ B -> A ∪ (B \ A) === B.
Proof.
  intros.
  rewrite event_union_diff by trivial.
  apply event_union_sub_r; trivial.
Qed.

(* Collections are *countable* sequences of subsets of the powerset of T. *)

Definition collection_is_pairwise_disjoint {T: Type} (collection: nat -> event T) :=
  forall n1 n2 : nat, n1 <> n2 ->
                      event_disjoint (collection n1) (collection n2).

 Global Instance collection_is_pairwise_disjoint_event_sub_proper {T: Type}:
   Proper (pointwise_relation _ event_sub  --> impl) (@collection_is_pairwise_disjoint T).
 Proof.
   unfold Proper, pointwise_relation, impl, respectful, collection_is_pairwise_disjoint, event_sub.
   intros ??? disj; intros; red; intros.
   eapply disj; eauto. 
 Qed.

(* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
Definition union_of_collection {T: Type} (collection: nat -> event T) : event T :=
  fun t:T => (exists n, (collection n) t).

Definition inter_of_collection {T: Type} (collection: nat -> event T) : event T :=
  fun t:T => (forall n, (collection n) t).


Global Instance union_of_collection_proper {T:Type} : Proper (pointwise_relation _ event_equiv ==> event_equiv) (@union_of_collection T).
Proof.
  firstorder.
Qed.

Global Instance inter_of_collection_proper {T:Type} : Proper (pointwise_relation _ event_equiv ==> event_equiv) (@inter_of_collection T).
Proof.
  firstorder.
Qed.

Lemma union_of_collection_const {T:Type} (c:event T) : event_equiv (union_of_collection (fun _ => c)) c.
 Proof.
   unfold union_of_collection.
   red; intros.
   split; [intros [_ HH] | intros HH]; trivial.
   now exists 0%nat.
 Qed.
 
 Hint Rewrite @union_of_collection_const : prob.

Lemma collection_is_pairwise_disjoint_sub {T:Type} (coll:nat -> event T) (f:event T -> event T):
  (forall a, f a ≤ a) ->
  collection_is_pairwise_disjoint coll ->
  collection_is_pairwise_disjoint (fun n => f (coll n)).
Proof.
  intros subs disj n1 n2 neq.
  specialize (disj _ _ neq).
  repeat rewrite subs; trivial.
Qed.  

Lemma event_inter_countable_union_distr {T} (A:event T) (coll:nat->event T) :
  A ∩ union_of_collection coll === union_of_collection (fun n => A ∩ (coll n)).
Proof.
  firstorder.
Qed.

Definition event_preimage {Ts: Type} {Td: Type}
           (X: Ts -> Td)
           (B: event Td)
  := fun omega: Ts => B (X omega).

Global Instance event_preimage_proper {Ts: Type} {Td: Type} :
  Proper (rv_eq ==> event_equiv ==> event_equiv) (@event_preimage Ts Td).
Proof.
  intros ???????.
  unfold event_preimage.
  rewrite H.
  apply H0.
Qed.

Class SigmaAlgebra (T:Type) :=
  {
    sa_sigma : event T -> Prop;
    
    sa_countable_union (collection: nat -> event T) :
      (forall n, sa_sigma (collection n)) ->
      sa_sigma (union_of_collection collection);
    
    sa_complement (A:event T) :
      sa_sigma A -> sa_sigma (¬ A) ;
    
    sa_all : sa_sigma Ω 
                       
  }.

Lemma sa_dec {T} {s: SigmaAlgebra T} {A:event T} : sa_sigma A -> event_lem A.
Proof.
  red; intros.
  apply classic.
Qed.

Global Instance sa_proper {T} (s: SigmaAlgebra T) : Proper (event_equiv ==> iff) sa_sigma.
Proof.
  intros ?? eqq.
  red in eqq.
  cut (x = y); [intros; subst; intuition | ].
  apply Ensembles.Extensionality_Ensembles.
  unfold Ensembles.Same_set, Ensembles.Included, Ensembles.In.
  firstorder.
Qed.

Hint Resolve sa_dec : prob.

Definition sa_sub {T} (s1 s2:SigmaAlgebra T) : Prop
  := event_sub (sa_sigma (SigmaAlgebra := s1)) (sa_sigma (SigmaAlgebra := s2)).

Definition sa_equiv {T} (s1 s2:SigmaAlgebra T) : Prop
  := event_equiv (sa_sigma (SigmaAlgebra := s1)) (sa_sigma (SigmaAlgebra := s2)).

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

(* restate some lemmas that rely on lem unconditionally *)
Lemma ps_event_union_complement {T} {s : SigmaAlgebra T} (A:event T) :
  sa_sigma A ->
  A ∪ ¬ A === Ω.
Proof.
  intros.
  apply event_union_complement.
  now eapply sa_dec.
Qed.

Lemma ps_event_union_not_self {T} {s : SigmaAlgebra T} (A:event T) :
  sa_sigma A ->
  A ∪ ¬ A === Ω.
Proof.
  intros.
  apply event_union_not_self.
  now eapply sa_dec.
Qed.

Lemma ps_event_union_diff {T:Type} {s : SigmaAlgebra T} (A B:event T) : sa_sigma A ->
  A ∪ (B \ A) === A ∪ B.
Proof.
  intros.
  apply event_union_diff.
  now eapply sa_dec.
Qed.

Lemma ps_event_union_diff_sub {T:Type} {s : SigmaAlgebra T} (A B:event T) : sa_sigma A ->
  A ≤ B -> A ∪ (B \ A) === B.
Proof.
  intros.
  apply event_union_diff_sub; trivial.
  now apply sa_dec.
Qed.

Hint Resolve ps_event_union_complement ps_event_union_not_self ps_event_union_diff ps_event_union_diff_sub : prob.

Lemma sa_notnot {T} {s: SigmaAlgebra T} (A:event T) : sa_sigma A -> forall x, ~ ~ A x -> A x.
Proof.
  intros.
  destruct (sa_dec H x); intuition.
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
    red; unfold Ω; intuition.
  - eapply sa_proper; [| apply sa_none].
    red; unfold Ω; intuition.
Qed.

Lemma sa_countable_inter {T} {s: SigmaAlgebra T} (collection: nat -> event T) :
  (forall n, sa_sigma (collection n)) ->
  sa_sigma (inter_of_collection collection).
Proof.
  intros H.
  generalize (sa_countable_union (fun n => event_complement (collection n)))
  ; intros HH.
  cut_to HH.
  - unfold inter_of_collection, union_of_collection in *.
    apply sa_complement in HH.
    eapply sa_proper; [| eapply HH]; intros x.
    unfold event_complement in *.
    split; intros.
    + intros [n ncoll].
      intuition.
    + destruct (sa_dec (H n) x); trivial.
      elim H0; eauto.
  - intros.
    apply sa_complement; auto.
Qed.

Definition list_collection {T} (l:list (event T)) (d:event T) : nat -> event T
  := fun n => nth n l d.

Definition list_union {T} (l:list (event T)) : event T
  := fun x => exists a, In a l /\ a x.

Definition list_inter {T}  (l:list (event T)) : event T
  := fun x => forall a, In a l -> a x.

Lemma event_inter_list_union_distr {T} (A:event T) (l: list (event T)) :
  A ∩ list_union l === list_union (map (event_inter A) l).
Proof.
  unfold list_union; intros.
  intros x; simpl.
  simpl; split; intros HH.
  - destruct HH as [ax [B [Bin Bx]]].
    exists (event_inter A B).
    split.
    + apply in_map_iff.
      eauto.
    + firstorder.
  - destruct HH as [Bi [Biin Bix]].
    apply in_map_iff in Biin.
    destruct Biin as [B [Bieq Bin]]; subst.
    firstorder.
Qed.

Lemma list_union_union {T} (l:list (event T)) :
  union_of_collection (list_collection l ∅) === list_union l.
Proof.
  unfold equiv, event_equiv, union_of_collection, list_collection, list_union.
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

Lemma list_inter_inter {T} (l:list (event T)) :
  inter_of_collection (list_collection l Ω) === list_inter l.
Proof.
  unfold equiv, event_equiv, inter_of_collection, list_collection, list_inter.
  intros x.
  split; intros H.
  - intros a inn.
    eapply In_nth in inn.
    destruct inn as [n [_ nnth]].
    rewrite <- nnth.
    eauto.
  - intros n.
    destruct (nth_in_or_default n l Ω).
    + eapply H; eauto.
    + rewrite e; vm_compute; trivial.
Qed.

Lemma list_union_nil {T:Type} :
  @list_union T [] === ∅.
Proof.
  firstorder.
Qed.

Lemma list_union_cons {T} (x1 : event T) (l:list (event T)):
  list_union (x1::l) === x1 ∪ (list_union l).
Proof.
  unfold equiv, event_equiv, list_union, event_union; simpl; intros.
  split.
  - intros [?[??]].
    intuition (congruence || eauto).
  - intros [?|[??]]; intuition eauto.
Qed.

Hint Rewrite @list_union_nil @list_union_cons : prob.

Lemma list_union_singleton {T} (En:event T) :
  list_union [En] === En.
 Proof.
   rewrite list_union_cons, list_union_nil, event_union_false_r.
   reflexivity.
Qed.

 Hint Rewrite @list_union_singleton : prob.

Lemma list_union_app {T} (l1 l2:list (event T)):
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

Lemma list_union2 {T} (x1 x2 : event T) :
  list_union [x1 ; x2] === x1 ∪ x2.
Proof.
  autorewrite with prob.
  reflexivity.
Qed.

Lemma list_inter_nil {T:Type} :
  @list_inter T [] === Ω.
Proof.
  firstorder.
Qed.

Lemma list_inter_cons {T} (x1 : event T) (l:list (event T)):
  list_inter (x1::l) === x1 ∩ (list_inter l).
Proof.
  unfold equiv, event_equiv, list_union, event_inter; simpl; intros.
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

Hint Rewrite @list_inter_nil @list_inter_cons : prob.

Lemma list_inter_singleton {T} (En:event T) :
  list_inter [En] === En.
 Proof.
   rewrite list_inter_cons, list_inter_nil, event_inter_true_r.
   reflexivity.
Qed.

 Hint Rewrite @list_inter_singleton : prob.

Lemma list_inter_app {T} (l1 l2:list (event T)):
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

Lemma list_inter2 {T} (x1 x2 : event T) :
  list_inter [x1 ; x2] === x1 ∩ x2.
Proof.
  autorewrite with prob.
  reflexivity.
Qed.

Lemma list_collection_disjoint {T} (l:list (event T)) :
    ForallOrdPairs event_disjoint l <->
    collection_is_pairwise_disjoint (list_collection l ∅).
Proof.
  unfold collection_is_pairwise_disjoint, event_disjoint, event_none, list_collection.
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
        specialize (H 0 (S b)).
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

Lemma list_collection_sigma {T} {s : SigmaAlgebra T} (l:list (event T)) (d:event T) :
  ((forall x : event T, In x l -> sa_sigma x) /\ sa_sigma d) <->
  (forall n : nat, sa_sigma (list_collection l d n)).
Proof.
  unfold list_collection.
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

Lemma sa_list_union {T} {s: SigmaAlgebra T} (l:list (event T)) :
  (forall x, In x l -> sa_sigma x) ->
  sa_sigma (list_union l).
Proof.
  intros.
  rewrite <- list_union_union.
  apply sa_countable_union.
  apply list_collection_sigma.
  auto with prob.
Qed.

Lemma sa_list_inter {T} {s: SigmaAlgebra T} (l:list (event T)) :
  (forall x, In x l -> sa_sigma x) ->
  sa_sigma (list_inter l).
Proof.
  intros.
  rewrite <- list_inter_inter.
  apply sa_countable_inter.
  apply list_collection_sigma.
  auto with prob.
Qed.

Lemma sa_union {T} {s: SigmaAlgebra T} {A₁ A₂} :
  sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ ∪ A₂).
Proof.
  intros.
  rewrite <- list_union2.
  apply sa_list_union.
  simpl; intuition congruence.
Qed.

Lemma sa_inter {T} {s: SigmaAlgebra T} {A₁ A₂} :
  sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ ∩ A₂).
Proof.
  intros.
  rewrite <- list_inter2.
  apply sa_list_inter.
  simpl; intuition congruence.
Qed.

Hint Resolve sa_union sa_inter : prob.

Lemma sa_diff {T} {s: SigmaAlgebra T} {A₁ A₂} :
  sa_sigma A₁ -> sa_sigma A₂ -> sa_sigma (A₁ \ A₂).
Proof.
  intros.
  rewrite event_diff_derived.
  auto with prob.
Qed.

Hint Resolve sa_diff : prob.

(* Prop: the sum of probabilities for everything in the collection == R. *)
Definition sum_of_probs_equals {T:Type}
           (p : event T -> R)
           (collection: nat -> event T) (result: R) :=
  infinite_sum' (fun n:nat => p (collection n)) result.

Class ProbSpace {T:Type} (S:SigmaAlgebra T) :=
  {
    ps_P: event T -> R;
    ps_proper :> Proper (event_equiv ==> eq) ps_P ;
    
    ps_countable_disjoint_union (collection: nat -> event T) :
      (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
      (forall n:nat, sa_sigma (collection n)) -> 
      collection_is_pairwise_disjoint collection ->
      sum_of_probs_equals ps_P collection (ps_P (union_of_collection collection));
    
    ps_one : ps_P Ω = R1;
    
    ps_pos (A:event T): sa_sigma A -> (0 <= ps_P A)%R
  }.

Lemma ps_all {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) : ps_P Ω = R1.
Proof.
  apply ps_one.
Qed.

(* P numbers are as per https://www.stat.washington.edu/~nehemyl/files/UW_MATH-STAT394_axioms-proba.pdf *)
(* P1.1 *)
Lemma ps_none {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) : ps_P ∅ = R0.
Proof.
  generalize (ps_countable_disjoint_union
                (fun n => match n with
                          | 0 => Ω
                          | _ => ∅
                          end))
  ; intros HH.
  cut_to HH.
  - simpl in HH.
    red in HH.
    apply (infinite_sum'_split 1) in HH.
    simpl in HH.

    apply (infinite_sum'_ext (fun x : nat => ps_P match (x + 1)%nat with
                                                  | 0%nat => Ω
                                                  | S _ => ∅
                                                  end)
                             (fun x : nat => ps_P ∅)) in HH.
    + rewrite (@ps_proper _ _ _ (union_of_collection
                           (fun n : nat => match n with
                                           | 0%nat => Ω
                                           | S _ => ∅
                                           end)) (Ω)) in HH.
      * replace (ps_P (ProbSpace:=ps) Ω) with R1 in HH
          by (symmetry; apply ps_one).
        replace (R1 - (0 + R1))%R with R0 in HH by lra.
        eapply infinite_sum'_const1; eauto.
      * unfold event_equiv, Ω; intuition.
        red.
        exists 0%nat; trivial.
    + destruct x; simpl; trivial.
  - destruct n.
    + apply sa_all.
    + apply sa_none. 
  - unfold collection_is_pairwise_disjoint.
    destruct n1; destruct n2; unfold Ω, event_none, event_disjoint; try tauto.
Qed.

Hint Rewrite @ps_none @ps_all : prob.

Local Open Scope R.

(* P1.2 *)
Lemma ps_list_disjoint_union {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (l: list (event T)) :
  (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
  (forall x : event T, In x l -> sa_sigma x) ->
  ForallOrdPairs event_disjoint l ->
  ps_P (list_union l) = fold_right Rplus 0 (map ps_P l).
Proof.
  intros Hs Hd.
  generalize (ps_countable_disjoint_union (list_collection l ∅)); intros HH.
  cut_to HH.
  - unfold sum_of_probs_equals in HH.
    erewrite ps_proper in HH; [| eapply list_union_union ].
    apply (infinite_sum'_split (length l)) in HH.
    apply (infinite_sum'_ext  (fun x : nat => ps_P (list_collection l ∅ (x + length l)))
                              (fun x : nat => 0)) in HH.
    + apply infinite_sum'_const2 in HH.
      apply Rminus_diag_uniq in HH.
      rewrite HH.
      clear.
      unfold list_collection.
      rewrite sum_f_R0'_as_fold_right.
      rewrite (list_as_nthseq l ∅) at 2.
      rewrite map_map.
      rewrite fold_right_map; trivial.
    + intros.
      erewrite ps_proper; [eapply ps_none | ]; intros.
      unfold list_collection.
      rewrite nth_overflow; intuition.
  - apply list_collection_sigma.
    intuition.
  - apply list_collection_disjoint; trivial.
Qed.

Lemma ps_disjoint_union {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (x1 x2: event T) :
  (* Assume: collection is a subset of Sigma and its elements are pairwise disjoint. *)
  sa_sigma x1 ->
  sa_sigma x2 ->
  event_disjoint x1 x2 ->
  ps_P (x1 ∪ x2) = ps_P x1 + ps_P x2.
Proof.
  intros sa1 sa2 disj.
  rewrite <- list_union2.
  rewrite ps_list_disjoint_union; simpl.
  - lra.
  - intuition congruence.
  - repeat constructor; trivial.
Qed.

(* P1.3 *)
Lemma ps_sub {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A B: event T) :
  sa_sigma A ->
  sa_sigma B ->
  A ≤ B -> ps_P A <= ps_P B.
Proof.
  intros sa1 sa2 impl.
  generalize (ps_disjoint_union ps
                                A (B \ A)); intros HH.
  cut_to HH; [ | auto with prob.. ].
  rewrite event_union_diff_sub in HH.
  - rewrite HH.
    generalize (ps_pos (B \ A)); intros.
    cut_to H; auto with prob.
    lra.
  - now apply sa_dec.
  - trivial.
Qed.

(* C1.1 *)
Lemma ps_le1 {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A: event T)
  : sa_sigma A ->
    ps_P A <= R1.
Proof.
  intros.
  rewrite <- ps_one.
  apply ps_sub; auto with prob.
Qed.

(* P1.4 *)
Lemma ps_countable_total {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A:event T) (coll:nat -> event T) :
  sa_sigma A ->
  (forall n, sa_sigma (coll n)) ->
  collection_is_pairwise_disjoint coll ->
  union_of_collection coll === Ω ->
  infinite_sum' (fun i => ps_P (A ∩ (coll i))) (ps_P A).
Proof.
  intros saA saC disjC partC.
  rewrite <- (event_inter_true_r A).
  rewrite <- partC.
  rewrite event_inter_countable_union_distr.
  apply ps_countable_disjoint_union.
  - auto with prob.
  - apply collection_is_pairwise_disjoint_sub; auto with prob.
Qed.

Lemma ps_list_total {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A:event T) (l: list (event T)) :
  sa_sigma A ->
  Forall sa_sigma l ->
  ForallOrdPairs event_disjoint l ->
  list_union l === Ω ->
  ps_P A = fold_right Rplus 0 (map ps_P (map (event_inter A) l)).
Proof.
  intros.
  rewrite <- ps_list_disjoint_union.
  - rewrite <- event_inter_list_union_distr.
    rewrite H2.
    autorewrite with prob.
    trivial.
  - intros x xin.
    apply in_map_iff in xin.
    destruct xin as [? [??]]; subst.
    rewrite Forall_forall in H0.
    auto with prob.
  - apply ForallOrdPairs_impl; trivial.
    apply ForallPairs_ForallOrdPairs.
    firstorder.
Qed.

Lemma ps_total {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A B C:event T) :
  sa_sigma A ->
  sa_sigma B ->
  sa_sigma C ->
  event_disjoint B C ->
  B ∪ C === Ω ->
  ps_P A = ps_P (A ∩ B) + ps_P (A ∩ C).
Proof.
  intros.
  intros.
  rewrite (ps_list_total ps A [B;C]); trivial.
  - simpl; lra.
  - repeat constructor; trivial.
  - repeat constructor; trivial.
  - rewrite list_union2; trivial.
Qed.

(* P1.5 *)
Lemma ps_complement {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A: event T) :
  sa_sigma A ->
  ps_P (¬ A) = 1 - ps_P A.
Proof.
  intros sa1.
  generalize (ps_total ps Ω A (¬ A)); intros HH.
  cut_to HH; eauto with prob.
  rewrite ps_one in HH.
  autorewrite with prob in HH.
  lra.
Qed.

(* P1.6 *)
Lemma ps_union {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A B: event T) :
  sa_sigma A ->
  sa_sigma B ->
  ps_P (A ∪ B) = ps_P A + ps_P B - ps_P (A ∩ B).
Proof.
  intros sa1 sa2.
  rewrite <- event_union_diff by eauto with prob.
  rewrite ps_disjoint_union by eauto with prob.
  rewrite (ps_total ps B A (¬ A)) by eauto with prob.
  rewrite event_diff_derived.  
  rewrite (event_inter_comm A B).
  lra.
Qed.

(* P1.7 inclusion/exclusion identity should not be hard to prove, 
   but is somewhat painful to state so it is omitted for now.
   We state and prove the case for n=3 for fun
 *)

Lemma ps_union3 {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) (A B C: event T) :
  sa_sigma A ->
  sa_sigma B ->
  sa_sigma C ->
  ps_P (A ∪ B ∪ C) =
  ps_P A + ps_P B + ps_P C
                    - ps_P (A ∩ B) - ps_P (A ∩ C) - ps_P (B ∩ C)
  + ps_P (A ∩ B ∩ C).
Proof.
  intros sa1 sa2 sa3.
  rewrite (ps_union ps (A ∪ B) C) by auto with prob.
  rewrite (ps_union ps A B) by auto with prob.
  rewrite (event_inter_comm (A ∪ B) C).
  rewrite event_inter_union_distr.
  rewrite (ps_union ps (C ∩ A) (C ∩ B)) by auto with prob.
  rewrite (event_inter_comm A C).
  rewrite (event_inter_comm B C).
  cut ((C ∩ A) ∩ (C ∩ B) === (A ∩ B) ∩ C).
  { intros eqq; rewrite eqq; lra. }
  rewrite event_inter_assoc.
  rewrite (event_inter_comm (C ∩ A) C).
  rewrite event_inter_assoc.
  autorewrite with prob.
  rewrite (event_inter_comm C A).
  rewrite <- event_inter_assoc.
  rewrite (event_inter_comm C B).
  rewrite event_inter_assoc.
  reflexivity.
Qed.

Lemma ps_boole_inequality {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S)
      (l: list (event T)) :
  Forall sa_sigma l ->
  ps_P (list_union l) <= fold_right Rplus 0 (map ps_P l).
Proof.
  intros.
  induction l; simpl.
  - autorewrite with prob.
    lra.
  - inversion H; clear H; subst.
    autorewrite with prob.
    rewrite ps_union; trivial.
    + specialize (IHl H3).
      generalize ( ps_pos (a ∩ list_union l)); intros.
      cut_to H.
      * lra.
      * rewrite Forall_forall in *.
        apply sa_inter; trivial.
        apply sa_list_union; auto.
    + apply sa_list_union.
      apply Forall_forall; trivial.
Qed.    

Definition make_collection_disjoint {T:Type} (coll:nat->event T) : nat -> event T
  := fun x => coll x \ (union_of_collection (fun y =>
                                               if lt_dec y x
                                               then coll y
                                               else ∅)).

Lemma sa_make_collection_disjoint {T:Type} {S:SigmaAlgebra T} (En:nat -> event T) :
  (forall (n:nat), sa_sigma (En n)) ->
  (forall n, sa_sigma (make_collection_disjoint En n)).
Proof.
  intros.
  unfold make_collection_disjoint.
  apply sa_diff; trivial.
  apply sa_countable_union.
  intros.
  match_destr.
  apply sa_none.
Qed.

Lemma make_collection_disjoint_sub {T:Type} (En:nat -> event T) n : event_sub (make_collection_disjoint En n) (En n).
Proof.
  now intros x [??].
Qed.

Lemma make_collection_disjoint0 {T:Type}  (En:nat -> event T) :
  event_equiv (make_collection_disjoint En 0) (En 0%nat).
Proof.
  unfold make_collection_disjoint.
  red; intros.
  split; intros.
  - destruct H; trivial.
  - split; trivial.
    unfold union_of_collection.
    intros [? HH].
    match_destr_in HH.
    lia.
Qed.

Hint Rewrite @make_collection_disjoint0 : prob.


Lemma make_collection_disjoint_in {T:Type} (coll:nat->event T) (x:nat) (e:T) :
  make_collection_disjoint coll x e <->
  (coll x e /\ forall y, (y < x)%nat -> ~ coll y e).
Proof.
  split.
  - unfold make_collection_disjoint; intros HH.
    destruct HH as [H1 H2].
    split; trivial.
    intros y ylt cy.
    apply H2.
    exists y.
    destruct (lt_dec y x); intuition.
  - intros [ce fce].
    unfold make_collection_disjoint.
    split; trivial.
    unfold union_of_collection.
    intros [n Hn].
    destruct (lt_dec n x); trivial.
    eapply fce; eauto.
Qed.
  
Lemma make_collection_disjoint_disjoint {T:Type} (coll:nat->event T) :
  collection_is_pairwise_disjoint (make_collection_disjoint coll).
Proof.
  intros x y xyneq e e1 e2.
  apply make_collection_disjoint_in in e1.
  apply make_collection_disjoint_in in e2.
  destruct e1 as [H11 H12].
  destruct e2 as [H21 H22].
  destruct (not_eq _ _ xyneq) as [xlt|ylt].
  - eapply H22; eauto.
  - eapply H12; eauto.
Qed.

Lemma union_of_make_collection_disjoint {T:Type} {sa:SigmaAlgebra T} (ps:ProbSpace sa) (coll:nat->event T) :
  (forall n : nat, sa_sigma (coll n)) ->
  sum_of_probs_equals ps_P  (make_collection_disjoint coll) (ps_P (union_of_collection  (make_collection_disjoint coll))).
Proof.
  intros.
  apply ps_countable_disjoint_union.
  - apply sa_make_collection_disjoint; trivial.
  - apply make_collection_disjoint_disjoint.
Qed.

(*
Section prob.
  Local Open Scope R.
  Local Open Scope prob.

  Definition Pr {Ts:Type} {Td:Type}
             {doms: SigmaAlgebra Ts}
             {dom: ProbSpace doms}
             {cod: SigmaAlgebra Td}
             {rv:RandomVariable dom cod}
             (S:Td->Prop)
    := ps_P (fun x:Ts => S (rv_X x)).

  Context {Ts:Type} {Td:Type}
          {doms: SigmaAlgebra Ts}
          {dom: ProbSpace doms}
          {cod: SigmaAlgebra Td}
          {rv:RandomVariable dom cod}.

  Definition independent (A B:Td->Prop) :=
    Pr (A ∩ B) = (Pr A * Pr B).

  Notation "a ⊥ b" := (independent a b) (at level 50) : prob. (* \perp *)

  Lemma pr_all : Pr Ω = R1.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_proper _ Ω) by firstorder. 
    apply ps_all.
  Qed.
  
  Lemma pr_none : Pr ∅ = R0.
  Proof.
    unfold Pr; simpl.
    rewrite (ps_proper _ ∅) by firstorder.
    apply ps_none.
  Qed.

End prob.
 *)

Notation "∅" := event_none : prob. (* \emptyset *)
Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
Notation "¬ a" := (event_complement a) (at level 20) : prob. (* \neg *)
Notation "a \ b" := (event_diff a b) (at level 50) : prob.
Notation "a ≤ b" := (event_sub a b) (at level 70) : prob. (* \leq *) 

Require Import Classical ClassicalFacts.

Section classic.

  Lemma sa_sigma_const_classic {T} (s: SigmaAlgebra T) P : sa_sigma (fun _ : T => P).
  Proof.
    apply sa_sigma_const.
    apply classic.
  Qed.
  
  Lemma make_collection_disjoint_union {T:Type} {S:SigmaAlgebra T} (coll:nat->event T) :
    union_of_collection coll
                        ===
                        union_of_collection (make_collection_disjoint coll).
  Proof.
    unfold union_of_collection.
    intros t.
    split; intros [n Hn].
    - generalize (excluded_middle_entails_unrestricted_minimization classic (fun n => coll n t))
      ; intros HH.
      specialize (HH _ Hn).
      destruct HH as [m mmin].
      exists m.
      destruct mmin.
      unfold make_collection_disjoint.
      split; trivial.
      unfold union_of_collection.
      intros [nn Hnn].
      destruct (lt_dec nn m); [ | tauto].
      specialize (H0 _ Hnn).
      lia.
    - apply make_collection_disjoint_in in Hn.
      exists n; tauto.
  Qed.

  Lemma ps_diff_le {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S) x y :
    sa_sigma x ->
    sa_sigma y ->
    ps_P (x \ y) <= ps_P x.
  Proof.
    intros.
    apply ps_sub; auto with prob.
  Qed.
  
  Lemma make_collection_disjoint_le {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S)
        (coll: nat -> event T) :
    (forall n, sa_sigma (coll n)) ->
    forall n, ps_P (make_collection_disjoint coll n) <= ps_P (coll n).
  Proof.
    intros sas n.
    unfold make_collection_disjoint.
    apply ps_diff_le; auto 2.
    apply sa_countable_union; intros nn.
    destruct (lt_dec nn n); auto with prob.
  Qed.
  
  Theorem ps_countable_boole_inequality {T:Type} {S:SigmaAlgebra T} (ps:ProbSpace S)
          (coll: nat -> event T) sum :
    (forall n, sa_sigma (coll n)) ->
    infinite_sum' (fun n => ps_P (coll n)) sum ->
    ps_P (union_of_collection coll) <= sum.
  Proof.
    intros sas.
    rewrite make_collection_disjoint_union.
    generalize (union_of_make_collection_disjoint ps coll sas); intros.
    unfold sum_of_probs_equals in H.
    eapply infinite_sum'_le; eauto.
    intros n; simpl.
    apply make_collection_disjoint_le; trivial.
  Qed.

  Lemma classic_event_none_or_has {A} (p:event A) : (exists y, p y) \/ event_equiv p event_none.
  Proof.
    destruct (classic (exists y, p y)).
    - eauto.
    - right; intros x.
      unfold event_none.
      split; [| tauto].
      intros px.
      apply H.
      eauto.
  Qed.

End classic.

Section take.
  (* define primitives for taking a prefix of a collection *)
  Context {Ts: Type}.
  Definition collection_take (En : nat -> event Ts) (n:nat) := map En (seq 0 n).

  Lemma collection_take_length (En : nat -> event Ts) (n:nat) :
    length (collection_take En n) = n.
  Proof.
    unfold collection_take.
    now rewrite map_length, seq_length.
  Qed.

  Lemma collection_take_nth_in a En n x:
    nth a (collection_take En n) event_none x <->
    (a < n /\ En a x)%nat.
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

  Lemma collection_take_Sn n En :
    (collection_take En (S n)) = collection_take En n ++ (En n::nil).
  Proof.
    unfold collection_take.
    rewrite seq_Sn, map_app.
    reflexivity.
  Qed.

  Lemma collection_take1 En : collection_take En 1 = [En 0%nat].
  Proof.
    reflexivity.
  Qed.

  Lemma collection_take_sub (En:nat -> event Ts) n :
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
  
End take.

Hint Rewrite @collection_take_Sn @collection_take1 : prob.

Section ascending.
  (* Define properties of ascending collections *)

  Context {Ts: Type}.
 Definition ascending_collection (En:nat -> event Ts) := (forall (n:nat), event_sub (En n) (En (S n))).

 Lemma ascending_collection_le (En:nat -> event Ts) :
   ascending_collection En ->
   (forall m n, (m <= n)%nat -> event_sub (En m) (En n)).
 Proof.
   intros asc.
   induction n; simpl.
   - intros.
     replace m with (0%nat) by lia.
     reflexivity.
   - intros.
     apply le_lt_or_eq in H.
     destruct H.
     + red in asc.
       rewrite <- asc.
       apply IHn.
       lia.
     + subst; reflexivity.
 Qed.

 
 Lemma ascending_collection_take_union (En:nat -> event Ts)  :
   ascending_collection En ->
   forall n, event_equiv (list_union (collection_take En (S n))) (En n).
 Proof.
   intros.
   induction n; simpl.
   - rewrite collection_take1, list_union_singleton.
     reflexivity.
   - rewrite collection_take_Sn.
     rewrite list_union_app.
     rewrite IHn.
     red in H.
     autorewrite with prob.
     rewrite event_union_sub_r; trivial.
     reflexivity.
 Qed.

 Lemma ascending_make_disjoint_collection_take_union (En:nat -> event Ts) :
   ascending_collection En ->
   forall n, event_equiv (list_union (collection_take (make_collection_disjoint En) (S n))) (En n).
 Proof.
   intros asc n.
   induction n; simpl.
   - autorewrite with prob.
     reflexivity.
   - autorewrite with prob.
     autorewrite with prob in IHn.
     rewrite IHn.
     intros a.
     split; intros HH.
     + destruct HH.
       * now apply asc.
       * now apply make_collection_disjoint_sub.
     + red.
       unfold make_collection_disjoint.
       unfold event_diff.
       destruct (classic (union_of_collection (fun y : nat => if lt_dec y (S n) then En y else event_none) a)).
       * destruct H as [x HH2].
         match_destr_in HH2; [ | red in HH2; tauto].
         left.
         red in asc.
         eapply (ascending_collection_le _ asc x); trivial.
         lia.
       * eauto.
 Qed.

End ascending.

Hint Resolve ps_none ps_one : prob.

  Lemma event_complement_union {Ts} (E1 E2:event Ts) :
    event_equiv (¬ (E1 ∪ E2))
                (¬ E1 ∩ ¬ E2).
  Proof.
    unfold event_complement, event_inter, event_union.
    red; intros.
    split; intros.
    - now apply not_or_and.
    - now apply and_not_or.
  Qed.

  Lemma event_complement_inter {Ts} (E1 E2:event Ts) :
    event_equiv (¬ (E1 ∩ E2))
                (¬ E1 ∪ ¬ E2).
  Proof.
    unfold event_complement, event_inter, event_union.
    red; intros.
    split; intros.
    - now apply not_and_or.
    - now apply or_not_and.
  Qed.

  Lemma ps_zero_union {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
    E1 E2 :
    sa_sigma E1 ->
    sa_sigma E2 ->
    ps_P E1 = 0 ->
    ps_P E2 = 0 ->
    ps_P (E1 ∪ E2) = 0.
  Proof.
    intros sa1 sa2 p1 p2.
    rewrite ps_union by auto with prob.
    rewrite p1, p2.
    field_simplify.
    cut (ps_P (event_inter E1 E2) = 0); try lra.

    assert (HH:event_sub ((event_inter E1 E2)) E1).
    {
      red; intros.
      now destruct H.
    }
    apply (ps_sub prts) in HH
    ; auto with prob.
    rewrite p1 in HH.
    apply Rle_antisym; trivial.
    apply ps_pos.
    auto with prob.
  Qed.
  
  Lemma ps_one_inter {Ts:Type} 
          {dom: SigmaAlgebra Ts}
          (prts: ProbSpace dom)
    E1 E2 :
    sa_sigma E1 ->
    sa_sigma E2 ->
    ps_P (E1)=1 -> ps_P (E2)=1 -> ps_P (E1 ∩ E2)=1.
  Proof.
    intros sa1 sa2 p1 p2.
    cut (1-ps_P (event_inter E1 E2) = 0); [lra |].
    rewrite <- ps_complement by auto with prob.    
    rewrite event_complement_inter.
    apply ps_zero_union; auto with prob.
    - rewrite ps_complement; auto with prob.
      rewrite p1.
      lra.
    - rewrite ps_complement; auto with prob.
      rewrite p2.
      lra.
  Qed.

(* vectors *)

Definition bounded_inter_of_collection {T} {n} {s: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event T)
  : event T
  := fun t => forall i pf, collection i pf t.

Definition bounded_inter_of_collection_unbound {T} {n} {s: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event T)
  : event T
  := inter_of_collection
       (fun i => match lt_dec i n with
              | left pf => collection i pf
              | right _ => Ω
              end).

Lemma bounded_inter_of_collection_unbound_eq {T} {n} {s: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event T) :
  bounded_inter_of_collection collection === bounded_inter_of_collection_unbound collection.
Proof.
  intros x.
  unfold bounded_inter_of_collection_unbound, bounded_inter_of_collection.
  split; intros.
  - intros i.
    match_destr.
    now red.
  - specialize (H i).
    simpl in H.
    match_destr_in H; try lia.
    now replace pf with l by apply le_uniqueness_proof.
Qed.

Lemma sa_bounded_inter {T} {n} {s: SigmaAlgebra T} (collection: forall i (pf:(i<n)%nat), event T) :
      (forall (i : nat) (pf : (i < n)%nat), sa_sigma (collection i pf)) ->
      sa_sigma (bounded_inter_of_collection collection).
Proof.
  intros.
  rewrite bounded_inter_of_collection_unbound_eq.
  apply sa_countable_inter; intros.
  match_destr.
  apply sa_all.
Qed.


Section dec.

  
  Definition dec_event {T} (a:event T) := forall x, {a x} + {~ a x}.

  Lemma dec_event_inter {T} {a b:event T} :
    dec_event a -> dec_event b -> dec_event (event_inter a b).
  Proof.
    intros ???.
    apply sumbool_and; trivial.
  Defined.

  Lemma dec_event_union {T} {a b:event T} :
    dec_event a -> dec_event b -> dec_event (event_union a b).
  Proof.
    unfold event_union.
    intros d1 d2 x.
    destruct (d1 x).
    - left; eauto.
    - destruct (d2 x).
      + left; eauto.
      + right.
        tauto.
  Defined.

  Context {Ts:Type} {dom:SigmaAlgebra Ts}.
  
  Record dec_sa_event :=
    {
    dsa_event : event Ts
    ; dsa_dec :  dec_event dsa_event
    ; dsa_sa : sa_sigma dsa_event
    }.

    Program Definition dsa_Ω : dec_sa_event
      := {| dsa_event := Ω |}.
    Next Obligation.
      left; now red.
    Defined.
    Next Obligation.
      apply sa_all.
    Qed.

    Program Definition dsa_none : dec_sa_event
      := {| dsa_event := event_none |}.
    Next Obligation.
      right; now red.
    Defined.
    Next Obligation.
      apply sa_none.
    Qed.

  Definition dec_sa_event_inter (e1 e2 : dec_sa_event) : dec_sa_event :=
    {| dsa_event := (event_inter (dsa_event e1) (dsa_event e2))
      ; dsa_dec := dec_event_inter (dsa_dec e1) (dsa_dec e2)
      ; dsa_sa := (sa_inter (dsa_sa e1) (dsa_sa e2))
    |} .

    Definition dec_sa_event_union (e1 e2 : dec_sa_event) : dec_sa_event :=
    {| dsa_event := (event_union (dsa_event e1) (dsa_event e2))
      ; dsa_dec := dec_event_union (dsa_dec e1) (dsa_dec e2)
      ; dsa_sa := (sa_union (dsa_sa e1) (dsa_sa e2))
    |} .

     
   Definition refine_dec_sa_event (e : dec_sa_event) (l : list (dec_sa_event)) :=
     map (fun e2 => dec_sa_event_inter e e2) l.

   Definition refine_dec_sa_partitions (l1 l2 : list dec_sa_event) :=
     flat_map (fun e1 => refine_dec_sa_event e1 l2) l1.

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
    unfold event_disjoint, event_inter; intros.
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
      + red; tauto.
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

End dec.
