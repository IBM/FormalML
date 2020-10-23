Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Coq.Reals.RiemannInt.
Require Import Lra Lia.
Require Import List.
Require Import Morphisms EquivDec.
Require Import Coquelicot.Rbar.
Require Import Coquelicot.Lub.

Require Import Utils.
Import ListNotations.

(* Declare Scope prob. *)

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

  Definition Ω {T} : event T   (* \Omega *)
    := fun x: T => True. 

  Definition event_none {T} : event T
    := fun x: T => False.
  
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
  Proper (event_sub --> event_sub --> Basics.impl) (@event_disjoint T).
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

Hint Resolve @event_sub_true @event_false_sub : prob.

Lemma event_sub_union_l {T} (A B:event T) : A ≤ A ∪ B.
Proof.
  firstorder.
Qed.

Lemma event_sub_union_r {T} (A B:event T) : B ≤ A ∪ B.
Proof.
  firstorder.
Qed.

Hint Resolve @event_sub_union_l @event_sub_union_r : prob.

Lemma event_inter_sub_l {T} (A B:event T) : A ∩ B ≤ A.
Proof.
  firstorder.
Qed.

Lemma event_inter_sub_r {T} (A B:event T) : A ∩ B ≤ B.
Proof.
  firstorder.
Qed.

Hint Resolve @event_inter_sub_l @event_inter_sub_r : prob.

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

(* Returns a new set prop (T->Prop) that returns true if t:T is in any of the sets within the collection. *)
Definition union_of_collection {T: Type} (collection: nat -> event T) : event T :=
  fun t:T => (exists n, (collection n) t).

Definition inter_of_collection {T: Type} (collection: nat -> event T) : event T :=
  fun t:T => (forall n, (collection n) t).


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

Class SigmaAlgebra (T:Type) :=
  {
    sa_sigma : event T -> Prop;
    
    (* alternative to assuming functional extensionality *)
    sa_proper :> Proper (event_equiv ==> iff) sa_sigma ;

    (* alternative to assuming LEM *)
    sa_dec (A:event T) : event_lem A;
    
    sa_countable_union (collection: nat -> event T) :
      (forall n, sa_sigma (collection n)) ->
      sa_sigma (union_of_collection collection);
    
    sa_complement (A:event T) :
      sa_sigma A -> sa_sigma (¬ A) ;
    
    sa_all : sa_sigma Ω 
                       
  }.

Hint Resolve sa_dec : prob.

(* restate some lemmas that rely on lem unconditionally *)
Lemma ps_event_union_complement {T} {s : SigmaAlgebra T} (A:event T) :
  A ∪ ¬ A === Ω.
Proof.
  apply event_union_complement.
  apply sa_dec.
Qed.

Lemma ps_event_union_not_self {T} {s : SigmaAlgebra T} (A:event T) :
  A ∪ ¬ A === Ω.
Proof.
  apply event_union_not_self.
  apply sa_dec.
Qed.

Lemma ps_event_union_diff {T:Type} {s : SigmaAlgebra T} (A B:event T) :
  A ∪ (B \ A) === A ∪ B.
Proof.
  apply event_union_diff.
  apply sa_dec.
Qed.

Lemma ps_event_union_diff_sub {T:Type} {s : SigmaAlgebra T} (A B:event T) :
  A ≤ B -> A ∪ (B \ A) === B.
Proof.
  apply event_union_diff_sub.
  apply sa_dec.
Qed.

Hint Resolve @ps_event_union_complement @ps_event_union_not_self 2ps_event_union_diff @ps_event_union_diff_sub : prob.

Lemma sa_notnot {T} {s: SigmaAlgebra T} (A:event T) : forall x, ~ ~ A x -> A x.
Proof.
  intros.
  destruct (sa_dec A x); intuition.
Qed.

Lemma sa_none {T} {s: SigmaAlgebra T} : sa_sigma (∅).
Proof.
  eapply sa_proper
  ; [ | eapply sa_complement; eapply sa_all].
  firstorder.
Qed.

Hint Resolve sa_all sa_none sa_complement : prob.

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
    + destruct (sa_dec (collection n) x); trivial.
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

Lemma list_inter2 {T} (x1 x2 : event T) :
  list_inter [x1 ; x2] === x1 ∩ x2.
Proof.
  autorewrite with prob.
  reflexivity.
Qed.

Lemma list_collection_disjoint {T} (l:list (event T)) :
    ForallOrdPairs event_disjoint l ->
    collection_is_pairwise_disjoint (list_collection l ∅).
Proof.
  unfold collection_is_pairwise_disjoint, event_disjoint, event_none, list_collection.
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
  rewrite event_union_diff_sub in HH by auto with prob.
  rewrite HH.
  generalize (ps_pos (B \ A)); intros.
  cut_to H; auto with prob.
  lra.
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
  cut_to HH; auto with prob.
  - rewrite ps_one in HH.
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
  rewrite <- event_union_diff by auto with prob.
  rewrite ps_disjoint_union by auto with prob.
  rewrite (ps_total ps B A (¬ A)) by auto with prob.
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

(*
Require Import Arith Wf.

Lemma make_collection_disjoint_in_exists {T:Type} (coll:nat->event T) (x:nat) (e:T) :
  coll x e ->
  exists n : nat, make_collection_disjoint coll n e.
Proof.
  intros.
  unfold make_collection_disjoint.
  assert ((exists y, y < x /\ coll y e) \/ ~(exists y, y < x /\ coll y e) )%nat.
  
  revert H.
  induction x as [ x IHx ] using (well_founded_induction lt_wf).
  induction x; intros H.
  - exists 0%nat.
    simpl.
    compute.
    split; trivial.
    firstorder.
  - 
*)

Lemma sa_make_collection_disjoint {T:Type} (sa:SigmaAlgebra T) (coll:nat->event T) :
  (forall n, sa_sigma (coll n)) ->
  (forall n : nat, sa_sigma (make_collection_disjoint coll n)).
Proof.
  unfold make_collection_disjoint; intros sas n.
  apply sa_diff; [eauto | ].
  apply sa_countable_union; intros.
  destruct (lt_dec n0 n)
  ; auto with prob.
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

Section RandomVariable.
  (* todo better type names. *)
  (* The preimage of the function X on codomain B. *)
  Definition preimage {Ts: Type} {Td: Type}
             (X: Ts -> Td)
             (B: event Td)
             := fun omega: Ts => B (X omega).

  (* A random variable is a mapping from a pobability space to a sigma algebra. *)
  Class RandomVariable {Ts:Type} {Td:Type}
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        (cod: SigmaAlgebra Td) :=
    {
      (* the random variable. *)
      rv_X: Ts -> Td;

      (* for every element B in the sigma algebra, 
           the preimage of rv_X on B is an event in the probability space *)
      rv_preimage: forall B: event Td, (sa_sigma (preimage rv_X B));
    }.

  Class RealValuedRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        (prts: ProbSpace dom)
        (cod: SigmaAlgebra R)  :=
  
    {
      (* the random variable. *)
      rrv_X: Ts -> R;

      rrv_is_real: forall r:R, sa_sigma (fun omega:Ts => (rrv_X omega) <= r);
    }.

  Class ConstantRealValuedRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R}
        (rrv : RealValuedRandomVariable prts cod) :=
    { 
      srv_val : R;
      srv_val_complete : forall x, rrv_X x =  srv_val
    }.

  Class SimpleRealValuedRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R}
        (rrv : RealValuedRandomVariable prts cod) :=
    { 
      srv_vals : list R;
      srv_vals_complete : forall x, In (rrv_X x) srv_vals
    }.

  Definition RealRandomVariable_le {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R} 
        (rv1 rv2: RealValuedRandomVariable prts cod) : Prop :=
    forall (x:Ts), rrv_X (RealValuedRandomVariable:=rv1) x <= 
                   rrv_X (RealValuedRandomVariable:=rv2) x.

  Definition PositiveRandomVariable {Ts:Type}
        {dom: SigmaAlgebra Ts}
        {prts: ProbSpace dom}
        {cod: SigmaAlgebra R} 
        (rv: RealValuedRandomVariable prts cod) : Prop :=
    forall (x:Ts), 0 <= rrv_X x.

End RandomVariable.

Section SimpleExpectation.
  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}
    {cod: SigmaAlgebra R}
    {rrv : RealValuedRandomVariable Prts cod}.

  Definition singleton_event {T} (m:T) := fun x => x=m.

  Definition simpleRandomVariable_partition_image 
             (srv : SimpleRealValuedRandomVariable rrv) : list (event Ts) :=
    map (preimage rrv_X) (map singleton_event srv_vals).
    
  Fixpoint list_sum (l : list R) : R :=
    match l with
    | nil => 0
    | x :: xs => x + list_sum xs
    end.

  Definition SimpleExpectation (srv : SimpleRealValuedRandomVariable rrv) : R :=
    list_sum (map (fun v => Rmult v (ps_P (preimage rrv_X (singleton_event v)))) 
                  srv_vals).

  Definition scaleSimpleVariable (c:R) (srv : SimpleRealValuedRandomVariable rrv) : 
    SimpleRealValuedRandomVariable rrv.
  Admitted.    

  Lemma scaleSimpleExpectation (c:R) (srv : SimpleRealValuedRandomVariable rrv) : 
    c * SimpleExpectation srv = SimpleExpectation (scaleSimpleVariable c srv).
  Proof.
  Admitted.
    
End SimpleExpectation.

Section Expectation.

  Context 
    {Ts:Type}
    {dom: SigmaAlgebra Ts}
    {Prts: ProbSpace dom}
    {cod: SigmaAlgebra R}.

  Definition BoundedPositiveRandomVariable
    (rv1 rv2 : RealValuedRandomVariable Prts cod) : Prop :=
    PositiveRandomVariable rv2 /\ RealRandomVariable_le rv2 rv1.

  Definition SimpleExpectationSup 
             (E :  forall 
                     (rrv: RealValuedRandomVariable Prts cod)
                     (srv:SimpleRealValuedRandomVariable rrv), Prop) : Rbar
    := Lub_Rbar (fun (x : R) => 
                   exists rrv srv, 
                     E rrv srv /\ (SimpleExpectation srv) = x).
    
  Definition Expection_posRV
             {rrv : RealValuedRandomVariable Prts cod}
             (posrv:PositiveRandomVariable rrv) :  Rbar   :=
      (SimpleExpectationSup
         (fun
            (rrv2: RealValuedRandomVariable Prts cod)
            (srv2:SimpleRealValuedRandomVariable rrv2) =>
            (BoundedPositiveRandomVariable rrv rrv2))).

  Program Definition pos_fun_part {Ts:Type} (f : Ts -> R) : (Ts -> nonnegreal) :=
    fun x => mknonnegreal (Rmax (f x) 0) _.
  Next Obligation.
    apply Rmax_r.
  Defined.

  Program Definition neg_fun_part {Ts:Type} (f : Ts -> R) : (Ts -> nonnegreal) :=
    fun x => mknonnegreal (Rmax (- f x) 0) _.
  Next Obligation.
    apply Rmax_r.
  Defined.

  Lemma Relu_measurable_neg (f : Ts -> R) :
    forall (r:R), r < 0 -> sa_sigma (fun omega : Ts => Rmax (f omega) 0 <= r).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => Rmax (f omega) 0 <= r) event_none).
    unfold event_equiv; intros.
    generalize (Rmax_r (f x) 0); intros.
    unfold event_none.
    lra.
    rewrite H0.
    apply sa_none.
  Qed.
    
  Lemma Relu_measurable_pos (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  0 <= r -> sa_sigma (fun omega : Ts => Rmax (f omega) 0 <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => Rmax (f omega) 0 <= r)
                        (fun omega : Ts => f omega <= r)).
    unfold event_equiv, event_union; intros.
    unfold Rmax.
    destruct (Rle_dec (f x) 0); lra.
    now rewrite H1.
  Qed.

  Lemma Relu_measurable (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => Rmax (f omega) 0 <= r)).
  Proof.
    intros.
    destruct (Rle_dec 0 r).
    now apply Relu_measurable_pos.
    apply Relu_measurable_neg.
    lra.
  Qed.

  Lemma equiv_le_lt (f : Ts -> R) (r:R) :
    event_equiv (fun omega : Ts => f omega < r)
                (union_of_collection
                   (fun (n:nat) => (fun omega : Ts => f omega <= r - / INR (S n)))).
  Proof.
    unfold event_equiv, union_of_collection.
    intros.
    split; intros.
    
    admit.
    destruct H.
    assert (0 < / INR (S x0)).
    apply Rinv_0_lt_compat.
    apply  lt_0_INR; lia.
    lra.
    Admitted.

  Lemma sa_le_ge (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega >= r)
                        (event_complement (fun omega : Ts => f omega < r))).
    {
      simpl.
      intro x.
      unfold event_complement.
      split; intros; lra.
    }
      rewrite H0.
      apply sa_complement.
      rewrite equiv_le_lt.
      apply sa_countable_union.
      intros.
      apply H.
  Qed.

  Lemma Ropp_measurable (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => - (f omega) <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => - (f omega) <= r)
                        (fun omega : Ts => (f omega) >= -r)).
    unfold event_equiv; intros.
    lra.
    rewrite H0.
    now apply sa_le_ge.
  Qed.

  Program Instance positive_part_rv (rvv : RealValuedRandomVariable Prts cod) : 
    RealValuedRandomVariable Prts cod
    := {
    rrv_X := (pos_fun_part rrv_X)
      }.
  Next Obligation.
    destruct rvv.
    now apply Relu_measurable.
  Qed.

  Lemma positive_part_prv (rrv : RealValuedRandomVariable Prts cod) : 
    PositiveRandomVariable (positive_part_rv rrv).
  Proof.
    unfold PositiveRandomVariable, rrv_X.
    unfold positive_part_rv, pos_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

 Program Instance negative_part_rv
          (rrv : RealValuedRandomVariable Prts cod) : RealValuedRandomVariable Prts cod
    := {
    rrv_X := (neg_fun_part rrv_X)
      }.
  Next Obligation.
    destruct rrv.
    apply Relu_measurable.
    now apply Ropp_measurable.
  Qed.

  Lemma negative_part_prv
           (rrv : RealValuedRandomVariable Prts cod) :
    PositiveRandomVariable (negative_part_rv rrv).
  Proof.
    unfold PositiveRandomVariable, rrv_X.
    unfold negative_part_rv, neg_fun_part.
    intros.
    apply cond_nonneg.
 Qed.

  Definition Expectation (rrv : RealValuedRandomVariable Prts cod) : option Rbar :=
    Rbar_plus' (Expection_posRV  (positive_part_prv rrv))
               (Rbar_opp (Expection_posRV  (negative_part_prv rrv))).

End Expectation.

Section lebesgueintegration.
  
  Class MeasurableFunction {Ts: Type} (dom: SigmaAlgebra Ts) :=
    {
      measure_mu: event Ts -> R;

      measure_none : measure_mu ∅ = R0 ;
      measure_ge_zero: forall A : event Ts, sa_sigma A -> 0 <= measure_mu A;
  
      measure_coutably_additive: forall collection: nat -> event Ts,
           (forall n : nat, sa_sigma (collection n)) ->
           collection_is_pairwise_disjoint collection ->
           sum_of_probs_equals measure_mu collection (measure_mu (union_of_collection collection))

    }.


  (* See https://en.wikipedia.org/wiki/Lebesgue_integration#Towards_a_formal_definition *)
  Definition F_star {dom:SigmaAlgebra R} (measure: MeasurableFunction dom) (f: R -> R) (t: R) :=
    measure_mu (fun (x: R) => (f x) > t).

  (* The integral $\int f d\mu defined in terms of the Riemann integral.
   * note that this definition assumes that f : R -> R+
   * Again, see https://en.wikipedia.org/wiki/Lebesgue_integration#Towards_a_formal_definition *)
  Definition Lebesgue_integrable_pos {dom: SigmaAlgebra R}
             (f : R -> R)
             (f_nonneg : forall x:R, f x > 0)
             (measure: MeasurableFunction dom)
             (a b : R) :=
    (Riemann_integrable (F_star measure f) a b).
End lebesgueintegration.

Instance ProbSpace_Measurable {T:Type} {sa: SigmaAlgebra T} (ps:ProbSpace sa) : MeasurableFunction sa
  := {
      measure_mu := ps_P ;
      measure_none := (ps_none ps) ;
      measure_ge_zero := ps_pos ;
      measure_coutably_additive := ps_countable_disjoint_union ; 
    }.

Section zmBoundedVariance.
  (* TODO finish this definition *)
  Class ZeroMeanVoundedVariance (t: nat -> R) :=
    {
      has_zero_mean: Prop;
      has_bounded_variance: Prop;
    }.
End zmBoundedVariance.

Section prob.
  Local Open Scope R.
  Local Open Scope prob.

  Context {Ts:Type} {Td:Type}
          {dom: SigmaAlgebra Ts}
          {prts: ProbSpace dom}
          {cod: SigmaAlgebra Td}
          {rv:RandomVariable prts cod}.

  Definition Pr 
             (S:Td->Prop)
    := ps_P (fun x:Ts => S (rv_X x)).

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
  
Notation "∅" := event_none : prob. (* \emptyset *)
Notation "a ∪ b" := (event_union a b) (at level 50) : prob. (* \cup *)
Notation "a ∩ b" := (event_inter a b) (at level 50) : prob. (* \cap *)
Notation "¬ a" := (event_complement a) (at level 20) : prob. (* \neg *)
Notation "a \ b" := (event_diff a b) (at level 50) : prob.
Notation "a ≤ b" := (event_sub a b) (at level 70) : prob. (* \leq *) 

Require Import Classical ClassicalFacts.

Section classic.
  
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

End classic.

