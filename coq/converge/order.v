Require Import LibUtilsLattice.
Require Import Sets.Ensembles.


Section range. 
  
  Definition range {A B : Type} (f : A -> B): Ensemble B := fun y:B => exists x:A, f x = y.

  Definition mem {A : Type}(a : A) (X : Ensemble A) : Prop := X a.  

  Notation "a ∈ X" := (mem a X) (at level 99). 

  Definition preimage {A B : Type} (f : A -> B) (s : Ensemble B) : Ensemble A :=
    fun x => f x ∈ s.
  
  Notation "f ⁻¹ s" := (preimage f s) (at level 99). 

  Definition image {A B : Type} (f : A -> B) (s : Ensemble A) : Ensemble B :=
    fun b => exists a, (a ∈ s) /\ f a = b. 
               
  Notation "f '' s" := (image f s) (at level 1000).
  
  Lemma mem_range_iff {A B : Type} (f : A -> B) (y : B) : (y ∈ range f) <-> exists x:A, f x = y.
  Proof.
    firstorder.
  Qed.
  
  Hint Resolve mem_range_iff : range. 

  Lemma mem_range_self {A B} (a : A) (f : A -> B) : (f a ∈ range f).
  Proof. 
    now exists a.
  Qed.

  Hint Resolve mem_range_self : range. 

  Lemma range_id {A} : range (fun x => x) = Full_set A.
  Proof.
    unfold range.
    apply Extensionality_Ensembles.
    split.
    - constructor. 
    - intros x Hx. now exists x. 
  Qed.

  Hint Resolve range_id : range. 

  Lemma exists_range_iff {A B} (f : A -> B) (p : B -> Prop):
    (exists b, (b ∈ range f) /\ p b) <-> (exists a, p (f a)).
  Proof.
    intuition. 
    * destruct H as [b [[a Ha] Hpb]].
      exists a ; subst ; auto.
    * destruct H.
      exists (f x). auto with range.
  Qed.

  Lemma forall_range {A B}(f : A -> B) (p : B -> Prop) :
    (forall b, (b ∈ range f) /\ p b) -> (forall a, p (f a)).
  Proof.
    intros H i. 
    now destruct (H (f i)). 
  Qed. 

  Lemma image_full_set {A B}(f : A -> B) :
    (f '' Full_set A) = range f.
  Proof. 
    apply Extensionality_Ensembles.
    split.
    - intros x Hx. 
      destruct Hx as [a [_ Hfa]] ; subst ;
      apply mem_range_self. 
    - intros x Hx. 
      destruct Hx as [a Ha]. now exists a.
  Qed.

  
End range. 
