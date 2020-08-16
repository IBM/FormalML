Require Import Sets.Ensembles.
Require Import Coq.Program.Basics. 

Section range. 
  Local Open Scope program_scope.

  Class NonEmpty (A : Type) :=
  ex : A.
    
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

  Notation "A ⊆ B" := (Included _ A B) (at level 50).

  Lemma image_subset_range {A B} (f : A -> B) (s : Ensemble A) :  (f '' s) ⊆ (range f).
  Proof.
    intros x [x0 [H1 H2]] ; subst.
    apply mem_range_self.
  Qed. 
  
  Lemma range_comp {A B C} (f : A -> B) (g: B -> C): range (fun x => g (f x)) = (g '' range f). 
  Proof.
    apply Extensionality_Ensembles. 
    split. 
    - intros x Hx. 
      destruct Hx ; subst. 
      exists (f x0).
      split ; trivial ; apply mem_range_self.
    - intros x [x0 [[x1 Hx1] H2]] ; subst.
      exists x1 ; trivial.
  Qed.

  Lemma range_subset_iff {A B} (f : A -> B) (s : Ensemble B) : range f ⊆ s <-> forall y, f y ∈ s.
  Proof.
    split.
    * intros H y.
      specialize (H (f y)).
      apply H. apply mem_range_self.
    * intros H y [x Hyx] ; subst.
      apply H.
  Qed.

  Lemma range_comp_subset_range {A B C} (f : A -> B) (g : B -> C) : range (g ∘ f) ⊆ range g.
  Proof.
    intros x [x0 Hx0]. 
    now exists (f x0).
  Qed.

  Lemma range_nonempty {A B} (f : A -> B) (ne : NonEmpty A) : exists x, (x ∈ range f). 
  Proof.
    exists (f ne). apply mem_range_self.
  Qed.

  Notation "A ∩ B" := (Intersection _ A B) (at level 50). 
   Lemma image_preimage_eq_subset_inter {A B} {f : A -> B} {s : Ensemble B} :
     (f '' (f ⁻¹ s)) = s ∩ (range f).
   Proof.
     apply Extensionality_Ensembles. 
     split.
     * intros x Hx ; destruct Hx ; subst.
       destruct H. 
       constructor. do 2 red in H. 
       now rewrite H0 in H.
       rewrite <-H0 ; apply mem_range_self.
     *  intros x Hx ; destruct Hx.
        destruct H0 as [x0 Hx0].
        exists x0 ; split ; trivial. 
        red ; now subst.
   Qed.


End range. 
