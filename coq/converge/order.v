Require Import LibUtilsLattice.
Require Import Sets.Ensembles.
Require Import Equations.Equations.


Section range. 
  
  Definition range {A B : Type} (f : A -> B): Ensemble B := fun y:B => exists x:A, f x = y.

  Definition mem {A : Type}(a : A) (X : Ensemble A) : Prop := X a.  

  Notation "a ∈ X" := (mem a X) (at level 99). 

  Lemma mem_range_iff {A B : Type} (f : A -> B) (y : B) : (y ∈ range f) <-> exists x:A, f x = y.
  Proof.
    firstorder.
  Qed.
  
  Hint Resolve mem_range_iff : range. 

  Lemma mem_range_self {A B} (a : A) (f : A -> B) : (f a ∈ range f).
  Proof. 
    now exists a.
  Qed.

  Import FunctionalExtensionality. 
  Lemma range_id {A} : range (fun x => x) = @Full_set A.
  Proof.
    unfold range.
    apply Extensionality_Ensembles.
    split.
    - constructor. 
    - intros x Hx. red. now exists x. 
  Qed. 
                                                            
Lemma forall_range_iff (p : Ensemble B)
End range. 
