Require Import String.
Require Import EquivDec.
Require Import RelationClasses.
Require Import List.
Require Import NPeano.
Require Import Lra Omega.
Require Reals.
Require Import Eqdep_dec.
Require Import LibUtils.

Require Import Floatish.


Set Bullet Behavior "Strict Subproofs".

Section Vector.

  Context {floatish_impl:floatish}.
  Local Open Scope float.

    Definition Vector (T:Type) (n : nat) := {n':nat | n' < n}%nat -> T.
    Definition Matrix (T:Type) (n m : nat) := 
      {n':nat | n' < n}%nat -> {m':nat | m' < m}%nat -> T.


  Definition ConstVector {T} (n:nat) (c:T) : (Vector T n) := fun (n': {n':nat | n' < n}%nat) => c.
  Definition ConstMatrix {T} (n m : nat) (c:T) : (Matrix T n m) := fun (n': {n':nat | n' < n}%nat) (m':{m':nat | m' < m}%nat) => c.
  


    Definition vector_fold_right1_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} (v:Vector B m) (n:nat) (pf:(n<=m)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - destruct n.
        + assert (pf2:(0 < m)%nat) by omega.
          exact (singleton (v (exist _ 0 pf2)%nat)).
        + assert (pf2:(S n <= m)%nat) by omega.
          assert (pf3:(S n < m)%nat) by omega.
          apply f.
          * exact (v (exist _ (S n) pf3)).
          * exact (IHn pf2).
    Defined.

    Definition vector_fold_right_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) (n:nat) (pf:(n<=m)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - apply f.
        + assert (pf2:(n < m)%nat) by omega.
          exact (v (exist _ n pf2)).
        + apply IHn.
          omega.
    Defined.

    Definition vnil {T} : Vector T 0.
    Proof.
      intros [i pf].
      omega.
    Defined.

    Definition vcons {T} {n} (x:T) (v:Vector T n) : (Vector T (S n)).
    Proof.
      intros [i pf].
      destruct (Nat.eq_dec i n).
      + exact x.
      + apply v.
        exists i.
        omega.
    Defined.

    
    Definition vhd {T} {n} (v:Vector T (S n)) : T := v (exist _ (0%nat) (Nat.lt_0_succ n)).
    Definition vlast {T} {n} (v:Vector T (S n)) : T := v (exist _ (n%nat) (Nat.lt_succ_diag_r n)).

    Definition vdrop_last {T} {n} (v:Vector T (S n)) : Vector T n.
    Proof.
      intros [i pf]; apply v.
      exists i.
      apply NPeano.Nat.lt_lt_succ_r; trivial.
    Defined.


    Definition vector_fold_right1_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) {m:nat} (v:Vector B m) : A m
      := vector_fold_right1_bounded_dep f init singleton v m (le_refl _).

    Definition vector_fold_right_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) {m:nat} (v:Vector B m) : A m
      := vector_fold_right_bounded_dep f init v m (le_refl _).

    Definition vector_fold_right1 {A B:Type} (f:B->A->A) (init:A) (singleton:B->A) {m:nat} (v:Vector B m)
      := vector_fold_right1_dep (A:=fun _ => A) (fun _ => f) init singleton v.

    Definition vector_fold_right {A B:Type} (f:B->A->A) (init:A) {m:nat} (v:Vector B m)
      := vector_fold_right_dep (fun _ => f) init v.


    Definition vsum {m:nat} (v:Vector float m) : float
      := vector_fold_right1 Fplus 0 id v.

    Definition vectoro_to_ovector {T} {n} (v:Vector (option T) n) : option (Vector T n)
      := vector_fold_right_dep (fun n => lift2 (@vcons _ n)) (Some vnil) v.

    Definition matrixo_to_omatrix {T} {m n} (v:Matrix (option T) m n) : option (Matrix T m n)
      := vectoro_to_ovector (fun i => vectoro_to_ovector (v i)).

    Definition vmap {A B} {n} (f:A->B) (v:Vector A n) : Vector B n
      := vector_fold_right_dep (fun n x y => vcons (n:=n) (f x) y) vnil v.

    Definition msum {m n:nat} (v:Matrix float m n) : float :=
      vsum (vmap vsum v).

    Definition mmap {A B} {m n} (f:A->B) (mat:Matrix A m n) : Matrix B m n
      := vmap (fun mrow => vmap f mrow) mat.

    Definition list_fold_right1_bounded_dep {A:nat->Type} {B} (f:forall n,B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) (l:list B) (n:nat) (pf:(n<=length l)%nat)
    : A n.
    Proof.
      induction n.
      - exact init.
      - destruct n.
        + assert (pf2:(0 < length l)%nat) by omega.
          destruct l.
          * simpl in pf; omega.
          * exact (singleton b).
        + assert (pf2:(S n <= length l)%nat) by omega.
          apply f.
          * destruct l; simpl in *; try omega.
            apply b.
          * apply IHn.
            apply pf2.
    Defined.

    Definition list_fold_right1_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) (singleton:B->A 1%nat) (l:list B) : A (length l)
      := list_fold_right1_bounded_dep f init singleton l (length l) (le_refl _).

    Definition list_fold_right_dep {A:nat->Type} {B} (f:forall n, B->A n->A (S n)) (init:A 0%nat) (l:list B) : A (length l)
      := list_fold_right1_dep f init (fun a => f _ a init) l.

    Definition list_to_vector {A} (l:list A) : Vector A (length l)
      := list_fold_right_dep (@vcons _) vnil l.

    Definition vector_to_list {A} {n} (v:Vector A n) : list A
      := vector_fold_right cons nil v.
    
    Definition vseq start len : Vector nat len
      := eq_rect _ _ (list_to_vector (seq start len)) _ (seq_length _ _).

    Definition vector_zip {A B} {m:nat} (v1:Vector A m) (v2:Vector B m) : Vector (A*B) m
      := fun i => (v1 i, v2 i).

    Definition matrix_zip {A B} {m n:nat} (mat1:Matrix A m n) (mat2:Matrix B m n) : Matrix (A*B) m n
      := let mat12:Vector (Vector A n*Vector B n) m := vector_zip mat1 mat2 in
         vmap (fun '(a,b) => vector_zip a b) mat12.
                                 
    Definition vector_split {A B} {m:nat} (v:Vector (A*B) m) : Vector A m * Vector B m
      := (fun i => fst (v i), fun i => snd (v i)).

    Program Definition vtake {A} {m:nat} (v:Vector (A) m) (n:nat) (pf:(n<=m)%nat) : Vector A n
      := fun i => v i.
    Next Obligation.
      omega.
    Defined.

    Definition vec_eq {A} {m:nat} (x y:Vector A m) := forall i, x i = y i.
    Notation "x =v= y" := (vec_eq x y) (at level 70).

    
    (* If we are willing to assume an axiom *)
    (*
    Lemma vec_eq_eq {A} {m:nat} (x y:Vector A m) : vec_eq x y -> x = y.
    Proof.
      Require Import FunctionalExtensionality.
      intros.
      apply functional_extensionality.
      apply H.
    Qed.
     *)

    Lemma index_pf_irrel n m pf1 pf2 : 
      exist (fun n' : nat => (n' < n)%nat) m pf1 =
      exist (fun n' : nat => (n' < n)%nat) m pf2.
      f_equal.
      apply digit_pf_irrel.
    Qed.
    
    Lemma vector_Sn_split {T} {n} (v:Vector T (S n)) :
      v =v= vcons (vlast v) (vdrop_last v).
    Proof.
      intros [i pf].
      unfold vcons, vlast, vdrop_last.
      destruct (Nat.eq_dec i n)
      ; subst
      ; f_equal
      ; apply index_pf_irrel.
    Qed.

    Lemma vector_split_zip {A B} {m:nat} (v:Vector (A*B) m) :
      let '(va,vb):=vector_split v in vector_zip va vb =v= v.
    Proof.
      simpl.
      intros i.
      vm_compute.
      now destruct (v i).
    Qed.

    Lemma split_vector_zip {A B} {m:nat} (va:Vector A m) (vb:Vector B m) :
      vector_split (vector_zip va vb) = (va,vb).
    Proof.
      vm_compute.
      f_equal.
    Qed.
    
End Vector.
