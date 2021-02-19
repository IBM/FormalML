Require Import List Lia.
Require Import Eqdep_dec.
Require Import LibUtils.
        
Import ListNotations.

Definition vector (T:Type) (n:nat)
  := { l : list T | length l = n}.

Lemma length_pf_irrel {T} {n:nat} {l:list T} (pf1 pf2:length l = n) : pf1 = pf2.
Proof.
  apply UIP_dec.
  apply PeanoNat.Nat.eq_dec.
Qed.

Lemma vector_pf_irrel {T:Type} {n:nat} {l:list T} pf1 pf2
  : exist (fun x=>length x = n) l pf1 = exist _ l pf2.
Proof.
  f_equal.
  apply length_pf_irrel.
Qed.

Lemma vector_ext {T:Type} {n:nat} {l1 l2:list T} pf1 pf2
  : l1 = l2 ->
    exist (fun x=>length x = n) l1 pf1 = exist _ l2 pf2.
Proof.
  intros; subst.
  apply vector_pf_irrel.
Qed.

Lemma vector_eq {T} {n:nat} (x y:vector T n)
  : proj1_sig x = proj1_sig y -> x = y.
Proof.
  destruct x; destruct y; simpl.
  apply vector_ext.
Qed.

Lemma vector_eqs {T} {n:nat} (x y:vector T n)
  : Forall2 eq (proj1_sig x) (proj1_sig y) -> x = y.
Proof.
  destruct x; destruct y; simpl.
  intros eqq.
  apply vector_ext.
  now apply Forall2_eq.
Qed.

Program Lemma vector_length {T:Type} {n:nat} (v:vector T n)
  : length v = n.
Proof.
  now destruct v; simpl.
Qed.

Program Fixpoint vector_create
           {T:Type}
           (n:nat)
           (f:forall m, (m < n)%nat -> T) : vector T n
  := match n with
     | 0 => []
     | S m => f m _ :: vector_create m (fun x pf => f x _)
     end.

Definition vector_const {T} (c:T) n : vector T n
  := vector_create n (fun _ _ => c).


Program Lemma vector_const_Forall {A} (c:A) n : Forall (fun a => a = c) (vector_const c n).
Proof.
  induction n; simpl; auto.
Qed.

Program Definition vector_nth
        {T:Type}
        {n:nat}
        (i:nat)
        (pf:(i<n)%nat)
        (v:vector T n)
        : T
  := match nth_error v i with
     | Some x => x
     | None => _
     end.
Next Obligation.
  symmetry in Heq_anonymous.
  apply nth_error_None in Heq_anonymous.
  rewrite vector_length in Heq_anonymous.
  lia.
Qed.

Program Definition vector_map {A B:Type}
           {n:nat} (f:A->B) (v:vector A n) : vector B n
  := map f v.
Next Obligation.
  rewrite map_length.
  now destruct v; simpl.
Qed.

Program Definition vector_zip {A B:Type}
           {n:nat} (v1:vector A n) (v2:vector B n) : vector (A*B) n
  := combine v1 v2.
Next Obligation.
  rewrite combine_length.
  repeat rewrite vector_length.
  now rewrite Min.min_idempotent.
Qed.

Program Definition vector_fold_left {A B:Type} (f:A->B->A)
           {n:nat} (v:vector B n) (a0:A) : A
  := fold_left f v a0.

