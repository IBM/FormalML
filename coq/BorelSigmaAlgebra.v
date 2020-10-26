Require Import ProbSpace SigmaAlgebras.
Require Import Reals.
Require Import Lra Lia.

(* specialized for R *)

Instance open_borel_sa : SigmaAlgebra R
  := generated_sa open_set.

Instance borel_sa : SigmaAlgebra R
  := generated_sa (fun (s:R->Prop) => exists r, forall m, m <= r <-> s m)%R.

Section Borel.

Local Open Scope R.

Context {Ts:Type}
        {dom : SigmaAlgebra Ts}.

Lemma borel_sa_preimage
      (rvx: Ts -> R)
      (pf_pre: forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) :
  (forall B: event R, sa_sigma B -> sa_sigma (event_preimage rvx B)).
Proof.
Admitted.


Lemma borel_sa_preimage2 
      (rvx: Ts -> R):
  (forall r:R, sa_sigma (fun omega:Ts => (rvx omega) <= r)%R) <-> 
  (forall B: event R, sa_sigma B -> (sa_sigma (event_preimage rvx B))).
Proof.
  split; intros.
  - now apply borel_sa_preimage.
  - unfold event_preimage in *.
    simpl in H.
    apply (H (fun x => x <= r)%R).
    apply generated_sa_sub.
    exists r; intuition.
Qed.

  Lemma equiv_le_lt (f : Ts -> R) (r:R) :
    event_equiv (fun omega : Ts => f omega < r)
                (union_of_collection
                   (fun (n:nat) => (fun omega : Ts => f omega <= r - / (1 + INR n)))).
  Proof.
    unfold event_equiv, union_of_collection.
    intros.
    split ; intros.
    + generalize (archimed_cor1 (r - f x)) ; intros.
      assert (r - f x > 0) by lra. specialize (H0 H1).
      clear H1.
      destruct H0 as [N [HNf HN]].
      exists N. left.
      replace (1 + INR N) with (INR (S N)) by (apply S_O_plus_INR).
      assert (f x < r - / INR N) by lra.
      eapply Rlt_trans ; eauto.
      unfold Rminus.
      apply Rplus_lt_compat_l. apply Ropp_lt_contravar.
      apply Rinv_lt_contravar.
      rewrite <-mult_INR. apply lt_0_INR ; lia.
      apply lt_INR ; lia.
    + destruct H.
      assert (0 < / INR (S x0)).
      apply Rinv_0_lt_compat.
      apply  lt_0_INR; lia.
      replace (1 + INR x0) with (INR (S x0)) in H by (apply S_O_plus_INR).
      lra.
  Qed.

  Lemma sa_le_gt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega > r)).
  Proof. 
    intros.
    assert (event_equiv (fun omega : Ts => f omega > r)
                        (event_complement (fun omega : Ts => f omega <= r))).
    - intro x.
      unfold event_complement.
      split; intros; lra.
    - rewrite H0.
      now apply sa_complement.
  Qed.

  Lemma sa_le_ge (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega >= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega >= r)
                        (event_complement (fun omega : Ts => f omega < r))).
    {
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

  Lemma sa_le_lt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega < r)).
  Proof. 
    intros.
    assert (event_equiv (fun omega : Ts => f omega < r)
                        (event_complement (fun omega : Ts => f omega >= r))).
    - intro x.
      unfold event_complement.
      split; intros; lra.
    - rewrite H0.
      apply sa_complement.
      now apply sa_le_ge.
  Qed.

  Lemma sa_closed_intervals (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (l r:R), sa_sigma (fun omega : Ts => l <= f omega <= r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => l <= f omega <= r) 
                        (event_inter (fun omega : Ts => l <= f omega) 
                                     (fun omega : Ts => f omega <= r))).
    now unfold event_equiv, event_inter.
    rewrite H0.
    apply sa_inter; trivial.
    assert (event_equiv (fun omega : Ts => l <= f omega)
                        (fun omega : Ts => f omega >= l)).
    red; intros; intuition.
    rewrite H1.
    now apply sa_le_ge.
  Qed.

  Lemma sa_open_intervals (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (l r:R), sa_sigma (fun omega : Ts => l < f omega < r)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => l < f omega < r) 
                        (event_inter (fun omega : Ts => l < f omega) 
                                     (fun omega : Ts => f omega < r))).
    now unfold event_equiv, event_inter.
    rewrite H0.
    apply sa_inter; trivial.
    assert (event_equiv (fun omega : Ts => l < f omega)
                        (fun omega : Ts => f omega > l)).
    red; intros; intuition.
    rewrite H1.
    now apply sa_le_gt.
    now apply sa_le_lt.
  Qed.

  Lemma sa_le_pt (f : Ts -> R) :
    (forall (r:R),  sa_sigma (fun omega : Ts => f omega <= r)) ->
    (forall (pt:R), sa_sigma (fun omega : Ts => f omega = pt)).
  Proof.
    intros.
    assert (event_equiv (fun omega : Ts => f omega = pt)
                        (event_inter (fun omega : Ts => f omega <= pt)
                                     (fun omega : Ts => f omega >= pt))).
    - unfold event_equiv, event_inter; intros.
      intuition.
    - rewrite H0.
      apply sa_inter; trivial.
      now apply sa_le_ge.
  Qed.

 End Borel.
