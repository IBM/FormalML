(*Require Import Morphisms.
Require Import Equivalence.
Require Import Program.Basics.
Require Import Classical.
Require Import FunctionalExtensionality.
Require Import IndefiniteDescription ClassicalDescription.

Require Import hilbert.

Require Export RandomVariableLpR.
Require Import quotient_space.
Require Import RbarExpectation.

Require Import Event.
Require Import AlmostEqual.
Require Import utils.Utils.
Require Import List.*)

Require Import Lra Lia Reals Coquelicot.Coquelicot.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".


Definition bounded (x : nat -> R) := exists c : R, forall n, Rabs (x n) <= c.

Lemma Series_ex_series (a : nat -> R) : ex_series a -> (exists c, Series a <= c).
Proof.
  intros H.
  destruct H as [c Hc].
  exists (1 + Series a).
  lra.
Qed.

Lemma ash_6_1_1_a {x : nat -> R}{a : nat -> nat -> R} (ha : forall j, is_lim_seq (fun n => a n j) 0)
      (hb : forall n, ex_series(fun j => Rabs(a n j)))
      (hx1 : bounded x) (hx2 : is_lim_seq x 0) :
  let y := fun n => Series (fun j => (a n j)*(x j)) in is_lim_seq y 0.
Proof.
  intros y. destruct hx1 as [M HMx].
  assert (hy1 : forall n j, Rabs (a n j * x j) <= M*Rabs(a n j)) by admit.
  assert (hy2 : forall n M, ex_series(fun j => M*Rabs(a n j)))
    by (intros; now apply (ex_series_scal_l) with (a0 := fun j => Rabs(a n j))).
  assert (hy3 : forall n, ex_series (fun j : nat => Rabs(a n j * x j))).
  {
    intros n.
    apply (ex_series_le (fun j => Rabs (a n j * x j)) (fun j => M*Rabs(a n j))); trivial.
    intros. rewrite Rabs_Rabsolu; auto.
  }
  assert (hy4 : forall n, ex_series (fun j : nat => a n j * x j))
    by (intro n; apply (ex_series_Rabs _ (hy3 n))).
  assert (hy5 : forall n N, ex_series (fun j => Rabs (a n (N + j)%nat * x (N + j)%nat)))
    by (intros; now rewrite <-ex_series_incr_n with (a0 := fun j => Rabs (a n j * x j))).
  assert (hy6 : forall n N, (0 < N)%nat -> Rabs(y n) <= sum_f_R0 (fun j => Rabs (a n j * x j)) (pred N)
                                               + Series (fun j => Rabs (a n (N + j)%nat * x (N +j)%nat)))
    by (intros; unfold y; eapply Rle_trans; try (apply Series_Rabs; trivial);
        right; apply Series_incr_n with (a := fun j => Rabs ( a n j * x j)); trivial).
  rewrite is_lim_seq_Reals; unfold Un_cv, R_dist; simpl.
  intros eps Heps.
  setoid_rewrite Rminus_0_r.

Admitted.

(*  assert (h : forall n, exists N:nat,
               Rabs(y n) <=
               sum_f_R0 (fun j => Rabs ( a n j )* Rabs(x j)) N +
               Series ((fun j => Rabs (a n (j+N+1)%nat )* Rabs( x (j + N + 1)%nat )))).
*)
