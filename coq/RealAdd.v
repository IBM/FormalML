Require Import Coq.Reals.Rbase.
Require Import Coq.Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List.
Require Import EquivDec Nat Omega Lra.

Require Import BasicTactics ListAdd.
Require Import Isomorphism.

Import ListNotations.

Local Open Scope R.


Lemma INR_nzero {n} :
  (n > 0)%nat -> INR n <> 0.
Proof.
  destruct n.
  - omega.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma INR_zero_lt {n} :
  (n > 0)%nat -> 0 < INR n.
Proof.
  destruct n.
  - omega.
  - rewrite S_INR.
    generalize (pos_INR n); intros.
    lra.
Qed.

Lemma Rinv_pos n :
  0 < n ->
  0 < / n.
Proof.
  intros.
  rewrite <- (Rmult_1_l ( / n)).
  apply Rdiv_lt_0_compat; lra.
Qed.

Lemma pos_Rl_nth (l:list R) n : pos_Rl (iso_b l) n = nth n l 0.
Proof.
  revert n.
  induction l; destruct n; simpl in *; trivial.
Qed.

Lemma Rlength_length (l:list R) : Rlength (iso_b l) = length l.
Proof.
  induction l; simpl in *; trivial.
  rewrite IHl; trivial.
Qed.

Hint Rewrite pos_Rl_nth Rlength_length : R_iso.

