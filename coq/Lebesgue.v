Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List Permutation.

Require Import Lra Omega.
Require Import BasicTactics Sums ListAdd RealAdd.
Require Import Isomorphism.


Local Open Scope R_scope.
Implicit Type f : R -> R.

Definition Partition (a b : R) (n : nat) : (list R) :=
  let inc := (b - a)/(INR n) in
  map (fun i => a + (INR i)*inc) (seq 0 (n+1)).


Lemma Partition_hd a b n d : hd d (Partition a b n) = a.
Proof.
  destruct n; simpl; lra.
Qed.

Lemma Partition_nnil a b n : Partition a b n <> nil.
Proof.
  unfold Partition.
  destruct n; simpl; congruence.
Qed.

Lemma Partition_nth a b n d nn : 
  (nn <= n)%nat ->
  nth nn (Partition a b n) d = a + (INR nn)*(b - a)/(INR n).
Proof.
  intros.
  unfold Partition.
  destruct (map_nth_in (fun i : nat => a + INR i * ((b - a) / INR n)) (seq 0 (n + 1)) d nn).
  + rewrite seq_length.
    omega.
  + rewrite H0.
    rewrite seq_nth by omega.
    simpl.
    lra.
Qed.

Lemma Partition_length a b n : length (Partition a b n) = S n.
Proof.
  unfold Partition.
  rewrite map_length, seq_length.
  omega.
Qed.

Lemma telescope f (a b : R) (n : nat) :
  (n > 0)%nat ->
  let pl := map f (Partition a b n) in
  (fold_right Rplus 0 (removelast pl)) - (fold_right Rplus 0 (tl pl)) =
  f(a) - f(b).
Proof.
  (* strategy: 
     A) show that we are mapping over 1..n+1 and 0..n . 
     B) Then reorder the folds to run over (n+1),1..n and 0,1..n .
     C) since the tail parts of the fold are the same, we just need to reduce the first
     elements and show the desired results
   *)

  (* A *)
  intros nzero.
  simpl.
  unfold Partition.
  repeat rewrite removelast_map, tl_map.
  rewrite removelast_seq, tl_seq.
  replace ((n + 1 - 1)%nat) with n by omega.

  (* B *)
  destruct n ; [ omega | ].
  replace (seq 0 (S n)) with (0%nat :: seq 1 n) by reflexivity.
  rewrite seq_Sn.
  match goal with
  | [|- context [fold_right ?f ?init (map ?f1 (map ?f2 (seq 1 n ++ ((1 + n)%nat::nil))))] ] =>
    replace (fold_right f init (map f1 (map f2 (seq 1 n ++ ((1 + n)%nat::nil)))))
      with (fold_right f init (map f1 (map f2 ((1 + n)%nat :: seq 1 n))))
  end.
  + (* C *)
    repeat rewrite map_cons.
    Opaque INR.
    simpl.
    field_simplify.
    Transparent INR.
    repeat f_equal.
    * simpl; lra.
    * apply INR_nzero in nzero.
      rewrite (Rmult_comm (INR (S n))).
      unfold Rdiv.
      rewrite Rmult_assoc.
      rewrite <- Rinv_l_sym; trivial.
      lra.
  + apply fold_right_perm.
    * intros; lra.
    * intros; lra.
    * apply Permutation_map.
      rewrite Permutation_app_comm.
      trivial.
Qed.

Lemma orderedPartition (a b : R) (n:nat)  :
 (n>0)%nat -> a <= b -> let rpl := iso_b (Partition a b n) in
           pos_Rl rpl 0 = a /\
           pos_Rl rpl (pred (Rlength rpl)) = b /\
           ordered_Rlist rpl.
Proof.
  intros.
  unfold rpl.
  autorewrite with R_iso.
  rewrite Partition_length.
  repeat rewrite Partition_nth by omega.
  split; [| split].
  - destruct n.
    + omega.
    + rewrite S_INR; simpl; lra.
  - simpl.
    field_simplify; [lra | ].
    apply INR_nzero; trivial.
  - intros i ilt.
    autorewrite with R_iso in *.
    rewrite Partition_length in ilt.
    repeat rewrite Partition_nth by omega.
    rewrite S_INR.
    apply Rplus_le_compat_l.
    apply Rmult_le_compat_r.
    + rewrite <- (Rmult_1_l (/ INR n)).
      left.
      apply Fourier_util.Rlt_mult_inv_pos.
      * lra.
      * { destruct n.
          - omega.
          - apply INR_zero_lt; trivial.
        }
    + lra.
Qed.
