Require Import Reals.Rbase.
Require Import Reals.Rfunctions.
Require Import Ranalysis_reg.
Require Import Reals.Integration.
Require Import Rtrigo_def.
Require Import List Permutation.
Require Import Sorted.

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
  destruct (map_nth_in_exists (fun i : nat => a + INR i * ((b - a) / INR n)) (seq 0 (n + 1)) d nn).
  + rewrite seq_length.
    omega.
  + rewrite H0.
    rewrite seq_nth by omega.
    simpl.
    lra.
Qed.

Lemma Partition_func_increasing a b n:
  a < b ->
  (0 < n)%nat ->
  Morphisms.Proper (Morphisms.respectful lt Rlt) (fun i : nat => a + INR i * ((b - a) / INR n)).
Proof.
  repeat red; intros.
  apply Rplus_lt_compat_l.
  apply Rmult_lt_compat_r.
  - apply Rmult_lt_0_compat; trivial.
    + lra.
    + apply Rinv_pos.
      apply INR_zero_lt; trivial.
  - apply lt_INR; trivial.
Qed.

Lemma Partition_StronglySorted a b n :
  a < b ->
  (0 < n)%nat ->
  StronglySorted Rlt (Partition a b n).
Proof.
  intros.
  unfold Partition.
  apply (StronglySorted_map lt Rlt).
  - apply Partition_func_increasing; trivial.
  - apply StronglySorted_seq.
Qed.

Lemma Partition_length a b n : length (Partition a b n) = S n.
Proof.
  unfold Partition.
  rewrite map_length, seq_length.
  omega.
Qed.

Lemma find_bucket_nth_finds_Rle needle l idx d1 d2:
  StronglySorted Rle l ->
  (S idx < length l)%nat ->
  nth idx l d1 < needle ->
  needle < nth (S idx) l d2 ->
  find_bucket Rle_dec needle l = Some (nth idx l d1, nth (S idx) l d2).
Proof.
  intros.
  apply find_bucket_nth_finds; trivial
  ; repeat red; intros; lra.
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
  (n>0)%nat ->
  a <= b ->
  let rpl := iso_b (Partition a b n) in
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
    + left.
      apply Rinv_pos.
      apply INR_zero_lt; trivial.
    + lra.
Qed.

Lemma find_bucket_Partition a b n idx d1 d2 needle:
  (n > 0)%nat ->
  (idx < n)%nat ->
  a < b ->
  nth idx (Partition a b n) d1 < needle < nth (S idx) (Partition a b n) d2 ->
  find_bucket Rle_dec needle (Partition a b n) = Some (nth idx (Partition a b n) d1, nth (S idx) (Partition a b n) d2).
Proof.
  intros.
  apply find_bucket_nth_finds_Rle; trivial.
  - eapply StronglySorted_sub; [ | eapply Partition_StronglySorted ]; trivial.
    apply Rlt_le_sub.
  - rewrite Partition_length.
    omega.
  - tauto.
  - tauto.
Qed.
    
Definition find_pt_le f a b n needle : R
  := match find_bucket Rle_dec needle (Partition a b n) with
     | Some (lower,upper) => f upper
     | None => 0
     end.

Lemma part2step (f:R -> R) (a b:R) (n : nat) :
  (n > 0)%nat ->
  a < b ->
  IsStepFun (find_pt_le f a b n) a b.
Proof.
  intros.
  unfold IsStepFun.
  exists (iso_b (Partition a b n)).
  unfold is_subdivision.
  exists (iso_b (map f (tl (Partition a b n)))).
  unfold adapted_couple.
  destruct (orderedPartition a b n) as [? [??]]; trivial; try lra.
  repeat split; trivial.
  - rewrite Rmin_left; lra.
  - rewrite Rmax_right; lra.
  - autorewrite with R_iso.
    rewrite map_length, length_S_tl; trivial.
    apply Partition_nnil.
  - unfold constant_D_eq, open_interval.
    intros idx idxlt x openx.
    autorewrite with R_iso in *.
    rewrite Partition_length in idxlt.
    simpl in idxlt.
    unfold find_pt_le.
    erewrite find_bucket_Partition; try eapply openx; trivial.
    erewrite map_nth_in with (d2:=0). 
    + rewrite nth_tl; trivial.
    + rewrite tl_length, Partition_length.
      omega.
Qed.

Lemma Partition_p2 (f : R -> R) (a b x : R) (idx n : nat) :
  (n > 0)%nat ->
  (idx < n)%nat ->
  a < b ->
  nth idx (Partition a b n) 0 < x < nth (S idx) (Partition a b n) 0 ->
  R_dist x (nth (S idx) (Partition a b n) 0) <= R_dist (nth idx (Partition a b n) 0) (nth (S idx) (Partition a b n) 0).
Proof.
  intros.
  rewrite (R_dist_sym x).
  rewrite (R_dist_sym (nth idx (Partition a b n) 0)).
  unfold R_dist.
  repeat rewrite Rabs_pos_eq by lra.
  lra.
Qed.

(*

This can't be true without additional assumptions on f

Lemma Partition_p2 (f : R -> R) (a b x : R) (idx n : nat) :
  (n > 0)%nat ->
  (idx < n)%nat ->
  a < b ->
  nth idx (Partition a b n) 0 < x < nth (S idx) (Partition a b n) 0 ->
  R_dist (f x) (f (nth (S idx) (Partition a b n) 0)) <= R_dist (f (nth idx (Partition a b n) 0)) (f (nth (S idx) (Partition a b n) 0)).
Proof.
  intros.
*)