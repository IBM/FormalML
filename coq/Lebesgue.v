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

Lemma Partition_length a b n : length (Partition a b n) = S n.
Proof.
  unfold Partition.
  rewrite map_length, seq_length.
  omega.
Qed.

Lemma Partition_last a b n d :
  (0 < n)%nat ->
  last (Partition a b n) d = b.
Proof.
  intros npos.
  rewrite <- nth_last.
  rewrite Partition_length.
  simpl.
  rewrite Partition_nth by trivial.
  field_simplify.
  - lra.
  - apply INR_nzero; trivial.
Qed.

Lemma list_hd_last {A} (l:list A) d1 d2 :
  (length l > 1)%nat ->
  l = hd d1 l :: tl (removelast l) ++ (last l d2::nil).
Proof.
  intros.
  generalize (@app_removelast_last _ l d2); intros.
  destruct l; simpl; simpl in *.
  - omega.
  - destruct l; simpl in *.
    + omega.
    + intuition congruence.
Qed.  
  
Lemma Partition_unfold_hd_tl (a b : R) (n : nat) : 
  (n > 0)%nat ->
  Partition a b n =
  a::
  let inc := (b - a)/(INR n) in
  (map (fun i => a + (INR i)*inc) (seq 1 (n-1)))
    ++ (b::nil).
Proof.
  intros.
  rewrite (list_hd_last (Partition a b n) 0 0).
  - rewrite Partition_hd.
    rewrite Partition_last by trivial.
    simpl.
    repeat f_equal.
    unfold Partition.
    rewrite removelast_map, tl_map.
    rewrite removelast_seq, tl_seq.
    repeat f_equal.
    omega.
  - rewrite Partition_length.
    omega.
Qed.

Lemma Partition_func_shift_nonneg a b n i:
  a <= b ->
  (0 < n)%nat ->
  0 <= INR i * (b - a) / INR n.
Proof.
  intros.
  destruct i.
  - simpl.
    lra.
  - { destruct H.
      - left.
        apply Rmult_lt_0_compat; trivial.
        + apply Rmult_lt_0_compat; trivial.
          * apply INR_zero_lt.
            omega.
          * lra.
        + apply Rinv_pos.
          apply INR_zero_lt; trivial.
      - right.
        subst.
        lra.
    }
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

Lemma Partition_func_eq a n i :
  (0 < n)%nat ->  
  a + INR i * ((a - a) / INR n) = a.
Proof.
  replace (a-a) with 0 by lra.
  intros.
  field_simplify
  ; trivial
  ; try apply INR_nzero; trivial.
  unfold Rdiv.
  rewrite Rmult_assoc.
  rewrite Rinv_r by (apply INR_nzero; trivial).
  lra.
Qed.

Lemma Partition_func_nondecreasing a b n:
  a <= b ->
  (0 < n)%nat ->
  Morphisms.Proper (Morphisms.respectful lt Rle) (fun i : nat => a + INR i * ((b - a) / INR n)).
Proof.
  repeat red; intros.
  destruct H.
  - left.
    apply Partition_func_increasing; trivial.
  - subst.
    repeat rewrite Partition_func_eq by trivial.
    eauto.
Qed.

Lemma Partition_StronglySorted_lt a b n :
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

Lemma Partition_StronglySorted_le a b n :
  a <= b ->
  (0 < n)%nat ->
  StronglySorted Rle (Partition a b n).
Proof.
  intros.
  unfold Partition.
  apply (StronglySorted_map lt Rle).
  - apply Partition_func_nondecreasing; trivial.
  - apply StronglySorted_seq.
Qed.
                                       
Lemma Partition_nth_le a b n idx1 idx2 d1 d2:
  a <= b ->
  (0 < n)%nat ->
  (idx2 <= n)%nat ->
  (idx1 <= idx2)%nat ->
  nth idx1 (Partition a b n) d1 <= nth idx2 (Partition a b n) d2.
Proof.
  intros.
  apply StronglySorted_nth_le; trivial.
  - repeat red; intros; eauto.
  - apply Partition_StronglySorted_le; trivial.
  - rewrite Partition_length.
    omega.
Qed.

Lemma Partition_lower_bound a b n idx :
  (a <= b) ->
  (0 < n)%nat ->
  (idx <= n)%nat ->
  a <= nth idx (Partition a b n) 0.
Proof.
  intros H1 H2 H3.
  erewrite <- (Partition_hd a b n 0) at 1.
  rewrite <- nth_hd.
  apply Partition_nth_le; trivial.
  omega.
Qed.

Lemma Partition_upper_bound a b n idx :
  (a <= b) ->
  (0 < n)%nat ->
  (idx <= n)%nat ->
  nth idx (Partition a b n) 0 <= b.
Proof.
  intros H1 H2 H3.
  erewrite <- (Partition_last a b n 0) at 2 by omega.
  rewrite <- nth_last.
  rewrite Partition_length.
  simpl.
  apply Partition_nth_le; trivial.
Qed.

Lemma Partition_telescope f (a b : R) (n : nat) :
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
  a <= b ->
  nth idx (Partition a b n) d1 < needle <= nth (S idx) (Partition a b n) d2 ->
  find_bucket Rle_dec needle (Partition a b n) = Some (nth idx (Partition a b n) d1, nth (S idx) (Partition a b n) d2).
Proof.
  intros.
  apply find_bucket_nth_finds_Rle; trivial.
  - eapply Partition_StronglySorted_le; trivial.
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
  a <= b ->
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
    + omega.
    + destruct openx.
      split; eauto; lra.
Qed.

Lemma Partition_f_increasing (f : R -> R) (a b x : R) (idx n : nat) :
  (0 < n)%nat ->
  (idx < n)%nat ->
  a <= b ->
  interval_increasing f a b ->
  nth idx (Partition a b n) 0 <= x <= nth (S idx) (Partition a b n) 0 ->
  R_dist (f x) (f (nth (S idx) (Partition a b n) 0)) <= R_dist (f (nth idx (Partition a b n) 0)) (f (nth (S idx) (Partition a b n) 0)).
Proof.
  intros.
  apply bounded_increasing_dist_le; trivial.
  apply (subinterval_increasing f a b); trivial.
  - apply Partition_lower_bound; trivial; omega.
  - apply Partition_nth_le; trivial; omega.
  - apply Partition_upper_bound; trivial; omega.
Qed.


Lemma Partition_f_decreasing (f : R -> R) (a b x : R) (idx n : nat) :
  (0 < n)%nat ->
  (idx < n)%nat ->
  a <= b ->
  interval_decreasing f a b ->
  nth idx (Partition a b n) 0 <= x <= nth (S idx) (Partition a b n) 0 ->
  R_dist (f x) (f (nth (S idx) (Partition a b n) 0)) <= R_dist (f (nth idx (Partition a b n) 0)) (f (nth (S idx) (Partition a b n) 0)).
Proof.
  intros.
  apply bounded_decreasing_dist_le; trivial.
  apply (subinterval_decreasing f a b); trivial.
  - apply Partition_lower_bound; trivial; omega.
  - apply Partition_nth_le; trivial; omega.
  - apply Partition_upper_bound; trivial; omega.
Qed.

Definition find_pt_le_psi f a b n needle : R
  := match find_bucket Rle_dec needle (Partition a b n) with
     | Some (lower,upper) => f lower - f upper
     | None => 0
     end.

Definition list_map_diffs f (l : list R) : (list R) :=
  map (fun '(x, y) => x-y) (adjacent_pairs (map f l)).

Lemma list_map_diffs_length f l : length (list_map_diffs f l) = pred (length l).
Proof.
  unfold list_map_diffs.
  rewrite map_length, adjacent_pairs_length, map_length; trivial.
Qed.

Lemma list_map_diff_nth_in n f (l:list R) d d1 d2 :
  (S n < length l)%nat ->
  nth n (list_map_diffs f l) d = (f (nth n l d1) - f (nth (S n) l d2)).
Proof.
  intros.
  unfold list_map_diffs; simpl.
  erewrite map_nth_in.
  - rewrite adjacent_pairs_nth_in.
    + repeat erewrite map_nth_in by omega.
      reflexivity.
    + rewrite map_length; trivial.
  - rewrite adjacent_pairs_length, map_length.
    omega.

    Unshelve.
    exact d1.
    exact d2.
Qed.

Lemma part2step_psi (f:R -> R) (a b:R) (n : nat) :
  (n > 0)%nat ->
  a <= b ->
  IsStepFun (find_pt_le_psi f a b n) a b.
Proof.
  intros.
  unfold IsStepFun.
  exists (iso_b (Partition a b n)).
  unfold is_subdivision.
  exists (iso_b (list_map_diffs f (Partition a b n))).
  unfold adapted_couple.
  destruct (orderedPartition a b n) as [? [??]]; trivial; try lra.
  repeat split; trivial.
  - rewrite Rmin_left; lra.
  - rewrite Rmax_right; lra.
  - autorewrite with R_iso.
    rewrite list_map_diffs_length.
    rewrite Partition_length.
    simpl; trivial.
  - unfold constant_D_eq, open_interval.
    intros idx idxlt.
    intros.
    autorewrite with R_iso in *.
    rewrite Partition_length in idxlt.
    simpl in idxlt.
    unfold find_pt_le_psi.
    erewrite find_bucket_Partition; try eapply H4; trivial.
    erewrite list_map_diff_nth_in.
    + reflexivity.
    + rewrite Partition_length.
      omega.
    + trivial.
    + destruct H4; split; intros; eauto.
      left; eauto.
Defined.

Lemma adjacent_pairs_Partition a b n :
  adjacent_pairs (Partition a b n) =
  let inc := (b - a)/(INR n) in
  map (fun i => (a + (INR i)*inc, a + (INR (i+1))*inc)) (seq 0 n).
Proof.
  intros.
  unfold Partition.
  rewrite adjacent_pairs_map.
  rewrite adjacent_pairs_seq.
  rewrite map_map.
  replace (n+1)%nat with (S n) by omega.
  simpl pred.
  apply map_ext; intros.
  replace (a0+1)%nat with (S a0) by omega.
  trivial.
Qed.

Lemma RiemannInt_SF_psi (f: R -> R) (a b:R) (n: nat) :
  forall (npos: (n > 0)%nat) (aleb: (a <= b)),
    RiemannInt_SF (mkStepFun (part2step_psi f a b n npos aleb)) = (f(a)-f(b))*(b-a)/(INR n).
Proof.
  intros npos aleb.
  unfold RiemannInt_SF.
  destruct (Rle_dec a b); [ | tauto].
  unfold subdivision_val, subdivision.
  simpl.
  rewrite Int_SF'_eq.
  rewrite Int_SF'_alt_eq.
  unfold Int_SF'_alt.
  unfold list_map_diffs.
  rewrite combine_map.
  rewrite adjacent_pairs_map.
  rewrite <- (map_id (adjacent_pairs (Partition a b n))) at 2.
  rewrite combine_map.
  rewrite combine_self.
  repeat rewrite map_map.
  rewrite adjacent_pairs_Partition.
  simpl.
  repeat rewrite map_map.

  rewrite (map_ext
             (fun x : nat =>
                (f (a + INR x * ((b - a) / INR n)) - f (a + INR (x + 1) * ((b - a) / INR n))) *
                (a + INR (x + 1) * ((b - a) / INR n) - (a + INR x * ((b - a) / INR n))))
  (fun x : nat =>
                (f (a + INR x * ((b - a) / INR n)) - f (a + INR (x + 1) * ((b - a) / INR n))) *
                (((b - a) / INR n)))).
  - rewrite fold_right_Rplus_mult_const.
    rewrite (telescope_plus_fold_right_sub_seq (fun x => (f(a + x * ((b - a) / INR n)))) 0 n) by trivial.
    simpl.
    replace (a + 0 * ((b - a) / INR n)) with a by lra.
    replace (a + INR n * ((b - a) / INR n)) with b.
    + lra.
    + unfold Rdiv.
      rewrite <- Rmult_comm.
      rewrite Rmult_assoc.
      rewrite Rinv_l.
      * lra.
      * apply INR_nzero; trivial.
  - intros.
    f_equal.
    replace (a0 + 1)%nat with (S a0) by omega.
    rewrite S_INR.
    field_simplify; trivial
    ; try apply INR_nzero; trivial.
Qed.


Lemma find_bucket_Partition_exists a b n needle:
  (n > 0)%nat ->
  a <= needle <= b ->
  exists lower upper,
    find_bucket Rle_dec needle (Partition a b n) = Some (lower, upper).
Proof.
  intros npos ineqs.
  rewrite (Partition_unfold_hd_tl a b n npos).
  apply find_bucket_bounded_Rle_exists; trivial.
Qed.
            
Lemma StepBounded (f : R -> R) (a b : R) (n : nat) :
  forall (npos: (n > 0)%nat) (aleb: (a <= b)),
    interval_decreasing f a b ->
    let phi := mkStepFun (part2step f a b n npos aleb) in
    let psi := mkStepFun (part2step_psi f a b n npos aleb) in
    (forall t:R,
        a <= t <= b -> Rabs (f t - phi t) <= psi t).
Proof.
  simpl; intros.
  unfold find_pt_le, find_pt_le_psi.
  destruct (find_bucket_Partition_exists a b n t npos H0)
    as [lower [upper eqq]].
  rewrite eqq.

  destruct (find_bucket_bucket_in Rle_dec t (Partition a b n) lower upper 0 0)
  as [r1 r2]; trivial.
  - red; intros; lra.
  - apply Partition_StronglySorted_le; trivial.
  - rewrite Partition_hd in r1.
    rewrite Partition_last in r2 by trivial.
    destruct (find_bucket_needle_in Rle_dec t (Partition a b n) lower upper)
             as [r3 r4]; trivial.
  rewrite Rabs_pos_eq.
    + unfold Rminus.
      apply Rplus_le_compat_r.
      apply H; lra.
    + cut (f upper <= f t); [intros; lra | ].
      apply H; lra.
Qed.

Lemma natp1gz (n : nat) : (n+1 > 0)%nat.
Proof.
  omega.
Qed.

Lemma INR_up_over_cancel r (epsilon:posreal) :
  r <> 0 ->
  Rabs (r / INR (Z.to_nat (up (Rabs r / epsilon)) + 1)) < epsilon.
Proof.
  intros.
  destruct epsilon as [epsilon pf].
  rewrite INR_IZR_INZ.
  rewrite Nat.add_1_r.
  simpl.
  rewrite Zpos_P_of_succ_nat.
  assert (repos:Rabs r / epsilon > 0).
  { apply Rdiv_lt_0_compat; try lra.
    apply Rabs_pos_lt; trivial.
  }
  destruct (archimed (Rabs r / epsilon)) as [lb ub].
  assert (izrpos: 0 < IZR (up (Rabs r / epsilon))).
  { lra. }
  rewrite Z2Nat.id.
  - rewrite succ_IZR.
    apply (Rmult_gt_compat_r epsilon) in lb; trivial.
    { replace ( Rabs r / epsilon * epsilon) with (Rabs r) in lb.
      - apply (Rmult_gt_compat_l (/ IZR (up (Rabs r / epsilon)))) in lb; trivial.
        + repeat rewrite <- Rmult_assoc in lb.
          rewrite <- Rinv_l_sym in lb by lra.
          rewrite Rmult_1_l in lb.
          rewrite Rmult_comm in lb.
          eapply Rlt_trans; try eapply lb.
          unfold Rdiv.
          rewrite Rabs_mult.
          { apply Rmult_lt_compat_l; trivial.
            - apply Rabs_pos_lt; trivial.
            - rewrite Rabs_Rinv by lra.
              rewrite Rabs_pos_eq at 1.
              + apply Rinv_lt_contravar.
                * apply Rmult_lt_0_compat; try lra.
                * lra.
              + lra.
          }
        + apply Rinv_pos.
          lra.
      - unfold Rdiv.
        rewrite Rmult_assoc.
        rewrite <- Rinv_l_sym; lra.
    } 
  - apply le_IZR.
    lra.
Qed.
                                             
Lemma RiemannInt_SF_psi_limit (f: R -> R) (a b:R) :
 forall (aleb: (a <= b)) (epsilon : posreal),
   {n:nat | 
    Rabs (RiemannInt_SF (mkStepFun (part2step_psi f a b (n+1)%nat (natp1gz n) aleb))) < epsilon}.
Proof.
  intros aleb epsilon.
  destruct (Rlt_dec a b).
  - destruct (Req_EM_T (f a) (f b)).
    + exists (0)%nat.
      rewrite RiemannInt_SF_psi.
      assert (f a = f b) by lra.
      rewrite H.
      replace (f b - f b) with 0 by lra.
      unfold Rdiv.
      repeat rewrite Rmult_0_l.
      rewrite Rabs_R0.
      destruct epsilon; trivial.
    + exists (Z.to_nat (up (Rabs ((f(a)-f(b))*(b-a))/epsilon))).
      rewrite RiemannInt_SF_psi.
      apply INR_up_over_cancel.
      intros eqq.
      apply Rmult_integral in eqq.
      intuition lra.
  - exists (0)%nat.
    rewrite RiemannInt_SF_psi.
    assert (a = b) by lra.
    rewrite H.
    replace (b-b) with 0 by lra.
    rewrite Rmult_0_r.
    unfold Rdiv.
    rewrite Rmult_0_l.
    rewrite Rabs_R0.
    destruct epsilon; trivial.
Qed.

Theorem RiemannInt_decreasing (f: R -> R) (a b:R) :
  a <= b ->
  interval_decreasing f a b ->
  Riemann_integrable f a b.
Proof.
  intros aleb fdecr.
  red; intros epsilon.
  destruct (RiemannInt_SF_psi_limit f a b aleb epsilon)
  as [n npf].
  exists (mkStepFun (part2step f a b (n+1) (natp1gz n) aleb)).
  exists (mkStepFun (part2step_psi f a b (n+1) (natp1gz n) aleb)).
  split; intros.
  - rewrite Rmin_left in H by lra.
    rewrite Rmax_right in H by lra.
    apply StepBounded; trivial.
  - apply npf.
Qed.
