Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms.
Require Import Sums.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".


Definition bounded (x : nat -> R) := exists c : R, forall n, Rabs (x n) <= c.

Lemma fin_seq_bounded (x : nat -> R) (N : nat) :
  exists (c : R),
    forall (n:nat), (n<N)%nat -> Rabs(x n) <= c.
 Proof.
 Admitted.

Lemma is_lim_seq0_bounded (x : nat -> R): is_lim_seq x 0 -> bounded x.
Proof.
  intros Hx.
  rewrite <- is_lim_seq_spec in Hx.
  unfold is_lim_seq' in Hx.
  unfold bounded.
  destruct (Hx posreal_one).
  destruct (fin_seq_bounded x x0).
  exists (Rmax x1 1); intros.
  destruct (lt_dec n x0).
  - eapply Rle_trans.
    + apply H0; lia.
    + apply Rmax_l.
  - left.
    eapply Rlt_le_trans.
    + specialize (H n).
      rewrite Rminus_0_r in H.
      apply H; lia.
    + apply Rmax_r.
  Qed.

Lemma sum_f_R0_Rabs_pos (x : nat -> R) : forall N, 0 <= sum_f_R0 (fun j => Rabs (x j)) N.
Proof.
  intros N.
  rewrite sum_f_R0_sum_f_R0'.
  apply sum_f_R0'_le.
  intros. apply Rabs_pos.
Qed.

Lemma sum_f_R0_nonneg_le_Series {x : nat -> R}(hx1 : ex_series x) (hx2 : forall n, 0 <= x n) :
  forall N, sum_f_R0 x N <= Series x.
Proof.
  intros N.
  unfold Series.
  rewrite <-sum_n_Reals.
  apply is_lim_seq_incr_compare.
  + apply Lim_seq_correct'.
    now rewrite ex_finite_lim_series.
  + intros n.
    apply sum_n_pos_incr; try lia; intros; auto.
Qed.

Lemma is_lim_seq_sum_f_R0 { a : nat -> nat -> R } (ha : forall j, is_lim_seq (fun n => a n j) 0):
  forall N, is_lim_seq (fun n => sum_f_R0 (fun j => a n j) N) 0.
Proof.
  intros N.
  induction N; simpl; eauto.
  apply is_lim_seq_plus with (l1 := 0) (l2 := 0); eauto.
  unfold is_Rbar_plus. simpl.
  f_equal. rewrite Rbar_finite_eq; lra.
Qed.

Lemma Series_shift_le {a : nat -> R} (ha : forall n, 0 <= a n) (he : ex_series a)
  : forall N, Series (fun j => a (N + j)%nat) <= Series a.
Proof.
  intros N.
  destruct (Nat.eq_decidable N 0); subst.
  + right. apply Series_ext; intros. f_equal.
  + rewrite Series_incr_n with (a := a) (n := N); try (now apply ex_series_incr_n); intuition.
    rewrite Rplus_comm. apply Rplus_le_pos_l.
    apply cond_pos_sum; auto.
Qed.

(*TODO(Kody) : Strengthen by using partial sums bounded instead of hb1 and hb2. *)
Lemma ash_6_1_1_a {x : nat -> R}{a : nat -> nat -> R} (ha : forall j, is_lim_seq (fun n => (a n j)) 0)
      (hb1 : forall n, ex_series(fun j => Rabs(a n j)))
      (hb2 : exists c, forall n, Series (fun j => Rabs (a n j)) < c)
      (hx1 : bounded x) (hx2 : is_lim_seq x 0) :
  let y := fun n => Series (fun j => (a n j)*(x j)) in is_lim_seq y 0.
Proof.
  intros y. destruct hx1 as [M HMx].
  destruct hb2 as [c Hc].
 assert (hy1 : forall n j, Rabs (a n j * x j) <= M*Rabs(a n j))
    by (intros ; rewrite Rabs_mult, Rmult_comm ;
        apply Rmult_le_compat_r; auto; apply Rabs_pos).
  assert (hy2 : forall n M, ex_series(fun j => M*Rabs(a n j)))
    by (intros; now apply (ex_series_scal_l) with (a0 := fun j => Rabs(a n j))).
  assert (hy3 : forall n, ex_series (fun j : nat => Rabs(a n j * x j))).
  {
    intros n.
    apply (ex_series_le (fun j => Rabs (a n j * x j)) (fun j => M*Rabs(a n j))); trivial.
    intros. rewrite Rabs_Rabsolu; auto.
  }
  assert (hy6 : forall n N, (0 < N)%nat -> Rabs(y n) <= sum_f_R0 (fun j => Rabs (a n j * x j)) (pred N)
                                               + Series (fun j => Rabs (a n (N + j)%nat * x (N +j)%nat)))
    by (intros; unfold y; eapply Rle_trans; try (apply Series_Rabs; trivial);
        right; apply Series_incr_n with (a := fun j => Rabs ( a n j * x j)); trivial).
  rewrite is_lim_seq_Reals; unfold Un_cv, R_dist; simpl.
  intros eps Heps.
  setoid_rewrite Rminus_0_r.
  assert (Hcc : c > 0).
  {
    specialize (Hc 0%nat). eapply Rle_lt_trans; try (apply Hc).
    eapply Rle_trans; try (apply sum_f_R0_nonneg_le_Series; eauto).
    + apply sum_f_R0_Rabs_pos. Unshelve. exact 0%nat.
    + intros; apply Rabs_pos.
  }
  assert (hy7 : exists N, forall j, (j >= N)%nat -> Rabs(x j) < eps/(2*c)).
  {
    rewrite is_lim_seq_Reals in hx2.
    assert (Heps' : eps/(2*c) > 0).
    {
      apply Rlt_gt. apply RIneq.Rdiv_lt_0_compat;lra.
    }
    specialize (hx2 (eps/(2*c)) Heps'). unfold R_dist in hx2.
    setoid_rewrite Rminus_0_r in hx2. exact hx2.
  }
  assert (hy8 : forall N, is_lim_seq (fun n => sum_f_R0 (fun j => Rabs (a n j * x j)) N) 0).
  { intros N.
    apply (is_lim_seq_le_le (fun _ => 0) _ (fun n => M*sum_f_R0 (fun j => Rabs(a n j)) N)).
    - intros n.
      split ; try (apply sum_f_R0_Rabs_pos).
      rewrite <-sum_f_R0_mult_const.
      apply sum_f_R0_le; intros.
      rewrite Rmult_comm.
      rewrite Rabs_mult.
      apply Rmult_le_compat_r; auto; try (apply Rabs_pos).
    - apply is_lim_seq_const.
    - replace (0:Rbar) with (Rbar_mult M 0) by (apply Rbar_mult_0_r).
      apply is_lim_seq_scal_l.
      apply is_lim_seq_sum_f_R0; intros; auto.
      replace 0 with (Rabs 0) by (apply Rabs_R0).
      apply is_lim_seq_continuous; auto.
      rewrite continuity_pt_filterlim; apply (continuous_Rabs 0).
  }
  setoid_rewrite is_lim_seq_Reals in hy8.
  destruct hy7 as [N0 HN0].
  assert (Heps' : eps/2 > 0) by (apply RIneq.Rdiv_lt_0_compat;lra).
  specialize (hy8 (N0) (eps/2) Heps').
  unfold R_dist in hy8. setoid_rewrite Rminus_0_r in hy8.
  destruct hy8 as [N1 HN1].
  exists N1; intros. specialize (hy6 n (N0 + 1)%nat).
  eapply Rle_lt_trans; try (apply hy6).
  ** lia.
  ** replace (eps) with ((eps/2) + c*(eps/(2*c))) by (field;lra).
     apply Rplus_le_lt_compat.
  -- replace (Init.Nat.pred (N0 + 1)) with N0 by lia.
     eapply Rle_trans; try (apply Rle_abs); left; eauto.
  -- assert
       (hy7 : Series (fun j => Rabs (a n (N0 + 1 + j)%nat * x(N0 + 1 + j)%nat))
       <= Series(fun j => (eps/(2*c))*Rabs (a n (N0+1+j)%nat))).
     {
       apply Series_le; intros.
       + split; try (apply Rabs_pos).
         rewrite Rabs_mult, Rmult_comm.
         apply Rmult_le_compat_r; try(apply Rabs_pos).
         left. apply HN0; lia.
       + apply (ex_series_scal_l) with (c0 := eps/(2*c))(a0 := fun j => Rabs(a n (N0+1+j)%nat)).
         now rewrite <-(ex_series_incr_n) with (n0 := (N0 + 1)%nat)(a0:=fun j => Rabs (a n j)).
     }
  eapply Rle_lt_trans; eauto.
  rewrite Series_scal_l. rewrite Rmult_comm.
  apply Rmult_lt_compat_r; eauto; try(apply RIneq.Rdiv_lt_0_compat;lra).
  generalize (Series_shift_le (fun n0 => Rabs_pos _) (hb1 n) (N0 + 1)); intros.
  eapply Rle_lt_trans; eauto.
Qed.

Global Instance Series_proper :
  Proper (pointwise_relation _ eq  ==> eq) (Series).
Proof.
  unfold Proper, pointwise_relation, respectful.
  apply Series_ext.
Qed.

Global Instance is_lim_seq_proper:
  Proper (pointwise_relation _ eq ==> eq ==> iff) (is_lim_seq).
Proof.
  unfold Proper, pointwise_relation, respectful.
  intros.
  split; subst; apply is_lim_seq_ext; eauto.
Qed.

Lemma is_lim_seq_sub_zero (x : nat -> R) (x0 : R) :
  is_lim_seq x x0 <-> is_lim_seq (fun j => x j - x0) 0.
Proof.
  split; intros.
  + rewrite is_lim_seq_Reals in *.
    unfold Un_cv,R_dist. now setoid_rewrite Rminus_0_r.
  + rewrite is_lim_seq_Reals in *.
    unfold Un_cv, R_dist in H. now setoid_rewrite Rminus_0_r in H.
Qed.

Lemma ash_6_1_1_b {x : nat -> R}{a : nat -> nat -> R} (ha1 : forall j, is_lim_seq (fun n => (a n j)) 0)
      (hb1 : forall n, ex_series(fun j => Rabs(a n j)))
      (hb2 : exists c, forall n, Series (fun j => Rabs (a n j)) < c)
      (hx1 : bounded x) (x0 : R) (hx2 : is_lim_seq x x0)
      (ha2 : is_lim_seq (fun n => Series (fun j => a n j)) 1) :
    let y := fun n => Series (fun j => (a n j)*(x j)) in is_lim_seq y x0.
Proof.
  intros y. unfold y.
  assert (hxx : is_lim_seq (fun j => x j - x0) 0).
  {
    replace 0 with (x0 - x0) by lra.
    apply is_lim_seq_minus'; auto.
    apply is_lim_seq_const.
  }
  generalize (ash_6_1_1_a ha1 hb1 hb2 (is_lim_seq0_bounded _ hxx) hxx); intros.
  unfold y in H.
  setoid_rewrite Rmult_minus_distr_l in H.
  replace x0 with (1*x0) by lra.
  rewrite is_lim_seq_sub_zero.
Admitted.
