Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms Finite.
Require Import Sums.
Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".


Definition bounded (x : nat -> R) := exists c : R, forall n, Rabs (x n) <= c.

Definition restrict (x : nat -> R) (N : nat) : {a : nat | (a < N)%nat} -> R :=
  fun H => let (H0,_) := H in x H0.

Lemma fin_seq_bounded (x : nat -> R) (N : nat) :
  exists (c : R),
    forall (n:nat), (n<N)%nat -> Rabs(x n) <= c.
Proof.
  generalize (bounded_nat_finite N); intros Hn.
  generalize (fin_fun_bounded_Rabs Hn (restrict x N)); intros.
  destruct H as [c Hc]. exists c; intros.
  now specialize (Hc (exist _ n H)).
Qed.

Lemma is_lim_seq_bounded (x : nat -> R) (c:R) : is_lim_seq x c -> bounded x.
Proof.
  intros Hx.
  rewrite <- is_lim_seq_spec in Hx.
  unfold is_lim_seq' in Hx.
  destruct (Hx posreal_one).
  destruct (fin_seq_bounded x x0).
  exists (Rmax x1 ((Rabs c)+1)); intros.
  destruct (lt_dec n x0).
  - eapply Rle_trans.
    + apply H0; lia.
    + apply Rmax_l.
  - left.
    assert (x0 <= n)%nat by lia.
    specialize (H n H1).
    generalize (Rabs_triang_inv (x n) c); intros.
    apply Rlt_le_trans with (r2 := (Rabs c)+1); [|apply Rmax_r].
    simpl in H.
    lra.
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

Global Instance Lim_seq_proper:
  Proper (pointwise_relation _ eq ==> eq) (Lim_seq).
Proof.
  unfold Proper, pointwise_relation, respectful; intros.
  now apply Lim_seq_ext.
Qed.

Check ex_lim_seq.

Global Instance ex_lim_seq_proper:
  Proper (pointwise_relation _ eq ==> iff) (ex_lim_seq).
Proof.
  unfold Proper,pointwise_relation, respectful; intros.
  split; intros.
  + eapply ex_lim_seq_ext; eauto.
  + symmetry in H. eapply ex_lim_seq_ext; eauto.
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

Lemma Rbar_minus_eq_zero_iff ( x y : Rbar ): Rbar_minus x y = 0 <-> x = y.
Proof.
  split; intros; try (subst; now apply Rbar_minus_eq_0).
  destruct x; destruct y; (simpl in H; try congruence).
  rewrite Rbar_finite_eq.
  rewrite Rbar_finite_eq in H.
  lra.
Qed.

Lemma is_lim_seq_seq_minus_1 {a b : nat -> R} (a0 : R)
      (ha : is_lim_seq a a0) (hb : is_lim_seq b 1) : is_lim_seq (fun j => a j - b j * a0) 0.
Proof.
  unfold Rminus.
  replace 0 with (a0 - 1*a0) by lra.
  apply is_lim_seq_minus'; trivial.
  apply (is_lim_seq_scal_r b a0 1 hb).
Qed.

Lemma ash_6_1_1_b {x : nat -> R}{a : nat -> nat -> R} (ha1 : forall j, is_lim_seq (fun n => (a n j)) 0)
      (hb1 : forall n, ex_series(fun j => Rabs(a n j)))
      (hb2 : exists c, forall n, Series (fun j => Rabs (a n j)) < c)
      (hx1 : bounded x) (x0 : R) (hx2 : is_lim_seq x x0)
      (ha2 : is_lim_seq (fun n => Series (fun j => a n j)) 1) :
    let y := fun n => Series (fun j => (a n j)*(x j)) in is_lim_seq y x0.
Proof.
  intros y. unfold y.
  destruct hx1 as [M HM].
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
  assert (hxx : is_lim_seq (fun j => x j - x0) 0).
  {
    replace 0 with (x0 - x0) by lra.
    apply is_lim_seq_minus'; auto.
    apply is_lim_seq_const.
  }
  generalize (ash_6_1_1_a ha1 hb1 hb2 (is_lim_seq_bounded _ 0 hxx) hxx); intros.
  unfold y in H.
  setoid_rewrite Rmult_minus_distr_l in H.
  apply is_lim_seq_ext with (v := fun n => Series(fun j => a n j * x j) - Series(fun j => a n j * x0)) in H.
  + setoid_rewrite Series_scal_r in H.
    apply is_lim_seq_plus with (l := x0) (l1 := x0) (u := fun n => Series (a n)*x0) in H.
    -- setoid_rewrite Rplus_comm in H.
       setoid_rewrite Rplus_assoc in H.
      setoid_rewrite Rplus_opp_l in H.
      now setoid_rewrite Rplus_0_r in H.
    --
      generalize (is_lim_seq_scal_r _ x0 _ ha2); intros.
      simpl in H0. now rewrite Rmult_1_l in H0.
    -- unfold is_Rbar_plus.
       simpl. f_equal. rewrite Rbar_finite_eq.
       lra.
  + intros n.
    apply Series_minus.
    ** apply ex_series_Rabs.
       apply (ex_series_le (fun j => Rabs (a n j * x j)) (fun j => M*Rabs(a n j))); trivial.
       intros. rewrite Rabs_Rabsolu; auto.
    ** apply ex_series_scal_r. now apply ex_series_Rabs.
Qed.

(*
Lemma series_partial_sums_bounded (a : nat -> nat -> R) :
  (exists c, forall n, sum_n (fun j => Rabs (a n j)) n <= c) ->
  exists c, forall n,
      ex_series (fun j => Rabs (a n j)) /\
      Series (fun j => Rabs (a n j)) <= c.
Proof.
  intros.
  destruct H as [c ?].
  exists c; intros.
  split.
  - rewrite <- ex_finite_lim_series.
    rewrite ex_finite_lim_seq_correct.
    split.
    + apply ex_lim_seq_incr.
      intros.
      rewrite sum_Sn.
      unfold plus; simpl.
      apply Rplus_le_pos_l.
      apply Rabs_pos.
    + 
*)      
  
Lemma sum_n_sum_f_clipped (f : nat -> R) (N : nat) :
  forall (n:nat), 
    (n >= N)%nat ->
    sum_f_R0 f N = sum_n (fun j => if (le_dec j N) then (f j) else 0) n.
Proof.
  intros.
  Admitted.

(* Toeplitz lemma. *)
Lemma ash_6_1_2  {a x : nat -> R} {x0 : R}(ha : forall n, 0 <= a n)
      (hb1 : forall n, 0 < sum_f_R0 a n)(hb2 : is_lim_seq (sum_f_R0 a) p_infty)  (hx : is_lim_seq x x0):
  is_lim_seq (fun n => (sum_f_R0 (fun j => a j * x j) n)/(sum_f_R0 a n)) x0.
  Proof.
    pose (A := fun (n j : nat) => if (le_dec j  n) then (a j)/(sum_f_R0 a n) else 0).
    assert (Apos: forall n j, 0 <= A n j).
    {
      intros.
      unfold A.
      match_destr; [|lra].
      unfold Rdiv.
      apply Rmult_le_pos; trivial.
      left.
      now apply Rinv_0_lt_compat.
    }
    assert (Aser: forall n, is_series (fun j => A n j) 1).
    {
      intros.
      unfold A.
      rewrite <-series_is_lim_seq.
      apply is_lim_seq_ext_loc with (u := fun n => 1); [|apply is_lim_seq_const].
      exists n.
      intros.
      rewrite <- sum_n_sum_f_clipped with (N := n); try lia.
      unfold Rdiv.
      rewrite <- scal_sum.
      apply Rinv_l_sym.
      apply Rgt_not_eq.
      apply hb1.
    }
    apply is_lim_seq_ext with 
        (u := fun n => Series (fun j => (A n j) * x j)).
    - intros.
      unfold Series.
      unfold A.
      rewrite Lim_seq_ext_loc with
          (v := fun _ => sum_f_R0 (fun j : nat => a j * x j) n / sum_f_R0 a n).
      + now rewrite Lim_seq_const.
      + exists n; intros.
        rewrite sum_n_ext with
            (b := (fun j : nat => (if le_dec j n then (((a j)*(x j)) / sum_f_R0 a n) else 0))).
        * rewrite <- sum_n_sum_f_clipped with (N := n); try lia.
          unfold Rdiv.
          rewrite <- scal_sum.
          now rewrite Rmult_comm at 1.
        * intros.
          match_destr; lra.
    - apply ash_6_1_1_b; trivial.
      + intros.
        unfold A.
        apply is_lim_seq_ext_loc with (u := fun n => a j / sum_f_R0 a n).
        * exists j.
          intros.
          match_destr; tauto.
        * apply is_lim_seq_div with (l1 := a j) (l2 := p_infty); trivial.
          -- apply is_lim_seq_const.
          -- discriminate.
          -- unfold is_Rbar_div; simpl.
             unfold is_Rbar_mult; simpl.
             now rewrite Rmult_0_r.
     + intros.
       apply ex_series_ext with (a0 := fun j => A n j).
       * intros.
         rewrite Rabs_right; trivial.
         specialize (Apos n n0); lra.
       * now exists 1.
     + exists 2.
       intros.
       specialize (Aser n).
       apply is_series_unique in Aser.
       rewrite Series_ext with (b := (fun j => A n j)); [rewrite Aser;lra|].
       intros.
       rewrite Rabs_right; trivial.
       specialize (Apos n n0); lra.
     + now apply is_lim_seq_bounded with (c := x0).
     + apply is_lim_seq_ext with ( u := fun n => 1); [|apply is_lim_seq_const].
       intros.
       specialize (Aser n).
       apply is_series_unique in Aser; now symmetry.
   Qed.


(* Kronecker Lemma *)
Lemma ash_6_1_3 {b x : nat -> R} (hb1 : forall n, 0 < b n < b (S n)) (hb2 : is_lim_seq b p_infty)
      (hx : ex_series x):
  is_lim_seq (fun n => (sum_f_R0 (fun j => b j * x j) n)/(b n)) 0.
Admitted.
