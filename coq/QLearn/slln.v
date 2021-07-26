Require Import Lra Lia Reals RealAdd RandomVariableL2 Coquelicot.Coquelicot.
Require Import Morphisms Finite List ListAdd.
Require Import Sums SimpleExpectation.
Require Import EquivDec.

Set Bullet Behavior "Strict Subproofs".
Set Default Goal Selector "!".

Import ListNotations.

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

(* Move these instances to RealAdd. *)
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
    -- generalize (is_lim_seq_scal_r _ x0 _ ha2); intros.
       simpl in H0. now rewrite Rmult_1_l in H0.
    -- unfold is_Rbar_plus.
       simpl. f_equal. rewrite Rbar_finite_eq.
       lra.
  + intros n.
    apply Series_minus.
    ** now apply ex_series_Rabs.
    ** apply ex_series_scal_r. now apply ex_series_Rabs.
Qed.

Lemma Lim_seq_partial_sums_bounded (a : nat -> nat -> R) :
  (exists (c:R), forall n n0, sum_n (fun j => Rabs (a n j)) n0 <= c) ->
  exists (c:R), forall n,
      ex_series (fun j => Rabs (a n j)) /\
      Rbar_le (Lim_seq (sum_n (fun j => Rabs (a n j)))) c.
Proof.
  intros.
  destruct H as [c ?].
  exists c; intros.
  unfold Series.
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
    + apply is_finite_Lim_bounded with (m := 0) (M := c).
      intros.
      split.
      * apply sum_n_nneg.
        intros.
        apply Rabs_pos.
      * apply H.
  - replace (Rbar.Finite c) with (Lim_seq (fun _ => c)) by apply Lim_seq_const.
    apply Lim_seq_le_loc.
    exists (0%nat).
    now intros.
 Qed.
    
Lemma Series_partial_sums_bounded (a : nat -> nat -> R) :
  (exists (c:R), forall n n0, sum_n (fun j => Rabs (a n j)) n0 <= c) ->
  exists (c:R), forall n,
      ex_series (fun j => Rabs (a n j)) /\
      Series (fun j => Rabs (a n j)) < c.
Proof.
  intros.
  destruct (Lim_seq_partial_sums_bounded _ H) as [c ?].
  exists (c+1); intros.
  destruct (H0 n).
  split; trivial.
  unfold Series.
  destruct (Lim_seq (sum_n (fun j : nat => Rabs (a n j)))).
  - simpl in H2.
    eapply Rle_lt_trans.
    + apply H2.
    + lra.
  - now simpl in H2.
  - simpl.
    destruct (H0 n).
    generalize (Lim_seq_pos (sum_n (fun j : nat => Rabs (a n j)))); intros.
    cut_to H5.
    + generalize (Rbar_le_trans _ _ _ H5 H4); intros.
      simpl in H6.
      eapply Rle_lt_trans.
      * apply H6.
      * lra.
    + intros.
      apply sum_n_nneg; intros.
      apply Rabs_pos.
 Qed.
    
Lemma sum_n_sum_f_clipped (f : nat -> R) (N : nat) :
  forall (n:nat), 
    (n >= N)%nat ->
    sum_n f N = sum_n (fun j => if (le_dec j N) then (f j) else 0) n.
Proof.
  intros.
  replace (n) with (N + (n - N))%nat by lia.
  induction (n-N)%nat.
  - replace (N + 0)%nat with N by lia.
    apply sum_n_ext_loc.
    intros.
    match_destr; tauto.
  - replace (N + S n0)%nat with (S (N + n0))%nat by lia.
    rewrite sum_Sn.
    match_destr.
    + assert ( S N <= S (N + n0))%nat by lia.
      lia.
    + unfold plus; simpl.
      now rewrite Rplus_0_r.
  Qed.
(*rewrite <- sum_n_Reals.*)

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
      rewrite sum_n_Reals.
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
          rewrite sum_n_Reals.
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
Lemma ash_6_1_3 {b x : nat -> R} (hb0: b (0%nat) = 0) (hb1 : forall n, 0 < b (S n) < b (S (S n))) (hb2 : is_lim_seq b p_infty)
      (hx : ex_series x):
  is_lim_seq (fun n => (sum_f_R0 (fun j => b j * x j) (S n))/(b (S n))) 0.
Proof.
  pose (s := sum_f_R0 x).
  assert (forall n, sum_f_R0 (fun j => b j * x j) (S n) = 
                    (b (S n))*(s (S n)) - sum_f_R0 (fun j => (s j) * ((b (S j)) - (b j))) n).
  {
    intros.
    induction n.
    - unfold s; simpl.
      ring_simplify; lra.
    - replace (S (S n)) with (S (n+1)) by lia.
      simpl.
      replace (n+1)%nat with (S n) by lia.
      rewrite IHn.
      apply Rplus_eq_reg_r with (r := sum_f_R0 (fun j : nat => s j * (b (S j) - b j)) n).
      ring_simplify.
      apply Rplus_eq_reg_r with (r := - (b (S n) * s (S n))).
      ring_simplify.
      unfold s.
      replace (S n) with (n+1)%nat by lia.
      simpl.
      now ring_simplify.
   }.
  assert (forall n, b (S n) <> 0).
  {
    intros.
    apply Rgt_not_eq.
    apply hb1.
  }
  assert (forall n,
             (s (S n)) - (sum_f_R0 (fun j : nat => s j * (b (S j) - b j)) n)/(b (S n)) = 
             (sum_f_R0 (fun j : nat => b j * x j) (S n))/(b (S n))).

  {
    intros.
    symmetry.
    unfold Rdiv.
    replace (s (S n)) with ((b (S n) * s (S n)) * / b (S n)).
    - rewrite <- Rmult_minus_distr_r.
      now apply Rmult_eq_compat_r.
    - now field_simplify.
  }
  assert (bser: forall n, b (S n) - b (0%nat) = sum_f_R0 (fun j : nat => b (S j) - b j) n).
  {
    induction n.
    - now simpl.
    - simpl.
      rewrite <- IHn.
      lra.
  }
  destruct hx.
  apply (is_lim_seq_ext _ _ _ H1).
  rewrite <- series_is_lim_seq in H2.
  apply is_lim_seq_ext with (v := s) in H2.
  - apply is_lim_seq_minus with (l1 := x0) (l2 := x0).
    + now rewrite is_lim_seq_incr_1 in H2.
    + generalize (@ash_6_1_2 (fun j => b (S j) - b j) s x0); intros.
      cut_to H3; trivial.
      * eapply (is_lim_seq_ext _ _ x0 _ H3).
      * intros.
        destruct (lt_dec 0 n).
        -- specialize (hb1 (n-1)%nat).
           replace (S (n-1)) with (n) in hb1 by lia.
           lra.
        -- assert (n = 0%nat) by lia.
           rewrite H4.
           rewrite hb0.
           rewrite Rminus_0_r.
           left; apply hb1.
      * intros.
        rewrite <- sum_n_Reals.
        apply sum_n_pos.
        intros.
        destruct (lt_dec 0 n0).
        -- specialize (hb1 (n0-1)%nat).
           replace (S (n0-1)) with (n0) in hb1 by lia.
           lra.
        -- assert (n0 = 0%nat) by lia.
           rewrite H5.
           rewrite hb0.
           rewrite Rminus_0_r.
           apply hb1.
      * apply (is_lim_seq_ext _ _ _ bser).
        apply is_lim_seq_minus with (l1 := p_infty) (l2 := b (0%nat)).
        -- now apply is_lim_seq_incr_1 in hb2.
        -- apply is_lim_seq_const.
        -- red; simpl.
           now red; simpl.
    + red; simpl.
      red; simpl.
      now rewrite Rplus_opp_r.
  - unfold s.
    intros.
    now rewrite sum_n_Reals.
    Unshelve.
    intros.
    simpl.
    specialize (bser n).
    rewrite <- bser.
    rewrite hb0.
    rewrite Rminus_0_r.
    f_equal.
    apply sum_f_R0_ext.
    intros.
    now rewrite Rmult_comm.
 Qed.

Context {Ts:Type} {dom: SigmaAlgebra Ts}{Prts: ProbSpace dom}.

Global Instance frfsum (X : nat -> Ts -> R)
       {rv : forall (n:nat), FiniteRangeFunction (X n)} (n : nat) :
  FiniteRangeFunction (rvsum X n).
Proof.
  induction n.
  - assert (rv_eq  (rvsum X 0) (X 0%nat)).
    + intro x.
      unfold rvsum. cbn.
      lra.
    + eapply FiniteRangeFunction_ext.
      * symmetry; apply H.
      * apply rv.
  - assert (rv_eq (rvsum X (S n)) (rvplus (X (S n)) (rvsum X n))).
    + intro x.
      unfold rvplus, rvsum.
      rewrite sum_Sn; unfold plus; simpl.
      lra.
    + eapply FiniteRangeFunction_ext.
      * rewrite H; reflexivity.
      * apply frfplus; trivial.
Qed.

Global Instance frfite (X Y : Ts -> R){p : Prop}(dec : {p} + {~ p})
       {rv_X : FiniteRangeFunction X} {rv_Y : FiniteRangeFunction Y} :
  FiniteRangeFunction (if dec then X else Y).
Proof.
  match_destr.
Qed.

Definition rvmaxlist (X : nat -> Ts -> R) (N : nat) : Ts -> R :=
  fun (omega : Ts) => Rmax_list (List.map (fun n => X n omega) (List.seq 0 (S N))).

Lemma seq_not_nil : forall n, (0 < n)%nat  -> [] <> seq 0 n.
Proof.
  induction n; simpl; intuition.
  generalize (nil_cons H0); trivial.
Qed.

(* Move this to RealAdd. *)
Lemma Rmax_list_app {A} {l : list A} (a : A) (f : A -> R) (hl : [] <> l) :
  Rmax_list (map f (l ++ [a])) = Rmax (Rmax_list (map f l)) (f a).
Proof.
  rewrite map_app.
  simpl.
  assert (Rmax (Rmax_list (map f l)) (f a) = Rmax_list ((f a) :: (map f l))).
  {
    simpl. rewrite <-map_not_nil with (f0 := f) in hl.
    match_destr; intuition.
    apply Rmax_comm.
  }
  rewrite H.
  now rewrite <-Permutation.Permutation_cons_append.
Qed.

Lemma rvmaxlist_monotone (X : nat -> Ts -> R) :
  forall n omega, rvmaxlist X n omega <= rvmaxlist X (S n) omega.
Proof.
  intros n omega.
  unfold rvmaxlist.
  assert (seq 0 (S (S n)) = seq 0 (S n) ++ [S n]).
  {
    generalize (S n); intros n0.
    rewrite seq_S.
    f_equal.
  }
  rewrite H.
  rewrite Rmax_list_app.
  + apply Rmax_l.
  + apply seq_not_nil; lia.
Qed.


Global Instance frfrvmaxlist (X : nat -> Ts -> R)
       {rv : forall n, FiniteRangeFunction (X n)} (N : nat):
  FiniteRangeFunction (rvmaxlist X N).
Proof.
  unfold rvmaxlist.
  generalize (0%nat).
  induction N; simpl; intros s.
  - apply rv.
  - assert (frf:FiniteRangeFunction (fun omega => Rmax (X s omega) (Rmax_list (map (fun n : nat => X n omega) (seq (S s) (S N)))))).
    {
      apply frfmax; auto.
    }
    destruct N.
    + simpl; auto.
    + eapply FiniteRangeFunction_ext; try eapply frf.
      intros ?.
      reflexivity.
Qed.

Global Instance rvmaxlist_rv (X : nat -> Ts -> R)
       {rv : forall n, RandomVariable dom borel_sa (X n)} (N : nat):
  RandomVariable dom borel_sa (rvmaxlist X N).
Proof.
   unfold rvmaxlist.
  generalize (0%nat).
  induction N; simpl; intros s.
  - apply rv.
  - assert (frf:RandomVariable dom borel_sa (fun omega => Rmax (X s omega) (Rmax_list (map (fun n : nat => X n omega) (seq (S s) (S N)))))).
    {
      apply rvmax_rv; auto.
    }
    destruct N.
    + simpl; auto.
    + eapply RandomVariable_proper; try eapply frf.
      intros ?.
      reflexivity.
Qed.

Fixpoint filtration_history (n : nat) (X : nat -> Ts -> R)
         {frf : forall n, FiniteRangeFunction (X n)}
         {rv : forall n, RandomVariable dom borel_sa (X n)}
  : list dec_sa_event :=
  match n with
  | 0 => []
  | S k => refine_dec_sa_partitions (induced_sigma_generators (frf k)) (filtration_history k X)
  end.

Lemma sublist_seq_le :
  forall n k, (n <= k)%nat -> sublist (seq 0 n) (seq 0 k).
Proof.
  intros n k Hnk.
  induction Hnk; intuition.
  replace (seq 0 (S m)) with (seq 0 m ++ [m]).
  + rewrite <-app_nil_r with (l := seq 0 n).
    apply sublist_app; trivial.
    apply sublist_nil_l.
  + replace (S m) with (m + 1)%nat by lia.
    rewrite seq_app.
    f_equal.
Qed.

Lemma Rmax_list_sublist_le {A : Type}(f : A -> R):
  forall l1 l2 : list A, ([] <> l1) -> sublist l1 l2 -> Rmax_list_map l1 f <= Rmax_list_map l2 f.
Proof.
  intros l1 l2 Hl1 Hl2.
  generalize (sublist_In Hl2); intros.
  unfold Rmax_list_map.
  apply Rmax_spec.
  rewrite in_map_iff.
  rewrite  <-(map_not_nil) with (f0 := f) (l := l1) in Hl1.
  generalize (Rmax_list_In _ Hl1); intros .
  rewrite in_map_iff in H0.
  destruct H0 as [x [Hx1 Hx2]].
  exists x; split; trivial; auto.
Qed.

Lemma Rmax_seq_map_monotone (X : nat -> R):
  forall n k, (0 < n <= k)%nat  -> Rmax_list_map (seq 0 n) X <= Rmax_list_map (seq 0 k) X.
Proof.
  intros n k Hnk.
  apply Rmax_list_sublist_le.
  + apply seq_not_nil; now destruct Hnk.
  + apply sublist_seq_le. destruct Hnk; lia.
Qed.

(* Few properties about cutoff sequences. Move to RealAdd. *)
Fixpoint cutoff_eps (n : nat) (eps : R) (X : nat -> R) :=
  match n with
  | 0 => X 0%nat
  | S k => if (Rlt_dec (Rmax_list_map (seq 0 (S k)) X) eps) then X (S k)
                    else (cutoff_eps k eps X)
  end.

Lemma cutoff_eps_lt_eps eps n (X : nat -> R) :
   (forall k, (k <= n)%nat -> X k < eps) -> (cutoff_eps n eps X = X n).
Proof.
  intros H.
  induction n.
  + now simpl.
  + simpl.
    match_destr.
    assert (H1 : Rmax_list_map (seq 0 (S n)) X < eps).
    {
      unfold Rmax_list_map.
      rewrite Rmax_list_lt_iff; try (apply map_not_nil; apply seq_not_nil; lia).
      intros.
      rewrite in_map_iff in H0.
      destruct H0 as [x0 [Hx0 Hx1]].
      subst; auto. apply H.
      rewrite in_seq in Hx1. destruct Hx1.
      intuition.
    }
    exfalso; firstorder.
Qed.

Lemma cutoff_eps_ge_eps eps (X : nat -> R) :
   (forall k:nat, eps <= X k) -> (forall n, cutoff_eps n eps X = X 0%nat).
Proof.
  intros H n.
  simpl.
  induction n.
  ++ now simpl in H.
  ++ simpl. match_destr.
     assert (X n <= Rmax_list_map (0%nat :: seq 1 n) X).
     {
       unfold Rmax_list_map.
       apply Rmax_spec.
       rewrite in_map_iff.
       exists n; split; trivial.
       replace (0%nat :: seq 1 (n)) with (seq 0%nat (S n)) by (now simpl).
       rewrite in_seq; lia.
     }
     specialize (H n).
     lra.
Qed.

Lemma ne_le_succ {k n : nat} (hk1 : k <> S n) (hk2 : (k <= S n)%nat) : (k <= n)%nat.
Proof.
  lia.
Qed.

Lemma Rmax_list_map_seq_ge (eps : R) {n : nat} (X : nat -> R):
  (0<n)%nat -> eps <= Rmax_list_map (seq 0 n) X <-> (exists k, (k < n)%nat /\ eps <= X k).
Proof.
  intros Hn.
  split; intros Heps.
  + unfold Rmax_list_map in Heps.
    generalize (Rmax_list_map_exist X (seq 0%nat n)); intros.
    generalize (seq_not_nil n Hn); intros.
    specialize (H H0).
    destruct H as [k [Hin Heq]].
    exists k; intros.
    rewrite <-Heq in Heps.
    split; trivial.
    rewrite in_seq in Hin; now destruct Hin.
  + destruct Heps as [k1 [Hk1 Heps1]].
    eapply Rle_trans; eauto.
    unfold Rmax_list_map.
    apply Rmax_spec. rewrite in_map_iff.
    exists k1; split; trivial.
    rewrite in_seq; split; lia.
Qed.

Lemma Rmax_list_map_seq_lt (eps : R) {n : nat} (X : nat -> R):
 (0 < n)%nat -> Rmax_list (map X (seq 0 n)) < eps <-> (forall k, (k < n)%nat -> X k < eps).
Proof.
  intros Hn. split.
  + intros Heps k Hk.
    rewrite Rmax_list_lt_iff in Heps; try (apply map_not_nil; now apply seq_not_nil).
    apply Heps.
    rewrite in_map_iff.
    exists k; split; trivial.
    rewrite in_seq; lia.
  + intros Heps.
    rewrite Rmax_list_lt_iff; try (apply map_not_nil; now apply seq_not_nil).
    intros x Hx. rewrite in_map_iff in Hx.
    destruct Hx as [k [Hk1 Hk2]].
    rewrite <-Hk1. apply Heps.
    rewrite in_seq in Hk2. now destruct Hk2.
Qed.

Lemma cutoff_ge_eps_exists  (n : nat) (eps : R) ( X : nat -> R ):
  (eps <= cutoff_eps n eps X) -> exists k, (k <= n)%nat /\ eps <= X k.
Proof.
  intros Hn.
  induction n.
  -- simpl in Hn. exists 0%nat.
     split; trivial; lra.
  -- simpl in Hn.
     match_destr_in Hn.
     ++  exists (S n). split; trivial; lra.
     ++ apply Rnot_lt_ge in n0.
        specialize (IHn Hn).
        destruct IHn as [k Hk].
        exists k. destruct Hk. split; trivial.
        etransitivity; eauto; lia.
Qed.

Lemma cutoff_ge_eps_exists_contrapose (n : nat) (eps : R) (X : nat -> R):
   (cutoff_eps n eps X < eps) -> (forall k, (k <= n)%nat -> X k < eps).
Proof.
  intros Heps.
  induction n.
  + simpl in Heps. intros.
    assert (k = 0%nat) by lia; subst; trivial.
  + simpl in Heps.
    match_destr_in Heps.
    ++ intros. destruct (k == S n).
       -- now rewrite e.
       -- apply IHn; try(apply ne_le_succ; eauto).
          unfold Rmax_list_map in r.
          replace (0%nat :: seq 1 n) with (seq 0%nat (S n)) in r by (now simpl).
          rewrite Rmax_list_lt_iff in r; try (apply map_not_nil; apply seq_not_nil; lia).
          rewrite cutoff_eps_lt_eps; intros; try (apply r; rewrite in_map_iff).
          ** exists n; split; trivial. rewrite in_seq; lia.
          ** exists k0; split; trivial. rewrite in_seq; lia.
    ++ intros. specialize (IHn Heps).
       apply Rnot_lt_ge in n0.
       replace (0%nat :: seq 1 n) with (seq 0%nat (S n)) in n0 by (now simpl).
       unfold Rmax_list_map in n0.
       assert ((0 < S n)%nat) by lia.
       apply Rge_le in n0.
       rewrite (Rmax_list_map_seq_ge eps X H0) in n0.
       destruct n0 as [k1 [Hk1 Heps1]].
       assert (k1 <= n)%nat by lia.
       specialize (IHn k1 H1).
       exfalso; lra.
Qed.

Lemma cutoff_ge_eps_exists_iff (n : nat) (eps : R) (X : nat -> R):
  (eps <= cutoff_eps n eps X) <-> exists k, (k <= n)%nat /\ eps <= X k.
Proof.
  split.
  + apply cutoff_ge_eps_exists.
  + intro H. apply ROrderedType.ROrder.not_gt_le.
    revert H. apply ssrbool.contraPnot.
    intro H. generalize (cutoff_ge_eps_exists_contrapose n eps X H); intros.
    apply Classical_Pred_Type.all_not_not_ex.
    intros k. specialize (H0 k).
    apply Classical_Prop.or_not_and.
    apply Classical_Prop.imply_to_or; intros.
    specialize (H0 H1).  apply Rgt_not_le; trivial.
Qed.

Lemma cutoff_ge_eps_Rmax_list_iff (n : nat) (eps : R) (X : nat -> R):
  (eps <= cutoff_eps n eps X) <-> eps <= Rmax_list_map (seq 0 (S n)) X.
Proof.
  assert (Hn : (0 < S n)%nat) by lia.
  rewrite (Rmax_list_map_seq_ge eps X Hn).
  rewrite cutoff_ge_eps_exists_iff.
  split; intros; destruct H as [x [Hx1 Hx2]]; exists x; split; trivial; lia.
Qed.


Definition cutoff_eps_rv (n : nat) (eps : R) (X : nat -> Ts -> R) :=
  fun omega => cutoff_eps n eps (fun k => X k omega).


Lemma rvmaxlist_ge (X : nat -> Ts -> R): forall n omega, X n omega <= rvmaxlist X n omega.
Proof.
  intros.
  unfold rvmaxlist.
  apply Rmax_spec.
  rewrite in_map_iff.
  exists n; split; trivial.
  rewrite in_seq; lia.
Qed.


Lemma cutoff_eps_rv_lt_eps eps (X : nat -> Ts -> R) : forall omega,
   (forall k, X k omega < eps) -> (forall n, cutoff_eps_rv n eps X omega = X n omega).
Proof.
  intros omega H n.
  unfold cutoff_eps_rv.
  now apply cutoff_eps_lt_eps.
Qed.

Lemma cutoff_eps_rv_ge_eps eps (X : nat -> Ts -> R) : forall omega,
   (forall k:nat, eps <= X k omega) -> (forall n, cutoff_eps_rv n eps X omega = X 0%nat omega).
Proof.
  intros omega H n.
  unfold cutoff_eps_rv.
  now apply cutoff_eps_ge_eps.
Qed.



Lemma ash_6_1_4 (X : nat -> Ts -> R)(n : nat)
      {rv : forall (n:nat), RandomVariable dom borel_sa (X n)}
      {frf : forall (n:nat), FiniteRangeFunction (X n)}
      (HC : forall n, 
          SimpleConditionalExpectationSA (X n) (filtration_history n X) = const 0)  :
  let S := fun j => rvabs (rvsum X j) in
  forall eps:posreal, ps_P (event_ge dom (rvmaxlist S n) eps) <=
           (SimpleExpectation (rvsqr (S n)))/eps^2.
Admitted.
